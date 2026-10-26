import V185TrunkScan23Chunk1051

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_6228214 : List Nat := [5, 1, 1, 1, 1, 1, 3, 1, 1, 1, 7]
def baseStart_6228214 : Nat := 118140960795 + 6228214 * 2 ^ 59
def prefixEnd_6228214 : Nat := 4983230072969 + 3 ^ 40 * 6228214 * 2
def baseEnd_6228214 : Nat := 3198067401061800317781971

theorem tailTrace_6228214 : CollatzResearch.WordTrace tailWord_6228214 prefixEnd_6228214 3198067401061800317781971 := by
  unfold tailWord_6228214
  simp only [CollatzResearch.WordTrace]
  refine ⟨14197601666140740444455231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 151441084438834564740855797 14197601666140740444455231)
  ·
    refine ⟨21296402499211110666682847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14197601666140740444455231 21296402499211110666682847)
    ·
      refine ⟨31944603748816666000024271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21296402499211110666682847 31944603748816666000024271)
      ·
        refine ⟨47916905623224999000036407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31944603748816666000024271 47916905623224999000036407)
        ·
          refine ⟨71875358434837498500054611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47916905623224999000036407 71875358434837498500054611)
          ·
            refine ⟨107813037652256247750081917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71875358434837498500054611 107813037652256247750081917)
            ·
              refine ⟨40429889119596092906280719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 107813037652256247750081917 40429889119596092906280719)
              ·
                refine ⟨60644833679394139359421079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40429889119596092906280719 60644833679394139359421079)
                ·
                  refine ⟨90967250519091209039131619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 60644833679394139359421079 90967250519091209039131619)
                  ·
                    refine ⟨136450875778636813558697429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 90967250519091209039131619 136450875778636813558697429)
                    ·
                      refine ⟨3198067401061800317781971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 136450875778636813558697429 3198067401061800317781971)
                      ·
                        rfl

theorem cell23_6228214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 3, 1, 1, 1, 7].length) (baseStart_6228214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6228214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6228214 prefixEnd_6228214 := by exact prefixLift 6228214
  have htrace : WordTrace (prefixWord ++ tailWord_6228214) baseStart_6228214 baseEnd_6228214 := by
    simpa [prefixWord, tailWord_6228214, baseEnd_6228214] using wordTrace_append hprefix tailTrace_6228214
  have hstable : (prefixWord ++ tailWord_6228214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6228214).length < 2 ^ (prefixWord ++ tailWord_6228214).sum := by decide
  have hdescent : baseEnd_6228214 < baseStart_6228214 := by decide
  rcases family_descends (prefixWord ++ tailWord_6228214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6228217 : List Nat := [1, 2, 1, 3, 1, 1, 2, 2, 2, 8]
def baseStart_6228217 : Nat := 118140960795 + 6228217 * 2 ^ 59
def prefixEnd_6228217 : Nat := 4983230072969 + 3 ^ 40 * 6228217 * 2
def baseEnd_6228217 : Nat := 1066022980501254602014819

theorem tailTrace_6228217 : CollatzResearch.WordTrace tailWord_6228217 prefixEnd_6228217 1066022980501254602014819 := by
  unfold tailWord_6228217
  simp only [CollatzResearch.WordTrace]
  refine ⟨227161736077240978623642905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151441157384827319082428603 227161736077240978623642905)
  ·
    refine ⟨170371302057930733967732179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 227161736077240978623642905 170371302057930733967732179)
    ·
      refine ⟨255556953086896100951598269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170371302057930733967732179 255556953086896100951598269)
      ·
        refine ⟨95833857407586037856849351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 255556953086896100951598269 95833857407586037856849351)
        ·
          refine ⟨143750786111379056785274027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95833857407586037856849351 143750786111379056785274027)
          ·
            refine ⟨215626179167068585177911041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 143750786111379056785274027 215626179167068585177911041)
            ·
              refine ⟨161719634375301438883433281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 215626179167068585177911041 161719634375301438883433281)
              ·
                refine ⟨121289725781476079162574961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 161719634375301438883433281 121289725781476079162574961)
                ·
                  refine ⟨90967294336107059371931221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 121289725781476079162574961 90967294336107059371931221)
                  ·
                    refine ⟨1066022980501254602014819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 90967294336107059371931221 1066022980501254602014819)
                    ·
                      rfl

theorem cell23_6228217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 2, 2, 8].length) (baseStart_6228217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6228217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6228217 prefixEnd_6228217 := by exact prefixLift 6228217
  have htrace : WordTrace (prefixWord ++ tailWord_6228217) baseStart_6228217 baseEnd_6228217 := by
    simpa [prefixWord, tailWord_6228217, baseEnd_6228217] using wordTrace_append hprefix tailTrace_6228217
  have hstable : (prefixWord ++ tailWord_6228217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6228217).length < 2 ^ (prefixWord ++ tailWord_6228217).sum := by decide
  have hdescent : baseEnd_6228217 < baseStart_6228217 := by decide
  rcases family_descends (prefixWord ++ tailWord_6228217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6228241 : List Nat := [1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 4]
def baseStart_6228241 : Nat := 118140960795 + 6228241 * 2 ^ 59
def prefixEnd_6228241 : Nat := 4983230072969 + 3 ^ 40 * 6228241 * 2
def baseEnd_6228241 : Nat := 3198081265039471712144347

theorem tailTrace_6228241 : CollatzResearch.WordTrace tailWord_6228241 prefixEnd_6228241 3198081265039471712144347 := by
  unfold tailWord_6228241
  simp only [CollatzResearch.WordTrace]
  refine ⟨227162611429154030722516577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151441740952769353815011051 227162611429154030722516577)
  ·
    refine ⟨170371958571865523041887433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 227162611429154030722516577 170371958571865523041887433)
    ·
      refine ⟨127778968928899142281415575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 170371958571865523041887433 127778968928899142281415575)
      ·
        refine ⟨191668453393348713422123363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127778968928899142281415575 191668453393348713422123363)
        ·
          refine ⟨287502680090023070133185045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 191668453393348713422123363 287502680090023070133185045)
          ·
            refine ⟨13476688129219831412493049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 287502680090023070133185045 13476688129219831412493049)
            ·
              refine ⟨10107516096914873559369787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13476688129219831412493049 10107516096914873559369787)
              ·
                refine ⟨15161274145372310339054681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10107516096914873559369787 15161274145372310339054681)
                ·
                  refine ⟨11370955609029232754291011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15161274145372310339054681 11370955609029232754291011)
                  ·
                    refine ⟨17056433413543849131436517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11370955609029232754291011 17056433413543849131436517)
                    ·
                      refine ⟨3198081265039471712144347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17056433413543849131436517 3198081265039471712144347)
                      ·
                        rfl

theorem cell23_6228241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 4].length) (baseStart_6228241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6228241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6228241 prefixEnd_6228241 := by exact prefixLift 6228241
  have htrace : WordTrace (prefixWord ++ tailWord_6228241) baseStart_6228241 baseEnd_6228241 := by
    simpa [prefixWord, tailWord_6228241, baseEnd_6228241] using wordTrace_append hprefix tailTrace_6228241
  have hstable : (prefixWord ++ tailWord_6228241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6228241).length < 2 ^ (prefixWord ++ tailWord_6228241).sum := by decide
  have hdescent : baseEnd_6228241 < baseStart_6228241 := by decide
  rcases family_descends (prefixWord ++ tailWord_6228241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6228281 : List Nat := [1, 2, 1, 6, 1, 1, 2, 3, 6]
def baseStart_6228281 : Nat := 118140960795 + 6228281 * 2 ^ 59
def prefixEnd_6228281 : Nat := 4983230072969 + 3 ^ 40 * 6228281 * 2
def baseEnd_6228281 : Nat := 355344644918405728404907

theorem tailTrace_6228281 : CollatzResearch.WordTrace tailWord_6228281 prefixEnd_6228281 355344644918405728404907 := by
  unfold tailWord_6228281
  simp only [CollatzResearch.WordTrace]
  refine ⟨227164070349009117553972697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151442713566006078369315131 227164070349009117553972697)
  ·
    refine ⟨170373052761756838165479523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 227164070349009117553972697 170373052761756838165479523)
    ·
      refine ⟨255559579142635257248219285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170373052761756838165479523 255559579142635257248219285)
      ·
        refine ⟨11979355272311027683510279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 255559579142635257248219285 11979355272311027683510279)
        ·
          refine ⟨17969032908466541525265419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11979355272311027683510279 17969032908466541525265419)
          ·
            refine ⟨26953549362699812287898129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17969032908466541525265419 26953549362699812287898129)
            ·
              refine ⟨20215162022024859215923597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26953549362699812287898129 20215162022024859215923597)
              ·
                refine ⟨7580685758259322205971349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20215162022024859215923597 7580685758259322205971349)
                ·
                  refine ⟨355344644918405728404907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7580685758259322205971349 355344644918405728404907)
                  ·
                    rfl

theorem cell23_6228281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 2, 3, 6].length) (baseStart_6228281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6228281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6228281 prefixEnd_6228281 := by exact prefixLift 6228281
  have htrace : WordTrace (prefixWord ++ tailWord_6228281) baseStart_6228281 baseEnd_6228281 := by
    simpa [prefixWord, tailWord_6228281, baseEnd_6228281] using wordTrace_append hprefix tailTrace_6228281
  have hstable : (prefixWord ++ tailWord_6228281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6228281).length < 2 ^ (prefixWord ++ tailWord_6228281).sum := by decide
  have hdescent : baseEnd_6228281 < baseStart_6228281 := by decide
  rcases family_descends (prefixWord ++ tailWord_6228281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6228291 : List Nat := [1, 1, 1, 3, 1, 3, 3, 1, 5, 1, 3]
def baseStart_6228291 : Nat := 118140960795 + 6228291 * 2 ^ 59
def prefixEnd_6228291 : Nat := 4983230072969 + 3 ^ 40 * 6228291 * 2
def baseEnd_6228291 : Nat := 3198106939072196516519117

theorem tailTrace_6228291 : CollatzResearch.WordTrace tailWord_6228291 prefixEnd_6228291 3198106939072196516519117 := by
  unfold tailWord_6228291
  simp only [CollatzResearch.WordTrace]
  refine ⟨227164435078972889261836727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151442956719315259507891151 227164435078972889261836727)
  ·
    refine ⟨340746652618459333892755091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227164435078972889261836727 340746652618459333892755091)
    ·
      refine ⟨511119978927689000839132637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 340746652618459333892755091 511119978927689000839132637)
      ·
        refine ⟨191669992097883375314674739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 511119978927689000839132637 191669992097883375314674739)
        ·
          refine ⟨287504988146825062972012109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 191669992097883375314674739 287504988146825062972012109)
          ·
            refine ⟨107814370555059398614504541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 287504988146825062972012109 107814370555059398614504541)
            ·
              refine ⟨40430388958147274480439203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 107814370555059398614504541 40430388958147274480439203)
              ·
                refine ⟨60645583437220911720658805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40430388958147274480439203 60645583437220911720658805)
                ·
                  refine ⟨5685523447239460473811763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 60645583437220911720658805 5685523447239460473811763)
                  ·
                    refine ⟨8528285170859190710717645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5685523447239460473811763 8528285170859190710717645)
                    ·
                      refine ⟨3198106939072196516519117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8528285170859190710717645 3198106939072196516519117)
                      ·
                        rfl

theorem cell23_6228291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 3, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 3, 1, 5, 1, 3].length) (baseStart_6228291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6228291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6228291 prefixEnd_6228291 := by exact prefixLift 6228291
  have htrace : WordTrace (prefixWord ++ tailWord_6228291) baseStart_6228291 baseEnd_6228291 := by
    simpa [prefixWord, tailWord_6228291, baseEnd_6228291] using wordTrace_append hprefix tailTrace_6228291
  have hstable : (prefixWord ++ tailWord_6228291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6228291).length < 2 ^ (prefixWord ++ tailWord_6228291).sum := by decide
  have hdescent : baseEnd_6228291 < baseStart_6228291 := by decide
  rcases family_descends (prefixWord ++ tailWord_6228291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6228292 : List Nat := [2, 3, 4, 1, 3, 1, 1, 1, 2, 1, 4]
def baseStart_6228292 : Nat := 118140960795 + 6228292 * 2 ^ 59
def prefixEnd_6228292 : Nat := 4983230072969 + 3 ^ 40 * 6228292 * 2
def baseEnd_6228292 : Nat := 3198107452552851012606613

theorem tailTrace_6228292 : CollatzResearch.WordTrace tailWord_6228292 prefixEnd_6228292 3198107452552851012606613 := by
  unfold tailWord_6228292
  simp only [CollatzResearch.WordTrace]
  refine ⟨113582235775984633216311565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151442981034646177621748753 113582235775984633216311565)
  ·
    refine ⟨42593338415994237456116837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113582235775984633216311565 42593338415994237456116837)
    ·
      refine ⟨7986250952998919523021907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 42593338415994237456116837 7986250952998919523021907)
      ·
        refine ⟨11979376429498379284532861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7986250952998919523021907 11979376429498379284532861)
        ·
          refine ⟨4492266161061892231699823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11979376429498379284532861 4492266161061892231699823)
          ·
            refine ⟨6738399241592838347549735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4492266161061892231699823 6738399241592838347549735)
            ·
              refine ⟨10107598862389257521324603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6738399241592838347549735 10107598862389257521324603)
              ·
                refine ⟨15161398293583886281986905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10107598862389257521324603 15161398293583886281986905)
                ·
                  refine ⟨11371048720187914711490179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15161398293583886281986905 11371048720187914711490179)
                  ·
                    refine ⟨17056573080281872067235269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11371048720187914711490179 17056573080281872067235269)
                    ·
                      refine ⟨3198107452552851012606613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17056573080281872067235269 3198107452552851012606613)
                      ·
                        rfl

theorem cell23_6228292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 3, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 3, 1, 1, 1, 2, 1, 4].length) (baseStart_6228292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6228292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6228292 prefixEnd_6228292 := by exact prefixLift 6228292
  have htrace : WordTrace (prefixWord ++ tailWord_6228292) baseStart_6228292 baseEnd_6228292 := by
    simpa [prefixWord, tailWord_6228292, baseEnd_6228292] using wordTrace_append hprefix tailTrace_6228292
  have hstable : (prefixWord ++ tailWord_6228292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6228292).length < 2 ^ (prefixWord ++ tailWord_6228292).sum := by decide
  have hdescent : baseEnd_6228292 < baseStart_6228292 := by decide
  rcases family_descends (prefixWord ++ tailWord_6228292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6228311 : List Nat := [1, 1, 3, 2, 3, 1, 3, 3, 1, 5]
def baseStart_6228311 : Nat := 118140960795 + 6228311 * 2 ^ 59
def prefixEnd_6228311 : Nat := 4983230072969 + 3 ^ 40 * 6228311 * 2
def baseEnd_6228311 : Nat := 1066039069561762146089675

theorem tailTrace_6228311 : CollatzResearch.WordTrace tailWord_6228311 prefixEnd_6228311 1066039069561762146089675 := by
  unfold tailWord_6228311
  simp only [CollatzResearch.WordTrace]
  refine ⟨227165164538900432677564787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151443443025933621785043191 227165164538900432677564787)
  ·
    refine ⟨340747746808350649016347181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227165164538900432677564787 340747746808350649016347181)
    ·
      refine ⟨127780405053131493381130193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 340747746808350649016347181 127780405053131493381130193)
      ·
        refine ⟨95835303789848620035847645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 127780405053131493381130193 95835303789848620035847645)
        ·
          refine ⟨35938238921193232513442867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 95835303789848620035847645 35938238921193232513442867)
          ·
            refine ⟨53907358381789848770164301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35938238921193232513442867 53907358381789848770164301)
            ·
              refine ⟨20215259393171193288811613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53907358381789848770164301 20215259393171193288811613)
              ·
                refine ⟨7580722272439197483304355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20215259393171193288811613 7580722272439197483304355)
                ·
                  refine ⟨11371083408658796224956533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7580722272439197483304355 11371083408658796224956533)
                  ·
                    refine ⟨1066039069561762146089675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11371083408658796224956533 1066039069561762146089675)
                    ·
                      rfl

theorem cell23_6228311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 3, 3, 1, 5].length) (baseStart_6228311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6228311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6228311 prefixEnd_6228311 := by exact prefixLift 6228311
  have htrace : WordTrace (prefixWord ++ tailWord_6228311) baseStart_6228311 baseEnd_6228311 := by
    simpa [prefixWord, tailWord_6228311, baseEnd_6228311] using wordTrace_append hprefix tailTrace_6228311
  have hstable : (prefixWord ++ tailWord_6228311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6228311).length < 2 ^ (prefixWord ++ tailWord_6228311).sum := by decide
  have hdescent : baseEnd_6228311 < baseStart_6228311 := by decide
  rcases family_descends (prefixWord ++ tailWord_6228311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6228325 : List Nat := [1, 3, 1, 3, 1, 3, 2, 4, 1, 1, 3]
def baseStart_6228325 : Nat := 118140960795 + 6228325 * 2 ^ 59
def prefixEnd_6228325 : Nat := 4983230072969 + 3 ^ 40 * 6228325 * 2
def baseEnd_6228325 : Nat := 3198124397414449383493961

theorem tailTrace_6228325 : CollatzResearch.WordTrace tailWord_6228325 prefixEnd_6228325 3198124397414449383493961 := by
  unfold tailWord_6228325
  simp only [CollatzResearch.WordTrace]
  refine ⟨227165675160849713068574429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151443783440566475379049619 227165675160849713068574429)
  ·
    refine ⟨85187128185318642400715411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 227165675160849713068574429 85187128185318642400715411)
    ·
      refine ⟨127780692277977963601073117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85187128185318642400715411 127780692277977963601073117)
      ·
        refine ⟨47917759604241736350402419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 127780692277977963601073117 47917759604241736350402419)
        ·
          refine ⟨71876639406362604525603629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47917759604241736350402419 71876639406362604525603629)
          ·
            refine ⟨26953739777385976697101361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 71876639406362604525603629 26953739777385976697101361)
            ·
              refine ⟨20215304833039482522826021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26953739777385976697101361 20215304833039482522826021)
              ·
                refine ⟨3790369656194902973029879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20215304833039482522826021 3790369656194902973029879)
                ·
                  refine ⟨5685554484292354459544819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3790369656194902973029879 5685554484292354459544819)
                  ·
                    refine ⟨8528331726438531689317229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5685554484292354459544819 8528331726438531689317229)
                    ·
                      refine ⟨3198124397414449383493961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8528331726438531689317229 3198124397414449383493961)
                      ·
                        rfl

theorem cell23_6228325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 2, 4, 1, 1, 3].length) (baseStart_6228325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6228325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6228325 prefixEnd_6228325 := by exact prefixLift 6228325
  have htrace : WordTrace (prefixWord ++ tailWord_6228325) baseStart_6228325 baseEnd_6228325 := by
    simpa [prefixWord, tailWord_6228325, baseEnd_6228325] using wordTrace_append hprefix tailTrace_6228325
  have hstable : (prefixWord ++ tailWord_6228325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6228325).length < 2 ^ (prefixWord ++ tailWord_6228325).sum := by decide
  have hdescent : baseEnd_6228325 < baseStart_6228325 := by decide
  rcases family_descends (prefixWord ++ tailWord_6228325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6228348 : List Nat := [2, 2, 2, 1, 1, 1, 2, 3, 5, 2, 2]
def baseStart_6228348 : Nat := 118140960795 + 6228348 * 2 ^ 59
def prefixEnd_6228348 : Nat := 4983230072969 + 3 ^ 40 * 6228348 * 2
def baseEnd_6228348 : Nat := 3198136207469502793506355

theorem tailTrace_6228348 : CollatzResearch.WordTrace tailWord_6228348 prefixEnd_6228348 3198136207469502793506355 := by
  unfold tailWord_6228348
  simp only [CollatzResearch.WordTrace]
  refine ⟨113583257019883193998330849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151444342693177591997774465 113583257019883193998330849)
  ·
    refine ⟨85187442764912395498748137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113583257019883193998330849 85187442764912395498748137)
    ·
      refine ⟨63890582073684296624061103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85187442764912395498748137 63890582073684296624061103)
      ·
        refine ⟨95835873110526444936091655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63890582073684296624061103 95835873110526444936091655)
        ·
          refine ⟨143753809665789667404137483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95835873110526444936091655 143753809665789667404137483)
          ·
            refine ⟨215630714498684501106206225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 143753809665789667404137483 215630714498684501106206225)
            ·
              refine ⟨161723035874013375829654669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 215630714498684501106206225 161723035874013375829654669)
              ·
                refine ⟨60646138452755015936120501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 161723035874013375829654669 60646138452755015936120501)
                ·
                  refine ⟨5685575479945782744011297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 60646138452755015936120501 5685575479945782744011297)
                  ·
                    refine ⟨4264181609959337058008473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5685575479945782744011297 4264181609959337058008473)
                    ·
                      refine ⟨3198136207469502793506355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4264181609959337058008473 3198136207469502793506355)
                      ·
                        rfl

theorem cell23_6228348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 3, 5, 2, 2].length) (baseStart_6228348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6228348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6228348 prefixEnd_6228348 := by exact prefixLift 6228348
  have htrace : WordTrace (prefixWord ++ tailWord_6228348) baseStart_6228348 baseEnd_6228348 := by
    simpa [prefixWord, tailWord_6228348, baseEnd_6228348] using wordTrace_append hprefix tailTrace_6228348
  have hstable : (prefixWord ++ tailWord_6228348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6228348).length < 2 ^ (prefixWord ++ tailWord_6228348).sum := by decide
  have hdescent : baseEnd_6228348 < baseStart_6228348 := by decide
  rcases family_descends (prefixWord ++ tailWord_6228348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6228392 : List Nat := [2, 1, 6, 1, 1, 1, 4, 1, 2, 4]
def baseStart_6228392 : Nat := 118140960795 + 6228392 * 2 ^ 59
def prefixEnd_6228392 : Nat := 4983230072969 + 3 ^ 40 * 6228392 * 2
def baseEnd_6228392 : Nat := 1066052933539433540452051

theorem tailTrace_6228392 : CollatzResearch.WordTrace tailWord_6228392 prefixEnd_6228392 1066052933539433540452051 := by
  unfold tailWord_6228392
  simp only [CollatzResearch.WordTrace]
  refine ⟨113584059425803491755631715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151445412567737989007508953 113584059425803491755631715)
  ·
    refine ⟨170376089138705237633447573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113584059425803491755631715 170376089138705237633447573)
    ·
      refine ⟨7986379178376808014067855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 170376089138705237633447573 7986379178376808014067855)
      ·
        refine ⟨11979568767565212021101783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7986379178376808014067855 11979568767565212021101783)
        ·
          refine ⟨17969353151347818031652675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11979568767565212021101783 17969353151347818031652675)
          ·
            refine ⟨26954029727021727047479013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17969353151347818031652675 26954029727021727047479013)
            ·
              refine ⟨5053880573816573821402315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26954029727021727047479013 5053880573816573821402315)
              ·
                refine ⟨7580820860724860732103473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5053880573816573821402315 7580820860724860732103473)
                ·
                  refine ⟨5685615645543645549077605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7580820860724860732103473 5685615645543645549077605)
                  ·
                    refine ⟨1066052933539433540452051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5685615645543645549077605 1066052933539433540452051)
                    ·
                      rfl

theorem cell23_6228392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 4, 1, 2, 4].length) (baseStart_6228392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6228392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6228392 prefixEnd_6228392 := by exact prefixLift 6228392
  have htrace : WordTrace (prefixWord ++ tailWord_6228392) baseStart_6228392 baseEnd_6228392 := by
    simpa [prefixWord, tailWord_6228392, baseEnd_6228392] using wordTrace_append hprefix tailTrace_6228392
  have hstable : (prefixWord ++ tailWord_6228392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6228392).length < 2 ^ (prefixWord ++ tailWord_6228392).sum := by decide
  have hdescent : baseEnd_6228392 < baseStart_6228392 := by decide
  rcases family_descends (prefixWord ++ tailWord_6228392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6228438 : List Nat := [5, 2, 1, 1, 1, 1, 1, 1, 1, 5, 4]
def baseStart_6228438 : Nat := 118140960795 + 6228438 * 2 ^ 59
def prefixEnd_6228438 : Nat := 4983230072969 + 3 ^ 40 * 6228438 * 2
def baseEnd_6228438 : Nat := 3198182420728407441380941

theorem tailTrace_6228438 : CollatzResearch.WordTrace tailWord_6228438 prefixEnd_6228438 3198182420728407441380941 := by
  unfold tailWord_6228438
  simp only [CollatzResearch.WordTrace]
  refine ⟨14198112288090020835464873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 151446531072960222244958645 14198112288090020835464873)
  ·
    refine ⟨10648584216067515626598655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14198112288090020835464873 10648584216067515626598655)
    ·
      refine ⟨15972876324101273439897983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10648584216067515626598655 15972876324101273439897983)
      ·
        refine ⟨23959314486151910159846975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15972876324101273439897983 23959314486151910159846975)
        ·
          refine ⟨35938971729227865239770463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23959314486151910159846975 35938971729227865239770463)
          ·
            refine ⟨53908457593841797859655695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35938971729227865239770463 53908457593841797859655695)
            ·
              refine ⟨80862686390762696789483543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53908457593841797859655695 80862686390762696789483543)
              ·
                refine ⟨121294029586144045184225315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 80862686390762696789483543 121294029586144045184225315)
                ·
                  refine ⟨181941044379216067776337973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 121294029586144045184225315 181941044379216067776337973)
                  ·
                    refine ⟨17056972910551506354031685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 181941044379216067776337973 17056972910551506354031685)
                    ·
                      refine ⟨3198182420728407441380941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17056972910551506354031685 3198182420728407441380941)
                      ·
                        rfl

theorem cell23_6228438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 1, 1, 5, 4].length) (baseStart_6228438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6228438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6228438 prefixEnd_6228438 := by exact prefixLift 6228438
  have htrace : WordTrace (prefixWord ++ tailWord_6228438) baseStart_6228438 baseEnd_6228438 := by
    simpa [prefixWord, tailWord_6228438, baseEnd_6228438] using wordTrace_append hprefix tailTrace_6228438
  have hstable : (prefixWord ++ tailWord_6228438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6228438).length < 2 ^ (prefixWord ++ tailWord_6228438).sum := by decide
  have hdescent : baseEnd_6228438 < baseStart_6228438 := by decide
  rcases family_descends (prefixWord ++ tailWord_6228438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6228441 : List Nat := [1, 2, 1, 2, 4, 1, 1, 1, 1, 6, 3]
def baseStart_6228441 : Nat := 118140960795 + 6228441 * 2 ^ 59
def prefixEnd_6228441 : Nat := 4983230072969 + 3 ^ 40 * 6228441 * 2
def baseEnd_6228441 : Nat := 3198183961170370929643427

theorem tailTrace_6228441 : CollatzResearch.WordTrace tailWord_6228441 prefixEnd_6228441 3198183961170370929643427 := by
  unfold tailWord_6228441
  simp only [CollatzResearch.WordTrace]
  refine ⟨227169906028429464879797177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151446604018952976586531451 227169906028429464879797177)
  ·
    refine ⟨170377429521322098659847883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 227169906028429464879797177 170377429521322098659847883)
    ·
      refine ⟨255566144281983147989771825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170377429521322098659847883 255566144281983147989771825)
      ·
        refine ⟨191674608211487360992328869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 255566144281983147989771825 191674608211487360992328869)
        ·
          refine ⟨35938989039653880186061663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 191674608211487360992328869 35938989039653880186061663)
          ·
            refine ⟨53908483559480820279092495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35938989039653880186061663 53908483559480820279092495)
            ·
              refine ⟨80862725339221230418638743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53908483559480820279092495 80862725339221230418638743)
              ·
                refine ⟨121294088008831845627958115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 80862725339221230418638743 121294088008831845627958115)
                ·
                  refine ⟨181941132013247768441937173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 121294088008831845627958115 181941132013247768441937173)
                  ·
                    refine ⟨8528490563120989145715805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 181941132013247768441937173 8528490563120989145715805)
                    ·
                      refine ⟨3198183961170370929643427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8528490563120989145715805 3198183961170370929643427)
                      ·
                        rfl

theorem cell23_6228441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 1, 1, 6, 3].length) (baseStart_6228441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6228441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6228441 prefixEnd_6228441 := by exact prefixLift 6228441
  have htrace : WordTrace (prefixWord ++ tailWord_6228441) baseStart_6228441 baseEnd_6228441 := by
    simpa [prefixWord, tailWord_6228441, baseEnd_6228441] using wordTrace_append hprefix tailTrace_6228441
  have hstable : (prefixWord ++ tailWord_6228441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6228441).length < 2 ^ (prefixWord ++ tailWord_6228441).sum := by decide
  have hdescent : baseEnd_6228441 < baseStart_6228441 := by decide
  rcases family_descends (prefixWord ++ tailWord_6228441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6228455 : List Nat := [1, 1, 5, 2, 1, 1, 4, 1, 1, 4, 2]
def baseStart_6228455 : Nat := 118140960795 + 6228455 * 2 ^ 59
def prefixEnd_6228455 : Nat := 4983230072969 + 3 ^ 40 * 6228455 * 2
def baseEnd_6228455 : Nat := 3198191149899533874868363

theorem tailTrace_6228455 : CollatzResearch.WordTrace tailWord_6228455 prefixEnd_6228455 3198191149899533874868363 := by
  unfold tailWord_6228455
  simp only [CollatzResearch.WordTrace]
  refine ⟨227170416650378745270806819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151446944433585830180537879 227170416650378745270806819)
  ·
    refine ⟨340755624975568117906210229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227170416650378745270806819 340755624975568117906210229)
    ·
      refine ⟨31945839841459511053707209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 340755624975568117906210229 31945839841459511053707209)
      ·
        refine ⟨23959379881094633290280407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31945839841459511053707209 23959379881094633290280407)
        ·
          refine ⟨35939069821641949935420611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23959379881094633290280407 35939069821641949935420611)
          ·
            refine ⟨53908604732462924903130917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35939069821641949935420611 53908604732462924903130917)
            ·
              refine ⟨10107863387336798419337047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 53908604732462924903130917 10107863387336798419337047)
              ·
                refine ⟨15161795081005197629005571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10107863387336798419337047 15161795081005197629005571)
                ·
                  refine ⟨22742692621507796443508357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15161795081005197629005571 22742692621507796443508357)
                  ·
                    refine ⟨4264254866532711833157817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22742692621507796443508357 4264254866532711833157817)
                    ·
                      refine ⟨3198191149899533874868363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4264254866532711833157817 3198191149899533874868363)
                      ·
                        rfl

theorem cell23_6228455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 4, 1, 1, 4, 2].length) (baseStart_6228455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6228455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6228455 prefixEnd_6228455 := by exact prefixLift 6228455
  have htrace : WordTrace (prefixWord ++ tailWord_6228455) baseStart_6228455 baseEnd_6228455 := by
    simpa [prefixWord, tailWord_6228455, baseEnd_6228455] using wordTrace_append hprefix tailTrace_6228455
  have hstable : (prefixWord ++ tailWord_6228455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6228455).length < 2 ^ (prefixWord ++ tailWord_6228455).sum := by decide
  have hdescent : baseEnd_6228455 < baseStart_6228455 := by decide
  rcases family_descends (prefixWord ++ tailWord_6228455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6228501 : List Nat := [1, 3, 2, 1, 3, 1, 2, 1, 1, 1, 7]
def baseStart_6228501 : Nat := 118140960795 + 6228501 * 2 ^ 59
def prefixEnd_6228501 : Nat := 4983230072969 + 3 ^ 40 * 6228501 * 2
def baseEnd_6228501 : Nat := 3198214770009640694893151

theorem tailTrace_6228501 : CollatzResearch.WordTrace tailWord_6228501 prefixEnd_6228501 3198214770009640694893151 := by
  unfold tailWord_6228501
  simp only [CollatzResearch.WordTrace]
  refine ⟨227172094408212095126981357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151448062938808063417987571 227172094408212095126981357)
  ·
    refine ⟨85189535403079535672618009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 227172094408212095126981357 85189535403079535672618009)
    ·
      refine ⟨63892151552309651754463507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85189535403079535672618009 63892151552309651754463507)
      ·
        refine ⟨95838227328464477631695261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63892151552309651754463507 95838227328464477631695261)
        ·
          refine ⟨35939335248174179111885723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 95838227328464477631695261 35939335248174179111885723)
          ·
            refine ⟨53909002872261268667828585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35939335248174179111885723 53909002872261268667828585)
            ·
              refine ⟨40431752154195951500871439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53909002872261268667828585 40431752154195951500871439)
              ·
                refine ⟨60647628231293927251307159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40431752154195951500871439 60647628231293927251307159)
                ·
                  refine ⟨90971442346940890876960739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 60647628231293927251307159 90971442346940890876960739)
                  ·
                    refine ⟨136457163520411336315441109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 90971442346940890876960739 136457163520411336315441109)
                    ·
                      refine ⟨3198214770009640694893151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 136457163520411336315441109 3198214770009640694893151)
                      ·
                        rfl

theorem cell23_6228501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 2, 1, 1, 1, 7].length) (baseStart_6228501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6228501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6228501 prefixEnd_6228501 := by exact prefixLift 6228501
  have htrace : WordTrace (prefixWord ++ tailWord_6228501) baseStart_6228501 baseEnd_6228501 := by
    simpa [prefixWord, tailWord_6228501, baseEnd_6228501] using wordTrace_append hprefix tailTrace_6228501
  have hstable : (prefixWord ++ tailWord_6228501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6228501).length < 2 ^ (prefixWord ++ tailWord_6228501).sum := by decide
  have hdescent : baseEnd_6228501 < baseStart_6228501 := by decide
  rcases family_descends (prefixWord ++ tailWord_6228501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6228528 : List Nat := [2, 1, 1, 1, 2, 3, 2, 2, 1, 6, 2]
def baseStart_6228528 : Nat := 118140960795 + 6228528 * 2 ^ 59
def prefixEnd_6228528 : Nat := 4983230072969 + 3 ^ 40 * 6228528 * 2
def baseEnd_6228528 : Nat := 3198228633987312089255527

theorem tailTrace_6228528 : CollatzResearch.WordTrace tailWord_6228528 prefixEnd_6228528 3198228633987312089255527 := by
  unfold tailWord_6228528
  simp only [CollatzResearch.WordTrace]
  refine ⟨113586539589557139369107119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151448719452742852492142825 113586539589557139369107119)
  ·
    refine ⟨170379809384335709053660679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113586539589557139369107119 170379809384335709053660679)
    ·
      refine ⟨255569714076503563580491019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170379809384335709053660679 255569714076503563580491019)
      ·
        refine ⟨383354571114755345370736529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 255569714076503563580491019 383354571114755345370736529)
        ·
          refine ⟨287515928336066509028052397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 383354571114755345370736529 287515928336066509028052397)
          ·
            refine ⟨107818473126024940885519649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 287515928336066509028052397 107818473126024940885519649)
            ·
              refine ⟨80863854844518705664139737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 107818473126024940885519649 80863854844518705664139737)
              ·
                refine ⟨60647891133389029248104803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 80863854844518705664139737 60647891133389029248104803)
                ·
                  refine ⟨90971836700083543872157205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 60647891133389029248104803 90971836700083543872157205)
                  ·
                    refine ⟨4264304845316416119007369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 90971836700083543872157205 4264304845316416119007369)
                    ·
                      refine ⟨3198228633987312089255527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4264304845316416119007369 3198228633987312089255527)
                      ·
                        rfl

theorem cell23_6228528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 2, 1, 6, 2].length) (baseStart_6228528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6228528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6228528 prefixEnd_6228528 := by exact prefixLift 6228528
  have htrace : WordTrace (prefixWord ++ tailWord_6228528) baseStart_6228528 baseEnd_6228528 := by
    simpa [prefixWord, tailWord_6228528, baseEnd_6228528] using wordTrace_append hprefix tailTrace_6228528
  have hstable : (prefixWord ++ tailWord_6228528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6228528).length < 2 ^ (prefixWord ++ tailWord_6228528).sum := by decide
  have hdescent : baseEnd_6228528 < baseStart_6228528 := by decide
  rcases family_descends (prefixWord ++ tailWord_6228528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6228542 : List Nat := [4, 2, 1, 4, 1, 1, 1, 2, 2, 5]
def baseStart_6228542 : Nat := 118140960795 + 6228542 * 2 ^ 59
def prefixEnd_6228542 : Nat := 4983230072969 + 3 ^ 40 * 6228542 * 2
def baseEnd_6228542 : Nat := 1066078607572158344826821

theorem tailTrace_6228542 : CollatzResearch.WordTrace tailWord_6228542 prefixEnd_6228542 1066078607572158344826821 := by
  unfold tailWord_6228542
  simp only [CollatzResearch.WordTrace]
  refine ⟨28396698725132944891152985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 151449059867375706086149253 28396698725132944891152985)
  ·
    refine ⟨21297524043849708668364739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28396698725132944891152985 21297524043849708668364739)
    ·
      refine ⟨31946286065774563002547109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21297524043849708668364739 31946286065774563002547109)
      ·
        refine ⟨5989928637332730562977583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31946286065774563002547109 5989928637332730562977583)
        ·
          refine ⟨8984892955999095844466375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5989928637332730562977583 8984892955999095844466375)
          ·
            refine ⟨13477339433998643766699563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8984892955999095844466375 13477339433998643766699563)
            ·
              refine ⟨20216009150997965650049345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13477339433998643766699563 20216009150997965650049345)
              ·
                refine ⟨15162006863248474237537009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20216009150997965650049345 15162006863248474237537009)
                ·
                  refine ⟨11371505147436355678152757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15162006863248474237537009 11371505147436355678152757)
                  ·
                    refine ⟨1066078607572158344826821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11371505147436355678152757 1066078607572158344826821)
                    ·
                      rfl

theorem cell23_6228542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 1, 2, 2, 5].length) (baseStart_6228542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6228542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6228542 prefixEnd_6228542 := by exact prefixLift 6228542
  have htrace : WordTrace (prefixWord ++ tailWord_6228542) baseStart_6228542 baseEnd_6228542 := by
    simpa [prefixWord, tailWord_6228542, baseEnd_6228542] using wordTrace_append hprefix tailTrace_6228542
  have hstable : (prefixWord ++ tailWord_6228542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6228542).length < 2 ^ (prefixWord ++ tailWord_6228542).sum := by decide
  have hdescent : baseEnd_6228542 < baseStart_6228542 := by decide
  rcases family_descends (prefixWord ++ tailWord_6228542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6228545 : List Nat := [1, 2, 5, 1, 1, 3, 1, 2, 2, 1, 4]
def baseStart_6228545 : Nat := 118140960795 + 6228545 * 2 ^ 59
def prefixEnd_6228545 : Nat := 4983230072969 + 3 ^ 40 * 6228545 * 2
def baseEnd_6228545 : Nat := 3198237363158438522742949

theorem tailTrace_6228545 : CollatzResearch.WordTrace tailWord_6228545 prefixEnd_6228545 3198237363158438522742949 := by
  unfold tailWord_6228545
  simp only [CollatzResearch.WordTrace]
  refine ⟨227173699220052690641583089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151449132813368460427722059 227173699220052690641583089)
  ·
    refine ⟨170380274415039517981187317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 227173699220052690641583089 170380274415039517981187317)
    ·
      refine ⟨15973150726409954810736311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 170380274415039517981187317 15973150726409954810736311)
      ·
        refine ⟨23959726089614932216104467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15973150726409954810736311 23959726089614932216104467)
        ·
          refine ⟨35939589134422398324156701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23959726089614932216104467 35939589134422398324156701)
          ·
            refine ⟨13477345925408399371558763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35939589134422398324156701 13477345925408399371558763)
            ·
              refine ⟨20216018888112599057338145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13477345925408399371558763 20216018888112599057338145)
              ·
                refine ⟨15162014166084449293003609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20216018888112599057338145 15162014166084449293003609)
                ·
                  refine ⟨11371510624563336969752707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15162014166084449293003609 11371510624563336969752707)
                  ·
                    refine ⟨17057265936845005454629061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11371510624563336969752707 17057265936845005454629061)
                    ·
                      refine ⟨3198237363158438522742949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17057265936845005454629061 3198237363158438522742949)
                      ·
                        rfl

theorem cell23_6228545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 1, 2, 2, 1, 4].length) (baseStart_6228545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6228545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6228545 prefixEnd_6228545 := by exact prefixLift 6228545
  have htrace : WordTrace (prefixWord ++ tailWord_6228545) baseStart_6228545 baseEnd_6228545 := by
    simpa [prefixWord, tailWord_6228545, baseEnd_6228545] using wordTrace_append hprefix tailTrace_6228545
  have hstable : (prefixWord ++ tailWord_6228545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6228545).length < 2 ^ (prefixWord ++ tailWord_6228545).sum := by decide
  have hdescent : baseEnd_6228545 < baseStart_6228545 := by decide
  rcases family_descends (prefixWord ++ tailWord_6228545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6228555 : List Nat := [1, 1, 1, 1, 3, 1, 4, 6, 1, 4]
def baseStart_6228555 : Nat := 118140960795 + 6228555 * 2 ^ 59
def prefixEnd_6228555 : Nat := 4983230072969 + 3 ^ 40 * 6228555 * 2
def baseEnd_6228555 : Nat := 1066080832654994494539301

theorem tailTrace_6228555 : CollatzResearch.WordTrace tailWord_6228555 prefixEnd_6228555 1066080832654994494539301 := by
  unfold tailWord_6228555
  simp only [CollatzResearch.WordTrace]
  refine ⟨227174063950016462349447119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151449375966677641566298079 227174063950016462349447119)
  ·
    refine ⟨340761095925024693524170679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227174063950016462349447119 340761095925024693524170679)
    ·
      refine ⟨511141643887537040286256019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 340761095925024693524170679 511141643887537040286256019)
      ·
        refine ⟨766712465831305560429384029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 511141643887537040286256019 766712465831305560429384029)
        ·
          refine ⟨287517174686739585161019011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 766712465831305560429384029 287517174686739585161019011)
          ·
            refine ⟨431275762030109377741528517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 287517174686739585161019011 431275762030109377741528517)
            ·
              refine ⟨80864205380645508326536597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 431275762030109377741528517 80864205380645508326536597)
              ·
                refine ⟨3790509627217758202806403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 80864205380645508326536597 3790509627217758202806403)
                ·
                  refine ⟨5685764440826637304209605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3790509627217758202806403 5685764440826637304209605)
                  ·
                    refine ⟨1066080832654994494539301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5685764440826637304209605 1066080832654994494539301)
                    ·
                      rfl

theorem cell23_6228555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 6, 1, 4].length) (baseStart_6228555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6228555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6228555 prefixEnd_6228555 := by exact prefixLift 6228555
  have htrace : WordTrace (prefixWord ++ tailWord_6228555) baseStart_6228555 baseEnd_6228555 := by
    simpa [prefixWord, tailWord_6228555, baseEnd_6228555] using wordTrace_append hprefix tailTrace_6228555
  have hstable : (prefixWord ++ tailWord_6228555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6228555).length < 2 ^ (prefixWord ++ tailWord_6228555).sum := by decide
  have hdescent : baseEnd_6228555 < baseStart_6228555 := by decide
  rcases family_descends (prefixWord ++ tailWord_6228555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6228669 : List Nat := [1, 4, 1, 2, 1, 4, 2, 1, 3, 2, 2]
def baseStart_6228669 : Nat := 118140960795 + 6228669 * 2 ^ 59
def prefixEnd_6228669 : Nat := 4983230072969 + 3 ^ 40 * 6228669 * 2
def baseEnd_6228669 : Nat := 3198301034759596037592379

theorem tailTrace_6228669 : CollatzResearch.WordTrace tailWord_6228669 prefixEnd_6228669 3198301034759596037592379 := by
  unfold tailWord_6228669
  simp only [CollatzResearch.WordTrace]
  refine ⟨227178221871603459819097061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151452147914402306546064707 227178221871603459819097061)
  ·
    refine ⟨42595916600925648716080699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 227178221871603459819097061 42595916600925648716080699)
    ·
      refine ⟨63893874901388473074121049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42595916600925648716080699 63893874901388473074121049)
      ·
        refine ⟨47920406176041354805590787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63893874901388473074121049 47920406176041354805590787)
        ·
          refine ⟨71880609264062032208386181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47920406176041354805590787 71880609264062032208386181)
          ·
            refine ⟨13477614237011631039072409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 71880609264062032208386181 13477614237011631039072409)
            ·
              refine ⟨10108210677758723279304307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13477614237011631039072409 10108210677758723279304307)
              ·
                refine ⟨15162316016638084918956461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10108210677758723279304307 15162316016638084918956461)
                ·
                  refine ⟨5685868506239281844608673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15162316016638084918956461 5685868506239281844608673)
                  ·
                    refine ⟨4264401379679461383456505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5685868506239281844608673 4264401379679461383456505)
                    ·
                      refine ⟨3198301034759596037592379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4264401379679461383456505 3198301034759596037592379)
                      ·
                        rfl

theorem cell23_6228669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 2, 1, 3, 2, 2].length) (baseStart_6228669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6228669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6228669 prefixEnd_6228669 := by exact prefixLift 6228669
  have htrace : WordTrace (prefixWord ++ tailWord_6228669) baseStart_6228669 baseEnd_6228669 := by
    simpa [prefixWord, tailWord_6228669, baseEnd_6228669] using wordTrace_append hprefix tailTrace_6228669
  have hstable : (prefixWord ++ tailWord_6228669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6228669).length < 2 ^ (prefixWord ++ tailWord_6228669).sum := by decide
  have hdescent : baseEnd_6228669 < baseStart_6228669 := by decide
  rcases family_descends (prefixWord ++ tailWord_6228669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6228682 : List Nat := [3, 1, 2, 1, 4, 3, 1, 1, 1, 2, 4]
def baseStart_6228682 : Nat := 118140960795 + 6228682 * 2 ^ 59
def prefixEnd_6228682 : Nat := 4983230072969 + 3 ^ 40 * 6228682 * 2
def baseEnd_6228682 : Nat := 3198307710008104486729819

theorem tailTrace_6228682 : CollatzResearch.WordTrace tailWord_6228682 prefixEnd_6228682 3198307710008104486729819 := by
  unfold tailWord_6228682
  simp only [CollatzResearch.WordTrace]
  refine ⟨56794674005139090759830075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151452464013704242026213533 56794674005139090759830075)
  ·
    refine ⟨85192011007708636139745113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56794674005139090759830075 85192011007708636139745113)
    ·
      refine ⟨63894008255781477104808835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85192011007708636139745113 63894008255781477104808835)
      ·
        refine ⟨95841012383672215657213253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63894008255781477104808835 95841012383672215657213253)
        ·
          refine ⟨17970189821938540435727485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 95841012383672215657213253 17970189821938540435727485)
          ·
            refine ⟨6738821183226952663397807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17970189821938540435727485 6738821183226952663397807)
            ·
              refine ⟨10108231774840428995096711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6738821183226952663397807 10108231774840428995096711)
              ·
                refine ⟨15162347662260643492645067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10108231774840428995096711 15162347662260643492645067)
                ·
                  refine ⟨22743521493390965238967601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15162347662260643492645067 22743521493390965238967601)
                  ·
                    refine ⟨17057641120043223929225701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22743521493390965238967601 17057641120043223929225701)
                    ·
                      refine ⟨3198307710008104486729819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17057641120043223929225701 3198307710008104486729819)
                      ·
                        rfl

theorem cell23_6228682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 3, 1, 1, 1, 2, 4].length) (baseStart_6228682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6228682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6228682 prefixEnd_6228682 := by exact prefixLift 6228682
  have htrace : WordTrace (prefixWord ++ tailWord_6228682) baseStart_6228682 baseEnd_6228682 := by
    simpa [prefixWord, tailWord_6228682, baseEnd_6228682] using wordTrace_append hprefix tailTrace_6228682
  have hstable : (prefixWord ++ tailWord_6228682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6228682).length < 2 ^ (prefixWord ++ tailWord_6228682).sum := by decide
  have hdescent : baseEnd_6228682 < baseStart_6228682 := by decide
  rcases family_descends (prefixWord ++ tailWord_6228682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6228698 : List Nat := [3, 1, 1, 2, 2, 2, 1, 1, 1, 4, 5]
def baseStart_6228698 : Nat := 118140960795 + 6228698 * 2 ^ 59
def prefixEnd_6228698 : Nat := 4983230072969 + 3 ^ 40 * 6228698 * 2
def baseEnd_6228698 : Nat := 3198315925698576424129745

theorem tailTrace_6228698 : CollatzResearch.WordTrace tailWord_6228698 prefixEnd_6228698 3198315925698576424129745 := by
  unfold tailWord_6228698
  simp only [CollatzResearch.WordTrace]
  refine ⟨56794819897124599442975687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151452853058998931847935165 56794819897124599442975687)
  ·
    refine ⟨85192229845686899164463531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56794819897124599442975687 85192229845686899164463531)
    ·
      refine ⟨127788344768530348746695297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85192229845686899164463531 127788344768530348746695297)
      ·
        refine ⟨95841258576397761560021473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 127788344768530348746695297 95841258576397761560021473)
        ·
          refine ⟨71880943932298321170016105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95841258576397761560021473 71880943932298321170016105)
          ·
            refine ⟨53910707949223740877512079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71880943932298321170016105 53910707949223740877512079)
            ·
              refine ⟨80866061923835611316268119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53910707949223740877512079 80866061923835611316268119)
              ·
                refine ⟨121299092885753416974402179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 80866061923835611316268119 121299092885753416974402179)
                ·
                  refine ⟨181948639328630125461603269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 121299092885753416974402179 181948639328630125461603269)
                  ·
                    refine ⟨34115369874118148524050613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 181948639328630125461603269 34115369874118148524050613)
                    ·
                      refine ⟨3198315925698576424129745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34115369874118148524050613 3198315925698576424129745)
                      ·
                        rfl

theorem cell23_6228698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 1, 1, 4, 5].length) (baseStart_6228698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6228698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6228698 prefixEnd_6228698 := by exact prefixLift 6228698
  have htrace : WordTrace (prefixWord ++ tailWord_6228698) baseStart_6228698 baseEnd_6228698 := by
    simpa [prefixWord, tailWord_6228698, baseEnd_6228698] using wordTrace_append hprefix tailTrace_6228698
  have hstable : (prefixWord ++ tailWord_6228698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6228698).length < 2 ^ (prefixWord ++ tailWord_6228698).sum := by decide
  have hdescent : baseEnd_6228698 < baseStart_6228698 := by decide
  rcases family_descends (prefixWord ++ tailWord_6228698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6228728 : List Nat := [2, 1, 2, 1, 1, 2, 3, 2, 1, 3, 5]
def baseStart_6228728 : Nat := 118140960795 + 6228728 * 2 ^ 59
def prefixEnd_6228728 : Nat := 4983230072969 + 3 ^ 40 * 6228728 * 2
def baseEnd_6228728 : Nat := 3198331330118211306754607

theorem tailTrace_6228728 : CollatzResearch.WordTrace tailWord_6228728 prefixEnd_6228728 3198331330118211306754607 := by
  unfold tailWord_6228728
  simp only [CollatzResearch.WordTrace]
  refine ⟨113590186889194856447747419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151453582518926475263663225 113590186889194856447747419)
  ·
    refine ⟨170385280333792284671621129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113590186889194856447747419 170385280333792284671621129)
    ·
      refine ⟨127788960250344213503715847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 170385280333792284671621129 127788960250344213503715847)
      ·
        refine ⟨191683440375516320255573771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127788960250344213503715847 191683440375516320255573771)
        ·
          refine ⟨287525160563274480383360657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 191683440375516320255573771 287525160563274480383360657)
          ·
            refine ⟨215643870422455860287520493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 287525160563274480383360657 215643870422455860287520493)
            ·
              refine ⟨80866451408420947607820185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 215643870422455860287520493 80866451408420947607820185)
              ·
                refine ⟨60649838556315710705865139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 80866451408420947607820185 60649838556315710705865139)
                ·
                  refine ⟨90974757834473566058797709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 60649838556315710705865139 90974757834473566058797709)
                  ·
                    refine ⟨34115534187927587272049141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 90974757834473566058797709 34115534187927587272049141)
                    ·
                      refine ⟨3198331330118211306754607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34115534187927587272049141 3198331330118211306754607)
                      ·
                        rfl

theorem cell23_6228728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 2, 1, 3, 5].length) (baseStart_6228728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6228728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6228728 prefixEnd_6228728 := by exact prefixLift 6228728
  have htrace : WordTrace (prefixWord ++ tailWord_6228728) baseStart_6228728 baseEnd_6228728 := by
    simpa [prefixWord, tailWord_6228728, baseEnd_6228728] using wordTrace_append hprefix tailTrace_6228728
  have hstable : (prefixWord ++ tailWord_6228728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6228728).length < 2 ^ (prefixWord ++ tailWord_6228728).sum := by decide
  have hdescent : baseEnd_6228728 < baseStart_6228728 := by decide
  rcases family_descends (prefixWord ++ tailWord_6228728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6228748 : List Nat := [2, 2, 1, 2, 2, 1, 1, 3, 9]
def baseStart_6228748 : Nat := 118140960795 + 6228748 * 2 ^ 59
def prefixEnd_6228748 : Nat := 4983230072969 + 3 ^ 40 * 6228748 * 2
def baseEnd_6228748 : Nat := 355371288859033469833835

theorem tailTrace_6228748 : CollatzResearch.WordTrace tailWord_6228748 prefixEnd_6228748 355371288859033469833835 := by
  unfold tailWord_6228748
  simp only [CollatzResearch.WordTrace]
  refine ⟨113590551619158628155611449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151454068825544837540815265 113590551619158628155611449)
  ·
    refine ⟨85192913714368971116708587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113590551619158628155611449 85192913714368971116708587)
    ·
      refine ⟨127789370571553456675062881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85192913714368971116708587 127789370571553456675062881)
      ·
        refine ⟨95842027928665092506297161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 127789370571553456675062881 95842027928665092506297161)
        ·
          refine ⟨71881520946498819379722871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95842027928665092506297161 71881520946498819379722871)
          ·
            refine ⟨107822281419748229069584307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71881520946498819379722871 107822281419748229069584307)
            ·
              refine ⟨161733422129622343604376461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 107822281419748229069584307 161733422129622343604376461)
              ·
                refine ⟨60650033298608378851641173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 161733422129622343604376461 60650033298608378851641173)
                ·
                  refine ⟨355371288859033469833835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 60650033298608378851641173 355371288859033469833835)
                  ·
                    rfl

theorem cell23_6228748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 3, 9].length) (baseStart_6228748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6228748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6228748 prefixEnd_6228748 := by exact prefixLift 6228748
  have htrace : WordTrace (prefixWord ++ tailWord_6228748) baseStart_6228748 baseEnd_6228748 := by
    simpa [prefixWord, tailWord_6228748, baseEnd_6228748] using wordTrace_append hprefix tailTrace_6228748
  have hstable : (prefixWord ++ tailWord_6228748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6228748).length < 2 ^ (prefixWord ++ tailWord_6228748).sum := by decide
  have hdescent : baseEnd_6228748 < baseStart_6228748 := by decide
  rcases family_descends (prefixWord ++ tailWord_6228748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6228759 : List Nat := [1, 1, 3, 4, 3, 1, 1, 2, 1, 4, 2]
def baseStart_6228759 : Nat := 118140960795 + 6228759 * 2 ^ 59
def prefixEnd_6228759 : Nat := 4983230072969 + 3 ^ 40 * 6228759 * 2
def baseEnd_6228759 : Nat := 3198347248018500685466965

theorem tailTrace_6228759 : CollatzResearch.WordTrace tailWord_6228759 prefixEnd_6228759 3198347248018500685466965 := by
  unfold tailWord_6228759
  simp only [CollatzResearch.WordTrace]
  refine ⟨227181504441277405189873331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151454336294184936793248887 227181504441277405189873331)
  ·
    refine ⟨340772256661916107784809997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227181504441277405189873331 340772256661916107784809997)
    ·
      refine ⟨127789596248218540419303749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 340772256661916107784809997 127789596248218540419303749)
      ·
        refine ⟨23960549296540976328619453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 127789596248218540419303749 23960549296540976328619453)
        ·
          refine ⟨8985205986202866123232295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23960549296540976328619453 8985205986202866123232295)
          ·
            refine ⟨13477808979304299184848443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8985205986202866123232295 13477808979304299184848443)
            ·
              refine ⟨20216713468956448777272665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13477808979304299184848443 20216713468956448777272665)
              ·
                refine ⟨15162535101717336582954499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20216713468956448777272665 15162535101717336582954499)
                ·
                  refine ⟨22743802652576004874431749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15162535101717336582954499 22743802652576004874431749)
                  ·
                    refine ⟨4264462997358000913955953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22743802652576004874431749 4264462997358000913955953)
                    ·
                      refine ⟨3198347248018500685466965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4264462997358000913955953 3198347248018500685466965)
                      ·
                        rfl

theorem cell23_6228759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 1, 2, 1, 4, 2].length) (baseStart_6228759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6228759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6228759 prefixEnd_6228759 := by exact prefixLift 6228759
  have htrace : WordTrace (prefixWord ++ tailWord_6228759) baseStart_6228759 baseEnd_6228759 := by
    simpa [prefixWord, tailWord_6228759, baseEnd_6228759] using wordTrace_append hprefix tailTrace_6228759
  have hstable : (prefixWord ++ tailWord_6228759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6228759).length < 2 ^ (prefixWord ++ tailWord_6228759).sum := by decide
  have hdescent : baseEnd_6228759 < baseStart_6228759 := by decide
  rcases family_descends (prefixWord ++ tailWord_6228759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6228776 : List Nat := [2, 1, 5, 1, 1, 1, 4, 2, 2, 2, 2]
def baseStart_6228776 : Nat := 118140960795 + 6228776 * 2 ^ 59
def prefixEnd_6228776 : Nat := 4983230072969 + 3 ^ 40 * 6228776 * 2
def baseEnd_6228776 : Nat := 3198355977189627118954387

theorem tailTrace_6228776 : CollatzResearch.WordTrace tailWord_6228776 prefixEnd_6228776 3198355977189627118954387 := by
  unfold tailWord_6228776
  simp only [CollatzResearch.WordTrace]
  refine ⟨113591062241107908546621091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151454749654810544728828121 113591062241107908546621091)
  ·
    refine ⟨170386593361661862819931637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113591062241107908546621091 170386593361661862819931637)
    ·
      refine ⟨15973743127655799639368591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 170386593361661862819931637 15973743127655799639368591)
      ·
        refine ⟨23960614691483699459052887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15973743127655799639368591 23960614691483699459052887)
        ·
          refine ⟨35940922037225549188579331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23960614691483699459052887 35940922037225549188579331)
          ·
            refine ⟨53911383055838323782868997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35940922037225549188579331 53911383055838323782868997)
            ·
              refine ⟨10108384322969685709287937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 53911383055838323782868997 10108384322969685709287937)
              ·
                refine ⟨7581288242227264281965953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10108384322969685709287937 7581288242227264281965953)
                ·
                  refine ⟨5685966181670448211474465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7581288242227264281965953 5685966181670448211474465)
                  ·
                    refine ⟨4264474636252836158605849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5685966181670448211474465 4264474636252836158605849)
                    ·
                      refine ⟨3198355977189627118954387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4264474636252836158605849 3198355977189627118954387)
                      ·
                        rfl

theorem cell23_6228776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 4, 2, 2, 2, 2].length) (baseStart_6228776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6228776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6228776 prefixEnd_6228776 := by exact prefixLift 6228776
  have htrace : WordTrace (prefixWord ++ tailWord_6228776) baseStart_6228776 baseEnd_6228776 := by
    simpa [prefixWord, tailWord_6228776, baseEnd_6228776] using wordTrace_append hprefix tailTrace_6228776
  have hstable : (prefixWord ++ tailWord_6228776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6228776).length < 2 ^ (prefixWord ++ tailWord_6228776).sum := by decide
  have hdescent : baseEnd_6228776 < baseStart_6228776 := by decide
  rcases family_descends (prefixWord ++ tailWord_6228776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6228812 : List Nat := [2, 2, 1, 3, 3, 1, 3, 1, 2, 5]
def baseStart_6228812 : Nat := 118140960795 + 6228812 * 2 ^ 59
def prefixEnd_6228812 : Nat := 4983230072969 + 3 ^ 40 * 6228812 * 2
def baseEnd_6228812 : Nat := 1066124820831062992701407

theorem tailTrace_6228812 : CollatzResearch.WordTrace tailWord_6228812 prefixEnd_6228812 1066124820831062992701407 := by
  unfold tailWord_6228812
  simp only [CollatzResearch.WordTrace]
  refine ⟨113591718755042697620776345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151455625006723596827701793 113591718755042697620776345)
  ·
    refine ⟨85193789066282023215582259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113591718755042697620776345 85193789066282023215582259)
    ·
      refine ⟨127790683599423034823373389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85193789066282023215582259 127790683599423034823373389)
      ·
        refine ⟨47921506349783638058765021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 127790683599423034823373389 47921506349783638058765021)
        ·
          refine ⟨17970564881168864272036883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47921506349783638058765021 17970564881168864272036883)
          ·
            refine ⟨26955847321753296408055325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17970564881168864272036883 26955847321753296408055325)
            ·
              refine ⟨10108442745657486153020747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26955847321753296408055325 10108442745657486153020747)
              ·
                refine ⟨15162664118486229229531121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10108442745657486153020747 15162664118486229229531121)
                ·
                  refine ⟨11371998088864671922148341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15162664118486229229531121 11371998088864671922148341)
                  ·
                    refine ⟨1066124820831062992701407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11371998088864671922148341 1066124820831062992701407)
                    ·
                      rfl

theorem cell23_6228812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 3, 1, 2, 5].length) (baseStart_6228812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6228812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6228812 prefixEnd_6228812 := by exact prefixLift 6228812
  have htrace : WordTrace (prefixWord ++ tailWord_6228812) baseStart_6228812 baseEnd_6228812 := by
    simpa [prefixWord, tailWord_6228812, baseEnd_6228812] using wordTrace_append hprefix tailTrace_6228812
  have hstable : (prefixWord ++ tailWord_6228812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6228812).length < 2 ^ (prefixWord ++ tailWord_6228812).sum := by decide
  have hdescent : baseEnd_6228812 < baseStart_6228812 := by decide
  rcases family_descends (prefixWord ++ tailWord_6228812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6228832 : List Nat := [2, 1, 1, 3, 3, 1, 1, 1, 4, 4, 2]
def baseStart_6228832 : Nat := 118140960795 + 6228832 * 2 ^ 59
def prefixEnd_6228832 : Nat := 4983230072969 + 3 ^ 40 * 6228832 * 2
def baseEnd_6228832 : Nat := 3198384732106278899854129

theorem tailTrace_6228832 : CollatzResearch.WordTrace tailWord_6228832 prefixEnd_6228832 3198384732106278899854129 := by
  unfold tailWord_6228832
  simp only [CollatzResearch.WordTrace]
  refine ⟨113592083485006469328640375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151456111313341959104853833 113592083485006469328640375)
  ·
    refine ⟨170388125227509703992960563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113592083485006469328640375 170388125227509703992960563)
    ·
      refine ⟨255582187841264555989440845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170388125227509703992960563 255582187841264555989440845)
      ·
        refine ⟨95843320440474208496040317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 255582187841264555989440845 95843320440474208496040317)
        ·
          refine ⟨35941245165177828186015119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 95843320440474208496040317 35941245165177828186015119)
          ·
            refine ⟨53911867747766742279022679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35941245165177828186015119 53911867747766742279022679)
            ·
              refine ⟨80867801621650113418534019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53911867747766742279022679 80867801621650113418534019)
              ·
                refine ⟨121301702432475170127801029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 80867801621650113418534019 121301702432475170127801029)
                ·
                  refine ⟨22744069206089094398962693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 121301702432475170127801029 22744069206089094398962693)
                  ·
                    refine ⟨4264512976141705199805505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22744069206089094398962693 4264512976141705199805505)
                    ·
                      refine ⟨3198384732106278899854129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4264512976141705199805505 3198384732106278899854129)
                      ·
                        rfl

theorem cell23_6228832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 1, 4, 4, 2].length) (baseStart_6228832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6228832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6228832 prefixEnd_6228832 := by exact prefixLift 6228832
  have htrace : WordTrace (prefixWord ++ tailWord_6228832) baseStart_6228832 baseEnd_6228832 := by
    simpa [prefixWord, tailWord_6228832, baseEnd_6228832] using wordTrace_append hprefix tailTrace_6228832
  have hstable : (prefixWord ++ tailWord_6228832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6228832).length < 2 ^ (prefixWord ++ tailWord_6228832).sum := by decide
  have hdescent : baseEnd_6228832 < baseStart_6228832 := by decide
  rcases family_descends (prefixWord ++ tailWord_6228832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6228845 : List Nat := [1, 5, 1, 1, 1, 1, 1, 1, 4, 1, 6]
def baseStart_6228845 : Nat := 118140960795 + 6228845 * 2 ^ 59
def prefixEnd_6228845 : Nat := 4983230072969 + 3 ^ 40 * 6228845 * 2
def baseEnd_6228845 : Nat := 3198391407354787348991569

theorem tailTrace_6228845 : CollatzResearch.WordTrace tailWord_6228845 prefixEnd_6228845 3198391407354787348991569 := by
  unfold tailWord_6228845
  simp only [CollatzResearch.WordTrace]
  refine ⟨227184641118965841877503989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151456427412643894585002659 227184641118965841877503989)
  ·
    refine ⟨21298560104903047676015999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 227184641118965841877503989 21298560104903047676015999)
    ·
      refine ⟨31947840157354571514023999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21298560104903047676015999 31947840157354571514023999)
      ·
        refine ⟨47921760236031857271035999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31947840157354571514023999 47921760236031857271035999)
        ·
          refine ⟨71882640354047785906553999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47921760236031857271035999 71882640354047785906553999)
          ·
            refine ⟨107823960531071678859830999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71882640354047785906553999 107823960531071678859830999)
            ·
              refine ⟨161735940796607518289746499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 107823960531071678859830999 161735940796607518289746499)
              ·
                refine ⟨242603911194911277434619749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 161735940796607518289746499 242603911194911277434619749)
                ·
                  refine ⟨45488233349045864518991203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 242603911194911277434619749 45488233349045864518991203)
                  ·
                    refine ⟨68232350023568796778486805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 45488233349045864518991203 68232350023568796778486805)
                    ·
                      refine ⟨3198391407354787348991569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 68232350023568796778486805 3198391407354787348991569)
                      ·
                        rfl

theorem cell23_6228845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 1, 4, 1, 6].length) (baseStart_6228845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6228845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6228845 prefixEnd_6228845 := by exact prefixLift 6228845
  have htrace : WordTrace (prefixWord ++ tailWord_6228845) baseStart_6228845 baseEnd_6228845 := by
    simpa [prefixWord, tailWord_6228845, baseEnd_6228845] using wordTrace_append hprefix tailTrace_6228845
  have hstable : (prefixWord ++ tailWord_6228845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6228845).length < 2 ^ (prefixWord ++ tailWord_6228845).sum := by decide
  have hdescent : baseEnd_6228845 < baseStart_6228845 := by decide
  rcases family_descends (prefixWord ++ tailWord_6228845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6228855 : List Nat := [1, 1, 3, 1, 1, 2, 1, 7, 6]
def baseStart_6228855 : Nat := 118140960795 + 6228855 * 2 ^ 59
def prefixEnd_6228855 : Nat := 4983230072969 + 3 ^ 40 * 6228855 * 2
def baseEnd_6228855 : Nat := 355377393573481367762947

theorem tailTrace_6228855 : CollatzResearch.WordTrace tailWord_6228855 prefixEnd_6228855 355377393573481367762947 := by
  unfold tailWord_6228855
  simp only [CollatzResearch.WordTrace]
  refine ⟨227185005848929613585368019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151456670565953075723578679 227185005848929613585368019)
  ·
    refine ⟨340777508773394420378052029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227185005848929613585368019 340777508773394420378052029)
    ·
      refine ⟨127791565790022907641769511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 340777508773394420378052029 127791565790022907641769511)
      ·
        refine ⟨191687348685034361462654267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127791565790022907641769511 191687348685034361462654267)
        ·
          refine ⟨287531023027551542193981401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 191687348685034361462654267 287531023027551542193981401)
          ·
            refine ⟨215648267270663656645486051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 287531023027551542193981401 215648267270663656645486051)
            ·
              refine ⟨323472400905995484968229077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 215648267270663656645486051 323472400905995484968229077)
              ·
                refine ⟨7581384396234269178942869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 323472400905995484968229077 7581384396234269178942869)
                ·
                  refine ⟨355377393573481367762947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7581384396234269178942869 355377393573481367762947)
                  ·
                    rfl

theorem cell23_6228855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 7, 6].length) (baseStart_6228855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6228855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6228855 prefixEnd_6228855 := by exact prefixLift 6228855
  have htrace : WordTrace (prefixWord ++ tailWord_6228855) baseStart_6228855 baseEnd_6228855 := by
    simpa [prefixWord, tailWord_6228855, baseEnd_6228855] using wordTrace_append hprefix tailTrace_6228855
  have hstable : (prefixWord ++ tailWord_6228855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6228855).length < 2 ^ (prefixWord ++ tailWord_6228855).sum := by decide
  have hdescent : baseEnd_6228855 < baseStart_6228855 := by decide
  rcases family_descends (prefixWord ++ tailWord_6228855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6228899 : List Nat := [1, 1, 1, 4, 1, 2, 5, 1, 3, 1, 3]
def baseStart_6228899 : Nat := 118140960795 + 6228899 * 2 ^ 59
def prefixEnd_6228899 : Nat := 4983230072969 + 3 ^ 40 * 6228899 * 2
def baseEnd_6228899 : Nat := 3198419135310130137716321

theorem tailTrace_6228899 : CollatzResearch.WordTrace tailWord_6228899 prefixEnd_6228899 3198419135310130137716321 := by
  unfold tailWord_6228899
  simp only [CollatzResearch.WordTrace]
  refine ⟨227186610660770209099969751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151457740440513472733313167 227186610660770209099969751)
  ·
    refine ⟨340779915991155313649954627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227186610660770209099969751 340779915991155313649954627)
    ·
      refine ⟨511169873986732970474931941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 340779915991155313649954627 511169873986732970474931941)
      ·
        refine ⟨95844351372512431964049739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 511169873986732970474931941 95844351372512431964049739)
        ·
          refine ⟨143766527058768647946074609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95844351372512431964049739 143766527058768647946074609)
          ·
            refine ⟨107824895294076485959555957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 143766527058768647946074609 107824895294076485959555957)
            ·
              refine ⟨10108583933819670558708371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 107824895294076485959555957 10108583933819670558708371)
              ·
                refine ⟨15162875900729505838062557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10108583933819670558708371 15162875900729505838062557)
                ·
                  refine ⟨5686078462773564689273459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15162875900729505838062557 5686078462773564689273459)
                  ·
                    refine ⟨8529117694160347033910189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5686078462773564689273459 8529117694160347033910189)
                    ·
                      refine ⟨3198419135310130137716321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8529117694160347033910189 3198419135310130137716321)
                      ·
                        rfl

theorem cell23_6228899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 5, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 5, 1, 3, 1, 3].length) (baseStart_6228899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6228899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6228899 prefixEnd_6228899 := by exact prefixLift 6228899
  have htrace : WordTrace (prefixWord ++ tailWord_6228899) baseStart_6228899 baseEnd_6228899 := by
    simpa [prefixWord, tailWord_6228899, baseEnd_6228899] using wordTrace_append hprefix tailTrace_6228899
  have hstable : (prefixWord ++ tailWord_6228899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6228899).length < 2 ^ (prefixWord ++ tailWord_6228899).sum := by decide
  have hdescent : baseEnd_6228899 < baseStart_6228899 := by decide
  rcases family_descends (prefixWord ++ tailWord_6228899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6228922 : List Nat := [3, 1, 1, 1, 2, 1, 5, 1, 3, 1, 4]
def baseStart_6228922 : Nat := 118140960795 + 6228922 * 2 ^ 59
def prefixEnd_6228922 : Nat := 4983230072969 + 3 ^ 40 * 6228922 * 2
def baseEnd_6228922 : Nat := 3198430945365183547728715

theorem tailTrace_6228922 : CollatzResearch.WordTrace tailWord_6228922 prefixEnd_6228922 3198430945365183547728715 := by
  unfold tailWord_6228922
  simp only [CollatzResearch.WordTrace]
  refine ⟨56796862384921721007014255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151458299693124589352038013 56796862384921721007014255)
  ·
    refine ⟨85195293577382581510521383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56796862384921721007014255 85195293577382581510521383)
    ·
      refine ⟨127792940366073872265782075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85195293577382581510521383 127792940366073872265782075)
      ·
        refine ⟨191689410549110808398673113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127792940366073872265782075 191689410549110808398673113)
        ·
          refine ⟨143767057911833106299004835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 191689410549110808398673113 143767057911833106299004835)
          ·
            refine ⟨215650586867749659448507253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 143767057911833106299004835 215650586867749659448507253)
            ·
              refine ⟨20217242518851530573297555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 215650586867749659448507253 20217242518851530573297555)
              ·
                refine ⟨30325863778277295859946333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20217242518851530573297555 30325863778277295859946333)
                ·
                  refine ⟨11372198916853985947479875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30325863778277295859946333 11372198916853985947479875)
                  ·
                    refine ⟨17058298375280978921219813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11372198916853985947479875 17058298375280978921219813)
                    ·
                      refine ⟨3198430945365183547728715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17058298375280978921219813 3198430945365183547728715)
                      ·
                        rfl

theorem cell23_6228922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 5, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 5, 1, 3, 1, 4].length) (baseStart_6228922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6228922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6228922 prefixEnd_6228922 := by exact prefixLift 6228922
  have htrace : WordTrace (prefixWord ++ tailWord_6228922) baseStart_6228922 baseEnd_6228922 := by
    simpa [prefixWord, tailWord_6228922, baseEnd_6228922] using wordTrace_append hprefix tailTrace_6228922
  have hstable : (prefixWord ++ tailWord_6228922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6228922).length < 2 ^ (prefixWord ++ tailWord_6228922).sum := by decide
  have hdescent : baseEnd_6228922 < baseStart_6228922 := by decide
  rcases family_descends (prefixWord ++ tailWord_6228922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6228926 : List Nat := [4, 2, 1, 1, 1, 2, 4, 1, 2, 3, 2]
def baseStart_6228926 : Nat := 118140960795 + 6228926 * 2 ^ 59
def prefixEnd_6228926 : Nat := 4983230072969 + 3 ^ 40 * 6228926 * 2
def baseEnd_6228926 : Nat := 3198432999287801532078697

theorem tailTrace_6228926 : CollatzResearch.WordTrace tailWord_6228926 prefixEnd_6228926 3198432999287801532078697 := by
  unfold tailWord_6228926
  simp only [CollatzResearch.WordTrace]
  refine ⟨28398449428959049088900329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 151458396954448261807468421 28398449428959049088900329)
  ·
    refine ⟨21298837071719286816675247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28398449428959049088900329 21298837071719286816675247)
    ·
      refine ⟨31948255607578930225012871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21298837071719286816675247 31948255607578930225012871)
      ·
        refine ⟨47922383411368395337519307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31948255607578930225012871 47922383411368395337519307)
        ·
          refine ⟨71883575117052593006278961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47922383411368395337519307 71883575117052593006278961)
          ·
            refine ⟨53912681337789444754709221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71883575117052593006278961 53912681337789444754709221)
            ·
              refine ⟨10108627750835520891507979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 53912681337789444754709221 10108627750835520891507979)
              ·
                refine ⟨15162941626253281337261969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10108627750835520891507979 15162941626253281337261969)
                ·
                  refine ⟨11372206219689961002946477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15162941626253281337261969 11372206219689961002946477)
                  ·
                    refine ⟨4264577332383735376104929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11372206219689961002946477 4264577332383735376104929)
                    ·
                      refine ⟨3198432999287801532078697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4264577332383735376104929 3198432999287801532078697)
                      ·
                        rfl

theorem cell23_6228926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 4, 1, 2, 3, 2].length) (baseStart_6228926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6228926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6228926 prefixEnd_6228926 := by exact prefixLift 6228926
  have htrace : WordTrace (prefixWord ++ tailWord_6228926) baseStart_6228926 baseEnd_6228926 := by
    simpa [prefixWord, tailWord_6228926, baseEnd_6228926] using wordTrace_append hprefix tailTrace_6228926
  have hstable : (prefixWord ++ tailWord_6228926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6228926).length < 2 ^ (prefixWord ++ tailWord_6228926).sum := by decide
  have hdescent : baseEnd_6228926 < baseStart_6228926 := by decide
  rcases family_descends (prefixWord ++ tailWord_6228926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6228936 : List Nat := [2, 1, 3, 1, 5, 1, 3, 1, 1, 5]
def baseStart_6228936 : Nat := 118140960795 + 6228936 * 2 ^ 59
def prefixEnd_6228936 : Nat := 4983230072969 + 3 ^ 40 * 6228936 * 2
def baseEnd_6228936 : Nat := 1066146044698115497651217

theorem tailTrace_6228936 : CollatzResearch.WordTrace tailWord_6228936 prefixEnd_6228936 1066146044698115497651217 := by
  unfold tailWord_6228936
  simp only [CollatzResearch.WordTrace]
  refine ⟨113593980080818082209533331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151458640107757442946044441 113593980080818082209533331)
  ·
    refine ⟨170390970121227123314299997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113593980080818082209533331 170390970121227123314299997)
    ·
      refine ⟨63896613795460171242862499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 170390970121227123314299997 63896613795460171242862499)
      ·
        refine ⟨95844920693190256864293749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63896613795460171242862499 95844920693190256864293749)
        ·
          refine ⟨8985461314986586581027539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 95844920693190256864293749 8985461314986586581027539)
          ·
            refine ⟨13478191972479879871541309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8985461314986586581027539 13478191972479879871541309)
            ·
              refine ⟨5054321989679954951827991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13478191972479879871541309 5054321989679954951827991)
              ·
                refine ⟨7581482984519932427741987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5054321989679954951827991 7581482984519932427741987)
                ·
                  refine ⟨11372224476779898641612981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7581482984519932427741987 11372224476779898641612981)
                  ·
                    refine ⟨1066146044698115497651217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11372224476779898641612981 1066146044698115497651217)
                    ·
                      rfl

theorem cell23_6228936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 3, 1, 1, 5].length) (baseStart_6228936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6228936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6228936 prefixEnd_6228936 := by exact prefixLift 6228936
  have htrace : WordTrace (prefixWord ++ tailWord_6228936) baseStart_6228936 baseEnd_6228936 := by
    simpa [prefixWord, tailWord_6228936, baseEnd_6228936] using wordTrace_append hprefix tailTrace_6228936
  have hstable : (prefixWord ++ tailWord_6228936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6228936).length < 2 ^ (prefixWord ++ tailWord_6228936).sum := by decide
  have hdescent : baseEnd_6228936 < baseStart_6228936 := by decide
  rcases family_descends (prefixWord ++ tailWord_6228936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6228950 : List Nat := [5, 2, 1, 1, 2, 2, 1, 4, 1, 1, 3]
def baseStart_6228950 : Nat := 118140960795 + 6228950 * 2 ^ 59
def prefixEnd_6228950 : Nat := 4983230072969 + 3 ^ 40 * 6228950 * 2
def baseEnd_6228950 : Nat := 3198445322823509438178587

theorem tailTrace_6228950 : CollatzResearch.WordTrace tailWord_6228950 prefixEnd_6228950 3198445322823509438178587 := by
  unfold tailWord_6228950
  simp only [CollatzResearch.WordTrace]
  refine ⟨14199279423974090300629769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 151458980522390296540050869 14199279423974090300629769)
  ·
    refine ⟨10649459567980567725472327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14199279423974090300629769 10649459567980567725472327)
    ·
      refine ⟨15974189351970851588208491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10649459567980567725472327 15974189351970851588208491)
      ·
        refine ⟨23961284027956277382312737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15974189351970851588208491 23961284027956277382312737)
        ·
          refine ⟨17970963020967208036734553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23961284027956277382312737 17970963020967208036734553)
          ·
            refine ⟨13478222265725406027550915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17970963020967208036734553 13478222265725406027550915)
            ·
              refine ⟨20217333398588109041326373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13478222265725406027550915 20217333398588109041326373)
              ·
                refine ⟨3790750012235270445248695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20217333398588109041326373 3790750012235270445248695)
                ·
                  refine ⟨5686125018352905667873043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3790750012235270445248695 5686125018352905667873043)
                  ·
                    refine ⟨8529187527529358501809565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5686125018352905667873043 8529187527529358501809565)
                    ·
                      refine ⟨3198445322823509438178587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8529187527529358501809565 3198445322823509438178587)
                      ·
                        rfl

theorem cell23_6228950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 1, 4, 1, 1, 3].length) (baseStart_6228950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6228950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6228950 prefixEnd_6228950 := by exact prefixLift 6228950
  have htrace : WordTrace (prefixWord ++ tailWord_6228950) baseStart_6228950 baseEnd_6228950 := by
    simpa [prefixWord, tailWord_6228950, baseEnd_6228950] using wordTrace_append hprefix tailTrace_6228950
  have hstable : (prefixWord ++ tailWord_6228950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6228950).length < 2 ^ (prefixWord ++ tailWord_6228950).sum := by decide
  have hdescent : baseEnd_6228950 < baseStart_6228950 := by decide
  rcases family_descends (prefixWord ++ tailWord_6228950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6228989 : List Nat := [1, 4, 1, 1, 1, 2, 1, 4, 4, 1, 3]
def baseStart_6228989 : Nat := 118140960795 + 6228989 * 2 ^ 59
def prefixEnd_6228989 : Nat := 4983230072969 + 3 ^ 40 * 6228989 * 2
def baseEnd_6228989 : Nat := 3198465348569034785590907

theorem tailTrace_6228989 : CollatzResearch.WordTrace tailWord_6228989 prefixEnd_6228989 3198465348569034785590907 := by
  unfold tailWord_6228989
  simp only [CollatzResearch.WordTrace]
  refine ⟨227189893230444154470746021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151459928820296102980497347 227189893230444154470746021)
  ·
    refine ⟨42598104980708278963264879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 227189893230444154470746021 42598104980708278963264879)
    ·
      refine ⟨63897157471062418444897319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42598104980708278963264879 63897157471062418444897319)
      ·
        refine ⟨95845736206593627667345979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63897157471062418444897319 95845736206593627667345979)
        ·
          refine ⟨143768604309890441501018969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95845736206593627667345979 143768604309890441501018969)
          ·
            refine ⟨107826453232417831125764227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 143768604309890441501018969 107826453232417831125764227)
            ·
              refine ⟨161739679848626746688646341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 107826453232417831125764227 161739679848626746688646341)
              ·
                refine ⟨30326189971617515004121189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 161739679848626746688646341 30326189971617515004121189)
                ·
                  refine ⟨5686160619678284063272723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30326189971617515004121189 5686160619678284063272723)
                  ·
                    refine ⟨8529240929517426094909085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5686160619678284063272723 8529240929517426094909085)
                    ·
                      refine ⟨3198465348569034785590907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8529240929517426094909085 3198465348569034785590907)
                      ·
                        rfl

theorem cell23_6228989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 4, 4, 1, 3].length) (baseStart_6228989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6228989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6228989 prefixEnd_6228989 := by exact prefixLift 6228989
  have htrace : WordTrace (prefixWord ++ tailWord_6228989) baseStart_6228989 baseEnd_6228989 := by
    simpa [prefixWord, tailWord_6228989, baseEnd_6228989] using wordTrace_append hprefix tailTrace_6228989
  have hstable : (prefixWord ++ tailWord_6228989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6228989).length < 2 ^ (prefixWord ++ tailWord_6228989).sum := by decide
  have hdescent : baseEnd_6228989 < baseStart_6228989 := by decide
  rcases family_descends (prefixWord ++ tailWord_6228989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6228990 : List Nat := [4, 2, 2, 2, 2, 2, 2, 1, 1, 1, 4]
def baseStart_6228990 : Nat := 118140960795 + 6228990 * 2 ^ 59
def prefixEnd_6228990 : Nat := 4983230072969 + 3 ^ 40 * 6228990 * 2
def baseEnd_6228990 : Nat := 3198465862049689281678403

theorem tailTrace_6228990 : CollatzResearch.WordTrace tailWord_6228990 prefixEnd_6228990 3198465862049689281678403 := by
  unfold tailWord_6228990
  simp only [CollatzResearch.WordTrace]
  refine ⟨28398741212930066455191553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 151459953135627021094354949 28398741212930066455191553)
  ·
    refine ⟨21299055909697549841393665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28398741212930066455191553 21299055909697549841393665)
    ·
      refine ⟨15974291932273162381045249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21299055909697549841393665 15974291932273162381045249)
      ·
        refine ⟨11980718949204871785783937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15974291932273162381045249 11980718949204871785783937)
        ·
          refine ⟨8985539211903653839337953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11980718949204871785783937 8985539211903653839337953)
          ·
            refine ⟨6739154408927740379503465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8985539211903653839337953 6739154408927740379503465)
            ·
              refine ⟨5054365806695805284627599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6739154408927740379503465 5054365806695805284627599)
              ·
                refine ⟨7581548710043707926941399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5054365806695805284627599 7581548710043707926941399)
                ·
                  refine ⟨11372323065065561890412099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7581548710043707926941399 11372323065065561890412099)
                  ·
                    refine ⟨17058484597598342835618149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11372323065065561890412099 17058484597598342835618149)
                    ·
                      refine ⟨3198465862049689281678403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17058484597598342835618149 3198465862049689281678403)
                      ·
                        rfl

theorem cell23_6228990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 2, 2, 1, 1, 1, 4].length) (baseStart_6228990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6228990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6228990 prefixEnd_6228990 := by exact prefixLift 6228990
  have htrace : WordTrace (prefixWord ++ tailWord_6228990) baseStart_6228990 baseEnd_6228990 := by
    simpa [prefixWord, tailWord_6228990, baseEnd_6228990] using wordTrace_append hprefix tailTrace_6228990
  have hstable : (prefixWord ++ tailWord_6228990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6228990).length < 2 ^ (prefixWord ++ tailWord_6228990).sum := by decide
  have hdescent : baseEnd_6228990 < baseStart_6228990 := by decide
  rcases family_descends (prefixWord ++ tailWord_6228990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6228993 : List Nat := [1, 2, 4, 1, 2, 4, 2, 1, 1, 2, 3]
def baseStart_6228993 : Nat := 118140960795 + 6228993 * 2 ^ 59
def prefixEnd_6228993 : Nat := 4983230072969 + 3 ^ 40 * 6228993 * 2
def baseEnd_6228993 : Nat := 3198467402491652769940889

theorem tailTrace_6228993 : CollatzResearch.WordTrace tailWord_6228993 prefixEnd_6228993 3198467402491652769940889 := by
  unfold tailWord_6228993
  simp only [CollatzResearch.WordTrace]
  refine ⟨227190039122429663153891633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151460026081619775435927755 227190039122429663153891633)
  ·
    refine ⟨170392529341822247365418725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 227190039122429663153891633 170392529341822247365418725)
    ·
      refine ⟨31948599251591671381016011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 170392529341822247365418725 31948599251591671381016011)
      ·
        refine ⟨47922898877387507071524017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31948599251591671381016011 47922898877387507071524017)
        ·
          refine ⟨35942174158040630303643013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47922898877387507071524017 35942174158040630303643013)
          ·
            refine ⟨6739157654632618181933065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35942174158040630303643013 6739157654632618181933065)
            ·
              refine ⟨5054368240974463636449799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6739157654632618181933065 5054368240974463636449799)
              ·
                refine ⟨7581552361461695454674699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5054368240974463636449799 7581552361461695454674699)
                ·
                  refine ⟨11372328542192543182012049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7581552361461695454674699 11372328542192543182012049)
                  ·
                    refine ⟨8529246406644407386509037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11372328542192543182012049 8529246406644407386509037)
                    ·
                      refine ⟨3198467402491652769940889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8529246406644407386509037 3198467402491652769940889)
                      ·
                        rfl

theorem cell23_6228993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 4, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 4, 2, 1, 1, 2, 3].length) (baseStart_6228993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6228993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6228993 prefixEnd_6228993 := by exact prefixLift 6228993
  have htrace : WordTrace (prefixWord ++ tailWord_6228993) baseStart_6228993 baseEnd_6228993 := by
    simpa [prefixWord, tailWord_6228993, baseEnd_6228993] using wordTrace_append hprefix tailTrace_6228993
  have hstable : (prefixWord ++ tailWord_6228993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6228993).length < 2 ^ (prefixWord ++ tailWord_6228993).sum := by decide
  have hdescent : baseEnd_6228993 < baseStart_6228993 := by decide
  rcases family_descends (prefixWord ++ tailWord_6228993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6229006 : List Nat := [4, 1, 1, 2, 2, 3, 1, 1, 4, 1, 3]
def baseStart_6229006 : Nat := 118140960795 + 6229006 * 2 ^ 59
def prefixEnd_6229006 : Nat := 4983230072969 + 3 ^ 40 * 6229006 * 2
def baseEnd_6229006 : Nat := 3198474077740161219078329

theorem tailTrace_6229006 : CollatzResearch.WordTrace tailWord_6229006 prefixEnd_6229006 3198474077740161219078329 := by
  unfold tailWord_6229006
  simp only [CollatzResearch.WordTrace]
  refine ⟨28398814158922820796764359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 151460342180921710916076581 28398814158922820796764359)
  ·
    refine ⟨42598221238384231195146539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28398814158922820796764359 42598221238384231195146539)
    ·
      refine ⟨63897331857576346792719809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42598221238384231195146539 63897331857576346792719809)
      ·
        refine ⟨47922998893182260094539857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63897331857576346792719809 47922998893182260094539857)
        ·
          refine ⟨35942249169886695070904893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47922998893182260094539857 35942249169886695070904893)
          ·
            refine ⟨13478343438707510651589335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35942249169886695070904893 13478343438707510651589335)
            ·
              refine ⟨20217515158061265977384003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13478343438707510651589335 20217515158061265977384003)
              ·
                refine ⟨30326272737091898966076005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20217515158061265977384003 30326272737091898966076005)
                ·
                  refine ⟨5686176138204731056139251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30326272737091898966076005 5686176138204731056139251)
                  ·
                    refine ⟨8529264207307096584208877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5686176138204731056139251 8529264207307096584208877)
                    ·
                      refine ⟨3198474077740161219078329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8529264207307096584208877 3198474077740161219078329)
                      ·
                        rfl

theorem cell23_6229006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 1, 1, 4, 1, 3].length) (baseStart_6229006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6229006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6229006 prefixEnd_6229006 := by exact prefixLift 6229006
  have htrace : WordTrace (prefixWord ++ tailWord_6229006) baseStart_6229006 baseEnd_6229006 := by
    simpa [prefixWord, tailWord_6229006, baseEnd_6229006] using wordTrace_append hprefix tailTrace_6229006
  have hstable : (prefixWord ++ tailWord_6229006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6229006).length < 2 ^ (prefixWord ++ tailWord_6229006).sum := by decide
  have hdescent : baseEnd_6229006 < baseStart_6229006 := by decide
  rcases family_descends (prefixWord ++ tailWord_6229006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6229023 : List Nat := [1, 1, 2, 4, 1, 4, 3, 1, 2, 1, 3]
def baseStart_6229023 : Nat := 118140960795 + 6229023 * 2 ^ 59
def prefixEnd_6229023 : Nat := 4983230072969 + 3 ^ 40 * 6229023 * 2
def baseEnd_6229023 : Nat := 3198482806911287652565751

theorem tailTrace_6229023 : CollatzResearch.WordTrace tailWord_6229023 prefixEnd_6229023 3198482806911287652565751 := by
  unfold tailWord_6229023
  simp only [CollatzResearch.WordTrace]
  refine ⟨227191133312320978277483723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151460755541547318851655815 227191133312320978277483723)
  ·
    refine ⟨340786699968481467416225585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227191133312320978277483723 340786699968481467416225585)
    ·
      refine ⟨255590024976361100562169189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 340786699968481467416225585 255590024976361100562169189)
      ·
        refine ⟨47923129683067706355406723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 255590024976361100562169189 47923129683067706355406723)
        ·
          refine ⟨71884694524601559533110085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47923129683067706355406723 71884694524601559533110085)
          ·
            refine ⟨13478380223362792412458141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 71884694524601559533110085 13478380223362792412458141)
            ·
              refine ⟨5054392583761047154671803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13478380223362792412458141 5054392583761047154671803)
              ·
                refine ⟨7581588875641570732007705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5054392583761047154671803 7581588875641570732007705)
                ·
                  refine ⟨5686191656731178049005779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7581588875641570732007705 5686191656731178049005779)
                  ·
                    refine ⟨8529287485096767073508669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5686191656731178049005779 8529287485096767073508669)
                    ·
                      refine ⟨3198482806911287652565751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8529287485096767073508669 3198482806911287652565751)
                      ·
                        rfl

theorem cell23_6229023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 3, 1, 2, 1, 3].length) (baseStart_6229023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6229023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6229023 prefixEnd_6229023 := by exact prefixLift 6229023
  have htrace : WordTrace (prefixWord ++ tailWord_6229023) baseStart_6229023 baseEnd_6229023 := by
    simpa [prefixWord, tailWord_6229023, baseEnd_6229023] using wordTrace_append hprefix tailTrace_6229023
  have hstable : (prefixWord ++ tailWord_6229023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6229023).length < 2 ^ (prefixWord ++ tailWord_6229023).sum := by decide
  have hdescent : baseEnd_6229023 < baseStart_6229023 := by decide
  rcases family_descends (prefixWord ++ tailWord_6229023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6229049 : List Nat := [1, 2, 1, 5, 2, 2, 1, 1, 2, 1, 5]
def baseStart_6229049 : Nat := 118140960795 + 6229049 * 2 ^ 59
def prefixEnd_6229049 : Nat := 4983230072969 + 3 ^ 40 * 6229049 * 2
def baseEnd_6229049 : Nat := 3198496157408304550840631

theorem tailTrace_6229049 : CollatzResearch.WordTrace tailWord_6229049 prefixEnd_6229049 3198496157408304550840631 := by
  unfold tailWord_6229049
  simp only [CollatzResearch.WordTrace]
  refine ⟨227192081610226784717930201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151461387740151189811953467 227192081610226784717930201)
  ·
    refine ⟨170394061207670088538447651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 227192081610226784717930201 170394061207670088538447651)
    ·
      refine ⟨255591091811505132807671477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170394061207670088538447651 255591091811505132807671477)
      ·
        refine ⟨23961664857328606200719201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 255591091811505132807671477 23961664857328606200719201)
        ·
          refine ⟨17971248642996454650539401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23961664857328606200719201 17971248642996454650539401)
          ·
            refine ⟨13478436482247340987904551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17971248642996454650539401 13478436482247340987904551)
            ·
              refine ⟨20217654723371011481856827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13478436482247340987904551 20217654723371011481856827)
              ·
                refine ⟨30326482085056517222785241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20217654723371011481856827 30326482085056517222785241)
                ·
                  refine ⟨22744861563792387917088931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30326482085056517222785241 22744861563792387917088931)
                  ·
                    refine ⟨34117292345688581875633397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22744861563792387917088931 34117292345688581875633397)
                    ·
                      refine ⟨3198496157408304550840631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34117292345688581875633397 3198496157408304550840631)
                      ·
                        rfl

theorem cell23_6229049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 1, 1, 2, 1, 5].length) (baseStart_6229049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6229049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6229049 prefixEnd_6229049 := by exact prefixLift 6229049
  have htrace : WordTrace (prefixWord ++ tailWord_6229049) baseStart_6229049 baseEnd_6229049 := by
    simpa [prefixWord, tailWord_6229049, baseEnd_6229049] using wordTrace_append hprefix tailTrace_6229049
  have hstable : (prefixWord ++ tailWord_6229049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6229049).length < 2 ^ (prefixWord ++ tailWord_6229049).sum := by decide
  have hdescent : baseEnd_6229049 < baseStart_6229049 := by decide
  rcases family_descends (prefixWord ++ tailWord_6229049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6229082 : List Nat := [3, 1, 1, 2, 1, 1, 2, 4, 1, 7]
def baseStart_6229082 : Nat := 118140960795 + 6229082 * 2 ^ 59
def prefixEnd_6229082 : Nat := 4983230072969 + 3 ^ 40 * 6229082 * 2
def baseEnd_6229082 : Nat := 1066171034089967640575993

theorem tailTrace_6229082 : CollatzResearch.WordTrace tailWord_6229082 prefixEnd_6229082 1066171034089967640575993 := by
  unfold tailWord_6229082
  simp only [CollatzResearch.WordTrace]
  refine ⟨56798321304776807838470375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151462190146071487569254333 56798321304776807838470375)
  ·
    refine ⟨85197481957165211757705563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56798321304776807838470375 85197481957165211757705563)
    ·
      refine ⟨127796222935747817636558345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85197481957165211757705563 127796222935747817636558345)
      ·
        refine ⟨95847167201810863227418759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 127796222935747817636558345 95847167201810863227418759)
        ·
          refine ⟨143770750802716294841128139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95847167201810863227418759 143770750802716294841128139)
          ·
            refine ⟨215656126204074442261692209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 143770750802716294841128139 215656126204074442261692209)
            ·
              refine ⟨161742094653055831696269157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 215656126204074442261692209 161742094653055831696269157)
              ·
                refine ⟨30326642747447968443050467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 161742094653055831696269157 30326642747447968443050467)
                ·
                  refine ⟨45489964121171952664575701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30326642747447968443050467 45489964121171952664575701)
                  ·
                    refine ⟨1066171034089967640575993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 45489964121171952664575701 1066171034089967640575993)
                    ·
                      rfl

theorem cell23_6229082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 4, 1, 7].length) (baseStart_6229082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6229082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6229082 prefixEnd_6229082 := by exact prefixLift 6229082
  have htrace : WordTrace (prefixWord ++ tailWord_6229082) baseStart_6229082 baseEnd_6229082 := by
    simpa [prefixWord, tailWord_6229082, baseEnd_6229082] using wordTrace_append hprefix tailTrace_6229082
  have hstable : (prefixWord ++ tailWord_6229082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6229082).length < 2 ^ (prefixWord ++ tailWord_6229082).sum := by decide
  have hdescent : baseEnd_6229082 < baseStart_6229082 := by decide
  rcases family_descends (prefixWord ++ tailWord_6229082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6229092 : List Nat := [2, 3, 1, 1, 2, 1, 1, 1, 3, 1, 7]
def baseStart_6229092 : Nat := 118140960795 + 6229092 * 2 ^ 59
def prefixEnd_6229092 : Nat := 4983230072969 + 3 ^ 40 * 6229092 * 2
def baseEnd_6229092 : Nat := 3198518237076447882602933

theorem tailTrace_6229092 : CollatzResearch.WordTrace tailWord_6229092 prefixEnd_6229092 3198518237076447882602933 := by
  unfold tailWord_6229092
  simp only [CollatzResearch.WordTrace]
  refine ⟨113596824974535501530872765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151462433299380668707830353 113596824974535501530872765)
  ·
    refine ⟨42598809365450813074077287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113596824974535501530872765 42598809365450813074077287)
    ·
      refine ⟨63898214048176219611115931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42598809365450813074077287 63898214048176219611115931)
      ·
        refine ⟨95847321072264329416673897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63898214048176219611115931 95847321072264329416673897)
        ·
          refine ⟨71885490804198247062505423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95847321072264329416673897 71885490804198247062505423)
          ·
            refine ⟨107828236206297370593758135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71885490804198247062505423 107828236206297370593758135)
            ·
              refine ⟨161742354309446055890637203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 107828236206297370593758135 161742354309446055890637203)
              ·
                refine ⟨242613531464169083835955805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 161742354309446055890637203 242613531464169083835955805)
                ·
                  refine ⟨90980074299063406438483427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 242613531464169083835955805 90980074299063406438483427)
                  ·
                    refine ⟨136470111448595109657725141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 90980074299063406438483427 136470111448595109657725141)
                    ·
                      refine ⟨3198518237076447882602933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 136470111448595109657725141 3198518237076447882602933)
                      ·
                        rfl

theorem cell23_6229092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 1, 3, 1, 7].length) (baseStart_6229092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6229092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6229092 prefixEnd_6229092 := by exact prefixLift 6229092
  have htrace : WordTrace (prefixWord ++ tailWord_6229092) baseStart_6229092 baseEnd_6229092 := by
    simpa [prefixWord, tailWord_6229092, baseEnd_6229092] using wordTrace_append hprefix tailTrace_6229092
  have hstable : (prefixWord ++ tailWord_6229092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6229092).length < 2 ^ (prefixWord ++ tailWord_6229092).sum := by decide
  have hdescent : baseEnd_6229092 < baseStart_6229092 := by decide
  rcases family_descends (prefixWord ++ tailWord_6229092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6229119 : List Nat := [1, 1, 2, 2, 1, 1, 1, 1, 5, 6, 2]
def baseStart_6229119 : Nat := 118140960795 + 6229119 * 2 ^ 59
def prefixEnd_6229119 : Nat := 4983230072969 + 3 ^ 40 * 6229119 * 2
def baseEnd_6229119 : Nat := 3198532101054119276965309

theorem tailTrace_6229119 : CollatzResearch.WordTrace tailWord_6229119 prefixEnd_6229119 3198532101054119276965309 := by
  unfold tailWord_6229119
  simp only [CollatzResearch.WordTrace]
  refine ⟨227194634719973186672978411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151463089813315457781985607 227194634719973186672978411)
  ·
    refine ⟨340791952079959780009467617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227194634719973186672978411 340791952079959780009467617)
    ·
      refine ⟨255593964059969835007100713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 340791952079959780009467617 255593964059969835007100713)
      ·
        refine ⟨191695473044977376255325535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 255593964059969835007100713 191695473044977376255325535)
        ·
          refine ⟨287543209567466064382988303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 191695473044977376255325535 287543209567466064382988303)
          ·
            refine ⟨431314814351199096574482455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 287543209567466064382988303 431314814351199096574482455)
            ·
              refine ⟨646972221526798644861723683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 431314814351199096574482455 646972221526798644861723683)
              ·
                refine ⟨970458332290197967292585525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 646972221526798644861723683 970458332290197967292585525)
                ·
                  refine ⟨90980468652206059433679893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 970458332290197967292585525 90980468652206059433679893)
                  ·
                    refine ⟨4264709468072159035953745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 90980468652206059433679893 4264709468072159035953745)
                    ·
                      refine ⟨3198532101054119276965309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4264709468072159035953745 3198532101054119276965309)
                      ·
                        rfl

theorem cell23_6229119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 1, 5, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 1, 5, 6, 2].length) (baseStart_6229119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6229119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6229119 prefixEnd_6229119 := by exact prefixLift 6229119
  have htrace : WordTrace (prefixWord ++ tailWord_6229119) baseStart_6229119 baseEnd_6229119 := by
    simpa [prefixWord, tailWord_6229119, baseEnd_6229119] using wordTrace_append hprefix tailTrace_6229119
  have hstable : (prefixWord ++ tailWord_6229119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6229119).length < 2 ^ (prefixWord ++ tailWord_6229119).sum := by decide
  have hdescent : baseEnd_6229119 < baseStart_6229119 := by decide
  rcases family_descends (prefixWord ++ tailWord_6229119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6229139 : List Nat := [1, 1, 1, 2, 1, 2, 4, 2, 4, 2, 3]
def baseStart_6229139 : Nat := 118140960795 + 6229139 * 2 ^ 59
def prefixEnd_6229139 : Nat := 4983230072969 + 3 ^ 40 * 6229139 * 2
def baseEnd_6229139 : Nat := 3198542370667209198715217

theorem tailTrace_6229139 : CollatzResearch.WordTrace tailWord_6229139 prefixEnd_6229139 3198542370667209198715217 := by
  unfold tailWord_6229139
  simp only [CollatzResearch.WordTrace]
  refine ⟨227195364179900730088706471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151463576119933820059137647 227195364179900730088706471)
  ·
    refine ⟨340793046269851095133059707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227195364179900730088706471 340793046269851095133059707)
    ·
      refine ⟨511189569404776642699589561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 340793046269851095133059707 511189569404776642699589561)
      ·
        refine ⟨383392177053582482024692171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 511189569404776642699589561 383392177053582482024692171)
        ·
          refine ⟨575088265580373723037038257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 383392177053582482024692171 575088265580373723037038257)
          ·
            refine ⟨431316199185280292277778693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 575088265580373723037038257 431316199185280292277778693)
            ·
              refine ⟨80871787347240054802083505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 431316199185280292277778693 80871787347240054802083505)
              ·
                refine ⟨60653840510430041101562629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 80871787347240054802083505 60653840510430041101562629)
                ·
                  refine ⟨11372595095705632706542993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 60653840510430041101562629 11372595095705632706542993)
                  ·
                    refine ⟨8529446321779224529907245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11372595095705632706542993 8529446321779224529907245)
                    ·
                      refine ⟨3198542370667209198715217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8529446321779224529907245 3198542370667209198715217)
                      ·
                        rfl

theorem cell23_6229139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 2, 4, 2, 3].length) (baseStart_6229139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6229139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6229139 prefixEnd_6229139 := by exact prefixLift 6229139
  have htrace : WordTrace (prefixWord ++ tailWord_6229139) baseStart_6229139 baseEnd_6229139 := by
    simpa [prefixWord, tailWord_6229139, baseEnd_6229139] using wordTrace_append hprefix tailTrace_6229139
  have hstable : (prefixWord ++ tailWord_6229139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6229139).length < 2 ^ (prefixWord ++ tailWord_6229139).sum := by decide
  have hdescent : baseEnd_6229139 < baseStart_6229139 := by decide
  rcases family_descends (prefixWord ++ tailWord_6229139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6229146 : List Nat := [3, 1, 1, 5, 1, 1, 1, 1, 5, 4]
def baseStart_6229146 : Nat := 118140960795 + 6229146 * 2 ^ 59
def prefixEnd_6229146 : Nat := 4983230072969 + 3 ^ 40 * 6229146 * 2
def baseEnd_6229146 : Nat := 1066181988343930223775895

theorem tailTrace_6229146 : CollatzResearch.WordTrace tailWord_6229146 prefixEnd_6229146 1066181988343930223775895 := by
  unfold tailWord_6229146
  simp only [CollatzResearch.WordTrace]
  refine ⟨56798904872718842571052823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151463746327250246856140861 56798904872718842571052823)
  ·
    refine ⟨85198357309078263856579235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56798904872718842571052823 85198357309078263856579235)
    ·
      refine ⟨127797535963617395784868853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85198357309078263856579235 127797535963617395784868853)
      ·
        refine ⟨11981018996589130854831455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 127797535963617395784868853 11981018996589130854831455)
        ·
          refine ⟨17971528494883696282247183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11981018996589130854831455 17971528494883696282247183)
          ·
            refine ⟨26957292742325544423370775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17971528494883696282247183 26957292742325544423370775)
            ·
              refine ⟨40435939113488316635056163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26957292742325544423370775 40435939113488316635056163)
              ·
                refine ⟨60653908670232474952584245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40435939113488316635056163 60653908670232474952584245)
                ·
                  refine ⟨5686303937834294526804773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 60653908670232474952584245 5686303937834294526804773)
                  ·
                    refine ⟨1066181988343930223775895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5686303937834294526804773 1066181988343930223775895)
                    ·
                      rfl

theorem cell23_6229146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 1, 1, 5, 4].length) (baseStart_6229146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6229146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6229146 prefixEnd_6229146 := by exact prefixLift 6229146
  have htrace : WordTrace (prefixWord ++ tailWord_6229146) baseStart_6229146 baseEnd_6229146 := by
    simpa [prefixWord, tailWord_6229146, baseEnd_6229146] using wordTrace_append hprefix tailTrace_6229146
  have hstable : (prefixWord ++ tailWord_6229146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6229146).length < 2 ^ (prefixWord ++ tailWord_6229146).sum := by decide
  have hdescent : baseEnd_6229146 < baseStart_6229146 := by decide
  rcases family_descends (prefixWord ++ tailWord_6229146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6229156 : List Nat := [2, 3, 1, 2, 3, 2, 1, 1, 1, 4, 3]
def baseStart_6229156 : Nat := 118140960795 + 6229156 * 2 ^ 59
def prefixEnd_6229156 : Nat := 4983230072969 + 3 ^ 40 * 6229156 * 2
def baseEnd_6229156 : Nat := 3198551099838335632202639

theorem tailTrace_6229156 : CollatzResearch.WordTrace tailWord_6229156 prefixEnd_6229156 3198551099838335632202639 := by
  unfold tailWord_6229156
  simp only [CollatzResearch.WordTrace]
  refine ⟨113597992110419570996037661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151463989480559427994716881 113597992110419570996037661)
  ·
    refine ⟨42599247041407339123514123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113597992110419570996037661 42599247041407339123514123)
    ·
      refine ⟨63898870562111008685271185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42599247041407339123514123 63898870562111008685271185)
      ·
        refine ⟨47924152921583256513953389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63898870562111008685271185 47924152921583256513953389)
        ·
          refine ⟨17971557345593721192732521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47924152921583256513953389 17971557345593721192732521)
          ·
            refine ⟨13478668009195290894549391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17971557345593721192732521 13478668009195290894549391)
            ·
              refine ⟨20218002013792936341824087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13478668009195290894549391 20218002013792936341824087)
              ·
                refine ⟨30327003020689404512736131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20218002013792936341824087 30327003020689404512736131)
                ·
                  refine ⟨45490504531034106769104197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30327003020689404512736131 45490504531034106769104197)
                  ·
                    refine ⟨8529469599568895019207037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 45490504531034106769104197 8529469599568895019207037)
                    ·
                      refine ⟨3198551099838335632202639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8529469599568895019207037 3198551099838335632202639)
                      ·
                        rfl

theorem cell23_6229156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 1, 1, 1, 4, 3].length) (baseStart_6229156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6229156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6229156 prefixEnd_6229156 := by exact prefixLift 6229156
  have htrace : WordTrace (prefixWord ++ tailWord_6229156) baseStart_6229156 baseEnd_6229156 := by
    simpa [prefixWord, tailWord_6229156, baseEnd_6229156] using wordTrace_append hprefix tailTrace_6229156
  have hstable : (prefixWord ++ tailWord_6229156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6229156).length < 2 ^ (prefixWord ++ tailWord_6229156).sum := by decide
  have hdescent : baseEnd_6229156 < baseStart_6229156 := by decide
  rcases family_descends (prefixWord ++ tailWord_6229156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6229220 : List Nat := [2, 3, 1, 1, 1, 2, 5, 3, 1, 1, 3]
def baseStart_6229220 : Nat := 118140960795 + 6229220 * 2 ^ 59
def prefixEnd_6229220 : Nat := 4983230072969 + 3 ^ 40 * 6229220 * 2
def baseEnd_6229220 : Nat := 3198583962600223381802345

theorem tailTrace_6229220 : CollatzResearch.WordTrace tailWord_6229220 prefixEnd_6229220 3198583962600223381802345 := by
  unfold tailWord_6229220
  simp only [CollatzResearch.WordTrace]
  refine ⟨113599159246303640461202557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151465545661738187281603409 113599159246303640461202557)
  ·
    refine ⟨42599684717363865172950959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113599159246303640461202557 42599684717363865172950959)
    ·
      refine ⟨63899527076045797759426439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42599684717363865172950959 63899527076045797759426439)
      ·
        refine ⟨95849290614068696639139659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63899527076045797759426439 95849290614068696639139659)
        ·
          refine ⟨143773935921103044958709489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95849290614068696639139659 143773935921103044958709489)
          ·
            refine ⟨107830451940827283719032117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 143773935921103044958709489 107830451940827283719032117)
            ·
              refine ⟨10109104869452557848659261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 107830451940827283719032117 10109104869452557848659261)
              ·
                refine ⟨3790914326044709193247223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10109104869452557848659261 3790914326044709193247223)
                ·
                  refine ⟨5686371489067063789870835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3790914326044709193247223 5686371489067063789870835)
                  ·
                    refine ⟨8529557233600595684806253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5686371489067063789870835 8529557233600595684806253)
                    ·
                      refine ⟨3198583962600223381802345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8529557233600595684806253 3198583962600223381802345)
                      ·
                        rfl

theorem cell23_6229220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 5, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 5, 3, 1, 1, 3].length) (baseStart_6229220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6229220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6229220 prefixEnd_6229220 := by exact prefixLift 6229220
  have htrace : WordTrace (prefixWord ++ tailWord_6229220) baseStart_6229220 baseEnd_6229220 := by
    simpa [prefixWord, tailWord_6229220, baseEnd_6229220] using wordTrace_append hprefix tailTrace_6229220
  have hstable : (prefixWord ++ tailWord_6229220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6229220).length < 2 ^ (prefixWord ++ tailWord_6229220).sum := by decide
  have hdescent : baseEnd_6229220 < baseStart_6229220 := by decide
  rcases family_descends (prefixWord ++ tailWord_6229220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6229239 : List Nat := [1, 1, 3, 1, 1, 1, 2, 4, 3, 2, 4]
def baseStart_6229239 : Nat := 118140960795 + 6229239 * 2 ^ 59
def prefixEnd_6229239 : Nat := 4983230072969 + 3 ^ 40 * 6229239 * 2
def baseEnd_6229239 : Nat := 3198593718732658807464757

theorem tailTrace_6229239 : CollatzResearch.WordTrace tailWord_6229239 prefixEnd_6229239 3198593718732658807464757 := by
  unfold tailWord_6229239
  simp only [CollatzResearch.WordTrace]
  refine ⟨227199011479538447167346771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151466007653025631444897847 227199011479538447167346771)
  ·
    refine ⟨340798517219307670751020157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227199011479538447167346771 340798517219307670751020157)
    ·
      refine ⟨127799443957240376531632559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 340798517219307670751020157 127799443957240376531632559)
      ·
        refine ⟨191699165935860564797448839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127799443957240376531632559 191699165935860564797448839)
        ·
          refine ⟨287548748903790847196173259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 191699165935860564797448839 287548748903790847196173259)
          ·
            refine ⟨431323123355686270794259889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 287548748903790847196173259 431323123355686270794259889)
            ·
              refine ⟨323492342516764703095694917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 431323123355686270794259889 323492342516764703095694917)
              ·
                refine ⟨60654814221893381830442797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 323492342516764703095694917 60654814221893381830442797)
                ·
                  refine ⟨22745555333210018186416049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 60654814221893381830442797 22745555333210018186416049)
                  ·
                    refine ⟨17059166499907513639812037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22745555333210018186416049 17059166499907513639812037)
                    ·
                      refine ⟨3198593718732658807464757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17059166499907513639812037 3198593718732658807464757)
                      ·
                        rfl

theorem cell23_6229239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 4, 3, 2, 4].length) (baseStart_6229239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6229239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6229239 prefixEnd_6229239 := by exact prefixLift 6229239
  have htrace : WordTrace (prefixWord ++ tailWord_6229239) baseStart_6229239 baseEnd_6229239 := by
    simpa [prefixWord, tailWord_6229239, baseEnd_6229239] using wordTrace_append hprefix tailTrace_6229239
  have hstable : (prefixWord ++ tailWord_6229239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6229239).length < 2 ^ (prefixWord ++ tailWord_6229239).sum := by decide
  have hdescent : baseEnd_6229239 < baseStart_6229239 := by decide
  rcases family_descends (prefixWord ++ tailWord_6229239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6229249 : List Nat := [1, 2, 4, 1, 1, 3, 1, 10]
def baseStart_6229249 : Nat := 118140960795 + 6229249 * 2 ^ 59
def prefixEnd_6229249 : Nat := 4983230072969 + 3 ^ 40 * 6229249 * 2
def baseEnd_6229249 : Nat := 118466624205155695123693

theorem tailTrace_6229249 : CollatzResearch.WordTrace tailWord_6229249 prefixEnd_6229249 118466624205155695123693 := by
  unfold tailWord_6229249
  simp only [CollatzResearch.WordTrace]
  refine ⟨227199376209502218875210801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151466250806334812583473867 227199376209502218875210801)
  ·
    refine ⟨170399532157126664156408101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 227199376209502218875210801 170399532157126664156408101)
    ·
      refine ⟨31949912279461249529326519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 170399532157126664156408101 31949912279461249529326519)
      ·
        refine ⟨47924868419191874293989779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31949912279461249529326519 47924868419191874293989779)
        ·
          refine ⟨71887302628787811440984669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47924868419191874293989779 71887302628787811440984669)
          ·
            refine ⟨26957738485795429290369251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 71887302628787811440984669 26957738485795429290369251)
            ·
              refine ⟨40436607728693143935553877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26957738485795429290369251 40436607728693143935553877)
              ·
                refine ⟨118466624205155695123693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 40436607728693143935553877 118466624205155695123693)
                ·
                  rfl

theorem cell23_6229249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 1, 10].length) (baseStart_6229249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6229249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6229249 prefixEnd_6229249 := by exact prefixLift 6229249
  have htrace : WordTrace (prefixWord ++ tailWord_6229249) baseStart_6229249 baseEnd_6229249 := by
    simpa [prefixWord, tailWord_6229249, baseEnd_6229249] using wordTrace_append hprefix tailTrace_6229249
  have hstable : (prefixWord ++ tailWord_6229249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6229249).length < 2 ^ (prefixWord ++ tailWord_6229249).sum := by decide
  have hdescent : baseEnd_6229249 < baseStart_6229249 := by decide
  rcases family_descends (prefixWord ++ tailWord_6229249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6229276 : List Nat := [2, 2, 3, 1, 1, 1, 3, 1, 3, 3, 3]
def baseStart_6229276 : Nat := 118140960795 + 6229276 * 2 ^ 59
def prefixEnd_6229276 : Nat := 4983230072969 + 3 ^ 40 * 6229276 * 2
def baseEnd_6229276 : Nat := 3198612717516875162702087

theorem tailTrace_6229276 : CollatzResearch.WordTrace tailWord_6229276 prefixEnd_6229276 3198612717516875162702087 := by
  unfold tailWord_6229276
  simp only [CollatzResearch.WordTrace]
  refine ⟨113600180490202201243221841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151466907320269601657629121 113600180490202201243221841)
  ·
    refine ⟨85200135367651650932416381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113600180490202201243221841 85200135367651650932416381)
    ·
      refine ⟨31950050762869369099656143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85200135367651650932416381 31950050762869369099656143)
      ·
        refine ⟨47925076144304053649484215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31950050762869369099656143 47925076144304053649484215)
        ·
          refine ⟨71887614216456080474226323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47925076144304053649484215 71887614216456080474226323)
          ·
            refine ⟨107831421324684120711339485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71887614216456080474226323 107831421324684120711339485)
            ·
              refine ⟨40436782996756545266752307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 107831421324684120711339485 40436782996756545266752307)
              ·
                refine ⟨60655174495134817900128461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40436782996756545266752307 60655174495134817900128461)
                ·
                  refine ⟨22745690435675556712548173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 60655174495134817900128461 22745690435675556712548173)
                  ·
                    refine ⟨8529633913378333767205565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22745690435675556712548173 8529633913378333767205565)
                    ·
                      refine ⟨3198612717516875162702087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8529633913378333767205565 3198612717516875162702087)
                      ·
                        rfl

theorem cell23_6229276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 3, 1, 3, 3, 3].length) (baseStart_6229276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6229276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6229276 prefixEnd_6229276 := by exact prefixLift 6229276
  have htrace : WordTrace (prefixWord ++ tailWord_6229276) baseStart_6229276 baseEnd_6229276 := by
    simpa [prefixWord, tailWord_6229276, baseEnd_6229276] using wordTrace_append hprefix tailTrace_6229276
  have hstable : (prefixWord ++ tailWord_6229276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6229276).length < 2 ^ (prefixWord ++ tailWord_6229276).sum := by decide
  have hdescent : baseEnd_6229276 < baseStart_6229276 := by decide
  rcases family_descends (prefixWord ++ tailWord_6229276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6229280 : List Nat := [2, 1, 1, 5, 4, 1, 1, 1, 1, 1, 5]
def baseStart_6229280 : Nat := 118140960795 + 6229280 * 2 ^ 59
def prefixEnd_6229280 : Nat := 4983230072969 + 3 ^ 40 * 6229280 * 2
def baseEnd_6229280 : Nat := 3198614771439493147052069

theorem tailTrace_6229280 : CollatzResearch.WordTrace tailWord_6229280 prefixEnd_6229280 3198614771439493147052069 := by
  unfold tailWord_6229280
  simp only [CollatzResearch.WordTrace]
  refine ⟨113600253436194955584794647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151467004581593274113059529 113600253436194955584794647)
  ·
    refine ⟨170400380154292433377191971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113600253436194955584794647 170400380154292433377191971)
    ·
      refine ⟨255600570231438650065787957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170400380154292433377191971 255600570231438650065787957)
      ·
        refine ⟨23962553459197373443667621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 255600570231438650065787957 23962553459197373443667621)
        ·
          refine ⟨4492978773599507520687679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23962553459197373443667621 4492978773599507520687679)
          ·
            refine ⟨6739468160399261281031519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4492978773599507520687679 6739468160399261281031519)
            ·
              refine ⟨10109202240598891921547279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6739468160399261281031519 10109202240598891921547279)
              ·
                refine ⟨15163803360898337882320919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10109202240598891921547279 15163803360898337882320919)
                ·
                  refine ⟨22745705041347506823481379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15163803360898337882320919 22745705041347506823481379)
                  ·
                    refine ⟨34118557562021260235222069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22745705041347506823481379 34118557562021260235222069)
                    ·
                      refine ⟨3198614771439493147052069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34118557562021260235222069 3198614771439493147052069)
                      ·
                        rfl

theorem cell23_6229280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 4, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 4, 1, 1, 1, 1, 1, 5].length) (baseStart_6229280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6229280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6229280 prefixEnd_6229280 := by exact prefixLift 6229280
  have htrace : WordTrace (prefixWord ++ tailWord_6229280) baseStart_6229280 baseEnd_6229280 := by
    simpa [prefixWord, tailWord_6229280, baseEnd_6229280] using wordTrace_append hprefix tailTrace_6229280
  have hstable : (prefixWord ++ tailWord_6229280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6229280).length < 2 ^ (prefixWord ++ tailWord_6229280).sum := by decide
  have hdescent : baseEnd_6229280 < baseStart_6229280 := by decide
  rcases family_descends (prefixWord ++ tailWord_6229280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6229310 : List Nat := [4, 2, 1, 2, 1, 1, 1, 5, 2, 1, 3]
def baseStart_6229310 : Nat := 118140960795 + 6229310 * 2 ^ 59
def prefixEnd_6229310 : Nat := 4983230072969 + 3 ^ 40 * 6229310 * 2
def baseEnd_6229310 : Nat := 3198630175859128029676931

theorem tailTrace_6229310 : CollatzResearch.WordTrace tailWord_6229310 prefixEnd_6229310 3198630175859128029676931 := by
  unfold tailWord_6229310
  simp only [CollatzResearch.WordTrace]
  refine ⟨28400200132785153286647673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 151467734041520817528787589 28400200132785153286647673)
  ·
    refine ⟨21300150099588864964985755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28400200132785153286647673 21300150099588864964985755)
    ·
      refine ⟨31950225149383297447478633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21300150099588864964985755 31950225149383297447478633)
      ·
        refine ⟨23962668862037473085608975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31950225149383297447478633 23962668862037473085608975)
        ·
          refine ⟨35944003293056209628413463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23962668862037473085608975 35944003293056209628413463)
          ·
            refine ⟨53916004939584314442620195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35944003293056209628413463 53916004939584314442620195)
            ·
              refine ⟨80874007409376471663930293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53916004939584314442620195 80874007409376471663930293)
              ·
                refine ⟨7581938194629044218493465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 80874007409376471663930293 7581938194629044218493465)
                ·
                  refine ⟨5686453645971783163870099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7581938194629044218493465 5686453645971783163870099)
                  ·
                    refine ⟨8529680468957674745805149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5686453645971783163870099 8529680468957674745805149)
                    ·
                      refine ⟨3198630175859128029676931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8529680468957674745805149 3198630175859128029676931)
                      ·
                        rfl

theorem cell23_6229310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 5, 2, 1, 3].length) (baseStart_6229310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6229310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6229310 prefixEnd_6229310 := by exact prefixLift 6229310
  have htrace : WordTrace (prefixWord ++ tailWord_6229310) baseStart_6229310 baseEnd_6229310 := by
    simpa [prefixWord, tailWord_6229310, baseEnd_6229310] using wordTrace_append hprefix tailTrace_6229310
  have hstable : (prefixWord ++ tailWord_6229310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6229310).length < 2 ^ (prefixWord ++ tailWord_6229310).sum := by decide
  have hdescent : baseEnd_6229310 < baseStart_6229310 := by decide
  rcases family_descends (prefixWord ++ tailWord_6229310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6229356 : List Nat := [2, 2, 1, 1, 5, 1, 1, 3, 7]
def baseStart_6229356 : Nat := 118140960795 + 6229356 * 2 ^ 59
def prefixEnd_6229356 : Nat := 4983230072969 + 3 ^ 40 * 6229356 * 2
def baseEnd_6229356 : Nat := 355405977329914983300191

theorem tailTrace_6229356 : CollatzResearch.WordTrace tailWord_6229356 prefixEnd_6229356 355405977329914983300191 := by
  unfold tailWord_6229356
  simp only [CollatzResearch.WordTrace]
  refine ⟨113601639410057288074677961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151468852546743050766237281 113601639410057288074677961)
  ·
    refine ⟨85201229557542966056008471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113601639410057288074677961 85201229557542966056008471)
    ·
      refine ⟨127801844336314449084012707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85201229557542966056008471 127801844336314449084012707)
      ·
        refine ⟨191702766504471673626019061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127801844336314449084012707 191702766504471673626019061)
        ·
          refine ⟨17972134359794219402439287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 191702766504471673626019061 17972134359794219402439287)
          ·
            refine ⟨26958201539691329103658931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17972134359794219402439287 26958201539691329103658931)
            ·
              refine ⟨40437302309536993655488397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26958201539691329103658931 40437302309536993655488397)
              ·
                refine ⟨15163988366076372620808149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40437302309536993655488397 15163988366076372620808149)
                ·
                  refine ⟨355405977329914983300191, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15163988366076372620808149 355405977329914983300191)
                  ·
                    rfl

theorem cell23_6229356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 7].length) (baseStart_6229356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6229356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6229356 prefixEnd_6229356 := by exact prefixLift 6229356
  have htrace : WordTrace (prefixWord ++ tailWord_6229356) baseStart_6229356 baseEnd_6229356 := by
    simpa [prefixWord, tailWord_6229356, baseEnd_6229356] using wordTrace_append hprefix tailTrace_6229356
  have hstable : (prefixWord ++ tailWord_6229356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6229356).length < 2 ^ (prefixWord ++ tailWord_6229356).sum := by decide
  have hdescent : baseEnd_6229356 < baseStart_6229356 := by decide
  rcases family_descends (prefixWord ++ tailWord_6229356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6229367 : List Nat := [1, 1, 3, 1, 1, 2, 7, 1, 2, 2, 2]
def baseStart_6229367 : Nat := 118140960795 + 6229367 * 2 ^ 59
def prefixEnd_6229367 : Nat := 4983230072969 + 3 ^ 40 * 6229367 * 2
def baseEnd_6229367 : Nat := 3198659444256434306664169

theorem tailTrace_6229367 : CollatzResearch.WordTrace tailWord_6229367 prefixEnd_6229367 3198659444256434306664169 := by
  unfold tailWord_6229367
  simp only [CollatzResearch.WordTrace]
  refine ⟨227203680023074725028006355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151469120015383150018670903 227203680023074725028006355)
  ·
    refine ⟨340805520034612087542009533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227203680023074725028006355 340805520034612087542009533)
    ·
      refine ⟨127802070012979532828253575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 340805520034612087542009533 127802070012979532828253575)
      ·
        refine ⟨191703105019469299242380363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127802070012979532828253575 191703105019469299242380363)
        ·
          refine ⟨287554657529203948863570545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 191703105019469299242380363 287554657529203948863570545)
          ·
            refine ⟨215665993146902961647677909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 287554657529203948863570545 215665993146902961647677909)
            ·
              refine ⟨5054671714380538163617451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 215665993146902961647677909 5054671714380538163617451)
              ·
                refine ⟨7582007571570807245426177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5054671714380538163617451 7582007571570807245426177)
                ·
                  refine ⟨5686505678678105434069633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7582007571570807245426177 5686505678678105434069633)
                  ·
                    refine ⟨4264879259008579075552225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5686505678678105434069633 4264879259008579075552225)
                    ·
                      refine ⟨3198659444256434306664169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4264879259008579075552225 3198659444256434306664169)
                      ·
                        rfl

theorem cell23_6229367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 7, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 7, 1, 2, 2, 2].length) (baseStart_6229367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6229367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6229367 prefixEnd_6229367 := by exact prefixLift 6229367
  have htrace : WordTrace (prefixWord ++ tailWord_6229367) baseStart_6229367 baseEnd_6229367 := by
    simpa [prefixWord, tailWord_6229367, baseEnd_6229367] using wordTrace_append hprefix tailTrace_6229367
  have hstable : (prefixWord ++ tailWord_6229367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6229367).length < 2 ^ (prefixWord ++ tailWord_6229367).sum := by decide
  have hdescent : baseEnd_6229367 < baseStart_6229367 := by decide
  rcases family_descends (prefixWord ++ tailWord_6229367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6229423 : List Nat := [1, 1, 2, 1, 2, 2, 1, 5, 2, 4, 2]
def baseStart_6229423 : Nat := 118140960795 + 6229423 * 2 ^ 59
def prefixEnd_6229423 : Nat := 4983230072969 + 3 ^ 40 * 6229423 * 2
def baseEnd_6229423 : Nat := 3198688199173086087563911

theorem tailTrace_6229423 : CollatzResearch.WordTrace tailWord_6229423 prefixEnd_6229423 3198688199173086087563911 := by
  unfold tailWord_6229423
  simp only [CollatzResearch.WordTrace]
  refine ⟨227205722510871846592044923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151470481673914564394696615 227205722510871846592044923)
  ·
    refine ⟨340808583766307769888067385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227205722510871846592044923 340808583766307769888067385)
    ·
      refine ⟨255606437824730827416050539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 340808583766307769888067385 255606437824730827416050539)
      ·
        refine ⟨383409656737096241124075809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 255606437824730827416050539 383409656737096241124075809)
        ·
          refine ⟨287557242552822180843056857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 383409656737096241124075809 287557242552822180843056857)
          ·
            refine ⟨215667931914616635632292643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 287557242552822180843056857 215667931914616635632292643)
            ·
              refine ⟨323501897871924953448438965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 215667931914616635632292643 323501897871924953448438965)
              ·
                refine ⟨30328302925492964385791153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 323501897871924953448438965 30328302925492964385791153)
                ·
                  refine ⟨22746227194119723289343365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30328302925492964385791153 22746227194119723289343365)
                  ·
                    refine ⟨4264917598897448116751881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22746227194119723289343365 4264917598897448116751881)
                    ·
                      refine ⟨3198688199173086087563911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4264917598897448116751881 3198688199173086087563911)
                      ·
                        rfl

theorem cell23_6229423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 5, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 5, 2, 4, 2].length) (baseStart_6229423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6229423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6229423 prefixEnd_6229423 := by exact prefixLift 6229423
  have htrace : WordTrace (prefixWord ++ tailWord_6229423) baseStart_6229423 baseEnd_6229423 := by
    simpa [prefixWord, tailWord_6229423, baseEnd_6229423] using wordTrace_append hprefix tailTrace_6229423
  have hstable : (prefixWord ++ tailWord_6229423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6229423).length < 2 ^ (prefixWord ++ tailWord_6229423).sum := by decide
  have hdescent : baseEnd_6229423 < baseStart_6229423 := by decide
  rcases family_descends (prefixWord ++ tailWord_6229423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6229443 : List Nat := [1, 1, 1, 3, 1, 1, 5, 3, 2, 2, 3]
def baseStart_6229443 : Nat := 118140960795 + 6229443 * 2 ^ 59
def prefixEnd_6229443 : Nat := 4983230072969 + 3 ^ 40 * 6229443 * 2
def baseEnd_6229443 : Nat := 3198698468786176009313819

theorem tailTrace_6229443 : CollatzResearch.WordTrace tailWord_6229443 prefixEnd_6229443 3198698468786176009313819 := by
  unfold tailWord_6229443
  simp only [CollatzResearch.WordTrace]
  refine ⟨227206451970799390007772983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151470967980532926671848655 227206451970799390007772983)
  ·
    refine ⟨340809677956199085011659475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227206451970799390007772983 340809677956199085011659475)
    ·
      refine ⟨511214516934298627517489213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 340809677956199085011659475 511214516934298627517489213)
      ·
        refine ⟨191705443850361985319058455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 511214516934298627517489213 191705443850361985319058455)
        ·
          refine ⟨287558165775542977978587683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 191705443850361985319058455 287558165775542977978587683)
          ·
            refine ⟨431337248663314466967881525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 287558165775542977978587683 431337248663314466967881525)
            ·
              refine ⟨40437867062185731278238893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 431337248663314466967881525 40437867062185731278238893)
              ·
                refine ⟨15164200148319649229339585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40437867062185731278238893 15164200148319649229339585)
                ·
                  refine ⟨11373150111239736922004689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15164200148319649229339585 11373150111239736922004689)
                  ·
                    refine ⟨8529862583429802691503517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11373150111239736922004689 8529862583429802691503517)
                    ·
                      refine ⟨3198698468786176009313819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8529862583429802691503517 3198698468786176009313819)
                      ·
                        rfl

theorem cell23_6229443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 5, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 5, 3, 2, 2, 3].length) (baseStart_6229443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6229443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6229443 prefixEnd_6229443 := by exact prefixLift 6229443
  have htrace : WordTrace (prefixWord ++ tailWord_6229443) baseStart_6229443 baseEnd_6229443 := by
    simpa [prefixWord, tailWord_6229443, baseEnd_6229443] using wordTrace_append hprefix tailTrace_6229443
  have hstable : (prefixWord ++ tailWord_6229443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6229443).length < 2 ^ (prefixWord ++ tailWord_6229443).sum := by decide
  have hdescent : baseEnd_6229443 < baseStart_6229443 := by decide
  rcases family_descends (prefixWord ++ tailWord_6229443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6229558 : List Nat := [5, 1, 2, 1, 3, 2, 1, 3, 1, 1, 3]
def baseStart_6229558 : Nat := 118140960795 + 6229558 * 2 ^ 59
def prefixEnd_6229558 : Nat := 4983230072969 + 3 ^ 40 * 6229558 * 2
def baseEnd_6229558 : Nat := 3198757519061443059375791

theorem tailTrace_6229558 : CollatzResearch.WordTrace tailWord_6229558 prefixEnd_6229558 3198757519061443059375791 := by
  unfold tailWord_6229558
  simp only [CollatzResearch.WordTrace]
  refine ⟨14200665397836422790513083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 151473764243588509765472885 14200665397836422790513083)
  ·
    refine ⟨21300998096754634185769625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14200665397836422790513083 21300998096754634185769625)
    ·
      refine ⟨15975748572565975639327219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21300998096754634185769625 15975748572565975639327219)
      ·
        refine ⟨23963622858848963458990829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15975748572565975639327219 23963622858848963458990829)
        ·
          refine ⟨8986358572068361297121561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23963622858848963458990829 8986358572068361297121561)
          ·
            refine ⟨6739768929051270972841171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8986358572068361297121561 6739768929051270972841171)
            ·
              refine ⟨10109653393576906459261757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6739768929051270972841171 10109653393576906459261757)
              ·
                refine ⟨3791120022591339922223159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10109653393576906459261757 3791120022591339922223159)
                ·
                  refine ⟨5686680033887009883334739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3791120022591339922223159 5686680033887009883334739)
                  ·
                    refine ⟨8530020050830514825002109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5686680033887009883334739 8530020050830514825002109)
                    ·
                      refine ⟨3198757519061443059375791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8530020050830514825002109 3198757519061443059375791)
                      ·
                        rfl

theorem cell23_6229558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 2, 1, 3, 1, 1, 3].length) (baseStart_6229558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6229558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6229558 prefixEnd_6229558 := by exact prefixLift 6229558
  have htrace : WordTrace (prefixWord ++ tailWord_6229558) baseStart_6229558 baseEnd_6229558 := by
    simpa [prefixWord, tailWord_6229558, baseEnd_6229558] using wordTrace_append hprefix tailTrace_6229558
  have hstable : (prefixWord ++ tailWord_6229558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6229558).length < 2 ^ (prefixWord ++ tailWord_6229558).sum := by decide
  have hdescent : baseEnd_6229558 < baseStart_6229558 := by decide
  rcases family_descends (prefixWord ++ tailWord_6229558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6229643 : List Nat := [1, 1, 1, 1, 4, 1, 4, 3, 7]
def baseStart_6229643 : Nat := 118140960795 + 6229643 * 2 ^ 59
def prefixEnd_6229643 : Nat := 4983230072969 + 3 ^ 40 * 6229643 * 2
def baseEnd_6229643 : Nat := 355422351657452802979211

theorem tailTrace_6229643 : CollatzResearch.WordTrace tailWord_6229643 prefixEnd_6229643 355422351657452802979211 := by
  unfold tailWord_6229643
  simp only [CollatzResearch.WordTrace]
  refine ⟨227213746570074824165053583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151475831046716549443369055 227213746570074824165053583)
  ·
    refine ⟨340820619855112236247580375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227213746570074824165053583 340820619855112236247580375)
    ·
      refine ⟨511230929782668354371370563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 340820619855112236247580375 511230929782668354371370563)
      ·
        refine ⟨766846394674002531557055845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 511230929782668354371370563 766846394674002531557055845)
        ·
          refine ⟨143783699001375474666947971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 766846394674002531557055845 143783699001375474666947971)
          ·
            refine ⟨215675548502063212000421957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 143783699001375474666947971 215675548502063212000421957)
            ·
              refine ⟨40439165344136852250079117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 215675548502063212000421957 40439165344136852250079117)
              ·
                refine ⟨15164687004051319593779669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40439165344136852250079117 15164687004051319593779669)
                ·
                  refine ⟨355422351657452802979211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15164687004051319593779669 355422351657452802979211)
                  ·
                    rfl

theorem cell23_6229643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 4, 3, 7].length) (baseStart_6229643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6229643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6229643 prefixEnd_6229643 := by exact prefixLift 6229643
  have htrace : WordTrace (prefixWord ++ tailWord_6229643) baseStart_6229643 baseEnd_6229643 := by
    simpa [prefixWord, tailWord_6229643, baseEnd_6229643] using wordTrace_append hprefix tailTrace_6229643
  have hstable : (prefixWord ++ tailWord_6229643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6229643).length < 2 ^ (prefixWord ++ tailWord_6229643).sum := by decide
  have hdescent : baseEnd_6229643 < baseStart_6229643 := by decide
  rcases family_descends (prefixWord ++ tailWord_6229643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6229700 : List Nat := [2, 3, 3, 1, 1, 1, 2, 1, 1, 1, 7]
def baseStart_6229700 : Nat := 118140960795 + 6229700 * 2 ^ 59
def prefixEnd_6229700 : Nat := 4983230072969 + 3 ^ 40 * 6229700 * 2
def baseEnd_6229700 : Nat := 3198830433314381503800137

theorem tailTrace_6229700 : CollatzResearch.WordTrace tailWord_6229700 prefixEnd_6229700 3198830433314381503800137 := by
  unfold tailWord_6229700
  simp only [CollatzResearch.WordTrace]
  refine ⟨113607912765434161449939277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151477217020578881933252369 113607912765434161449939277)
  ·
    refine ⟨42602967287037810543727229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113607912765434161449939277 42602967287037810543727229)
    ·
      refine ⟨15976112732639178953897711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42602967287037810543727229 15976112732639178953897711)
      ·
        refine ⟨23964169098958768430846567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15976112732639178953897711 23964169098958768430846567)
        ·
          refine ⟨35946253648438152646269851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23964169098958768430846567 35946253648438152646269851)
          ·
            refine ⟨53919380472657228969404777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35946253648438152646269851 53919380472657228969404777)
            ·
              refine ⟨40439535354492921727053583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53919380472657228969404777 40439535354492921727053583)
              ·
                refine ⟨60659303031739382590580375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40439535354492921727053583 60659303031739382590580375)
                ·
                  refine ⟨90988954547609073885870563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 60659303031739382590580375 90988954547609073885870563)
                  ·
                    refine ⟨136483431821413610828805845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 90988954547609073885870563 136483431821413610828805845)
                    ·
                      refine ⟨3198830433314381503800137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 136483431821413610828805845 3198830433314381503800137)
                      ·
                        rfl

theorem cell23_6229700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 2, 1, 1, 1, 7].length) (baseStart_6229700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6229700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6229700 prefixEnd_6229700 := by exact prefixLift 6229700
  have htrace : WordTrace (prefixWord ++ tailWord_6229700) baseStart_6229700 baseEnd_6229700 := by
    simpa [prefixWord, tailWord_6229700, baseEnd_6229700] using wordTrace_append hprefix tailTrace_6229700
  have hstable : (prefixWord ++ tailWord_6229700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6229700).length < 2 ^ (prefixWord ++ tailWord_6229700).sum := by decide
  have hdescent : baseEnd_6229700 < baseStart_6229700 := by decide
  rcases family_descends (prefixWord ++ tailWord_6229700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6229710 : List Nat := [4, 1, 1, 1, 3, 1, 1, 1, 3, 3, 4]
def baseStart_6229710 : Nat := 118140960795 + 6229710 * 2 ^ 59
def prefixEnd_6229710 : Nat := 4983230072969 + 3 ^ 40 * 6229710 * 2
def baseEnd_6229710 : Nat := 3198835568120926464675091

theorem tailTrace_6229710 : CollatzResearch.WordTrace tailWord_6229710 prefixEnd_6229710 3198835568120926464675091 := by
  unfold tailWord_6229710
  simp only [CollatzResearch.WordTrace]
  refine ⟨28402023782604011825967823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 151477460173888063071828389 28402023782604011825967823)
  ·
    refine ⟨42603035673906017738951735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28402023782604011825967823 42603035673906017738951735)
    ·
      refine ⟨63904553510859026608427603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42603035673906017738951735 63904553510859026608427603)
      ·
        refine ⟨95856830266288539912641405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63904553510859026608427603 95856830266288539912641405)
        ·
          refine ⟨35946311349858202467240527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 95856830266288539912641405 35946311349858202467240527)
          ·
            refine ⟨53919467024787303700860791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35946311349858202467240527 53919467024787303700860791)
            ·
              refine ⟨80879200537180955551291187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53919467024787303700860791 80879200537180955551291187)
              ·
                refine ⟨121318800805771433326936781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 80879200537180955551291187 121318800805771433326936781)
                ·
                  refine ⟨45494550302164287497601293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 121318800805771433326936781 45494550302164287497601293)
                  ·
                    refine ⟨17060456363311607811600485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 45494550302164287497601293 17060456363311607811600485)
                    ·
                      refine ⟨3198835568120926464675091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17060456363311607811600485 3198835568120926464675091)
                      ·
                        rfl

theorem cell23_6229710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 1, 3, 3, 4].length) (baseStart_6229710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6229710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6229710 prefixEnd_6229710 := by exact prefixLift 6229710
  have htrace : WordTrace (prefixWord ++ tailWord_6229710) baseStart_6229710 baseEnd_6229710 := by
    simpa [prefixWord, tailWord_6229710, baseEnd_6229710] using wordTrace_append hprefix tailTrace_6229710
  have hstable : (prefixWord ++ tailWord_6229710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6229710).length < 2 ^ (prefixWord ++ tailWord_6229710).sum := by decide
  have hdescent : baseEnd_6229710 < baseStart_6229710 := by decide
  rcases family_descends (prefixWord ++ tailWord_6229710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6229777 : List Nat := [1, 2, 2, 1, 1, 3, 1, 3, 5, 1, 3]
def baseStart_6229777 : Nat := 118140960795 + 6229777 * 2 ^ 59
def prefixEnd_6229777 : Nat := 4983230072969 + 3 ^ 40 * 6229777 * 2
def baseEnd_6229777 : Nat := 3198869971324777702537283

theorem tailTrace_6229777 : CollatzResearch.WordTrace tailWord_6229777 prefixEnd_6229777 3198869971324777702537283 := by
  unfold tailWord_6229777
  simp only [CollatzResearch.WordTrace]
  refine ⟨227218633951589365050431585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151479089301059576700287723 227218633951589365050431585)
  ·
    refine ⟨170413975463692023787823689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 227218633951589365050431585 170413975463692023787823689)
    ·
      refine ⟨127810481597769017840867767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 170413975463692023787823689 127810481597769017840867767)
      ·
        refine ⟨191715722396653526761301651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127810481597769017840867767 191715722396653526761301651)
        ·
          refine ⟨287573583594980290141952477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 191715722396653526761301651 287573583594980290141952477)
          ·
            refine ⟨107840093848117608803232179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 287573583594980290141952477 107840093848117608803232179)
            ·
              refine ⟨161760140772176413204848269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 107840093848117608803232179 161760140772176413204848269)
              ·
                refine ⟨60660052789566154951818101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 161760140772176413204848269 60660052789566154951818101)
                ·
                  refine ⟨5686879949021827026732947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 60660052789566154951818101 5686879949021827026732947)
                  ·
                    refine ⟨8530319923532740540099421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5686879949021827026732947 8530319923532740540099421)
                    ·
                      refine ⟨3198869971324777702537283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8530319923532740540099421 3198869971324777702537283)
                      ·
                        rfl

theorem cell23_6229777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 3, 5, 1, 3].length) (baseStart_6229777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6229777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6229777 prefixEnd_6229777 := by exact prefixLift 6229777
  have htrace : WordTrace (prefixWord ++ tailWord_6229777) baseStart_6229777 baseEnd_6229777 := by
    simpa [prefixWord, tailWord_6229777, baseEnd_6229777] using wordTrace_append hprefix tailTrace_6229777
  have hstable : (prefixWord ++ tailWord_6229777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6229777).length < 2 ^ (prefixWord ++ tailWord_6229777).sum := by decide
  have hdescent : baseEnd_6229777 < baseStart_6229777 := by decide
  rcases family_descends (prefixWord ++ tailWord_6229777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6229787 : List Nat := [1, 1, 1, 1, 1, 1, 4, 2, 6, 3, 2]
def baseStart_6229787 : Nat := 118140960795 + 6229787 * 2 ^ 59
def prefixEnd_6229787 : Nat := 4983230072969 + 3 ^ 40 * 6229787 * 2
def baseEnd_6229787 : Nat := 3198875106131322663412237

theorem tailTrace_6229787 : CollatzResearch.WordTrace tailWord_6229787 prefixEnd_6229787 3198875106131322663412237 := by
  unfold tailWord_6229787
  simp only [CollatzResearch.WordTrace]
  refine ⟨227218998681553136758295615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151479332454368757838863743 227218998681553136758295615)
  ·
    refine ⟨340828498022329705137443423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227218998681553136758295615 340828498022329705137443423)
    ·
      refine ⟨511242747033494557706165135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 340828498022329705137443423 511242747033494557706165135)
      ·
        refine ⟨766864120550241836559247703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 511242747033494557706165135 766864120550241836559247703)
        ·
          refine ⟨1150296180825362754838871555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 766864120550241836559247703 1150296180825362754838871555)
          ·
            refine ⟨1725444271238044132258307333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1150296180825362754838871555 1725444271238044132258307333)
            ·
              refine ⟨323520800857133274798432625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1725444271238044132258307333 323520800857133274798432625)
              ·
                refine ⟨242640600642849956098824469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 323520800857133274798432625 242640600642849956098824469)
                ·
                  refine ⟨11373778155133591692132397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 242640600642849956098824469 11373778155133591692132397)
                  ·
                    refine ⟨4265166808175096884549649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11373778155133591692132397 4265166808175096884549649)
                    ·
                      refine ⟨3198875106131322663412237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4265166808175096884549649 3198875106131322663412237)
                      ·
                        rfl

theorem cell23_6229787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 2, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 2, 6, 3, 2].length) (baseStart_6229787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6229787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6229787 prefixEnd_6229787 := by exact prefixLift 6229787
  have htrace : WordTrace (prefixWord ++ tailWord_6229787) baseStart_6229787 baseEnd_6229787 := by
    simpa [prefixWord, tailWord_6229787, baseEnd_6229787] using wordTrace_append hprefix tailTrace_6229787
  have hstable : (prefixWord ++ tailWord_6229787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6229787).length < 2 ^ (prefixWord ++ tailWord_6229787).sum := by decide
  have hdescent : baseEnd_6229787 < baseStart_6229787 := by decide
  rcases family_descends (prefixWord ++ tailWord_6229787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6229804 : List Nat := [2, 2, 1, 1, 1, 5, 2, 2, 2, 3, 2]
def baseStart_6229804 : Nat := 118140960795 + 6229804 * 2 ^ 59
def prefixEnd_6229804 : Nat := 4983230072969 + 3 ^ 40 * 6229804 * 2
def baseEnd_6229804 : Nat := 3198883835302449096899659

theorem tailTrace_6229804 : CollatzResearch.WordTrace tailWord_6229804 prefixEnd_6229804 3198883835302449096899659 := by
  unfold tailWord_6229804
  simp only [CollatzResearch.WordTrace]
  refine ⟨113609809361245774330832233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151479745814994365774442977 113609809361245774330832233)
  ·
    refine ⟨85207357020934330748124175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113609809361245774330832233 85207357020934330748124175)
    ·
      refine ⟨127811035531401496122186263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85207357020934330748124175 127811035531401496122186263)
      ·
        refine ⟨191716553297102244183279395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127811035531401496122186263 191716553297102244183279395)
        ·
          refine ⟨287574829945653366274919093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 191716553297102244183279395 287574829945653366274919093)
          ·
            refine ⟨26960140307405003088273665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 287574829945653366274919093 26960140307405003088273665)
            ·
              refine ⟨20220105230553752316205249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26960140307405003088273665 20220105230553752316205249)
              ·
                refine ⟨15165078922915314237153937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20220105230553752316205249 15165078922915314237153937)
                ·
                  refine ⟨11373809192186485677865453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15165078922915314237153937 11373809192186485677865453)
                  ·
                    refine ⟨4265178447069932129199545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11373809192186485677865453 4265178447069932129199545)
                    ·
                      refine ⟨3198883835302449096899659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4265178447069932129199545 3198883835302449096899659)
                      ·
                        rfl

theorem cell23_6229804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 3, 2].length) (baseStart_6229804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6229804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6229804 prefixEnd_6229804 := by exact prefixLift 6229804
  have htrace : WordTrace (prefixWord ++ tailWord_6229804) baseStart_6229804 baseEnd_6229804 := by
    simpa [prefixWord, tailWord_6229804, baseEnd_6229804] using wordTrace_append hprefix tailTrace_6229804
  have hstable : (prefixWord ++ tailWord_6229804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6229804).length < 2 ^ (prefixWord ++ tailWord_6229804).sum := by decide
  have hdescent : baseEnd_6229804 < baseStart_6229804 := by decide
  rcases family_descends (prefixWord ++ tailWord_6229804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6229814 : List Nat := [5, 1, 2, 2, 1, 1, 1, 2, 3, 5]
def baseStart_6229814 : Nat := 118140960795 + 6229814 * 2 ^ 59
def prefixEnd_6229814 : Nat := 4983230072969 + 3 ^ 40 * 6229814 * 2
def baseEnd_6229814 : Nat := 1066296323369664685924871

theorem tailTrace_6229814 : CollatzResearch.WordTrace tailWord_6229814 prefixEnd_6229814 1066296323369664685924871 := by
  unfold tailWord_6229814
  simp only [CollatzResearch.WordTrace]
  refine ⟨14201248965778457523095531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 151479988968303546913018997 14201248965778457523095531)
  ·
    refine ⟨21301873448667686284643297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14201248965778457523095531 21301873448667686284643297)
    ·
      refine ⟨15976405086500764713482473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21301873448667686284643297 15976405086500764713482473)
      ·
        refine ⟨11982303814875573535111855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15976405086500764713482473 11982303814875573535111855)
        ·
          refine ⟨17973455722313360302667783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11982303814875573535111855 17973455722313360302667783)
          ·
            refine ⟨26960183583470040454001675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17973455722313360302667783 26960183583470040454001675)
            ·
              refine ⟨40440275375205060681002513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26960183583470040454001675 40440275375205060681002513)
              ·
                refine ⟨30330206531403795510751885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40440275375205060681002513 30330206531403795510751885)
                ·
                  refine ⟨11373827449276423316531957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30330206531403795510751885 11373827449276423316531957)
                  ·
                    refine ⟨1066296323369664685924871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11373827449276423316531957 1066296323369664685924871)
                    ·
                      rfl

theorem cell23_6229814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 1, 2, 3, 5].length) (baseStart_6229814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6229814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6229814 prefixEnd_6229814 := by exact prefixLift 6229814
  have htrace : WordTrace (prefixWord ++ tailWord_6229814) baseStart_6229814 baseEnd_6229814 := by
    simpa [prefixWord, tailWord_6229814, baseEnd_6229814] using wordTrace_append hprefix tailTrace_6229814
  have hstable : (prefixWord ++ tailWord_6229814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6229814).length < 2 ^ (prefixWord ++ tailWord_6229814).sum := by decide
  have hdescent : baseEnd_6229814 < baseStart_6229814 := by decide
  rcases family_descends (prefixWord ++ tailWord_6229814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6229827 : List Nat := [1, 1, 1, 3, 1, 6, 2, 1, 1, 6]
def baseStart_6229827 : Nat := 118140960795 + 6229827 * 2 ^ 59
def prefixEnd_6229827 : Nat := 4983230072969 + 3 ^ 40 * 6229827 * 2
def baseEnd_6229827 : Nat := 1066298548452500835637351

theorem tailTrace_6229827 : CollatzResearch.WordTrace tailWord_6229827 prefixEnd_6229827 1066298548452500835637351 := by
  unfold tailWord_6229827
  simp only [CollatzResearch.WordTrace]
  refine ⟨227220457601408223589751735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151480305067605482393167823 227220457601408223589751735)
  ·
    refine ⟨340830686402112335384627603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227220457601408223589751735 340830686402112335384627603)
    ·
      refine ⟨511246029603168503076941405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 340830686402112335384627603 511246029603168503076941405)
      ·
        refine ⟨191717261101188188653853027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 511246029603168503076941405 191717261101188188653853027)
        ·
          refine ⟨287575891651782282980779541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 191717261101188188653853027 287575891651782282980779541)
          ·
            refine ⟨13480119921177294514724041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 287575891651782282980779541 13480119921177294514724041)
            ·
              refine ⟨10110089940882970886043031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13480119921177294514724041 10110089940882970886043031)
              ·
                refine ⟨15165134911324456329064547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10110089940882970886043031 15165134911324456329064547)
                ·
                  refine ⟨22747702366986684493596821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15165134911324456329064547 22747702366986684493596821)
                  ·
                    refine ⟨1066298548452500835637351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22747702366986684493596821 1066298548452500835637351)
                    ·
                      rfl

theorem cell23_6229827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 2, 1, 1, 6].length) (baseStart_6229827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6229827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6229827 prefixEnd_6229827 := by exact prefixLift 6229827
  have htrace : WordTrace (prefixWord ++ tailWord_6229827) baseStart_6229827 baseEnd_6229827 := by
    simpa [prefixWord, tailWord_6229827, baseEnd_6229827] using wordTrace_append hprefix tailTrace_6229827
  have hstable : (prefixWord ++ tailWord_6229827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6229827).length < 2 ^ (prefixWord ++ tailWord_6229827).sum := by decide
  have hdescent : baseEnd_6229827 < baseStart_6229827 := by decide
  rcases family_descends (prefixWord ++ tailWord_6229827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6229868 : List Nat := [2, 2, 1, 1, 4, 2, 2, 4, 1, 2, 2]
def baseStart_6229868 : Nat := 118140960795 + 6229868 * 2 ^ 59
def prefixEnd_6229868 : Nat := 4983230072969 + 3 ^ 40 * 6229868 * 2
def baseEnd_6229868 : Nat := 3198916698064336846499365

theorem tailTrace_6229868 : CollatzResearch.WordTrace tailWord_6229868 prefixEnd_6229868 3198916698064336846499365 := by
  unfold tailWord_6229868
  simp only [CollatzResearch.WordTrace]
  refine ⟨113610976497129843795997129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151481301996173125061329505 113610976497129843795997129)
  ·
    refine ⟨85208232372847382846997847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113610976497129843795997129 85208232372847382846997847)
    ·
      refine ⟨127812348559271074270496771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85208232372847382846997847 127812348559271074270496771)
      ·
        refine ⟨191718522838906611405745157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127812348559271074270496771 191718522838906611405745157)
        ·
          refine ⟨35947223032294989638577217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 191718522838906611405745157 35947223032294989638577217)
          ·
            refine ⟨26960417274221242228932913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35947223032294989638577217 26960417274221242228932913)
            ·
              refine ⟨20220312955665931671699685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26960417274221242228932913 20220312955665931671699685)
              ·
                refine ⟨3791308679187362188443691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20220312955665931671699685 3791308679187362188443691)
                ·
                  refine ⟨5686963018781043282665537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3791308679187362188443691 5686963018781043282665537)
                  ·
                    refine ⟨4265222264085782461999153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5686963018781043282665537 4265222264085782461999153)
                    ·
                      refine ⟨3198916698064336846499365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4265222264085782461999153 3198916698064336846499365)
                      ·
                        rfl

theorem cell23_6229868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 2, 4, 1, 2, 2].length) (baseStart_6229868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6229868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6229868 prefixEnd_6229868 := by exact prefixLift 6229868
  have htrace : WordTrace (prefixWord ++ tailWord_6229868) baseStart_6229868 baseEnd_6229868 := by
    simpa [prefixWord, tailWord_6229868, baseEnd_6229868] using wordTrace_append hprefix tailTrace_6229868
  have hstable : (prefixWord ++ tailWord_6229868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6229868).length < 2 ^ (prefixWord ++ tailWord_6229868).sum := by decide
  have hdescent : baseEnd_6229868 < baseStart_6229868 := by decide
  rcases family_descends (prefixWord ++ tailWord_6229868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6229878 : List Nat := [5, 1, 1, 3, 3, 1, 1, 1, 1, 6]
def baseStart_6229878 : Nat := 118140960795 + 6229878 * 2 ^ 59
def prefixEnd_6229878 : Nat := 4983230072969 + 3 ^ 40 * 6229878 * 2
def baseEnd_6229878 : Nat := 1066307277623627269124773

theorem tailTrace_6229878 : CollatzResearch.WordTrace tailWord_6229878 prefixEnd_6229878 1066307277623627269124773 := by
  unfold tailWord_6229878
  simp only [CollatzResearch.WordTrace]
  refine ⟨14201394857763966206241143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 151481545149482306199905525 14201394857763966206241143)
  ·
    refine ⟨21302092286645949309361715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14201394857763966206241143 21302092286645949309361715)
    ·
      refine ⟨31953138429968923964042573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21302092286645949309361715 31953138429968923964042573)
      ·
        refine ⟨11982426911238346486515965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31953138429968923964042573 11982426911238346486515965)
        ·
          refine ⟨4493410091714379932443487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11982426911238346486515965 4493410091714379932443487)
          ·
            refine ⟨6740115137571569898665231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4493410091714379932443487 6740115137571569898665231)
            ·
              refine ⟨10110172706357354847997847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6740115137571569898665231 10110172706357354847997847)
              ·
                refine ⟨15165259059536032271996771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10110172706357354847997847 15165259059536032271996771)
                ·
                  refine ⟨22747888589304048407995157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15165259059536032271996771 22747888589304048407995157)
                  ·
                    refine ⟨1066307277623627269124773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22747888589304048407995157 1066307277623627269124773)
                    ·
                      rfl

theorem cell23_6229878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 3, 1, 1, 1, 1, 6].length) (baseStart_6229878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6229878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6229878 prefixEnd_6229878 := by exact prefixLift 6229878
  have htrace : WordTrace (prefixWord ++ tailWord_6229878) baseStart_6229878 baseEnd_6229878 := by
    simpa [prefixWord, tailWord_6229878, baseEnd_6229878] using wordTrace_append hprefix tailTrace_6229878
  have hstable : (prefixWord ++ tailWord_6229878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6229878).length < 2 ^ (prefixWord ++ tailWord_6229878).sum := by decide
  have hdescent : baseEnd_6229878 < baseStart_6229878 := by decide
  rcases family_descends (prefixWord ++ tailWord_6229878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6229911 : List Nat := [1, 1, 3, 3, 1, 3, 2, 3, 1, 3, 2]
def baseStart_6229911 : Nat := 118140960795 + 6229911 * 2 ^ 59
def prefixEnd_6229911 : Nat := 4983230072969 + 3 ^ 40 * 6229911 * 2
def baseEnd_6229911 : Nat := 3198938777732480178261667

theorem tailTrace_6229911 : CollatzResearch.WordTrace tailWord_6229911 prefixEnd_6229911 3198938777732480178261667 := by
  unfold tailWord_6229911
  simp only [CollatzResearch.WordTrace]
  refine ⟨227223521333103905935809587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151482347555402603957206391 227223521333103905935809587)
  ·
    refine ⟨340835281999655858903714381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227223521333103905935809587 340835281999655858903714381)
    ·
      refine ⟨127813230749870947088892893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 340835281999655858903714381 127813230749870947088892893)
      ·
        refine ⟨47929961531201605158334835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 127813230749870947088892893 47929961531201605158334835)
        ·
          refine ⟨71894942296802407737502253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47929961531201605158334835 71894942296802407737502253)
          ·
            refine ⟨26960603361300902901563345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 71894942296802407737502253 26960603361300902901563345)
            ·
              refine ⟨20220452520975677176172509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26960603361300902901563345 20220452520975677176172509)
              ·
                refine ⟨7582669695365878941064691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20220452520975677176172509 7582669695365878941064691)
                ·
                  refine ⟨11374004543048818411597037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7582669695365878941064691 11374004543048818411597037)
                  ·
                    refine ⟨4265251703643306904348889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11374004543048818411597037 4265251703643306904348889)
                    ·
                      refine ⟨3198938777732480178261667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4265251703643306904348889 3198938777732480178261667)
                      ·
                        rfl

theorem cell23_6229911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 2, 3, 1, 3, 2].length) (baseStart_6229911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6229911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6229911 prefixEnd_6229911 := by exact prefixLift 6229911
  have htrace : WordTrace (prefixWord ++ tailWord_6229911) baseStart_6229911 baseEnd_6229911 := by
    simpa [prefixWord, tailWord_6229911, baseEnd_6229911] using wordTrace_append hprefix tailTrace_6229911
  have hstable : (prefixWord ++ tailWord_6229911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6229911).length < 2 ^ (prefixWord ++ tailWord_6229911).sum := by decide
  have hdescent : baseEnd_6229911 < baseStart_6229911 := by decide
  rcases family_descends (prefixWord ++ tailWord_6229911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6229957 : List Nat := [1, 3, 1, 1, 1, 1, 1, 3, 3, 5, 3]
def baseStart_6229957 : Nat := 118140960795 + 6229957 * 2 ^ 59
def prefixEnd_6229957 : Nat := 4983230072969 + 3 ^ 40 * 6229957 * 2
def baseEnd_6229957 : Nat := 3198962397842586998286455

theorem tailTrace_6229957 : CollatzResearch.WordTrace tailWord_6229957 prefixEnd_6229957 3198962397842586998286455 := by
  unfold tailWord_6229957
  simp only [CollatzResearch.WordTrace]
  refine ⟨227225199090937255791984125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151483466060624837194656083 227225199090937255791984125)
  ·
    refine ⟨85209449659101470921994047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 227225199090937255791984125 85209449659101470921994047)
    ·
      refine ⟨127814174488652206382991071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85209449659101470921994047 127814174488652206382991071)
      ·
        refine ⟨191721261732978309574486607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127814174488652206382991071 191721261732978309574486607)
        ·
          refine ⟨287581892599467464361729911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 191721261732978309574486607 287581892599467464361729911)
          ·
            refine ⟨431372838899201196542594867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 287581892599467464361729911 431372838899201196542594867)
            ·
              refine ⟨647059258348801794813892301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 431372838899201196542594867 647059258348801794813892301)
              ·
                refine ⟨242647221880800673055209613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 647059258348801794813892301 242647221880800673055209613)
                ·
                  refine ⟨90992708205300252395703605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 242647221880800673055209613 90992708205300252395703605)
                  ·
                    refine ⟨8530566394246898662097213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 90992708205300252395703605 8530566394246898662097213)
                    ·
                      refine ⟨3198962397842586998286455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8530566394246898662097213 3198962397842586998286455)
                      ·
                        rfl

theorem cell23_6229957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 3, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 3, 3, 5, 3].length) (baseStart_6229957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6229957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6229957 prefixEnd_6229957 := by exact prefixLift 6229957
  have htrace : WordTrace (prefixWord ++ tailWord_6229957) baseStart_6229957 baseEnd_6229957 := by
    simpa [prefixWord, tailWord_6229957, baseEnd_6229957] using wordTrace_append hprefix tailTrace_6229957
  have hstable : (prefixWord ++ tailWord_6229957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6229957).length < 2 ^ (prefixWord ++ tailWord_6229957).sum := by decide
  have hdescent : baseEnd_6229957 < baseStart_6229957 := by decide
  rcases family_descends (prefixWord ++ tailWord_6229957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6229991 : List Nat := [1, 1, 5, 2, 3, 1, 1, 1, 2, 3, 3]
def baseStart_6229991 : Nat := 118140960795 + 6229991 * 2 ^ 59
def prefixEnd_6229991 : Nat := 4983230072969 + 3 ^ 40 * 6229991 * 2
def baseEnd_6229991 : Nat := 3198979856184839865261299

theorem tailTrace_6229991 : CollatzResearch.WordTrace tailWord_6229991 prefixEnd_6229991 3198979856184839865261299 := by
  unfold tailWord_6229991
  simp only [CollatzResearch.WordTrace]
  refine ⟨227226439172814079598721827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151484292781876053065814551 227226439172814079598721827)
  ·
    refine ⟨340839658759221119398082741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227226439172814079598721827 340839658759221119398082741)
    ·
      refine ⟨31953718008676979943570257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 340839658759221119398082741 31953718008676979943570257)
      ·
        refine ⟨23965288506507734957677693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31953718008676979943570257 23965288506507734957677693)
        ·
          refine ⟨8986983189940400609129135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23965288506507734957677693 8986983189940400609129135)
          ·
            refine ⟨13480474784910600913693703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8986983189940400609129135 13480474784910600913693703)
            ·
              refine ⟨20220712177365901370540555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13480474784910600913693703 20220712177365901370540555)
              ·
                refine ⟨30331068266048852055810833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20220712177365901370540555 30331068266048852055810833)
                ·
                  refine ⟨22748301199536639041858125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30331068266048852055810833 22748301199536639041858125)
                  ·
                    refine ⟨8530612949826239640696797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22748301199536639041858125 8530612949826239640696797)
                    ·
                      refine ⟨3198979856184839865261299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8530612949826239640696797 3198979856184839865261299)
                      ·
                        rfl

theorem cell23_6229991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 1, 1, 2, 3, 3].length) (baseStart_6229991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6229991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6229991 prefixEnd_6229991 := by exact prefixLift 6229991
  have htrace : WordTrace (prefixWord ++ tailWord_6229991) baseStart_6229991 baseEnd_6229991 := by
    simpa [prefixWord, tailWord_6229991, baseEnd_6229991] using wordTrace_append hprefix tailTrace_6229991
  have hstable : (prefixWord ++ tailWord_6229991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6229991).length < 2 ^ (prefixWord ++ tailWord_6229991).sum := by decide
  have hdescent : baseEnd_6229991 < baseStart_6229991 := by decide
  rcases family_descends (prefixWord ++ tailWord_6229991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6230024 : List Nat := [2, 1, 3, 2, 1, 2, 1, 2, 5, 4]
def baseStart_6230024 : Nat := 118140960795 + 6230024 * 2 ^ 59
def prefixEnd_6230024 : Nat := 4983230072969 + 3 ^ 40 * 6230024 * 2
def baseEnd_6230024 : Nat := 1066332267015479412049549

theorem tailTrace_6230024 : CollatzResearch.WordTrace tailWord_6230024 prefixEnd_6230024 1066332267015479412049549 := by
  unfold tailWord_6230024
  simp only [CollatzResearch.WordTrace]
  refine ⟨113613821390847263117336563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151485095187796350823115417 113613821390847263117336563)
  ·
    refine ⟨170420732086270894676004845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113613821390847263117336563 170420732086270894676004845)
    ·
      refine ⟨63907774532351585503501817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 170420732086270894676004845 63907774532351585503501817)
      ·
        refine ⟨47930830899263689127626363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63907774532351585503501817 47930830899263689127626363)
        ·
          refine ⟨71896246348895533691439545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47930830899263689127626363 71896246348895533691439545)
          ·
            refine ⟨53922184761671650268579659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71896246348895533691439545 53922184761671650268579659)
            ·
              refine ⟨80883277142507475402869489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53922184761671650268579659 80883277142507475402869489)
              ·
                refine ⟨60662457856880606552152117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 80883277142507475402869489 60662457856880606552152117)
                ·
                  refine ⟨5687105424082556864264261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 60662457856880606552152117 5687105424082556864264261)
                  ·
                    refine ⟨1066332267015479412049549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5687105424082556864264261 1066332267015479412049549)
                    ·
                      rfl

theorem cell23_6230024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 2, 5, 4].length) (baseStart_6230024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6230024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6230024 prefixEnd_6230024 := by exact prefixLift 6230024
  have htrace : WordTrace (prefixWord ++ tailWord_6230024) baseStart_6230024 baseEnd_6230024 := by
    simpa [prefixWord, tailWord_6230024, baseEnd_6230024] using wordTrace_append hprefix tailTrace_6230024
  have hstable : (prefixWord ++ tailWord_6230024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6230024).length < 2 ^ (prefixWord ++ tailWord_6230024).sum := by decide
  have hdescent : baseEnd_6230024 < baseStart_6230024 := by decide
  rcases family_descends (prefixWord ++ tailWord_6230024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6230027 : List Nat := [1, 1, 1, 1, 6, 1, 1, 1, 1, 3, 6]
def baseStart_6230027 : Nat := 118140960795 + 6230027 * 2 ^ 59
def prefixEnd_6230027 : Nat := 4983230072969 + 3 ^ 40 * 6230027 * 2
def baseEnd_6230027 : Nat := 3198998341488401724411133

theorem tailTrace_6230027 : CollatzResearch.WordTrace tailWord_6230027 prefixEnd_6230027 3198998341488401724411133 := by
  unfold tailWord_6230027
  simp only [CollatzResearch.WordTrace]
  refine ⟨227227752200683657747032335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151485168133789105164688223 227227752200683657747032335)
  ·
    refine ⟨340841628301025486620548503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227227752200683657747032335 340841628301025486620548503)
    ·
      refine ⟨511262442451538229930822755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 340841628301025486620548503 511262442451538229930822755)
      ·
        refine ⟨766893663677307344896234133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 511262442451538229930822755 766893663677307344896234133)
        ·
          refine ⟨35948140484873781792010975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 766893663677307344896234133 35948140484873781792010975)
          ·
            refine ⟨53922210727310672688016463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35948140484873781792010975 53922210727310672688016463)
            ·
              refine ⟨80883316090966009032024695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53922210727310672688016463 80883316090966009032024695)
              ·
                refine ⟨121324974136449013548037043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 80883316090966009032024695 121324974136449013548037043)
                ·
                  refine ⟨181987461204673520322055565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 121324974136449013548037043 181987461204673520322055565)
                  ·
                    refine ⟨68245297951752570120770837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 181987461204673520322055565 68245297951752570120770837)
                    ·
                      refine ⟨3198998341488401724411133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 68245297951752570120770837 3198998341488401724411133)
                      ·
                        rfl

theorem cell23_6230027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 1, 1, 3, 6].length) (baseStart_6230027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6230027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6230027 prefixEnd_6230027 := by exact prefixLift 6230027
  have htrace : WordTrace (prefixWord ++ tailWord_6230027) baseStart_6230027 baseEnd_6230027 := by
    simpa [prefixWord, tailWord_6230027, baseEnd_6230027] using wordTrace_append hprefix tailTrace_6230027
  have hstable : (prefixWord ++ tailWord_6230027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6230027).length < 2 ^ (prefixWord ++ tailWord_6230027).sum := by decide
  have hdescent : baseEnd_6230027 < baseStart_6230027 := by decide
  rcases family_descends (prefixWord ++ tailWord_6230027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6230091 : List Nat := [1, 1, 1, 1, 3, 1, 2, 6, 2, 3, 2]
def baseStart_6230091 : Nat := 118140960795 + 6230091 * 2 ^ 59
def prefixEnd_6230091 : Nat := 4983230072969 + 3 ^ 40 * 6230091 * 2
def baseEnd_6230091 : Nat := 3199031204250289474010839

theorem tailTrace_6230091 : CollatzResearch.WordTrace tailWord_6230091 prefixEnd_6230091 3199031204250289474010839 := by
  unfold tailWord_6230091
  simp only [CollatzResearch.WordTrace]
  refine ⟨227230086472451796677362127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151486724314967864451574751 227230086472451796677362127)
  ·
    refine ⟨340845129708677695016043191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227230086472451796677362127 340845129708677695016043191)
    ·
      refine ⟨511267694563016542524064787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 340845129708677695016043191 511267694563016542524064787)
      ·
        refine ⟨766901541844524813786097181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 511267694563016542524064787 766901541844524813786097181)
        ·
          refine ⟨287588078191696805169786443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 766901541844524813786097181 287588078191696805169786443)
          ·
            refine ⟨431382117287545207754679665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 287588078191696805169786443 431382117287545207754679665)
            ·
              refine ⟨323536587965658905816009749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 431382117287545207754679665 323536587965658905816009749)
              ·
                refine ⟨15165777560890261210125457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 323536587965658905816009749 15165777560890261210125457)
                ·
                  refine ⟨11374333170667695907594093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15165777560890261210125457 11374333170667695907594093)
                  ·
                    refine ⟨4265374939000385965347785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11374333170667695907594093 4265374939000385965347785)
                    ·
                      refine ⟨3199031204250289474010839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4265374939000385965347785 3199031204250289474010839)
                      ·
                        rfl

theorem cell23_6230091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 6, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 6, 2, 3, 2].length) (baseStart_6230091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6230091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6230091 prefixEnd_6230091 := by exact prefixLift 6230091
  have htrace : WordTrace (prefixWord ++ tailWord_6230091) baseStart_6230091 baseEnd_6230091 := by
    simpa [prefixWord, tailWord_6230091, baseEnd_6230091] using wordTrace_append hprefix tailTrace_6230091
  have hstable : (prefixWord ++ tailWord_6230091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6230091).length < 2 ^ (prefixWord ++ tailWord_6230091).sum := by decide
  have hdescent : baseEnd_6230091 < baseStart_6230091 := by decide
  rcases family_descends (prefixWord ++ tailWord_6230091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6230141 : List Nat := [1, 4, 1, 1, 3, 2, 3, 1, 1, 1, 5]
def baseStart_6230141 : Nat := 118140960795 + 6230141 * 2 ^ 59
def prefixEnd_6230141 : Nat := 4983230072969 + 3 ^ 40 * 6230141 * 2
def baseEnd_6230141 : Nat := 3199056878283014278385609

theorem tailTrace_6230141 : CollatzResearch.WordTrace tailWord_6230141 prefixEnd_6230141 3199056878283014278385609 := by
  unfold tailWord_6230141
  simp only [CollatzResearch.WordTrace]
  refine ⟨227231910122270655216682277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151487940081513770144454851 227231910122270655216682277)
  ·
    refine ⟨42605983147925747853127927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 227231910122270655216682277 42605983147925747853127927)
    ·
      refine ⟨63908974721888621779691891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42605983147925747853127927 63908974721888621779691891)
      ·
        refine ⟨95863462082832932669537837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63908974721888621779691891 95863462082832932669537837)
        ·
          refine ⟨35948798281062349751076689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 95863462082832932669537837 35948798281062349751076689)
          ·
            refine ⟨26961598710796762313307517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35948798281062349751076689 26961598710796762313307517)
            ·
              refine ⟨10110599516548785867490319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26961598710796762313307517 10110599516548785867490319)
              ·
                refine ⟨15165899274823178801235479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10110599516548785867490319 15165899274823178801235479)
                ·
                  refine ⟨22748848912234768201853219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15165899274823178801235479 22748848912234768201853219)
                  ·
                    refine ⟨34123273368352152302779829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22748848912234768201853219 34123273368352152302779829)
                    ·
                      refine ⟨3199056878283014278385609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34123273368352152302779829 3199056878283014278385609)
                      ·
                        rfl

theorem cell23_6230141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 3, 1, 1, 1, 5].length) (baseStart_6230141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6230141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6230141 prefixEnd_6230141 := by exact prefixLift 6230141
  have htrace : WordTrace (prefixWord ++ tailWord_6230141) baseStart_6230141 baseEnd_6230141 := by
    simpa [prefixWord, tailWord_6230141, baseEnd_6230141] using wordTrace_append hprefix tailTrace_6230141
  have hstable : (prefixWord ++ tailWord_6230141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6230141).length < 2 ^ (prefixWord ++ tailWord_6230141).sum := by decide
  have hdescent : baseEnd_6230141 < baseStart_6230141 := by decide
  rcases family_descends (prefixWord ++ tailWord_6230141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6230148 : List Nat := [2, 3, 2, 1, 2, 1, 4, 2, 2, 4]
def baseStart_6230148 : Nat := 118140960795 + 6230148 * 2 ^ 59
def prefixEnd_6230148 : Nat := 4983230072969 + 3 ^ 40 * 6230148 * 2
def baseEnd_6230148 : Nat := 1066353490882531916999359

theorem tailTrace_6230148 : CollatzResearch.WordTrace tailWord_6230148 prefixEnd_6230148 1066353490882531916999359 := by
  unfold tailWord_6230148
  simp only [CollatzResearch.WordTrace]
  refine ⟨113616082716622647706093549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151488110288830196941458065 113616082716622647706093549)
  ·
    refine ⟨42606031018733492889785081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113616082716622647706093549 42606031018733492889785081)
    ·
      refine ⟨31954523264050119667338811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42606031018733492889785081 31954523264050119667338811)
      ·
        refine ⟨47931784896075179501008217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31954523264050119667338811 47931784896075179501008217)
        ·
          refine ⟨35948838672056384625756163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47931784896075179501008217 35948838672056384625756163)
          ·
            refine ⟨53923258008084576938634245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35948838672056384625756163 53923258008084576938634245)
            ·
              refine ⟨10110610876515858175993921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 53923258008084576938634245 10110610876515858175993921)
              ·
                refine ⟨7582958157386893631995441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10110610876515858175993921 7582958157386893631995441)
                ·
                  refine ⟨5687218618040170223996581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7582958157386893631995441 5687218618040170223996581)
                  ·
                    refine ⟨1066353490882531916999359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5687218618040170223996581 1066353490882531916999359)
                    ·
                      rfl

theorem cell23_6230148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 4, 2, 2, 4].length) (baseStart_6230148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6230148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6230148 prefixEnd_6230148 := by exact prefixLift 6230148
  have htrace : WordTrace (prefixWord ++ tailWord_6230148) baseStart_6230148 baseEnd_6230148 := by
    simpa [prefixWord, tailWord_6230148, baseEnd_6230148] using wordTrace_append hprefix tailTrace_6230148
  have hstable : (prefixWord ++ tailWord_6230148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6230148).length < 2 ^ (prefixWord ++ tailWord_6230148).sum := by decide
  have hdescent : baseEnd_6230148 < baseStart_6230148 := by decide
  rcases family_descends (prefixWord ++ tailWord_6230148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6230166 : List Nat := [5, 3, 2, 1, 1, 1, 1, 2, 3, 1, 3]
def baseStart_6230166 : Nat := 118140960795 + 6230166 * 2 ^ 59
def prefixEnd_6230166 : Nat := 4983230072969 + 3 ^ 40 * 6230166 * 2
def baseEnd_6230166 : Nat := 3199069715299376680572995

theorem tailTrace_6230166 : CollatzResearch.WordTrace tailWord_6230166 prefixEnd_6230166 3199069715299376680572995 := by
  unfold tailWord_6230166
  simp only [CollatzResearch.WordTrace]
  refine ⟨14202051371698755280396397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 151488547964786722990894901 14202051371698755280396397)
  ·
    refine ⟨5325769264387033230148649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14202051371698755280396397 5325769264387033230148649)
    ·
      refine ⟨3994326948290274922611487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5325769264387033230148649 3994326948290274922611487)
      ·
        refine ⟨5991490422435412383917231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3994326948290274922611487 5991490422435412383917231)
        ·
          refine ⟨8987235633653118575875847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5991490422435412383917231 8987235633653118575875847)
          ·
            refine ⟨13480853450479677863813771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8987235633653118575875847 13480853450479677863813771)
            ·
              refine ⟨20221280175719516795720657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13480853450479677863813771 20221280175719516795720657)
              ·
                refine ⟨15165960131789637596790493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20221280175719516795720657 15165960131789637596790493)
                ·
                  refine ⟨5687235049421114098796435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15165960131789637596790493 5687235049421114098796435)
                  ·
                    refine ⟨8530852574131671148194653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5687235049421114098796435 8530852574131671148194653)
                    ·
                      refine ⟨3199069715299376680572995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8530852574131671148194653 3199069715299376680572995)
                      ·
                        rfl

theorem cell23_6230166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 1, 2, 3, 1, 3].length) (baseStart_6230166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6230166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6230166 prefixEnd_6230166 := by exact prefixLift 6230166
  have htrace : WordTrace (prefixWord ++ tailWord_6230166) baseStart_6230166 baseEnd_6230166 := by
    simpa [prefixWord, tailWord_6230166, baseEnd_6230166] using wordTrace_append hprefix tailTrace_6230166
  have hstable : (prefixWord ++ tailWord_6230166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6230166).length < 2 ^ (prefixWord ++ tailWord_6230166).sum := by decide
  have hdescent : baseEnd_6230166 < baseStart_6230166 := by decide
  rcases family_descends (prefixWord ++ tailWord_6230166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6230168 : List Nat := [2, 1, 2, 4, 3, 1, 2, 1, 1, 2, 4]
def baseStart_6230168 : Nat := 118140960795 + 6230168 * 2 ^ 59
def prefixEnd_6230168 : Nat := 4983230072969 + 3 ^ 40 * 6230168 * 2
def baseEnd_6230168 : Nat := 3199070742260685672747985

theorem tailTrace_6230168 : CollatzResearch.WordTrace tailWord_6230168 prefixEnd_6230168 3199070742260685672747985 := by
  unfold tailWord_6230168
  simp only [CollatzResearch.WordTrace]
  refine ⟨113616447446586419413957579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151488596595448559218610105 113616447446586419413957579)
  ·
    refine ⟨170424671169879629120936369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113616447446586419413957579 170424671169879629120936369)
    ·
      refine ⟨127818503377409721840702277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 170424671169879629120936369 127818503377409721840702277)
      ·
        refine ⟨23965969383264322845131677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 127818503377409721840702277 23965969383264322845131677)
        ·
          refine ⟨8987238518724121066924379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23965969383264322845131677 8987238518724121066924379)
          ·
            refine ⟨13480857778086181600386569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8987238518724121066924379 13480857778086181600386569)
            ·
              refine ⟨10110643333564636200289927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13480857778086181600386569 10110643333564636200289927)
              ·
                refine ⟨15165965000346954300434891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10110643333564636200289927 15165965000346954300434891)
                ·
                  refine ⟨22748947500520431450652337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15165965000346954300434891 22748947500520431450652337)
                  ·
                    refine ⟨17061710625390323587989253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22748947500520431450652337 17061710625390323587989253)
                    ·
                      refine ⟨3199070742260685672747985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17061710625390323587989253 3199070742260685672747985)
                      ·
                        rfl

theorem cell23_6230168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 2, 1, 1, 2, 4].length) (baseStart_6230168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6230168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6230168 prefixEnd_6230168 := by exact prefixLift 6230168
  have htrace : WordTrace (prefixWord ++ tailWord_6230168) baseStart_6230168 baseEnd_6230168 := by
    simpa [prefixWord, tailWord_6230168, baseEnd_6230168] using wordTrace_append hprefix tailTrace_6230168
  have hstable : (prefixWord ++ tailWord_6230168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6230168).length < 2 ^ (prefixWord ++ tailWord_6230168).sum := by decide
  have hdescent : baseEnd_6230168 < baseStart_6230168 := by decide
  rcases family_descends (prefixWord ++ tailWord_6230168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6230178 : List Nat := [3, 3, 1, 3, 1, 2, 3, 7]
def baseStart_6230178 : Nat := 118140960795 + 6230178 * 2 ^ 59
def prefixEnd_6230178 : Nat := 4983230072969 + 3 ^ 40 * 6230178 * 2
def baseEnd_6230178 : Nat := 118484291743230764208257

theorem tailTrace_6230178 : CollatzResearch.WordTrace tailWord_6230178 prefixEnd_6230178 118484291743230764208257 := by
  unfold tailWord_6230178
  simp only [CollatzResearch.WordTrace]
  refine ⟨56808314905784152633944797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151488839748757740357186125 56808314905784152633944797)
  ·
    refine ⟨21303118089669057237729299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56808314905784152633944797 21303118089669057237729299)
    ·
      refine ⟨31954677134503585856593949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21303118089669057237729299 31954677134503585856593949)
      ·
        refine ⟨11983003925438844696222731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31954677134503585856593949 11983003925438844696222731)
        ·
          refine ⟨17974505888158267044334097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11983003925438844696222731 17974505888158267044334097)
          ·
            refine ⟨13480879416118700283250573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17974505888158267044334097 13480879416118700283250573)
            ·
              refine ⟨5055329781044512606218965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13480879416118700283250573 5055329781044512606218965)
              ·
                refine ⟨118484291743230764208257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5055329781044512606218965 118484291743230764208257)
                ·
                  rfl

theorem cell23_6230178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 3, 7].length) (baseStart_6230178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6230178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6230178 prefixEnd_6230178 := by exact prefixLift 6230178
  have htrace : WordTrace (prefixWord ++ tailWord_6230178) baseStart_6230178 baseEnd_6230178 := by
    simpa [prefixWord, tailWord_6230178, baseEnd_6230178] using wordTrace_append hprefix tailTrace_6230178
  have hstable : (prefixWord ++ tailWord_6230178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6230178).length < 2 ^ (prefixWord ++ tailWord_6230178).sum := by decide
  have hdescent : baseEnd_6230178 < baseStart_6230178 := by decide
  rcases family_descends (prefixWord ++ tailWord_6230178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6230189 : List Nat := [1, 5, 2, 1, 2, 2, 2, 3, 1, 2, 2]
def baseStart_6230189 : Nat := 118140960795 + 6230189 * 2 ^ 59
def prefixEnd_6230189 : Nat := 4983230072969 + 3 ^ 40 * 6230189 * 2
def baseEnd_6230189 : Nat := 3199081525354430090585389

theorem tailTrace_6230189 : CollatzResearch.WordTrace tailWord_6230189 prefixEnd_6230189 3199081525354430090585389 := by
  unfold tailWord_6230189
  simp only [CollatzResearch.WordTrace]
  refine ⟨227233660826096759414429621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151489107217397839609619747 227233660826096759414429621)
  ·
    refine ⟨21303155702446571195102777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 227233660826096759414429621 21303155702446571195102777)
    ·
      refine ⟨15977366776834928396327083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21303155702446571195102777 15977366776834928396327083)
      ·
        refine ⟨23966050165252392594490625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15977366776834928396327083 23966050165252392594490625)
        ·
          refine ⟨17974537623939294445867969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23966050165252392594490625 17974537623939294445867969)
          ·
            refine ⟨13480903217954470834400977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17974537623939294445867969 13480903217954470834400977)
            ·
              refine ⟨10110677413465853125800733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13480903217954470834400977 10110677413465853125800733)
              ·
                refine ⟨3791504030049694922175275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10110677413465853125800733 3791504030049694922175275)
                ·
                  refine ⟨5687256045074542383262913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3791504030049694922175275 5687256045074542383262913)
                  ·
                    refine ⟨4265442033805906787447185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5687256045074542383262913 4265442033805906787447185)
                    ·
                      refine ⟨3199081525354430090585389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4265442033805906787447185 3199081525354430090585389)
                      ·
                        rfl

theorem cell23_6230189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 2, 3, 1, 2, 2].length) (baseStart_6230189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6230189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6230189 prefixEnd_6230189 := by exact prefixLift 6230189
  have htrace : WordTrace (prefixWord ++ tailWord_6230189) baseStart_6230189 baseEnd_6230189 := by
    simpa [prefixWord, tailWord_6230189, baseEnd_6230189] using wordTrace_append hprefix tailTrace_6230189
  have hstable : (prefixWord ++ tailWord_6230189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6230189).length < 2 ^ (prefixWord ++ tailWord_6230189).sum := by decide
  have hdescent : baseEnd_6230189 < baseStart_6230189 := by decide
  rcases family_descends (prefixWord ++ tailWord_6230189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6230222 : List Nat := [4, 1, 1, 1, 4, 2, 3, 1, 2, 1, 3]
def baseStart_6230222 : Nat := 118140960795 + 6230222 * 2 ^ 59
def prefixEnd_6230222 : Nat := 4983230072969 + 3 ^ 40 * 6230222 * 2
def baseEnd_6230222 : Nat := 3199098470216028461472737

theorem tailTrace_6230222 : CollatzResearch.WordTrace tailWord_6230222 prefixEnd_6230222 3199098470216028461472737 := by
  unfold tailWord_6230222
  simp only [CollatzResearch.WordTrace]
  refine ⟨28404358054372150756297615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 151489909623318137366920613 28404358054372150756297615)
  ·
    refine ⟨42606537081558226134446423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28404358054372150756297615 42606537081558226134446423)
    ·
      refine ⟨63909805622337339201669635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42606537081558226134446423 63909805622337339201669635)
      ·
        refine ⟨95864708433506008802504453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63909805622337339201669635 95864708433506008802504453)
        ·
          refine ⟨17974632831282376650469585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 95864708433506008802504453 17974632831282376650469585)
          ·
            refine ⟨13480974623461782487852189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17974632831282376650469585 13480974623461782487852189)
            ·
              refine ⟨5055365483798168432944571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13480974623461782487852189 5055365483798168432944571)
              ·
                refine ⟨7583048225697252649416857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5055365483798168432944571 7583048225697252649416857)
                ·
                  refine ⟨5687286169272939487062643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7583048225697252649416857 5687286169272939487062643)
                  ·
                    refine ⟨8530929253909409230593965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5687286169272939487062643 8530929253909409230593965)
                    ·
                      refine ⟨3199098470216028461472737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8530929253909409230593965 3199098470216028461472737)
                      ·
                        rfl

theorem cell23_6230222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 3, 1, 2, 1, 3].length) (baseStart_6230222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6230222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6230222 prefixEnd_6230222 := by exact prefixLift 6230222
  have htrace : WordTrace (prefixWord ++ tailWord_6230222) baseStart_6230222 baseEnd_6230222 := by
    simpa [prefixWord, tailWord_6230222, baseEnd_6230222] using wordTrace_append hprefix tailTrace_6230222
  have hstable : (prefixWord ++ tailWord_6230222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6230222).length < 2 ^ (prefixWord ++ tailWord_6230222).sum := by decide
  have hdescent : baseEnd_6230222 < baseStart_6230222 := by decide
  rcases family_descends (prefixWord ++ tailWord_6230222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6230245 : List Nat := [1, 3, 1, 4, 2, 1, 1, 2, 4, 2, 2]
def baseStart_6230245 : Nat := 118140960795 + 6230245 * 2 ^ 59
def prefixEnd_6230245 : Nat := 4983230072969 + 3 ^ 40 * 6230245 * 2
def baseEnd_6230245 : Nat := 3199110280271081871485131

theorem tailTrace_6230245 : CollatzResearch.WordTrace tailWord_6230245 prefixEnd_6230245 3199110280271081871485131 := by
  unfold tailWord_6230245
  simp only [CollatzResearch.WordTrace]
  refine ⟨227235703313893880978468189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151490468875929253985645459 227235703313893880978468189)
  ·
    refine ⟨85213388742710205366925571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 227235703313893880978468189 85213388742710205366925571)
    ·
      refine ⟨127820083114065308050388357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85213388742710205366925571 127820083114065308050388357)
      ·
        refine ⟨23966265583887245259447817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 127820083114065308050388357 23966265583887245259447817)
        ·
          refine ⟨17974699187915433944585863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23966265583887245259447817 17974699187915433944585863)
          ·
            refine ⟨26962048781873150916878795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17974699187915433944585863 26962048781873150916878795)
            ·
              refine ⟨40443073172809726375318193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26962048781873150916878795 40443073172809726375318193)
              ·
                refine ⟨30332304879607294781488645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40443073172809726375318193 30332304879607294781488645)
                ·
                  refine ⟨5687307164926367771529121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30332304879607294781488645 5687307164926367771529121)
                  ·
                    refine ⟨4265480373694775828646841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5687307164926367771529121 4265480373694775828646841)
                    ·
                      refine ⟨3199110280271081871485131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4265480373694775828646841 3199110280271081871485131)
                      ·
                        rfl

theorem cell23_6230245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 1, 2, 4, 2, 2].length) (baseStart_6230245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6230245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6230245 prefixEnd_6230245 := by exact prefixLift 6230245
  have htrace : WordTrace (prefixWord ++ tailWord_6230245) baseStart_6230245 baseEnd_6230245 := by
    simpa [prefixWord, tailWord_6230245, baseEnd_6230245] using wordTrace_append hprefix tailTrace_6230245
  have hstable : (prefixWord ++ tailWord_6230245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6230245).length < 2 ^ (prefixWord ++ tailWord_6230245).sum := by decide
  have hdescent : baseEnd_6230245 < baseStart_6230245 := by decide
  rcases family_descends (prefixWord ++ tailWord_6230245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6230268 : List Nat := [2, 2, 2, 1, 4, 3, 1, 1, 7]
def baseStart_6230268 : Nat := 118140960795 + 6230268 * 2 ^ 59
def prefixEnd_6230268 : Nat := 4983230072969 + 3 ^ 40 * 6230268 * 2
def baseEnd_6230268 : Nat := 355458010036237253499725

theorem tailTrace_6230268 : CollatzResearch.WordTrace tailWord_6230268 prefixEnd_6230268 355458010036237253499725 := by
  unfold tailWord_6230268
  simp only [CollatzResearch.WordTrace]
  refine ⟨113618271096405277953277729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151491028128540370604370305 113618271096405277953277729)
  ·
    refine ⟨85213703322303958464958297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113618271096405277953277729 85213703322303958464958297)
    ·
      refine ⟨63910277491727968848718723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85213703322303958464958297 63910277491727968848718723)
      ·
        refine ⟨95865416237591953273078085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63910277491727968848718723 95865416237591953273078085)
        ·
          refine ⟨17974765544548491238702141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 95865416237591953273078085 17974765544548491238702141)
          ·
            refine ⟨6740537079205684214513303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17974765544548491238702141 6740537079205684214513303)
            ·
              refine ⟨10110805618808526321769955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6740537079205684214513303 10110805618808526321769955)
              ·
                refine ⟨15166208428212789482654933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10110805618808526321769955 15166208428212789482654933)
                ·
                  refine ⟨355458010036237253499725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15166208428212789482654933 355458010036237253499725)
                  ·
                    rfl

theorem cell23_6230268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 3, 1, 1, 7].length) (baseStart_6230268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6230268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6230268 prefixEnd_6230268 := by exact prefixLift 6230268
  have htrace : WordTrace (prefixWord ++ tailWord_6230268) baseStart_6230268 baseEnd_6230268 := by
    simpa [prefixWord, tailWord_6230268, baseEnd_6230268] using wordTrace_append hprefix tailTrace_6230268
  have hstable : (prefixWord ++ tailWord_6230268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6230268).length < 2 ^ (prefixWord ++ tailWord_6230268).sum := by decide
  have hdescent : baseEnd_6230268 < baseStart_6230268 := by decide
  rcases family_descends (prefixWord ++ tailWord_6230268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6230279 : List Nat := [1, 1, 4, 5, 1, 1, 1, 3, 2, 2, 2]
def baseStart_6230279 : Nat := 118140960795 + 6230279 * 2 ^ 59
def prefixEnd_6230279 : Nat := 4983230072969 + 3 ^ 40 * 6230279 * 2
def baseEnd_6230279 : Nat := 3199127738613334738459975

theorem tailTrace_6230279 : CollatzResearch.WordTrace tailWord_6230279 prefixEnd_6230279 3199127738613334738459975 := by
  unfold tailWord_6230279
  simp only [CollatzResearch.WordTrace]
  refine ⟨227236943395770704785205891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151491295597180469856803927 227236943395770704785205891)
  ·
    refine ⟨340855415093656057177808837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227236943395770704785205891 340855415093656057177808837)
    ·
      refine ⟨63910390330060510720839157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 340855415093656057177808837 63910390330060510720839157)
      ·
        refine ⟨5991599093443172880078671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 63910390330060510720839157 5991599093443172880078671)
        ·
          refine ⟨8987398640164759320118007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5991599093443172880078671 8987398640164759320118007)
          ·
            refine ⟨13481097960247138980177011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8987398640164759320118007 13481097960247138980177011)
            ·
              refine ⟨20221646940370708470265517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13481097960247138980177011 20221646940370708470265517)
              ·
                refine ⟨7583117602639015676349569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20221646940370708470265517 7583117602639015676349569)
                ·
                  refine ⟨5687338201979261757262177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7583117602639015676349569 5687338201979261757262177)
                  ·
                    refine ⟨4265503651484446317946633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5687338201979261757262177 4265503651484446317946633)
                    ·
                      refine ⟨3199127738613334738459975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4265503651484446317946633 3199127738613334738459975)
                      ·
                        rfl

theorem cell23_6230279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 1, 3, 2, 2, 2].length) (baseStart_6230279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6230279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6230279 prefixEnd_6230279 := by exact prefixLift 6230279
  have htrace : WordTrace (prefixWord ++ tailWord_6230279) baseStart_6230279 baseEnd_6230279 := by
    simpa [prefixWord, tailWord_6230279, baseEnd_6230279] using wordTrace_append hprefix tailTrace_6230279
  have hstable : (prefixWord ++ tailWord_6230279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6230279).length < 2 ^ (prefixWord ++ tailWord_6230279).sum := by decide
  have hdescent : baseEnd_6230279 < baseStart_6230279 := by decide
  rcases family_descends (prefixWord ++ tailWord_6230279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6230351 : List Nat := [1, 1, 2, 1, 1, 2, 1, 3, 1, 7, 3]
def baseStart_6230351 : Nat := 118140960795 + 6230351 * 2 ^ 59
def prefixEnd_6230351 : Nat := 4983230072969 + 3 ^ 40 * 6230351 * 2
def baseEnd_6230351 : Nat := 3199164709220458456759643

theorem tailTrace_6230351 : CollatzResearch.WordTrace tailWord_6230351 prefixEnd_6230351 3199164709220458456759643 := by
  unfold tailWord_6230351
  simp only [CollatzResearch.WordTrace]
  refine ⟨227239569451509861081826907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151493046301006574054551271 227239569451509861081826907)
  ·
    refine ⟨340859354177264791622740361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227239569451509861081826907 340859354177264791622740361)
    ·
      refine ⟨255644515632948593717055271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 340859354177264791622740361 255644515632948593717055271)
      ·
        refine ⟨383466773449422890575582907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 255644515632948593717055271 383466773449422890575582907)
        ·
          refine ⟨575200160174134335863374361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 383466773449422890575582907 575200160174134335863374361)
          ·
            refine ⟨431400120130600751897530771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 575200160174134335863374361 431400120130600751897530771)
            ·
              refine ⟨647100180195901127846296157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 431400120130600751897530771 647100180195901127846296157)
              ·
                refine ⟨242662567573462922942361059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 647100180195901127846296157 242662567573462922942361059)
                ·
                  refine ⟨363993851360194384413541589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 242662567573462922942361059 363993851360194384413541589)
                  ·
                    refine ⟨8531105891254555884692381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 363993851360194384413541589 8531105891254555884692381)
                    ·
                      refine ⟨3199164709220458456759643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8531105891254555884692381 3199164709220458456759643)
                      ·
                        rfl

theorem cell23_6230351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 3, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 3, 1, 7, 3].length) (baseStart_6230351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6230351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6230351 prefixEnd_6230351 := by exact prefixLift 6230351
  have htrace : WordTrace (prefixWord ++ tailWord_6230351) baseStart_6230351 baseEnd_6230351 := by
    simpa [prefixWord, tailWord_6230351, baseEnd_6230351] using wordTrace_append hprefix tailTrace_6230351
  have hstable : (prefixWord ++ tailWord_6230351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6230351).length < 2 ^ (prefixWord ++ tailWord_6230351).sum := by decide
  have hdescent : baseEnd_6230351 < baseStart_6230351 := by decide
  rcases family_descends (prefixWord ++ tailWord_6230351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6230375 : List Nat := [1, 1, 5, 1, 3, 3, 1, 2, 6]
def baseStart_6230375 : Nat := 118140960795 + 6230375 * 2 ^ 59
def prefixEnd_6230375 : Nat := 4983230072969 + 3 ^ 40 * 6230375 * 2
def baseEnd_6230375 : Nat := 355464114750685151428837

theorem tailTrace_6230375 : CollatzResearch.WordTrace tailWord_6230375 prefixEnd_6230375 355464114750685151428837 := by
  unfold tailWord_6230375
  simp only [CollatzResearch.WordTrace]
  refine ⟨227240444803422913180700579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151493629868948608787133719 227240444803422913180700579)
  ·
    refine ⟨340860667205134369771050869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227240444803422913180700579 340860667205134369771050869)
    ·
      refine ⟨31955687550481347166036019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 340860667205134369771050869 31955687550481347166036019)
      ·
        refine ⟨47933531325722020749054029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31955687550481347166036019 47933531325722020749054029)
        ·
          refine ⟨17975074247145757780895261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47933531325722020749054029 17975074247145757780895261)
          ·
            refine ⟨6740652842679659167835723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17975074247145757780895261 6740652842679659167835723)
            ·
              refine ⟨10110979264019488751753585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6740652842679659167835723 10110979264019488751753585)
              ·
                refine ⟨7583234448014616563815189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10110979264019488751753585 7583234448014616563815189)
                ·
                  refine ⟨355464114750685151428837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7583234448014616563815189 355464114750685151428837)
                  ·
                    rfl

theorem cell23_6230375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 3, 1, 2, 6].length) (baseStart_6230375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6230375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6230375 prefixEnd_6230375 := by exact prefixLift 6230375
  have htrace : WordTrace (prefixWord ++ tailWord_6230375) baseStart_6230375 baseEnd_6230375 := by
    simpa [prefixWord, tailWord_6230375, baseEnd_6230375] using wordTrace_append hprefix tailTrace_6230375
  have hstable : (prefixWord ++ tailWord_6230375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6230375).length < 2 ^ (prefixWord ++ tailWord_6230375).sum := by decide
  have hdescent : baseEnd_6230375 < baseStart_6230375 := by decide
  rcases family_descends (prefixWord ++ tailWord_6230375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6230378 : List Nat := [3, 1, 3, 3, 1, 1, 1, 1, 1, 2, 6]
def baseStart_6230378 : Nat := 118140960795 + 6230378 * 2 ^ 59
def prefixEnd_6230378 : Nat := 4983230072969 + 3 ^ 40 * 6230378 * 2
def baseEnd_6230378 : Nat := 3199178573198129851122019

theorem tailTrace_6230378 : CollatzResearch.WordTrace tailWord_6230378 prefixEnd_6230378 3199178573198129851122019 := by
  unfold tailWord_6230378
  simp only [CollatzResearch.WordTrace]
  refine ⟨56810138555603011173264947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151493702814941363128706525 56810138555603011173264947)
  ·
    refine ⟨85215207833404516759897421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56810138555603011173264947 85215207833404516759897421)
    ·
      refine ⟨31955702937526693784961533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85215207833404516759897421 31955702937526693784961533)
      ·
        refine ⟨11983388601572510169360575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31955702937526693784961533 11983388601572510169360575)
        ·
          refine ⟨17975082902358765254040863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11983388601572510169360575 17975082902358765254040863)
          ·
            refine ⟨26962624353538147881061295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17975082902358765254040863 26962624353538147881061295)
            ·
              refine ⟨40443936530307221821591943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26962624353538147881061295 40443936530307221821591943)
              ·
                refine ⟨60665904795460832732387915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40443936530307221821591943 60665904795460832732387915)
                ·
                  refine ⟨90998857193191249098581873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 60665904795460832732387915 90998857193191249098581873)
                  ·
                    refine ⟨68249142894893436823936405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 90998857193191249098581873 68249142894893436823936405)
                    ·
                      refine ⟨3199178573198129851122019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 68249142894893436823936405 3199178573198129851122019)
                      ·
                        rfl

theorem cell23_6230378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 1, 1, 1, 2, 6].length) (baseStart_6230378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6230378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6230378 prefixEnd_6230378 := by exact prefixLift 6230378
  have htrace : WordTrace (prefixWord ++ tailWord_6230378) baseStart_6230378 baseEnd_6230378 := by
    simpa [prefixWord, tailWord_6230378, baseEnd_6230378] using wordTrace_append hprefix tailTrace_6230378
  have hstable : (prefixWord ++ tailWord_6230378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6230378).length < 2 ^ (prefixWord ++ tailWord_6230378).sum := by decide
  have hdescent : baseEnd_6230378 < baseStart_6230378 := by decide
  rcases family_descends (prefixWord ++ tailWord_6230378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6230391 : List Nat := [1, 1, 3, 1, 1, 2, 2, 1, 2, 5, 4]
def baseStart_6230391 : Nat := 118140960795 + 6230391 * 2 ^ 59
def prefixEnd_6230391 : Nat := 4983230072969 + 3 ^ 40 * 6230391 * 2
def baseEnd_6230391 : Nat := 3199185248446638300259459

theorem tailTrace_6230391 : CollatzResearch.WordTrace tailWord_6230391 prefixEnd_6230391 3199185248446638300259459 := by
  unfold tailWord_6230391
  simp only [CollatzResearch.WordTrace]
  refine ⟨227241028371364947913283027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151494018914243298608855351 227241028371364947913283027)
  ·
    refine ⟨340861542557047421869924541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227241028371364947913283027 340861542557047421869924541)
    ·
      refine ⟨127823078458892783201221703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 340861542557047421869924541 127823078458892783201221703)
      ·
        refine ⟨191734617688339174801832555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127823078458892783201221703 191734617688339174801832555)
        ·
          refine ⟨287601926532508762202748833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 191734617688339174801832555 287601926532508762202748833)
          ·
            refine ⟨215701444899381571652061625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 287601926532508762202748833 215701444899381571652061625)
            ·
              refine ⟨161776083674536178739046219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 215701444899381571652061625 161776083674536178739046219)
              ·
                refine ⟨242664125511804268108569329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 161776083674536178739046219 242664125511804268108569329)
                ·
                  refine ⟨181998094133853201081426997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 242664125511804268108569329 181998094133853201081426997)
                  ·
                    refine ⟨17062321325048737601383781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 181998094133853201081426997 17062321325048737601383781)
                    ·
                      refine ⟨3199185248446638300259459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17062321325048737601383781 3199185248446638300259459)
                      ·
                        rfl

theorem cell23_6230391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 1, 2, 5, 4].length) (baseStart_6230391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6230391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6230391 prefixEnd_6230391 := by exact prefixLift 6230391
  have htrace : WordTrace (prefixWord ++ tailWord_6230391) baseStart_6230391 baseEnd_6230391 := by
    simpa [prefixWord, tailWord_6230391, baseEnd_6230391] using wordTrace_append hprefix tailTrace_6230391
  have hstable : (prefixWord ++ tailWord_6230391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6230391).length < 2 ^ (prefixWord ++ tailWord_6230391).sum := by decide
  have hdescent : baseEnd_6230391 < baseStart_6230391 := by decide
  rcases family_descends (prefixWord ++ tailWord_6230391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6230458 : List Nat := [3, 1, 1, 1, 2, 1, 1, 2, 5, 3, 3]
def baseStart_6230458 : Nat := 118140960795 + 6230458 * 2 ^ 59
def prefixEnd_6230458 : Nat := 4983230072969 + 3 ^ 40 * 6230458 * 2
def baseEnd_6230458 : Nat := 3199219651650489538121651

theorem tailTrace_6230458 : CollatzResearch.WordTrace tailWord_6230458 prefixEnd_6230458 3199219651650489538121651 := by
  unfold tailWord_6230458
  simp only [CollatzResearch.WordTrace]
  refine ⟨56810868015530554588993007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151495648041414812237314685 56810868015530554588993007)
  ·
    refine ⟨85216302023295831883489511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56810868015530554588993007 85216302023295831883489511)
    ·
      refine ⟨127824453034943747825234267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85216302023295831883489511 127824453034943747825234267)
      ·
        refine ⟨191736679552415621737851401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127824453034943747825234267 191736679552415621737851401)
        ·
          refine ⟨143802509664311716303388551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 191736679552415621737851401 143802509664311716303388551)
          ·
            refine ⟨215703764496467574455082827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 143802509664311716303388551 215703764496467574455082827)
            ·
              refine ⟨323555646744701361682624241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 215703764496467574455082827 323555646744701361682624241)
              ·
                refine ⟨242666735058526021261968181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 323555646744701361682624241 242666735058526021261968181)
                ·
                  refine ⟨22750006411736814493309517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 242666735058526021261968181 22750006411736814493309517)
                  ·
                    refine ⟨8531252404401305434991069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22750006411736814493309517 8531252404401305434991069)
                    ·
                      refine ⟨3199219651650489538121651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8531252404401305434991069 3199219651650489538121651)
                      ·
                        rfl

theorem cell23_6230458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 2, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 2, 5, 3, 3].length) (baseStart_6230458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6230458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6230458 prefixEnd_6230458 := by exact prefixLift 6230458
  have htrace : WordTrace (prefixWord ++ tailWord_6230458) baseStart_6230458 baseEnd_6230458 := by
    simpa [prefixWord, tailWord_6230458, baseEnd_6230458] using wordTrace_append hprefix tailTrace_6230458
  have hstable : (prefixWord ++ tailWord_6230458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6230458).length < 2 ^ (prefixWord ++ tailWord_6230458).sum := by decide
  have hdescent : baseEnd_6230458 < baseStart_6230458 := by decide
  rcases family_descends (prefixWord ++ tailWord_6230458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6230462 : List Nat := [4, 2, 1, 1, 1, 1, 5, 2, 1, 2, 3]
def baseStart_6230462 : Nat := 118140960795 + 6230462 * 2 ^ 59
def prefixEnd_6230462 : Nat := 4983230072969 + 3 ^ 40 * 6230462 * 2
def baseEnd_6230462 : Nat := 3199221705573107522471633

theorem tailTrace_6230462 : CollatzResearch.WordTrace tailWord_6230462 prefixEnd_6230462 3199221705573107522471633 := by
  unfold tailWord_6230462
  simp only [CollatzResearch.WordTrace]
  refine ⟨28405452244263465879889705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 151495745302738484692745093 28405452244263465879889705)
  ·
    refine ⟨21304089183197599409917279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28405452244263465879889705 21304089183197599409917279)
    ·
      refine ⟨31956133774796399114875919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21304089183197599409917279 31956133774796399114875919)
      ·
        refine ⟨47934200662194598672313879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31956133774796399114875919 47934200662194598672313879)
        ·
          refine ⟨71901300993291898008470819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47934200662194598672313879 71901300993291898008470819)
          ·
            refine ⟨107851951489937847012706229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71901300993291898008470819 107851951489937847012706229)
            ·
              refine ⟨10111120452181673157441209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 107851951489937847012706229 10111120452181673157441209)
              ·
                refine ⟨7583340339136254868080907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10111120452181673157441209 7583340339136254868080907)
                ·
                  refine ⟨11375010508704382302121361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7583340339136254868080907 11375010508704382302121361)
                  ·
                    refine ⟨8531257881528286726591021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11375010508704382302121361 8531257881528286726591021)
                    ·
                      refine ⟨3199221705573107522471633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8531257881528286726591021 3199221705573107522471633)
                      ·
                        rfl

theorem cell23_6230462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 5, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 5, 2, 1, 2, 3].length) (baseStart_6230462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6230462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6230462 prefixEnd_6230462 := by exact prefixLift 6230462
  have htrace : WordTrace (prefixWord ++ tailWord_6230462) baseStart_6230462 baseEnd_6230462 := by
    simpa [prefixWord, tailWord_6230462, baseEnd_6230462] using wordTrace_append hprefix tailTrace_6230462
  have hstable : (prefixWord ++ tailWord_6230462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6230462).length < 2 ^ (prefixWord ++ tailWord_6230462).sum := by decide
  have hdescent : baseEnd_6230462 < baseStart_6230462 := by decide
  rcases family_descends (prefixWord ++ tailWord_6230462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6230508 : List Nat := [2, 2, 1, 1, 2, 1, 5, 1, 2, 6]
def baseStart_6230508 : Nat := 118140960795 + 6230508 * 2 ^ 59
def prefixEnd_6230508 : Nat := 4983230072969 + 3 ^ 40 * 6230508 * 2
def baseEnd_6230508 : Nat := 1066415108561071447498807

theorem tailTrace_6230508 : CollatzResearch.WordTrace tailWord_6230508 prefixEnd_6230508 1066415108561071447498807 := by
  unfold tailWord_6230508
  simp only [CollatzResearch.WordTrace]
  refine ⟨113622647855970538447646089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151496863807960717930194785 113622647855970538447646089)
  ·
    refine ⟨85216985891977903835734567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113622647855970538447646089 85216985891977903835734567)
    ·
      refine ⟨127825478837966855753601851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85216985891977903835734567 127825478837966855753601851)
      ·
        refine ⟨191738218256950283630402777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127825478837966855753601851 191738218256950283630402777)
        ·
          refine ⟨143803663692712712722802083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 191738218256950283630402777 143803663692712712722802083)
          ·
            refine ⟨215705495539069069084203125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 143803663692712712722802083 215705495539069069084203125)
            ·
              refine ⟨20222390206787725226644043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 215705495539069069084203125 20222390206787725226644043)
              ·
                refine ⟨30333585310181587839966065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20222390206787725226644043 30333585310181587839966065)
                ·
                  refine ⟨22750188982636190879974549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30333585310181587839966065 22750188982636190879974549)
                  ·
                    refine ⟨1066415108561071447498807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22750188982636190879974549 1066415108561071447498807)
                    ·
                      rfl

theorem cell23_6230508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 6].length) (baseStart_6230508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6230508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6230508 prefixEnd_6230508 := by exact prefixLift 6230508
  have htrace : WordTrace (prefixWord ++ tailWord_6230508) baseStart_6230508 baseEnd_6230508 := by
    simpa [prefixWord, tailWord_6230508, baseEnd_6230508] using wordTrace_append hprefix tailTrace_6230508
  have hstable : (prefixWord ++ tailWord_6230508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6230508).length < 2 ^ (prefixWord ++ tailWord_6230508).sum := by decide
  have hdescent : baseEnd_6230508 < baseStart_6230508 := by decide
  rcases family_descends (prefixWord ++ tailWord_6230508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6230509 : List Nat := [1, 5, 1, 3, 1, 1, 2, 3, 2, 1, 3]
def baseStart_6230509 : Nat := 118140960795 + 6230509 * 2 ^ 59
def prefixEnd_6230509 : Nat := 4983230072969 + 3 ^ 40 * 6230509 * 2
def baseEnd_6230509 : Nat := 3199245839163868838583917

theorem tailTrace_6230509 : CollatzResearch.WordTrace tailWord_6230509 prefixEnd_6230509 3199245839163868838583917 := by
  unfold tailWord_6230509
  simp only [CollatzResearch.WordTrace]
  refine ⟨227245332184937454066078581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151496888123291636044052387 227245332184937454066078581)
  ·
    refine ⟨21304249892337886318694867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 227245332184937454066078581 21304249892337886318694867)
    ·
      refine ⟨31956374838506829478042301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21304249892337886318694867 31956374838506829478042301)
      ·
        refine ⟨11983640564440061054265863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31956374838506829478042301 11983640564440061054265863)
        ·
          refine ⟨17975460846660091581398795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11983640564440061054265863 17975460846660091581398795)
          ·
            refine ⟨26963191269990137372098193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17975460846660091581398795 26963191269990137372098193)
            ·
              refine ⟨20222393452492603029073645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26963191269990137372098193 20222393452492603029073645)
              ·
                refine ⟨7583397544684726135902617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20222393452492603029073645 7583397544684726135902617)
                ·
                  refine ⟨5687548158513544601926963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7583397544684726135902617 5687548158513544601926963)
                  ·
                    refine ⟨8531322237770316902890445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5687548158513544601926963 8531322237770316902890445)
                    ·
                      refine ⟨3199245839163868838583917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8531322237770316902890445 3199245839163868838583917)
                      ·
                        rfl

theorem cell23_6230509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 2, 3, 2, 1, 3].length) (baseStart_6230509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6230509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6230509 prefixEnd_6230509 := by exact prefixLift 6230509
  have htrace : WordTrace (prefixWord ++ tailWord_6230509) baseStart_6230509 baseEnd_6230509 := by
    simpa [prefixWord, tailWord_6230509, baseEnd_6230509] using wordTrace_append hprefix tailTrace_6230509
  have hstable : (prefixWord ++ tailWord_6230509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6230509).length < 2 ^ (prefixWord ++ tailWord_6230509).sum := by decide
  have hdescent : baseEnd_6230509 < baseStart_6230509 := by decide
  rcases family_descends (prefixWord ++ tailWord_6230509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6230538 : List Nat := [3, 1, 2, 2, 2, 1, 1, 2, 9]
def baseStart_6230538 : Nat := 118140960795 + 6230538 * 2 ^ 59
def prefixEnd_6230538 : Nat := 4983230072969 + 3 ^ 40 * 6230538 * 2
def baseEnd_6230538 : Nat := 355473414455872136124587

theorem tailTrace_6230538 : CollatzResearch.WordTrace tailWord_6230538 prefixEnd_6230538 355473414455872136124587 := by
  unfold tailWord_6230538
  simp only [CollatzResearch.WordTrace]
  refine ⟨56811597475458098004721067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151497593267888261345922845 56811597475458098004721067)
  ·
    refine ⟨85217396213187147007081601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56811597475458098004721067 85217396213187147007081601)
    ·
      refine ⟨63913047159890360255311201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85217396213187147007081601 63913047159890360255311201)
      ·
        refine ⟨47934785369917770191483401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63913047159890360255311201 47934785369917770191483401)
        ·
          refine ⟨35951089027438327643612551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47934785369917770191483401 35951089027438327643612551)
          ·
            refine ⟨53926633541157491465418827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35951089027438327643612551 53926633541157491465418827)
            ·
              refine ⟨80889950311736237198128241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53926633541157491465418827 80889950311736237198128241)
              ·
                refine ⟨60667462733802177898596181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 80889950311736237198128241 60667462733802177898596181)
                ·
                  refine ⟨355473414455872136124587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 60667462733802177898596181 355473414455872136124587)
                  ·
                    rfl

theorem cell23_6230538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 2, 9].length) (baseStart_6230538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6230538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6230538 prefixEnd_6230538 := by exact prefixLift 6230538
  have htrace : WordTrace (prefixWord ++ tailWord_6230538) baseStart_6230538 baseEnd_6230538 := by
    simpa [prefixWord, tailWord_6230538, baseEnd_6230538] using wordTrace_append hprefix tailTrace_6230538
  have hstable : (prefixWord ++ tailWord_6230538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6230538).length < 2 ^ (prefixWord ++ tailWord_6230538).sum := by decide
  have hdescent : baseEnd_6230538 < baseStart_6230538 := by decide
  rcases family_descends (prefixWord ++ tailWord_6230538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6230565 : List Nat := [1, 3, 1, 2, 2, 1, 4, 1, 2, 3, 3]
def baseStart_6230565 : Nat := 118140960795 + 6230565 * 2 ^ 59
def prefixEnd_6230565 : Nat := 4983230072969 + 3 ^ 40 * 6230565 * 2
def baseEnd_6230565 : Nat := 3199274594080520619483659

theorem tailTrace_6230565 : CollatzResearch.WordTrace tailWord_6230565 prefixEnd_6230565 3199274594080520619483659 := by
  unfold tailWord_6230565
  simp only [CollatzResearch.WordTrace]
  refine ⟨227247374672734575630117149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151498249781823050420078099 227247374672734575630117149)
  ·
    refine ⟨85217765502275465861293931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 227247374672734575630117149 85217765502275465861293931)
    ·
      refine ⟨127826648253413198791940897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85217765502275465861293931 127826648253413198791940897)
      ·
        refine ⟨95869986190059899093955673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 127826648253413198791940897 95869986190059899093955673)
        ·
          refine ⟨71902489642544924320466755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95869986190059899093955673 71902489642544924320466755)
          ·
            refine ⟨107853734463817386480700133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71902489642544924320466755 107853734463817386480700133)
            ·
              refine ⟨20222575211965759965131275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 107853734463817386480700133 20222575211965759965131275)
              ·
                refine ⟨30333862817948639947696913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20222575211965759965131275 30333862817948639947696913)
                ·
                  refine ⟨22750397113461479960772685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30333862817948639947696913 22750397113461479960772685)
                  ·
                    refine ⟨8531398917548054985289757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22750397113461479960772685 8531398917548054985289757)
                    ·
                      refine ⟨3199274594080520619483659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8531398917548054985289757 3199274594080520619483659)
                      ·
                        rfl

theorem cell23_6230565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 4, 1, 2, 3, 3].length) (baseStart_6230565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6230565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6230565 prefixEnd_6230565 := by exact prefixLift 6230565
  have htrace : WordTrace (prefixWord ++ tailWord_6230565) baseStart_6230565 baseEnd_6230565 := by
    simpa [prefixWord, tailWord_6230565, baseEnd_6230565] using wordTrace_append hprefix tailTrace_6230565
  have hstable : (prefixWord ++ tailWord_6230565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6230565).length < 2 ^ (prefixWord ++ tailWord_6230565).sum := by decide
  have hdescent : baseEnd_6230565 < baseStart_6230565 := by decide
  rcases family_descends (prefixWord ++ tailWord_6230565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6230585 : List Nat := [1, 2, 1, 5, 1, 1, 2, 3, 2, 5]
def baseStart_6230585 : Nat := 118140960795 + 6230585 * 2 ^ 59
def prefixEnd_6230585 : Nat := 4983230072969 + 3 ^ 40 * 6230585 * 2
def baseEnd_6230585 : Nat := 1066428287897870180411189

theorem tailTrace_6230585 : CollatzResearch.WordTrace tailWord_6230585 prefixEnd_6230585 1066428287897870180411189 := by
  unfold tailWord_6230585
  simp only [CollatzResearch.WordTrace]
  refine ⟨227248104132662119045845209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151498736088441412697230139 227248104132662119045845209)
  ·
    refine ⟨170436078099496589284383907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 227248104132662119045845209 170436078099496589284383907)
    ·
      refine ⟨255654117149244883926575861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170436078099496589284383907 255654117149244883926575861)
      ·
        refine ⟨23967573482741707868116487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 255654117149244883926575861 23967573482741707868116487)
        ·
          refine ⟨35951360224112561802174731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23967573482741707868116487 35951360224112561802174731)
          ·
            refine ⟨53927040336168842703262097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35951360224112561802174731 53927040336168842703262097)
            ·
              refine ⟨40445280252126632027446573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53927040336168842703262097 40445280252126632027446573)
              ·
                refine ⟨15166980094547487010292465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40445280252126632027446573 15166980094547487010292465)
                ·
                  refine ⟨11375235070910615257719349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15166980094547487010292465 11375235070910615257719349)
                  ·
                    refine ⟨1066428287897870180411189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11375235070910615257719349 1066428287897870180411189)
                    ·
                      rfl

theorem cell23_6230585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 2, 3, 2, 5].length) (baseStart_6230585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6230585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6230585 prefixEnd_6230585 := by exact prefixLift 6230585
  have htrace : WordTrace (prefixWord ++ tailWord_6230585) baseStart_6230585 baseEnd_6230585 := by
    simpa [prefixWord, tailWord_6230585, baseEnd_6230585] using wordTrace_append hprefix tailTrace_6230585
  have hstable : (prefixWord ++ tailWord_6230585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6230585).length < 2 ^ (prefixWord ++ tailWord_6230585).sum := by decide
  have hdescent : baseEnd_6230585 < baseStart_6230585 := by decide
  rcases family_descends (prefixWord ++ tailWord_6230585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6230589 : List Nat := [1, 4, 1, 3, 2, 3, 1, 3, 5]
def baseStart_6230589 : Nat := 118140960795 + 6230589 * 2 ^ 59
def prefixEnd_6230589 : Nat := 4983230072969 + 3 ^ 40 * 6230589 * 2
def baseEnd_6230589 : Nat := 355476324179580947287061

theorem tailTrace_6230589 : CollatzResearch.WordTrace tailWord_6230589 prefixEnd_6230589 355476324179580947287061 := by
  unfold tailWord_6230589
  simp only [CollatzResearch.WordTrace]
  refine ⟨227248250024647627728990821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151498833349765085152660547 227248250024647627728990821)
  ·
    refine ⟨42609046879621430199185779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 227248250024647627728990821 42609046879621430199185779)
    ·
      refine ⟨63913570319432145298778669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42609046879621430199185779 63913570319432145298778669)
      ·
        refine ⟨23967588869787054487042001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63913570319432145298778669 23967588869787054487042001)
        ·
          refine ⟨17975691652340290865281501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23967588869787054487042001 17975691652340290865281501)
          ·
            refine ⟨6740884369627609074480563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17975691652340290865281501 6740884369627609074480563)
            ·
              refine ⟨10111326554441413611720845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6740884369627609074480563 10111326554441413611720845)
              ·
                refine ⟨3791747457915530104395317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10111326554441413611720845 3791747457915530104395317)
                ·
                  refine ⟨355476324179580947287061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3791747457915530104395317 355476324179580947287061)
                  ·
                    rfl

theorem cell23_6230589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 3, 1, 3, 5].length) (baseStart_6230589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6230589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6230589 prefixEnd_6230589 := by exact prefixLift 6230589
  have htrace : WordTrace (prefixWord ++ tailWord_6230589) baseStart_6230589 baseEnd_6230589 := by
    simpa [prefixWord, tailWord_6230589, baseEnd_6230589] using wordTrace_append hprefix tailTrace_6230589
  have hstable : (prefixWord ++ tailWord_6230589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6230589).length < 2 ^ (prefixWord ++ tailWord_6230589).sum := by decide
  have hdescent : baseEnd_6230589 < baseStart_6230589 := by decide
  rcases family_descends (prefixWord ++ tailWord_6230589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6230608 : List Nat := [2, 1, 1, 1, 1, 3, 2, 1, 1, 5, 5]
def baseStart_6230608 : Nat := 118140960795 + 6230608 * 2 ^ 59
def prefixEnd_6230608 : Nat := 4983230072969 + 3 ^ 40 * 6230608 * 2
def baseEnd_6230608 : Nat := 3199296673748663951245961

theorem tailTrace_6230608 : CollatzResearch.WordTrace tailWord_6230608 prefixEnd_6230608 3199296673748663951245961 := by
  unfold tailWord_6230608
  simp only [CollatzResearch.WordTrace]
  refine ⟨113624471505789396986966239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151499295341052529315954985 113624471505789396986966239)
  ·
    refine ⟨170436707258684095480449359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113624471505789396986966239 170436707258684095480449359)
    ·
      refine ⟨255655060888026143220674039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170436707258684095480449359 255655060888026143220674039)
      ·
        refine ⟨383482591332039214831011059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 255655060888026143220674039 383482591332039214831011059)
        ·
          refine ⟨575223886998058822246516589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 383482591332039214831011059 575223886998058822246516589)
          ·
            refine ⟨215708957624272058342443721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 575223886998058822246516589 215708957624272058342443721)
            ·
              refine ⟨161781718218204043756832791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 215708957624272058342443721 161781718218204043756832791)
              ·
                refine ⟨242672577327306065635249187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 161781718218204043756832791 242672577327306065635249187)
                ·
                  refine ⟨364008865990959098452873781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 242672577327306065635249187 364008865990959098452873781)
                  ·
                    refine ⟨34125831186652415479956917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 364008865990959098452873781 34125831186652415479956917)
                    ·
                      refine ⟨3199296673748663951245961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34125831186652415479956917 3199296673748663951245961)
                      ·
                        rfl

theorem cell23_6230608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 1, 1, 5, 5].length) (baseStart_6230608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6230608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6230608 prefixEnd_6230608 := by exact prefixLift 6230608
  have htrace : WordTrace (prefixWord ++ tailWord_6230608) baseStart_6230608 baseEnd_6230608 := by
    simpa [prefixWord, tailWord_6230608, baseEnd_6230608] using wordTrace_append hprefix tailTrace_6230608
  have hstable : (prefixWord ++ tailWord_6230608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6230608).length < 2 ^ (prefixWord ++ tailWord_6230608).sum := by decide
  have hdescent : baseEnd_6230608 < baseStart_6230608 := by decide
  rcases family_descends (prefixWord ++ tailWord_6230608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6230666 : List Nat := [3, 1, 2, 3, 3, 1, 1, 4, 1, 4]
def baseStart_6230666 : Nat := 118140960795 + 6230666 * 2 ^ 59
def prefixEnd_6230666 : Nat := 4983230072969 + 3 ^ 40 * 6230666 * 2
def baseEnd_6230666 : Nat := 1066442151875541574773565

theorem tailTrace_6230666 : CollatzResearch.WordTrace tailWord_6230666 prefixEnd_6230666 1066442151875541574773565 := by
  unfold tailWord_6230666
  simp only [CollatzResearch.WordTrace]
  refine ⟨56812764611342167469885963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151500705630245779919695901 56812764611342167469885963)
  ·
    refine ⟨85219146917013251204828945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56812764611342167469885963 85219146917013251204828945)
    ·
      refine ⟨63914360187759938403621709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85219146917013251204828945 63914360187759938403621709)
      ·
        refine ⟨23967885070409976901358141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63914360187759938403621709 23967885070409976901358141)
        ·
          refine ⟨8987956901403741338009303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23967885070409976901358141 8987956901403741338009303)
          ·
            refine ⟨13481935352105612007013955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8987956901403741338009303 13481935352105612007013955)
            ·
              refine ⟨20222903028158418010520933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13481935352105612007013955 20222903028158418010520933)
              ·
                refine ⟨3791794317779703376972675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20222903028158418010520933 3791794317779703376972675)
                ·
                  refine ⟨5687691476669555065459013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3791794317779703376972675 5687691476669555065459013)
                  ·
                    refine ⟨1066442151875541574773565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5687691476669555065459013 1066442151875541574773565)
                    ·
                      rfl

theorem cell23_6230666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 1, 4, 1, 4].length) (baseStart_6230666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6230666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6230666 prefixEnd_6230666 := by exact prefixLift 6230666
  have htrace : WordTrace (prefixWord ++ tailWord_6230666) baseStart_6230666 baseEnd_6230666 := by
    simpa [prefixWord, tailWord_6230666, baseEnd_6230666] using wordTrace_append hprefix tailTrace_6230666
  have hstable : (prefixWord ++ tailWord_6230666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6230666).length < 2 ^ (prefixWord ++ tailWord_6230666).sum := by decide
  have hdescent : baseEnd_6230666 < baseStart_6230666 := by decide
  rcases family_descends (prefixWord ++ tailWord_6230666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6230692 : List Nat := [2, 3, 1, 2, 2, 1, 2, 4, 1, 5]
def baseStart_6230692 : Nat := 118140960795 + 6230692 * 2 ^ 59
def prefixEnd_6230692 : Nat := 4983230072969 + 3 ^ 40 * 6230692 * 2
def baseEnd_6230692 : Nat := 1066446602041213874198525

theorem tailTrace_6230692 : CollatzResearch.WordTrace tailWord_6230692 prefixEnd_6230692 1066446602041213874198525 := by
  unfold tailWord_6230692
  simp only [CollatzResearch.WordTrace]
  refine ⟨113626003371637238159995165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151501337828849650879993553 113626003371637238159995165)
  ·
    refine ⟨42609751264363964309998187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113626003371637238159995165 42609751264363964309998187)
    ·
      refine ⟨63914626896545946464997281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42609751264363964309998187 63914626896545946464997281)
      ·
        refine ⟨47935970172409459848747961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63914626896545946464997281 47935970172409459848747961)
        ·
          refine ⟨35951977629307094886560971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47935970172409459848747961 35951977629307094886560971)
          ·
            refine ⟨53927966443960642329841457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35951977629307094886560971 53927966443960642329841457)
            ·
              refine ⟨40445974832970481747381093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53927966443960642329841457 40445974832970481747381093)
              ·
                refine ⟨7583620281181965327633955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40445974832970481747381093 7583620281181965327633955)
                ·
                  refine ⟨11375430421772947991450933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7583620281181965327633955 11375430421772947991450933)
                  ·
                    refine ⟨1066446602041213874198525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11375430421772947991450933 1066446602041213874198525)
                    ·
                      rfl

theorem cell23_6230692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 2, 4, 1, 5].length) (baseStart_6230692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6230692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6230692 prefixEnd_6230692 := by exact prefixLift 6230692
  have htrace : WordTrace (prefixWord ++ tailWord_6230692) baseStart_6230692 baseEnd_6230692 := by
    simpa [prefixWord, tailWord_6230692, baseEnd_6230692] using wordTrace_append hprefix tailTrace_6230692
  have hstable : (prefixWord ++ tailWord_6230692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6230692).length < 2 ^ (prefixWord ++ tailWord_6230692).sum := by decide
  have hdescent : baseEnd_6230692 < baseStart_6230692 := by decide
  rcases family_descends (prefixWord ++ tailWord_6230692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6230709 : List Nat := [1, 3, 3, 3, 1, 2, 1, 3, 1, 5]
def baseStart_6230709 : Nat := 118140960795 + 6230709 * 2 ^ 59
def prefixEnd_6230709 : Nat := 4983230072969 + 3 ^ 40 * 6230709 * 2
def baseEnd_6230709 : Nat := 1066449511764922685360999

theorem tailTrace_6230709 : CollatzResearch.WordTrace tailWord_6230709 prefixEnd_6230709 1066449511764922685360999 := by
  unfold tailWord_6230709
  simp only [CollatzResearch.WordTrace]
  refine ⟨227252626784212888223359181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151501751189475258815572787 227252626784212888223359181)
  ·
    refine ⟨85219735044079833083759693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 227252626784212888223359181 85219735044079833083759693)
    ·
      refine ⟨31957400641529937406409885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85219735044079833083759693 31957400641529937406409885)
      ·
        refine ⟨11984025240573726527403707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31957400641529937406409885 11984025240573726527403707)
        ·
          refine ⟨17976037860860589791105561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11984025240573726527403707 17976037860860589791105561)
          ·
            refine ⟨13482028395645442343329171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17976037860860589791105561 13482028395645442343329171)
            ·
              refine ⟨20223042593468163514993757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13482028395645442343329171 20223042593468163514993757)
              ·
                refine ⟨7583640972550561318122659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20223042593468163514993757 7583640972550561318122659)
                ·
                  refine ⟨11375461458825841977183989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7583640972550561318122659 11375461458825841977183989)
                  ·
                    refine ⟨1066449511764922685360999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11375461458825841977183989 1066449511764922685360999)
                    ·
                      rfl

theorem cell23_6230709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 1, 3, 1, 5].length) (baseStart_6230709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6230709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6230709 prefixEnd_6230709 := by exact prefixLift 6230709
  have htrace : WordTrace (prefixWord ++ tailWord_6230709) baseStart_6230709 baseEnd_6230709 := by
    simpa [prefixWord, tailWord_6230709, baseEnd_6230709] using wordTrace_append hprefix tailTrace_6230709
  have hstable : (prefixWord ++ tailWord_6230709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6230709).length < 2 ^ (prefixWord ++ tailWord_6230709).sum := by decide
  have hdescent : baseEnd_6230709 < baseStart_6230709 := by decide
  rcases family_descends (prefixWord ++ tailWord_6230709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6230732 : List Nat := [2, 2, 1, 5, 1, 1, 1, 1, 3, 1, 5]
def baseStart_6230732 : Nat := 118140960795 + 6230732 * 2 ^ 59
def prefixEnd_6230732 : Nat := 4983230072969 + 3 ^ 40 * 6230732 * 2
def baseEnd_6230732 : Nat := 3199360345349821466095391

theorem tailTrace_6230732 : CollatzResearch.WordTrace tailWord_6230732 prefixEnd_6230732 3199360345349821466095391 := by
  unfold tailWord_6230732
  simp only [CollatzResearch.WordTrace]
  refine ⟨113626732831564781575723225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151502310442086375434297633 113626732831564781575723225)
  ·
    refine ⟨85220049623673586181792419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113626732831564781575723225 85220049623673586181792419)
    ·
      refine ⟨127830074435510379272688629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85220049623673586181792419 127830074435510379272688629)
      ·
        refine ⟨11984069478329098056814559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 127830074435510379272688629 11984069478329098056814559)
        ·
          refine ⟨17976104217493647085221839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11984069478329098056814559 17976104217493647085221839)
          ·
            refine ⟨26964156326240470627832759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17976104217493647085221839 26964156326240470627832759)
            ·
              refine ⟨40446234489360705941749139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26964156326240470627832759 40446234489360705941749139)
              ·
                refine ⟨60669351734041058912623709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40446234489360705941749139 60669351734041058912623709)
                ·
                  refine ⟨22751006900265397092233891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 60669351734041058912623709 22751006900265397092233891)
                  ·
                    refine ⟨34126510350398095638350837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22751006900265397092233891 34126510350398095638350837)
                    ·
                      refine ⟨3199360345349821466095391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34126510350398095638350837 3199360345349821466095391)
                      ·
                        rfl

theorem cell23_6230732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 1, 1, 3, 1, 5].length) (baseStart_6230732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6230732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6230732 prefixEnd_6230732 := by exact prefixLift 6230732
  have htrace : WordTrace (prefixWord ++ tailWord_6230732) baseStart_6230732 baseEnd_6230732 := by
    simpa [prefixWord, tailWord_6230732, baseEnd_6230732] using wordTrace_append hprefix tailTrace_6230732
  have hstable : (prefixWord ++ tailWord_6230732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6230732).length < 2 ^ (prefixWord ++ tailWord_6230732).sum := by decide
  have hdescent : baseEnd_6230732 < baseStart_6230732 := by decide
  rcases family_descends (prefixWord ++ tailWord_6230732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6230762 : List Nat := [3, 1, 3, 1, 1, 1, 1, 3, 3, 3, 3]
def baseStart_6230762 : Nat := 118140960795 + 6230762 * 2 ^ 59
def prefixEnd_6230762 : Nat := 4983230072969 + 3 ^ 40 * 6230762 * 2
def baseEnd_6230762 : Nat := 3199375749769456348720253

theorem tailTrace_6230762 : CollatzResearch.WordTrace tailWord_6230762 prefixEnd_6230762 3199375749769456348720253 := by
  unfold tailWord_6230762
  simp only [CollatzResearch.WordTrace]
  refine ⟨56813639963255219568759635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151503039902013918850025693 56813639963255219568759635)
  ·
    refine ⟨85220459944882829353139453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56813639963255219568759635 85220459944882829353139453)
    ·
      refine ⟨31957672479331061007427295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85220459944882829353139453 31957672479331061007427295)
      ·
        refine ⟨47936508718996591511140943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31957672479331061007427295 47936508718996591511140943)
        ·
          refine ⟨71904763078494887266711415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47936508718996591511140943 71904763078494887266711415)
          ·
            refine ⟨107857144617742330900067123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71904763078494887266711415 107857144617742330900067123)
            ·
              refine ⟨161785716926613496350100685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 107857144617742330900067123 161785716926613496350100685)
              ·
                refine ⟨60669643847480061131287757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 161785716926613496350100685 60669643847480061131287757)
                ·
                  refine ⟨22751116442805022924232909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 60669643847480061131287757 22751116442805022924232909)
                  ·
                    refine ⟨8531668666051883596587341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22751116442805022924232909 8531668666051883596587341)
                    ·
                      refine ⟨3199375749769456348720253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8531668666051883596587341 3199375749769456348720253)
                      ·
                        rfl

theorem cell23_6230762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 3, 3, 3, 3].length) (baseStart_6230762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6230762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6230762 prefixEnd_6230762 := by exact prefixLift 6230762
  have htrace : WordTrace (prefixWord ++ tailWord_6230762) baseStart_6230762 baseEnd_6230762 := by
    simpa [prefixWord, tailWord_6230762, baseEnd_6230762] using wordTrace_append hprefix tailTrace_6230762
  have hstable : (prefixWord ++ tailWord_6230762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6230762).length < 2 ^ (prefixWord ++ tailWord_6230762).sum := by decide
  have hdescent : baseEnd_6230762 < baseStart_6230762 := by decide
  rcases family_descends (prefixWord ++ tailWord_6230762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6230775 : List Nat := [1, 1, 3, 1, 1, 1, 3, 1, 4, 2, 5]
def baseStart_6230775 : Nat := 118140960795 + 6230775 * 2 ^ 59
def prefixEnd_6230775 : Nat := 4983230072969 + 3 ^ 40 * 6230775 * 2
def baseEnd_6230775 : Nat := 3199382425017964797857693

theorem tailTrace_6230775 : CollatzResearch.WordTrace tailWord_6230775 prefixEnd_6230775 3199382425017964797857693 := by
  unfold tailWord_6230775
  simp only [CollatzResearch.WordTrace]
  refine ⟨227255034001973781495261779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151503356001315854330174519 227255034001973781495261779)
  ·
    refine ⟨340882551002960672242892669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227255034001973781495261779 340882551002960672242892669)
    ·
      refine ⟨127830956626110252091084751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 340882551002960672242892669 127830956626110252091084751)
      ·
        refine ⟨191746434939165378136627127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127830956626110252091084751 191746434939165378136627127)
        ·
          refine ⟨287619652408748067204940691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 191746434939165378136627127 287619652408748067204940691)
          ·
            refine ⟨431429478613122100807411037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 287619652408748067204940691 431429478613122100807411037)
            ·
              refine ⟨161786054479920787802779139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 431429478613122100807411037 161786054479920787802779139)
              ·
                refine ⟨242679081719881181704168709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 161786054479920787802779139 242679081719881181704168709)
                ·
                  refine ⟨45502327822477721569531633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 242679081719881181704168709 45502327822477721569531633)
                  ·
                    refine ⟨34126745866858291177148725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 45502327822477721569531633 34126745866858291177148725)
                    ·
                      refine ⟨3199382425017964797857693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34126745866858291177148725 3199382425017964797857693)
                      ·
                        rfl

theorem cell23_6230775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 1, 4, 2, 5].length) (baseStart_6230775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6230775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6230775 prefixEnd_6230775 := by exact prefixLift 6230775
  have htrace : WordTrace (prefixWord ++ tailWord_6230775) baseStart_6230775 baseEnd_6230775 := by
    simpa [prefixWord, tailWord_6230775, baseEnd_6230775] using wordTrace_append hprefix tailTrace_6230775
  have hstable : (prefixWord ++ tailWord_6230775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6230775).length < 2 ^ (prefixWord ++ tailWord_6230775).sum := by decide
  have hdescent : baseEnd_6230775 < baseStart_6230775 := by decide
  rcases family_descends (prefixWord ++ tailWord_6230775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6230780 : List Nat := [2, 2, 2, 1, 3, 3, 3, 2, 1, 2, 2]
def baseStart_6230780 : Nat := 118140960795 + 6230780 * 2 ^ 59
def prefixEnd_6230780 : Nat := 4983230072969 + 3 ^ 40 * 6230780 * 2
def baseEnd_6230780 : Nat := 3199384992421237278295171

theorem tailTrace_6230780 : CollatzResearch.WordTrace tailWord_6230780 prefixEnd_6230780 3199384992421237278295171 := by
  unfold tailWord_6230780
  simp only [CollatzResearch.WordTrace]
  refine ⟨113627608183477833674596897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151503477577970444899462529 113627608183477833674596897)
  ·
    refine ⟨85220706137608375255947673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113627608183477833674596897 85220706137608375255947673)
    ·
      refine ⟨63915529603206281441960755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85220706137608375255947673 63915529603206281441960755)
      ·
        refine ⟨95873294404809422162941133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63915529603206281441960755 95873294404809422162941133)
        ·
          refine ⟨35952485401803533311102925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 95873294404809422162941133 35952485401803533311102925)
          ·
            refine ⟨13482182025676324991663597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35952485401803533311102925 13482182025676324991663597)
            ·
              refine ⟨5055818259628621871873849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13482182025676324991663597 5055818259628621871873849)
              ·
                refine ⟨3791863694721466403905387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5055818259628621871873849 3791863694721466403905387)
                ·
                  refine ⟨5687795542082199605858081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3791863694721466403905387 5687795542082199605858081)
                  ·
                    refine ⟨4265846656561649704393561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5687795542082199605858081 4265846656561649704393561)
                    ·
                      refine ⟨3199384992421237278295171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4265846656561649704393561 3199384992421237278295171)
                      ·
                        rfl

theorem cell23_6230780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 3, 2, 1, 2, 2].length) (baseStart_6230780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6230780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6230780 prefixEnd_6230780 := by exact prefixLift 6230780
  have htrace : WordTrace (prefixWord ++ tailWord_6230780) baseStart_6230780 baseEnd_6230780 := by
    simpa [prefixWord, tailWord_6230780, baseEnd_6230780] using wordTrace_append hprefix tailTrace_6230780
  have hstable : (prefixWord ++ tailWord_6230780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6230780).length < 2 ^ (prefixWord ++ tailWord_6230780).sum := by decide
  have hdescent : baseEnd_6230780 < baseStart_6230780 := by decide
  rcases family_descends (prefixWord ++ tailWord_6230780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6230795 : List Nat := [1, 1, 1, 1, 5, 1, 1, 3, 1, 8]
def baseStart_6230795 : Nat := 118140960795 + 6230795 * 2 ^ 59
def prefixEnd_6230795 : Nat := 4983230072969 + 3 ^ 40 * 6230795 * 2
def baseEnd_6230795 : Nat := 1066464231543684906535867

theorem tailTrace_6230795 : CollatzResearch.WordTrace tailWord_6230795 prefixEnd_6230795 1066464231543684906535867 := by
  unfold tailWord_6230795
  simp only [CollatzResearch.WordTrace]
  refine ⟨227255763461901324910989839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151503842307934216607326559 227255763461901324910989839)
  ·
    refine ⟨340883645192851987366484759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227255763461901324910989839 340883645192851987366484759)
    ·
      refine ⟨511325467789277981049727139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 340883645192851987366484759 511325467789277981049727139)
      ·
        refine ⟨766988201683916971574590709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 511325467789277981049727139 766988201683916971574590709)
        ·
          refine ⟨71905143907867216085117879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 766988201683916971574590709 71905143907867216085117879)
          ·
            refine ⟨107857715861800824127676819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71905143907867216085117879 107857715861800824127676819)
            ·
              refine ⟨161786573792701236191515229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 107857715861800824127676819 161786573792701236191515229)
              ·
                refine ⟨60669965172262963571818211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 161786573792701236191515229 60669965172262963571818211)
                ·
                  refine ⟨91004947758394445357727317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 60669965172262963571818211 91004947758394445357727317)
                  ·
                    refine ⟨1066464231543684906535867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 91004947758394445357727317 1066464231543684906535867)
                    ·
                      rfl

theorem cell23_6230795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 3, 1, 8].length) (baseStart_6230795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6230795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6230795 prefixEnd_6230795 := by exact prefixLift 6230795
  have htrace : WordTrace (prefixWord ++ tailWord_6230795) baseStart_6230795 baseEnd_6230795 := by
    simpa [prefixWord, tailWord_6230795, baseEnd_6230795] using wordTrace_append hprefix tailTrace_6230795
  have hstable : (prefixWord ++ tailWord_6230795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6230795).length < 2 ^ (prefixWord ++ tailWord_6230795).sum := by decide
  have hdescent : baseEnd_6230795 < baseStart_6230795 := by decide
  rcases family_descends (prefixWord ++ tailWord_6230795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6230825 : List Nat := [1, 2, 1, 1, 1, 1, 1, 6, 9]
def baseStart_6230825 : Nat := 118140960795 + 6230825 * 2 ^ 59
def prefixEnd_6230825 : Nat := 4983230072969 + 3 ^ 40 * 6230825 * 2
def baseEnd_6230825 : Nat := 355489788783409955803607

theorem tailTrace_6230825 : CollatzResearch.WordTrace tailWord_6230825 prefixEnd_6230825 355489788783409955803607 := by
  unfold tailWord_6230825
  simp only [CollatzResearch.WordTrace]
  refine ⟨227256857651792640034581929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151504571767861760023054619 227256857651792640034581929)
  ·
    refine ⟨170442643238844480025936447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 227256857651792640034581929 170442643238844480025936447)
    ·
      refine ⟨255663964858266720038904671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170442643238844480025936447 255663964858266720038904671)
      ·
        refine ⟨383495947287400080058357007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 255663964858266720038904671 383495947287400080058357007)
        ·
          refine ⟨575243920931100120087535511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 383495947287400080058357007 575243920931100120087535511)
          ·
            refine ⟨862865881396650180131303267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 575243920931100120087535511 862865881396650180131303267)
            ·
              refine ⟨1294298822094975270196954901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 862865881396650180131303267 1294298822094975270196954901)
              ·
                refine ⟨60670257285701965790482261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1294298822094975270196954901 60670257285701965790482261)
                ·
                  refine ⟨355489788783409955803607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 60670257285701965790482261 355489788783409955803607)
                  ·
                    rfl

theorem cell23_6230825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 6, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 6, 9].length) (baseStart_6230825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6230825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6230825 prefixEnd_6230825 := by exact prefixLift 6230825
  have htrace : WordTrace (prefixWord ++ tailWord_6230825) baseStart_6230825 baseEnd_6230825 := by
    simpa [prefixWord, tailWord_6230825, baseEnd_6230825] using wordTrace_append hprefix tailTrace_6230825
  have hstable : (prefixWord ++ tailWord_6230825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6230825).length < 2 ^ (prefixWord ++ tailWord_6230825).sum := by decide
  have hdescent : baseEnd_6230825 < baseStart_6230825 := by decide
  rcases family_descends (prefixWord ++ tailWord_6230825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6230876 : List Nat := [2, 2, 4, 2, 1, 1, 1, 5, 5]
def baseStart_6230876 : Nat := 118140960795 + 6230876 * 2 ^ 59
def prefixEnd_6230876 : Nat := 4983230072969 + 3 ^ 40 * 6230876 * 2
def baseEnd_6230876 : Nat := 355492698507118766966081

theorem tailTrace_6230876 : CollatzResearch.WordTrace tailWord_6230876 prefixEnd_6230876 355492698507118766966081 := by
  unfold tailWord_6230876
  simp only [CollatzResearch.WordTrace]
  refine ⟨113629358887303937872344241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151505811849738583829792321 113629358887303937872344241)
  ·
    refine ⟨85222019165477953404258181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113629358887303937872344241 85222019165477953404258181)
    ·
      refine ⟨15979128593527116263298409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 85222019165477953404258181 15979128593527116263298409)
      ·
        refine ⟨11984346445145337197473807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15979128593527116263298409 11984346445145337197473807)
        ·
          refine ⟨17976519667718005796210711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11984346445145337197473807 17976519667718005796210711)
          ·
            refine ⟨26964779501577008694316067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17976519667718005796210711 26964779501577008694316067)
            ·
              refine ⟨40447169252365513041474101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26964779501577008694316067 40447169252365513041474101)
              ·
                refine ⟨3791922117409266847638197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 40447169252365513041474101 3791922117409266847638197)
                ·
                  refine ⟨355492698507118766966081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3791922117409266847638197 355492698507118766966081)
                  ·
                    rfl

theorem cell23_6230876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 1, 5, 5].length) (baseStart_6230876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6230876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6230876 prefixEnd_6230876 := by exact prefixLift 6230876
  have htrace : WordTrace (prefixWord ++ tailWord_6230876) baseStart_6230876 baseEnd_6230876 := by
    simpa [prefixWord, tailWord_6230876, baseEnd_6230876] using wordTrace_append hprefix tailTrace_6230876
  have hstable : (prefixWord ++ tailWord_6230876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6230876).length < 2 ^ (prefixWord ++ tailWord_6230876).sum := by decide
  have hdescent : baseEnd_6230876 < baseStart_6230876 := by decide
  rcases family_descends (prefixWord ++ tailWord_6230876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6230929 : List Nat := [1, 2, 2, 1, 1, 1, 3, 5, 2, 2, 3]
def baseStart_6230929 : Nat := 118140960795 + 6230929 * 2 ^ 59
def prefixEnd_6230929 : Nat := 4983230072969 + 3 ^ 40 * 6230929 * 2
def baseEnd_6230929 : Nat := 3199461501038757195331985

theorem tailTrace_6230929 : CollatzResearch.WordTrace tailWord_6230929 prefixEnd_6230929 3199461501038757195331985 := by
  unfold tailWord_6230929
  simp only [CollatzResearch.WordTrace]
  refine ⟨227260650843415865796367841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151507100562277243864245227 227260650843415865796367841)
  ·
    refine ⟨170445488132561899347275881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 227260650843415865796367841 170445488132561899347275881)
    ·
      refine ⟨127834116099421424510456911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 170445488132561899347275881 127834116099421424510456911)
      ·
        refine ⟨191751174149132136765685367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127834116099421424510456911 191751174149132136765685367)
        ·
          refine ⟨287626761223698205148528051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 191751174149132136765685367 287626761223698205148528051)
          ·
            refine ⟨431440141835547307722792077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 287626761223698205148528051 431440141835547307722792077)
            ·
              refine ⟨161790053188330240396047029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 431440141835547307722792077 161790053188330240396047029)
              ·
                refine ⟨15167817486405960037129409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 161790053188330240396047029 15167817486405960037129409)
                ·
                  refine ⟨11375863114804470027847057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15167817486405960037129409 11375863114804470027847057)
                  ·
                    refine ⟨8531897336103352520885293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11375863114804470027847057 8531897336103352520885293)
                    ·
                      refine ⟨3199461501038757195331985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8531897336103352520885293 3199461501038757195331985)
                      ·
                        rfl

theorem cell23_6230929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 2, 3].length) (baseStart_6230929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6230929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6230929 prefixEnd_6230929 := by exact prefixLift 6230929
  have htrace : WordTrace (prefixWord ++ tailWord_6230929) baseStart_6230929 baseEnd_6230929 := by
    simpa [prefixWord, tailWord_6230929, baseEnd_6230929] using wordTrace_append hprefix tailTrace_6230929
  have hstable : (prefixWord ++ tailWord_6230929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6230929).length < 2 ^ (prefixWord ++ tailWord_6230929).sum := by decide
  have hdescent : baseEnd_6230929 < baseStart_6230929 := by decide
  rcases family_descends (prefixWord ++ tailWord_6230929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6230946 : List Nat := [3, 3, 1, 2, 2, 1, 1, 1, 4, 2, 3]
def baseStart_6230946 : Nat := 118140960795 + 6230946 * 2 ^ 59
def prefixEnd_6230946 : Nat := 4983230072969 + 3 ^ 40 * 6230946 * 2
def baseEnd_6230946 : Nat := 3199470230209883628819407

theorem tailTrace_6230946 : CollatzResearch.WordTrace tailWord_6230946 prefixEnd_6230946 3199470230209883628819407 := by
  unfold tailWord_6230946
  simp only [CollatzResearch.WordTrace]
  refine ⟨56815317721088569424934173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151507513922902851799824461 56815317721088569424934173)
  ·
    refine ⟨21305744145408213534350315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56815317721088569424934173 21305744145408213534350315)
    ·
      refine ⟨31958616218112320301525473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21305744145408213534350315 31958616218112320301525473)
      ·
        refine ⟨23968962163584240226144105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31958616218112320301525473 23968962163584240226144105)
        ·
          refine ⟨17976721622688180169608079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23968962163584240226144105 17976721622688180169608079)
          ·
            refine ⟨26965082434032270254412119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17976721622688180169608079 26965082434032270254412119)
            ·
              refine ⟨40447623651048405381618179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26965082434032270254412119 40447623651048405381618179)
              ·
                refine ⟨60671435476572608072427269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40447623651048405381618179 60671435476572608072427269)
                ·
                  refine ⟨11375894151857364013580113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 60671435476572608072427269 11375894151857364013580113)
                  ·
                    refine ⟨8531920613893023010185085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11375894151857364013580113 8531920613893023010185085)
                    ·
                      refine ⟨3199470230209883628819407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8531920613893023010185085 3199470230209883628819407)
                      ·
                        rfl

theorem cell23_6230946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 1, 1, 4, 2, 3].length) (baseStart_6230946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6230946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6230946 prefixEnd_6230946 := by exact prefixLift 6230946
  have htrace : WordTrace (prefixWord ++ tailWord_6230946) baseStart_6230946 baseEnd_6230946 := by
    simpa [prefixWord, tailWord_6230946, baseEnd_6230946] using wordTrace_append hprefix tailTrace_6230946
  have hstable : (prefixWord ++ tailWord_6230946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6230946).length < 2 ^ (prefixWord ++ tailWord_6230946).sum := by decide
  have hdescent : baseEnd_6230946 < baseStart_6230946 := by decide
  rcases family_descends (prefixWord ++ tailWord_6230946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6230953 : List Nat := [1, 2, 1, 1, 1, 1, 9, 2, 1, 4]
def baseStart_6230953 : Nat := 118140960795 + 6230953 * 2 ^ 59
def prefixEnd_6230953 : Nat := 4983230072969 + 3 ^ 40 * 6230953 * 2
def baseEnd_6230953 : Nat := 1066491274858155033810625

theorem tailTrace_6230953 : CollatzResearch.WordTrace tailWord_6230953 prefixEnd_6230953 1066491274858155033810625 := by
  unfold tailWord_6230953
  simp only [CollatzResearch.WordTrace]
  refine ⟨227261526195328917895241513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151507684130219278596827675 227261526195328917895241513)
  ·
    refine ⟨170446144646496688421431135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 227261526195328917895241513 170446144646496688421431135)
    ·
      refine ⟨255669216969745032632146703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170446144646496688421431135 255669216969745032632146703)
      ·
        refine ⟨383503825454617548948220055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 255669216969745032632146703 383503825454617548948220055)
        ·
          refine ⟨575255738181926323422330083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 383503825454617548948220055 575255738181926323422330083)
          ·
            refine ⟨862883607272889485133495125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 575255738181926323422330083 862883607272889485133495125)
            ·
              refine ⟨5055958636364586826954073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 862883607272889485133495125 5055958636364586826954073)
              ·
                refine ⟨3791968977273440120215555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5055958636364586826954073 3791968977273440120215555)
                ·
                  refine ⟨5687953465910160180323333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3791968977273440120215555 5687953465910160180323333)
                  ·
                    refine ⟨1066491274858155033810625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5687953465910160180323333 1066491274858155033810625)
                    ·
                      rfl

theorem cell23_6230953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 9, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 9, 2, 1, 4].length) (baseStart_6230953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6230953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6230953 prefixEnd_6230953 := by exact prefixLift 6230953
  have htrace : WordTrace (prefixWord ++ tailWord_6230953) baseStart_6230953 baseEnd_6230953 := by
    simpa [prefixWord, tailWord_6230953, baseEnd_6230953] using wordTrace_append hprefix tailTrace_6230953
  have hstable : (prefixWord ++ tailWord_6230953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6230953).length < 2 ^ (prefixWord ++ tailWord_6230953).sum := by decide
  have hdescent : baseEnd_6230953 < baseStart_6230953 := by decide
  rcases family_descends (prefixWord ++ tailWord_6230953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6230962 : List Nat := [3, 2, 1, 1, 1, 1, 1, 1, 1, 11]
def baseStart_6230962 : Nat := 118140960795 + 6230962 * 2 ^ 59
def prefixEnd_6230962 : Nat := 4983230072969 + 3 ^ 40 * 6230962 * 2
def baseEnd_6230962 : Nat := 1066492815300118522073111

theorem tailTrace_6230962 : CollatzResearch.WordTrace tailWord_6230962 prefixEnd_6230962 1066492815300118522073111 := by
  unfold tailWord_6230962
  simp only [CollatzResearch.WordTrace]
  refine ⟨56815463613074078108079785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151507902968197541621546093 56815463613074078108079785)
  ·
    refine ⟨42611597709805558581059839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56815463613074078108079785 42611597709805558581059839)
    ·
      refine ⟨63917396564708337871589759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42611597709805558581059839 63917396564708337871589759)
      ·
        refine ⟨95876094847062506807384639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63917396564708337871589759 95876094847062506807384639)
        ·
          refine ⟨143814142270593760211076959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95876094847062506807384639 143814142270593760211076959)
          ·
            refine ⟨215721213405890640316615439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 143814142270593760211076959 215721213405890640316615439)
            ·
              refine ⟨323581820108835960474923159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 215721213405890640316615439 323581820108835960474923159)
              ·
                refine ⟨485372730163253940712384739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 323581820108835960474923159 485372730163253940712384739)
                ·
                  refine ⟨728059095244880911068577109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 485372730163253940712384739 728059095244880911068577109)
                  ·
                    refine ⟨1066492815300118522073111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 11 728059095244880911068577109 1066492815300118522073111)
                    ·
                      rfl

theorem cell23_6230962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 1, 1, 11].length) (baseStart_6230962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6230962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6230962 prefixEnd_6230962 := by exact prefixLift 6230962
  have htrace : WordTrace (prefixWord ++ tailWord_6230962) baseStart_6230962 baseEnd_6230962 := by
    simpa [prefixWord, tailWord_6230962, baseEnd_6230962] using wordTrace_append hprefix tailTrace_6230962
  have hstable : (prefixWord ++ tailWord_6230962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6230962).length < 2 ^ (prefixWord ++ tailWord_6230962).sum := by decide
  have hdescent : baseEnd_6230962 < baseStart_6230962 := by decide
  rcases family_descends (prefixWord ++ tailWord_6230962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6230980 : List Nat := [2, 3, 3, 3, 1, 1, 2, 1, 2, 2, 3]
def baseStart_6230980 : Nat := 118140960795 + 6230980 * 2 ^ 59
def prefixEnd_6230980 : Nat := 4983230072969 + 3 ^ 40 * 6230980 * 2
def baseEnd_6230980 : Nat := 3199487688552136495794251

theorem tailTrace_6230980 : CollatzResearch.WordTrace tailWord_6230980 prefixEnd_6230980 3199487688552136495794251 := by
  unfold tailWord_6230980
  simp only [CollatzResearch.WordTrace]
  refine ⟨113631255483115550753237197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151508340644154067670982929 113631255483115550753237197)
  ·
    refine ⟨42611720806168331532463949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113631255483115550753237197 42611720806168331532463949)
    ·
      refine ⟨15979395302313124324673981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42611720806168331532463949 15979395302313124324673981)
      ·
        refine ⟨5992273238367421621752743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15979395302313124324673981 5992273238367421621752743)
        ·
          refine ⟨8988409857551132432629115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5992273238367421621752743 8988409857551132432629115)
          ·
            refine ⟨13482614786326698648943673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8988409857551132432629115 13482614786326698648943673)
            ·
              refine ⟨10111961089745023986707755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13482614786326698648943673 10111961089745023986707755)
              ·
                refine ⟨15167941634617535980061633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10111961089745023986707755 15167941634617535980061633)
                ·
                  refine ⟨11375956225963151985046225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15167941634617535980061633 11375956225963151985046225)
                  ·
                    refine ⟨8531967169472363988784669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11375956225963151985046225 8531967169472363988784669)
                    ·
                      refine ⟨3199487688552136495794251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8531967169472363988784669 3199487688552136495794251)
                      ·
                        rfl

theorem cell23_6230980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 2, 1, 2, 2, 3].length) (baseStart_6230980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6230980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6230980 prefixEnd_6230980 := by exact prefixLift 6230980
  have htrace : WordTrace (prefixWord ++ tailWord_6230980) baseStart_6230980 baseEnd_6230980 := by
    simpa [prefixWord, tailWord_6230980, baseEnd_6230980] using wordTrace_append hprefix tailTrace_6230980
  have hstable : (prefixWord ++ tailWord_6230980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6230980).length < 2 ^ (prefixWord ++ tailWord_6230980).sum := by decide
  have hdescent : baseEnd_6230980 < baseStart_6230980 := by decide
  rcases family_descends (prefixWord ++ tailWord_6230980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6230993 : List Nat := [1, 2, 2, 1, 2, 1, 4, 5, 1, 1, 3]
def baseStart_6230993 : Nat := 118140960795 + 6230993 * 2 ^ 59
def prefixEnd_6230993 : Nat := 4983230072969 + 3 ^ 40 * 6230993 * 2
def baseEnd_6230993 : Nat := 3199494363800644944931691

theorem tailTrace_6230993 : CollatzResearch.WordTrace tailWord_6230993 prefixEnd_6230993 3199494363800644944931691 := by
  unfold tailWord_6230993
  simp only [CollatzResearch.WordTrace]
  refine ⟨227262985115184004726697633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151508656743456003151131755 227262985115184004726697633)
  ·
    refine ⟨170447238836388003545023225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 227262985115184004726697633 170447238836388003545023225)
    ·
      refine ⟨127835429127291002658767419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 170447238836388003545023225 127835429127291002658767419)
      ·
        refine ⟨191753143690936503988151129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127835429127291002658767419 191753143690936503988151129)
        ·
          refine ⟨143814857768202377991113347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 191753143690936503988151129 143814857768202377991113347)
          ·
            refine ⟨215722286652303566986670021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 143814857768202377991113347 215722286652303566986670021)
            ·
              refine ⟨40447928747306918810000629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 215722286652303566986670021 40447928747306918810000629)
              ·
                refine ⟨3791993320060023638437559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 40447928747306918810000629 3791993320060023638437559)
                ·
                  refine ⟨5687989980090035457656339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3791993320060023638437559 5687989980090035457656339)
                  ·
                    refine ⟨8531984970135053186484509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5687989980090035457656339 8531984970135053186484509)
                    ·
                      refine ⟨3199494363800644944931691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8531984970135053186484509 3199494363800644944931691)
                      ·
                        rfl

theorem cell23_6230993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 4, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 4, 5, 1, 1, 3].length) (baseStart_6230993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6230993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6230993 prefixEnd_6230993 := by exact prefixLift 6230993
  have htrace : WordTrace (prefixWord ++ tailWord_6230993) baseStart_6230993 baseEnd_6230993 := by
    simpa [prefixWord, tailWord_6230993, baseEnd_6230993] using wordTrace_append hprefix tailTrace_6230993
  have hstable : (prefixWord ++ tailWord_6230993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6230993).length < 2 ^ (prefixWord ++ tailWord_6230993).sum := by decide
  have hdescent : baseEnd_6230993 < baseStart_6230993 := by decide
  rcases family_descends (prefixWord ++ tailWord_6230993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6231033 : List Nat := [1, 2, 1, 3, 1, 3, 3, 2, 3, 2, 2]
def baseStart_6231033 : Nat := 118140960795 + 6231033 * 2 ^ 59
def prefixEnd_6231033 : Nat := 4983230072969 + 3 ^ 40 * 6231033 * 2
def baseEnd_6231033 : Nat := 3199514903026824788431507

theorem tailTrace_6231033 : CollatzResearch.WordTrace tailWord_6231033 prefixEnd_6231033 3199514903026824788431507 := by
  unfold tailWord_6231033
  simp only [CollatzResearch.WordTrace]
  refine ⟨227264444035039091558153753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151509629356692727705435835 227264444035039091558153753)
  ·
    refine ⟨170448333026279318668615315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 227264444035039091558153753 170448333026279318668615315)
    ·
      refine ⟨255672499539418978002922973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170448333026279318668615315 255672499539418978002922973)
      ·
        refine ⟨95877187327282116751096115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 255672499539418978002922973 95877187327282116751096115)
        ·
          refine ⟨143815780990923175126644173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95877187327282116751096115 143815780990923175126644173)
          ·
            refine ⟨53930917871596190672491565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 143815780990923175126644173 53930917871596190672491565)
            ·
              refine ⟨20224094201848571502184337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53930917871596190672491565 20224094201848571502184337)
              ·
                refine ⟨15168070651386428626638253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20224094201848571502184337 15168070651386428626638253)
                ·
                  refine ⟨5688026494269910734989345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15168070651386428626638253 5688026494269910734989345)
                  ·
                    refine ⟨4266019870702433051242009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5688026494269910734989345 4266019870702433051242009)
                    ·
                      refine ⟨3199514903026824788431507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4266019870702433051242009 3199514903026824788431507)
                      ·
                        rfl

theorem cell23_6231033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 3, 2, 3, 2, 2].length) (baseStart_6231033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6231033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6231033 prefixEnd_6231033 := by exact prefixLift 6231033
  have htrace : WordTrace (prefixWord ++ tailWord_6231033) baseStart_6231033 baseEnd_6231033 := by
    simpa [prefixWord, tailWord_6231033, baseEnd_6231033] using wordTrace_append hprefix tailTrace_6231033
  have hstable : (prefixWord ++ tailWord_6231033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6231033).length < 2 ^ (prefixWord ++ tailWord_6231033).sum := by decide
  have hdescent : baseEnd_6231033 < baseStart_6231033 := by decide
  rcases family_descends (prefixWord ++ tailWord_6231033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6231036 : List Nat := [2, 2, 2, 1, 2, 3, 2, 1, 3, 2, 3]
def baseStart_6231036 : Nat := 118140960795 + 6231036 * 2 ^ 59
def prefixEnd_6231036 : Nat := 4983230072969 + 3 ^ 40 * 6231036 * 2
def baseEnd_6231036 : Nat := 3199516443468788276693993

theorem tailTrace_6231036 : CollatzResearch.WordTrace tailWord_6231036 prefixEnd_6231036 3199516443468788276693993 := by
  unfold tailWord_6231036
  simp only [CollatzResearch.WordTrace]
  refine ⟨113632276727014111535256481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151509702302685482047008641 113632276727014111535256481)
  ·
    refine ⟨85224207545260583651442361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113632276727014111535256481 85224207545260583651442361)
    ·
      refine ⟨63918155658945437738581771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85224207545260583651442361 63918155658945437738581771)
      ·
        refine ⟨95877233488418156607872657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63918155658945437738581771 95877233488418156607872657)
        ·
          refine ⟨71907925116313617455904493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95877233488418156607872657 71907925116313617455904493)
          ·
            refine ⟨26965471918617606545964185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 71907925116313617455904493 26965471918617606545964185)
            ·
              refine ⟨20224103938963204909473139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26965471918617606545964185 20224103938963204909473139)
              ·
                refine ⟨30336155908444807364209709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20224103938963204909473139 30336155908444807364209709)
                ·
                  refine ⟨11376058465666802761578641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30336155908444807364209709 11376058465666802761578641)
                  ·
                    refine ⟨8532043849250102071183981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11376058465666802761578641 8532043849250102071183981)
                    ·
                      refine ⟨3199516443468788276693993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8532043849250102071183981 3199516443468788276693993)
                      ·
                        rfl

theorem cell23_6231036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 2, 1, 3, 2, 3].length) (baseStart_6231036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6231036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6231036 prefixEnd_6231036 := by exact prefixLift 6231036
  have htrace : WordTrace (prefixWord ++ tailWord_6231036) baseStart_6231036 baseEnd_6231036 := by
    simpa [prefixWord, tailWord_6231036, baseEnd_6231036] using wordTrace_append hprefix tailTrace_6231036
  have hstable : (prefixWord ++ tailWord_6231036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6231036).length < 2 ^ (prefixWord ++ tailWord_6231036).sum := by decide
  have hdescent : baseEnd_6231036 < baseStart_6231036 := by decide
  rcases family_descends (prefixWord ++ tailWord_6231036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6231050 : List Nat := [3, 1, 2, 2, 3, 3, 2, 1, 1, 1, 4]
def baseStart_6231050 : Nat := 118140960795 + 6231050 * 2 ^ 59
def prefixEnd_6231050 : Nat := 4983230072969 + 3 ^ 40 * 6231050 * 2
def baseEnd_6231050 : Nat := 3199523632197951221918929

theorem tailTrace_6231050 : CollatzResearch.WordTrace tailWord_6231050 prefixEnd_6231050 3199523632197951221918929 := by
  unfold tailWord_6231050
  simp only [CollatzResearch.WordTrace]
  refine ⟨56816266018994375865380651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151510042717318335641015069 56816266018994375865380651)
  ·
    refine ⟨85224399028491563798070977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56816266018994375865380651 85224399028491563798070977)
    ·
      refine ⟨63918299271368672848553233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85224399028491563798070977 63918299271368672848553233)
      ·
        refine ⟨47938724453526504636414925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63918299271368672848553233 47938724453526504636414925)
        ·
          refine ⟨17977021670072439238655597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47938724453526504636414925 17977021670072439238655597)
          ·
            refine ⟨6741383126277164714495849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17977021670072439238655597 6741383126277164714495849)
            ·
              refine ⟨5056037344707873535871887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6741383126277164714495849 5056037344707873535871887)
              ·
                refine ⟨7584056017061810303807831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5056037344707873535871887 7584056017061810303807831)
                ·
                  refine ⟨11376084025592715455711747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7584056017061810303807831 11376084025592715455711747)
                  ·
                    refine ⟨17064126038389073183567621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11376084025592715455711747 17064126038389073183567621)
                    ·
                      refine ⟨3199523632197951221918929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17064126038389073183567621 3199523632197951221918929)
                      ·
                        rfl

theorem cell23_6231050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 3, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 3, 2, 1, 1, 1, 4].length) (baseStart_6231050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6231050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6231050 prefixEnd_6231050 := by exact prefixLift 6231050
  have htrace : WordTrace (prefixWord ++ tailWord_6231050) baseStart_6231050 baseEnd_6231050 := by
    simpa [prefixWord, tailWord_6231050, baseEnd_6231050] using wordTrace_append hprefix tailTrace_6231050
  have hstable : (prefixWord ++ tailWord_6231050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6231050).length < 2 ^ (prefixWord ++ tailWord_6231050).sum := by decide
  have hdescent : baseEnd_6231050 < baseStart_6231050 := by decide
  rcases family_descends (prefixWord ++ tailWord_6231050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6231109 : List Nat := [1, 3, 1, 1, 1, 3, 3, 1, 1, 3, 5]
def baseStart_6231109 : Nat := 118140960795 + 6231109 * 2 ^ 59
def prefixEnd_6231109 : Nat := 4983230072969 + 3 ^ 40 * 6231109 * 2
def baseEnd_6231109 : Nat := 3199553927556566491081157

theorem tailTrace_6231109 : CollatzResearch.WordTrace tailWord_6231109 prefixEnd_6231109 3199553927556566491081157 := by
  unfold tailWord_6231109
  simp only [CollatzResearch.WordTrace]
  refine ⟨227267215982763756537920381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151511477321842504358613587 227267215982763756537920381)
  ·
    refine ⟨85225205993536408701720143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 227267215982763756537920381 85225205993536408701720143)
    ·
      refine ⟨127837808990304613052580215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85225205993536408701720143 127837808990304613052580215)
      ·
        refine ⟨191756713485456919578870323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127837808990304613052580215 191756713485456919578870323)
        ·
          refine ⟨287635070228185379368305485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 191756713485456919578870323 287635070228185379368305485)
          ·
            refine ⟨107863151335569517263114557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 287635070228185379368305485 107863151335569517263114557)
            ·
              refine ⟨40448681750838568973667959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 107863151335569517263114557 40448681750838568973667959)
              ·
                refine ⟨60673022626257853460501939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40448681750838568973667959 60673022626257853460501939)
                ·
                  refine ⟨91009533939386780190752909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 60673022626257853460501939 91009533939386780190752909)
                  ·
                    refine ⟨34128575227270042571532341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 91009533939386780190752909 34128575227270042571532341)
                    ·
                      refine ⟨3199553927556566491081157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34128575227270042571532341 3199553927556566491081157)
                      ·
                        rfl

theorem cell23_6231109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 3, 1, 1, 3, 5].length) (baseStart_6231109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6231109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6231109 prefixEnd_6231109 := by exact prefixLift 6231109
  have htrace : WordTrace (prefixWord ++ tailWord_6231109) baseStart_6231109 baseEnd_6231109 := by
    simpa [prefixWord, tailWord_6231109, baseEnd_6231109] using wordTrace_append hprefix tailTrace_6231109
  have hstable : (prefixWord ++ tailWord_6231109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6231109).length < 2 ^ (prefixWord ++ tailWord_6231109).sum := by decide
  have hdescent : baseEnd_6231109 < baseStart_6231109 := by decide
  rcases family_descends (prefixWord ++ tailWord_6231109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6231129 : List Nat := [1, 2, 1, 2, 2, 1, 2, 5, 7]
def baseStart_6231129 : Nat := 118140960795 + 6231129 * 2 ^ 59
def prefixEnd_6231129 : Nat := 4983230072969 + 3 ^ 40 * 6231129 * 2
def baseEnd_6231129 : Nat := 355507133018850712536785

theorem tailTrace_6231129 : CollatzResearch.WordTrace tailWord_6231129 prefixEnd_6231129 355507133018850712536785 := by
  unfold tailWord_6231129
  simp only [CollatzResearch.WordTrace]
  refine ⟨227267945442691299953648441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151511963628460866635765627 227267945442691299953648441)
  ·
    refine ⟨170450959082018474965236331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 227267945442691299953648441 170450959082018474965236331)
    ·
      refine ⟨255676438623027712447854497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170450959082018474965236331 255676438623027712447854497)
      ·
        refine ⟨191757328967270784335890873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 255676438623027712447854497 191757328967270784335890873)
        ·
          refine ⟨143817996725453088251918155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 191757328967270784335890873 143817996725453088251918155)
          ·
            refine ⟨215726995088179632377877233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 143817996725453088251918155 215726995088179632377877233)
            ·
              refine ⟨161795246316134724283407925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 215726995088179632377877233 161795246316134724283407925)
              ·
                refine ⟨15168304342137630401569493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 161795246316134724283407925 15168304342137630401569493)
                ·
                  refine ⟨355507133018850712536785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15168304342137630401569493 355507133018850712536785)
                  ·
                    rfl

theorem cell23_6231129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 5, 7].length) (baseStart_6231129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6231129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6231129 prefixEnd_6231129 := by exact prefixLift 6231129
  have htrace : WordTrace (prefixWord ++ tailWord_6231129) baseStart_6231129 baseEnd_6231129 := by
    simpa [prefixWord, tailWord_6231129, baseEnd_6231129] using wordTrace_append hprefix tailTrace_6231129
  have hstable : (prefixWord ++ tailWord_6231129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6231129).length < 2 ^ (prefixWord ++ tailWord_6231129).sum := by decide
  have hdescent : baseEnd_6231129 < baseStart_6231129 := by decide
  rcases family_descends (prefixWord ++ tailWord_6231129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6231134 : List Nat := [4, 4, 1, 1, 1, 2, 1, 3, 2, 1, 3]
def baseStart_6231134 : Nat := 118140960795 + 6231134 * 2 ^ 59
def prefixEnd_6231134 : Nat := 4983230072969 + 3 ^ 40 * 6231134 * 2
def baseEnd_6231134 : Nat := 3199566764572928893268543

theorem tailTrace_6231134 : CollatzResearch.WordTrace tailWord_6231134 prefixEnd_6231134 3199566764572928893268543 := by
  unfold tailWord_6231134
  simp only [CollatzResearch.WordTrace]
  refine ⟨28408515975959148225947557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 151512085205115457205053637 28408515975959148225947557)
  ·
    refine ⟨5326596745492340292365167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28408515975959148225947557 5326596745492340292365167)
    ·
      refine ⟨7989895118238510438547751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5326596745492340292365167 7989895118238510438547751)
      ·
        refine ⟨11984842677357765657821627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7989895118238510438547751 11984842677357765657821627)
        ·
          refine ⟨17977264016036648486732441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11984842677357765657821627 17977264016036648486732441)
          ·
            refine ⟨13482948012027486365049331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17977264016036648486732441 13482948012027486365049331)
            ·
              refine ⟨20224422018041229547573997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13482948012027486365049331 20224422018041229547573997)
              ·
                refine ⟨7584158256765461080340249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20224422018041229547573997 7584158256765461080340249)
                ·
                  refine ⟨5688118692574095810255187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7584158256765461080340249 5688118692574095810255187)
                  ·
                    refine ⟨8532178038861143715382781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5688118692574095810255187 8532178038861143715382781)
                    ·
                      refine ⟨3199566764572928893268543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8532178038861143715382781 3199566764572928893268543)
                      ·
                        rfl

theorem cell23_6231134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 1, 3, 2, 1, 3].length) (baseStart_6231134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6231134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6231134 prefixEnd_6231134 := by exact prefixLift 6231134
  have htrace : WordTrace (prefixWord ++ tailWord_6231134) baseStart_6231134 baseEnd_6231134 := by
    simpa [prefixWord, tailWord_6231134, baseEnd_6231134] using wordTrace_append hprefix tailTrace_6231134
  have hstable : (prefixWord ++ tailWord_6231134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6231134).length < 2 ^ (prefixWord ++ tailWord_6231134).sum := by decide
  have hdescent : baseEnd_6231134 < baseStart_6231134 := by decide
  rcases family_descends (prefixWord ++ tailWord_6231134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6231144 : List Nat := [2, 1, 4, 4, 1, 2, 1, 2, 1, 3, 2]
def baseStart_6231144 : Nat := 118140960795 + 6231144 * 2 ^ 59
def prefixEnd_6231144 : Nat := 4983230072969 + 3 ^ 40 * 6231144 * 2
def baseEnd_6231144 : Nat := 3199571899379473854143497

theorem tailTrace_6231144 : CollatzResearch.WordTrace tailWord_6231144 prefixEnd_6231144 3199571899379473854143497 := by
  unfold tailWord_6231144
  simp only [CollatzResearch.WordTrace]
  refine ⟨113634246268818478757722243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151512328358424638343629657 113634246268818478757722243)
  ·
    refine ⟨170451369403227718136583365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113634246268818478757722243 170451369403227718136583365)
    ·
      refine ⟨31959631763105197150609381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 170451369403227718136583365 31959631763105197150609381)
      ·
        refine ⟨5992430955582224465739259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31959631763105197150609381 5992430955582224465739259)
        ·
          refine ⟨8988646433373336698608889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5992430955582224465739259 8988646433373336698608889)
          ·
            refine ⟨6741484825030002523956667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8988646433373336698608889 6741484825030002523956667)
            ·
              refine ⟨10112227237545003785935001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6741484825030002523956667 10112227237545003785935001)
              ·
                refine ⟨7584170428158752839451251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10112227237545003785935001 7584170428158752839451251)
                ·
                  refine ⟨11376255642238129259176877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7584170428158752839451251 11376255642238129259176877)
                  ·
                    refine ⟨4266095865839298472191329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11376255642238129259176877 4266095865839298472191329)
                    ·
                      refine ⟨3199571899379473854143497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4266095865839298472191329 3199571899379473854143497)
                      ·
                        rfl

theorem cell23_6231144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 2, 1, 2, 1, 3, 2].length) (baseStart_6231144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6231144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6231144 prefixEnd_6231144 := by exact prefixLift 6231144
  have htrace : WordTrace (prefixWord ++ tailWord_6231144) baseStart_6231144 baseEnd_6231144 := by
    simpa [prefixWord, tailWord_6231144, baseEnd_6231144] using wordTrace_append hprefix tailTrace_6231144
  have hstable : (prefixWord ++ tailWord_6231144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6231144).length < 2 ^ (prefixWord ++ tailWord_6231144).sum := by decide
  have hdescent : baseEnd_6231144 < baseStart_6231144 := by decide
  rcases family_descends (prefixWord ++ tailWord_6231144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6231157 : List Nat := [1, 3, 4, 3, 1, 1, 1, 2, 1, 4, 2]
def baseStart_6231157 : Nat := 118140960795 + 6231157 * 2 ^ 59
def prefixEnd_6231157 : Nat := 4983230072969 + 3 ^ 40 * 6231157 * 2
def baseEnd_6231157 : Nat := 3199578574627982303280937

theorem tailTrace_6231157 : CollatzResearch.WordTrace tailWord_6231157 prefixEnd_6231157 3199578574627982303280937 := by
  unfold tailWord_6231157
  simp only [CollatzResearch.WordTrace]
  refine ⟨227268966686589860735667725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151512644457726573823778483 227268966686589860735667725)
  ·
    refine ⟨85225862507471197775875397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 227268966686589860735667725 85225862507471197775875397)
    ·
      refine ⟨15979849220150849582976637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 85225862507471197775875397 15979849220150849582976637)
      ·
        refine ⟨5992443457556568593616239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15979849220150849582976637 5992443457556568593616239)
        ·
          refine ⟨8988665186334852890424359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5992443457556568593616239 8988665186334852890424359)
          ·
            refine ⟨13482997779502279335636539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8988665186334852890424359 13482997779502279335636539)
            ·
              refine ⟨20224496669253419003454809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13482997779502279335636539 20224496669253419003454809)
              ·
                refine ⟨15168372501940064252591107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20224496669253419003454809 15168372501940064252591107)
                ·
                  refine ⟨22752558752910096378886661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15168372501940064252591107 22752558752910096378886661)
                  ·
                    refine ⟨4266104766170643071041249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22752558752910096378886661 4266104766170643071041249)
                    ·
                      refine ⟨3199578574627982303280937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4266104766170643071041249 3199578574627982303280937)
                      ·
                        rfl

theorem cell23_6231157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 1, 2, 1, 4, 2].length) (baseStart_6231157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6231157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6231157 prefixEnd_6231157 := by exact prefixLift 6231157
  have htrace : WordTrace (prefixWord ++ tailWord_6231157) baseStart_6231157 baseEnd_6231157 := by
    simpa [prefixWord, tailWord_6231157, baseEnd_6231157] using wordTrace_append hprefix tailTrace_6231157
  have hstable : (prefixWord ++ tailWord_6231157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6231157).length < 2 ^ (prefixWord ++ tailWord_6231157).sum := by decide
  have hdescent : baseEnd_6231157 < baseStart_6231157 := by decide
  rcases family_descends (prefixWord ++ tailWord_6231157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6231210 : List Nat := [3, 1, 5, 1, 1, 1, 3, 1, 2, 5]
def baseStart_6231210 : Nat := 118140960795 + 6231210 * 2 ^ 59
def prefixEnd_6231210 : Nat := 4983230072969 + 3 ^ 40 * 6231210 * 2
def baseEnd_6231210 : Nat := 1066535263034223531972731

theorem tailTrace_6231210 : CollatzResearch.WordTrace tailWord_6231210 prefixEnd_6231210 1066535263034223531972731 := by
  unfold tailWord_6231210
  simp only [CollatzResearch.WordTrace]
  refine ⟨56817724938849462696836771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151513933170265233858231389 56817724938849462696836771)
  ·
    refine ⟨85226587408274194045255157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56817724938849462696836771 85226587408274194045255157)
    ·
      refine ⟨7989992569525705691742671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 85226587408274194045255157 7989992569525705691742671)
      ·
        refine ⟨11984988854288558537614007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7989992569525705691742671 11984988854288558537614007)
        ·
          refine ⟨17977483281432837806421011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11984988854288558537614007 17977483281432837806421011)
          ·
            refine ⟨26966224922149256709631517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17977483281432837806421011 26966224922149256709631517)
            ·
              refine ⟨10112334345805971266111819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26966224922149256709631517 10112334345805971266111819)
              ·
                refine ⟨15168501518708956899167729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10112334345805971266111819 15168501518708956899167729)
                ·
                  refine ⟨11376376139031717674375797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15168501518708956899167729 11376376139031717674375797)
                  ·
                    refine ⟨1066535263034223531972731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11376376139031717674375797 1066535263034223531972731)
                    ·
                      rfl

theorem cell23_6231210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 3, 1, 2, 5].length) (baseStart_6231210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6231210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6231210 prefixEnd_6231210 := by exact prefixLift 6231210
  have htrace : WordTrace (prefixWord ++ tailWord_6231210) baseStart_6231210 baseEnd_6231210 := by
    simpa [prefixWord, tailWord_6231210, baseEnd_6231210] using wordTrace_append hprefix tailTrace_6231210
  have hstable : (prefixWord ++ tailWord_6231210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6231210).length < 2 ^ (prefixWord ++ tailWord_6231210).sum := by decide
  have hdescent : baseEnd_6231210 < baseStart_6231210 := by decide
  rcases family_descends (prefixWord ++ tailWord_6231210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6231216 : List Nat := [2, 1, 1, 1, 2, 1, 2, 5, 1, 4, 3]
def baseStart_6231216 : Nat := 118140960795 + 6231216 * 2 ^ 59
def prefixEnd_6231216 : Nat := 4983230072969 + 3 ^ 40 * 6231216 * 2
def baseEnd_6231216 : Nat := 3199608869986597572443165

theorem tailTrace_6231216 : CollatzResearch.WordTrace tailWord_6231216 prefixEnd_6231216 3199608869986597572443165 := by
  unfold tailWord_6231216
  simp only [CollatzResearch.WordTrace]
  refine ⟨113635559296688056906032751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151514079062250742541377001 113635559296688056906032751)
  ·
    refine ⟨170453338945032085359049127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113635559296688056906032751 170453338945032085359049127)
    ·
      refine ⟨255680008417548128038573691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170453338945032085359049127 255680008417548128038573691)
      ·
        refine ⟨383520012626322192057860537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 255680008417548128038573691 383520012626322192057860537)
        ·
          refine ⟨287640009469741644043395403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 383520012626322192057860537 287640009469741644043395403)
          ·
            refine ⟨431460014204612466065093105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 287640009469741644043395403 431460014204612466065093105)
            ·
              refine ⟨323595010653459349548819829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 431460014204612466065093105 323595010653459349548819829)
              ·
                refine ⟨30337032248761814020201859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 323595010653459349548819829 30337032248761814020201859)
                ·
                  refine ⟨45505548373142721030302789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30337032248761814020201859 45505548373142721030302789)
                  ·
                    refine ⟨8532290319964260193181773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 45505548373142721030302789 8532290319964260193181773)
                    ·
                      refine ⟨3199608869986597572443165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8532290319964260193181773 3199608869986597572443165)
                      ·
                        rfl

theorem cell23_6231216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 5, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 5, 1, 4, 3].length) (baseStart_6231216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6231216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6231216 prefixEnd_6231216 := by exact prefixLift 6231216
  have htrace : WordTrace (prefixWord ++ tailWord_6231216) baseStart_6231216 baseEnd_6231216 := by
    simpa [prefixWord, tailWord_6231216, baseEnd_6231216] using wordTrace_append hprefix tailTrace_6231216
  have hstable : (prefixWord ++ tailWord_6231216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6231216).length < 2 ^ (prefixWord ++ tailWord_6231216).sum := by decide
  have hdescent : baseEnd_6231216 < baseStart_6231216 := by decide
  rcases family_descends (prefixWord ++ tailWord_6231216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6231230 : List Nat := [4, 2, 1, 1, 3, 1, 1, 2, 2, 4, 2]
def baseStart_6231230 : Nat := 118140960795 + 6231230 * 2 ^ 59
def prefixEnd_6231230 : Nat := 4983230072969 + 3 ^ 40 * 6231230 * 2
def baseEnd_6231230 : Nat := 3199616058715760517668101

theorem tailTrace_6231230 : CollatzResearch.WordTrace tailWord_6231230 prefixEnd_6231230 3199616058715760517668101 := by
  unfold tailWord_6231230
  simp only [CollatzResearch.WordTrace]
  refine ⟨28408953651915674275384393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 151514419476883596135383429 28408953651915674275384393)
  ·
    refine ⟨21306715238936755706538295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28408953651915674275384393 21306715238936755706538295)
    ·
      refine ⟨31960072858405133559807443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21306715238936755706538295 31960072858405133559807443)
      ·
        refine ⟨47940109287607700339711165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31960072858405133559807443 47940109287607700339711165)
        ·
          refine ⟨17977540982852887627391687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47940109287607700339711165 17977540982852887627391687)
          ·
            refine ⟨26966311474279331441087531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17977540982852887627391687 26966311474279331441087531)
            ·
              refine ⟨40449467211418997161631297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26966311474279331441087531 40449467211418997161631297)
              ·
                refine ⟨30337100408564247871223473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40449467211418997161631297 30337100408564247871223473)
                ·
                  refine ⟨22752825306423185903417605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30337100408564247871223473 22752825306423185903417605)
                  ·
                    refine ⟨4266154744954347356890801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22752825306423185903417605 4266154744954347356890801)
                    ·
                      refine ⟨3199616058715760517668101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4266154744954347356890801 3199616058715760517668101)
                      ·
                        rfl

theorem cell23_6231230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 1, 2, 2, 4, 2].length) (baseStart_6231230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6231230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6231230 prefixEnd_6231230 := by exact prefixLift 6231230
  have htrace : WordTrace (prefixWord ++ tailWord_6231230) baseStart_6231230 baseEnd_6231230 := by
    simpa [prefixWord, tailWord_6231230, baseEnd_6231230] using wordTrace_append hprefix tailTrace_6231230
  have hstable : (prefixWord ++ tailWord_6231230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6231230).length < 2 ^ (prefixWord ++ tailWord_6231230).sum := by decide
  have hdescent : baseEnd_6231230 < baseStart_6231230 := by decide
  rcases family_descends (prefixWord ++ tailWord_6231230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6231240 : List Nat := [2, 1, 3, 1, 2, 1, 4, 4, 1, 4]
def baseStart_6231240 : Nat := 118140960795 + 6231240 * 2 ^ 59
def prefixEnd_6231240 : Nat := 4983230072969 + 3 ^ 40 * 6231240 * 2
def baseEnd_6231240 : Nat := 1066540397840768492847685

theorem tailTrace_6231240 : CollatzResearch.WordTrace tailWord_6231240 prefixEnd_6231240 1066540397840768492847685 := by
  unfold tailWord_6231240
  simp only [CollatzResearch.WordTrace]
  refine ⟨113635996972644582955469587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151514662630192777273959449 113635996972644582955469587)
  ·
    refine ⟨170453995458966874433204381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113635996972644582955469587 170453995458966874433204381)
    ·
      refine ⟨63920248297112577912451643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 170453995458966874433204381 63920248297112577912451643)
      ·
        refine ⟨95880372445668866868677465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63920248297112577912451643 95880372445668866868677465)
        ·
          refine ⟨71910279334251650151508099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95880372445668866868677465 71910279334251650151508099)
          ·
            refine ⟨107865419001377475227262149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71910279334251650151508099 107865419001377475227262149)
            ·
              refine ⟨20224766062758276605111653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 107865419001377475227262149 20224766062758276605111653)
              ·
                refine ⟨3792143636767176863458435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20224766062758276605111653 3792143636767176863458435)
                ·
                  refine ⟨5688215455150765295187653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3792143636767176863458435 5688215455150765295187653)
                  ·
                    refine ⟨1066540397840768492847685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5688215455150765295187653 1066540397840768492847685)
                    ·
                      rfl

theorem cell23_6231240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 4, 4, 1, 4].length) (baseStart_6231240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6231240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6231240 prefixEnd_6231240 := by exact prefixLift 6231240
  have htrace : WordTrace (prefixWord ++ tailWord_6231240) baseStart_6231240 baseEnd_6231240 := by
    simpa [prefixWord, tailWord_6231240, baseEnd_6231240] using wordTrace_append hprefix tailTrace_6231240
  have hstable : (prefixWord ++ tailWord_6231240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6231240).length < 2 ^ (prefixWord ++ tailWord_6231240).sum := by decide
  have hdescent : baseEnd_6231240 < baseStart_6231240 := by decide
  rcases family_descends (prefixWord ++ tailWord_6231240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6231283 : List Nat := [1, 1, 1, 2, 2, 5, 2, 3, 1, 5]
def baseStart_6231283 : Nat := 118140960795 + 6231283 * 2 ^ 59
def prefixEnd_6231283 : Nat := 4983230072969 + 3 ^ 40 * 6231283 * 2
def baseEnd_6231283 : Nat := 1066547757730149603435119

theorem tailTrace_6231283 : CollatzResearch.WordTrace tailWord_6231283 prefixEnd_6231283 1066547757730149603435119 := by
  unfold tailWord_6231283
  simp only [CollatzResearch.WordTrace]
  refine ⟨227273562284133384254754503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151515708189422256169836335 227273562284133384254754503)
  ·
    refine ⟨340910343426200076382131755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227273562284133384254754503 340910343426200076382131755)
    ·
      refine ⟨511365515139300114573197633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 340910343426200076382131755 511365515139300114573197633)
      ·
        refine ⟨383524136354475085929898225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 511365515139300114573197633 383524136354475085929898225)
        ·
          refine ⟨287643102265856314447423669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 383524136354475085929898225 287643102265856314447423669)
          ·
            refine ⟨26966540837424029479445969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 287643102265856314447423669 26966540837424029479445969)
            ·
              refine ⟨20224905628068022109584477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26966540837424029479445969 20224905628068022109584477)
              ·
                refine ⟨7584339610525508291094179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20224905628068022109584477 7584339610525508291094179)
                ·
                  refine ⟨11376509415788262436641269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7584339610525508291094179 11376509415788262436641269)
                  ·
                    refine ⟨1066547757730149603435119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11376509415788262436641269 1066547757730149603435119)
                    ·
                      rfl

theorem cell23_6231283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 2, 3, 1, 5].length) (baseStart_6231283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6231283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6231283 prefixEnd_6231283 := by exact prefixLift 6231283
  have htrace : WordTrace (prefixWord ++ tailWord_6231283) baseStart_6231283 baseEnd_6231283 := by
    simpa [prefixWord, tailWord_6231283, baseEnd_6231283] using wordTrace_append hprefix tailTrace_6231283
  have hstable : (prefixWord ++ tailWord_6231283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6231283).length < 2 ^ (prefixWord ++ tailWord_6231283).sum := by decide
  have hdescent : baseEnd_6231283 < baseStart_6231283 := by decide
  rcases family_descends (prefixWord ++ tailWord_6231283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6231290 : List Nat := [3, 1, 1, 1, 1, 4, 3, 2, 2, 3, 2]
def baseStart_6231290 : Nat := 118140960795 + 6231290 * 2 ^ 59
def prefixEnd_6231290 : Nat := 4983230072969 + 3 ^ 40 * 6231290 * 2
def baseEnd_6231290 : Nat := 3199646867555030282917825

theorem tailTrace_6231290 : CollatzResearch.WordTrace tailWord_6231290 prefixEnd_6231290 3199646867555030282917825 := by
  unfold tailWord_6231290
  simp only [CollatzResearch.WordTrace]
  refine ⟨56818454398777006112564831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151515878396738682966839549 56818454398777006112564831)
  ·
    refine ⟨85227681598165509168847247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56818454398777006112564831 85227681598165509168847247)
    ·
      refine ⟨127841522397248263753270871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85227681598165509168847247 127841522397248263753270871)
      ·
        refine ⟨191762283595872395629906307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127841522397248263753270871 191762283595872395629906307)
        ·
          refine ⟨287643425393808593444859461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 191762283595872395629906307 287643425393808593444859461)
          ·
            refine ⟨53933142261339111270911149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 287643425393808593444859461 53933142261339111270911149)
            ·
              refine ⟨20224928348002166726591681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53933142261339111270911149 20224928348002166726591681)
              ·
                refine ⟨15168696261001625044943761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20224928348002166726591681 15168696261001625044943761)
                ·
                  refine ⟨11376522195751218783707821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15168696261001625044943761 11376522195751218783707821)
                  ·
                    refine ⟨4266195823406707043890433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11376522195751218783707821 4266195823406707043890433)
                    ·
                      refine ⟨3199646867555030282917825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4266195823406707043890433 3199646867555030282917825)
                      ·
                        rfl

theorem cell23_6231290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 3, 2, 2, 3, 2].length) (baseStart_6231290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6231290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6231290 prefixEnd_6231290 := by exact prefixLift 6231290
  have htrace : WordTrace (prefixWord ++ tailWord_6231290) baseStart_6231290 baseEnd_6231290 := by
    simpa [prefixWord, tailWord_6231290, baseEnd_6231290] using wordTrace_append hprefix tailTrace_6231290
  have hstable : (prefixWord ++ tailWord_6231290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6231290).length < 2 ^ (prefixWord ++ tailWord_6231290).sum := by decide
  have hdescent : baseEnd_6231290 < baseStart_6231290 := by decide
  rcases family_descends (prefixWord ++ tailWord_6231290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6231297 : List Nat := [1, 2, 4, 1, 1, 5, 1, 1, 3, 1, 3]
def baseStart_6231297 : Nat := 118140960795 + 6231297 * 2 ^ 59
def prefixEnd_6231297 : Nat := 4983230072969 + 3 ^ 40 * 6231297 * 2
def baseEnd_6231297 : Nat := 3199650461919611755530293

theorem tailTrace_6231297 : CollatzResearch.WordTrace tailWord_6231297 prefixEnd_6231297 3199650461919611755530293 := by
  unfold tailWord_6231297
  simp only [CollatzResearch.WordTrace]
  refine ⟨227274072906082664645764145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151516048604055109763842763 227274072906082664645764145)
  ·
    refine ⟨170455554679561998484323109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 227274072906082664645764145 170455554679561998484323109)
    ·
      refine ⟨31960416502417874715810583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 170455554679561998484323109 31960416502417874715810583)
      ·
        refine ⟨47940624753626812073715875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31960416502417874715810583 47940624753626812073715875)
        ·
          refine ⟨71910937130440218110573813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47940624753626812073715875 71910937130440218110573813)
          ·
            refine ⟨6741650355978770447866295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 71910937130440218110573813 6741650355978770447866295)
            ·
              refine ⟨10112475533968155671799443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6741650355978770447866295 10112475533968155671799443)
              ·
                refine ⟨15168713300952233507699165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10112475533968155671799443 15168713300952233507699165)
                ·
                  refine ⟨5688267487857087565387187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15168713300952233507699165 5688267487857087565387187)
                  ·
                    refine ⟨8532401231785631348080781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5688267487857087565387187 8532401231785631348080781)
                    ·
                      refine ⟨3199650461919611755530293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8532401231785631348080781 3199650461919611755530293)
                      ·
                        rfl

theorem cell23_6231297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 5, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 5, 1, 1, 3, 1, 3].length) (baseStart_6231297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6231297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6231297 prefixEnd_6231297 := by exact prefixLift 6231297
  have htrace : WordTrace (prefixWord ++ tailWord_6231297) baseStart_6231297 baseEnd_6231297 := by
    simpa [prefixWord, tailWord_6231297, baseEnd_6231297] using wordTrace_append hprefix tailTrace_6231297
  have hstable : (prefixWord ++ tailWord_6231297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6231297).length < 2 ^ (prefixWord ++ tailWord_6231297).sum := by decide
  have hdescent : baseEnd_6231297 < baseStart_6231297 := by decide
  rcases family_descends (prefixWord ++ tailWord_6231297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6231320 : List Nat := [2, 1, 2, 3, 1, 3, 3, 2, 1, 1, 4]
def baseStart_6231320 : Nat := 118140960795 + 6231320 * 2 ^ 59
def prefixEnd_6231320 : Nat := 4983230072969 + 3 ^ 40 * 6231320 * 2
def baseEnd_6231320 : Nat := 3199662271974665165542687

theorem tailTrace_6231320 : CollatzResearch.WordTrace tailWord_6231320 prefixEnd_6231320 3199662271974665165542687 := by
  unfold tailWord_6231320
  simp only [CollatzResearch.WordTrace]
  refine ⟨113637455892499669786925707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151516607856666226382567609 113637455892499669786925707)
  ·
    refine ⟨170456183838749504680388561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113637455892499669786925707 170456183838749504680388561)
    ·
      refine ⟨127842137879062128510291421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 170456183838749504680388561 127842137879062128510291421)
      ·
        refine ⟨47940801704648298191359283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 127842137879062128510291421 47940801704648298191359283)
        ·
          refine ⟨71911202556972447287038925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47940801704648298191359283 71911202556972447287038925)
          ·
            refine ⟨26966700958864667732639597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 71911202556972447287038925 26966700958864667732639597)
            ·
              refine ⟨10112512859574250399739849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26966700958864667732639597 10112512859574250399739849)
              ·
                refine ⟨7584384644680687799804887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10112512859574250399739849 7584384644680687799804887)
                ·
                  refine ⟨11376576967021031699707331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7584384644680687799804887 11376576967021031699707331)
                  ·
                    refine ⟨17064865450531547549560997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11376576967021031699707331 17064865450531547549560997)
                    ·
                      refine ⟨3199662271974665165542687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17064865450531547549560997 3199662271974665165542687)
                      ·
                        rfl

theorem cell23_6231320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 3, 2, 1, 1, 4].length) (baseStart_6231320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6231320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6231320 prefixEnd_6231320 := by exact prefixLift 6231320
  have htrace : WordTrace (prefixWord ++ tailWord_6231320) baseStart_6231320 baseEnd_6231320 := by
    simpa [prefixWord, tailWord_6231320, baseEnd_6231320] using wordTrace_append hprefix tailTrace_6231320
  have hstable : (prefixWord ++ tailWord_6231320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6231320).length < 2 ^ (prefixWord ++ tailWord_6231320).sum := by decide
  have hdescent : baseEnd_6231320 < baseStart_6231320 := by decide
  rcases family_descends (prefixWord ++ tailWord_6231320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6231330 : List Nat := [3, 3, 1, 1, 4, 1, 1, 2, 1, 6]
def baseStart_6231330 : Nat := 118140960795 + 6231330 * 2 ^ 59
def prefixEnd_6231330 : Nat := 4983230072969 + 3 ^ 40 * 6231330 * 2
def baseEnd_6231330 : Nat := 1066555802260403375472547

theorem tailTrace_6231330 : CollatzResearch.WordTrace tailWord_6231330 prefixEnd_6231330 1066555802260403375472547 := by
  unfold tailWord_6231330
  simp only [CollatzResearch.WordTrace]
  refine ⟨56818819128740777820428861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151516851009975407521143629 56818819128740777820428861)
  ·
    refine ⟨21307057173277791682660823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56818819128740777820428861 21307057173277791682660823)
    ·
      refine ⟨31960585759916687523991235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21307057173277791682660823 31960585759916687523991235)
      ·
        refine ⟨47940878639875031285986853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31960585759916687523991235 47940878639875031285986853)
        ·
          refine ⟨8988914744976568366122535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 47940878639875031285986853 8988914744976568366122535)
          ·
            refine ⟨13483372117464852549183803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8988914744976568366122535 13483372117464852549183803)
            ·
              refine ⟨20225058176197278823775705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13483372117464852549183803 20225058176197278823775705)
              ·
                refine ⟨15168793632147959117831779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20225058176197278823775705 15168793632147959117831779)
                ·
                  refine ⟨22753190448221938676747669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15168793632147959117831779 22753190448221938676747669)
                  ·
                    refine ⟨1066555802260403375472547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22753190448221938676747669 1066555802260403375472547)
                    ·
                      rfl

theorem cell23_6231330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 1, 2, 1, 6].length) (baseStart_6231330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6231330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6231330 prefixEnd_6231330 := by exact prefixLift 6231330
  have htrace : WordTrace (prefixWord ++ tailWord_6231330) baseStart_6231330 baseEnd_6231330 := by
    simpa [prefixWord, tailWord_6231330, baseEnd_6231330] using wordTrace_append hprefix tailTrace_6231330
  have hstable : (prefixWord ++ tailWord_6231330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6231330).length < 2 ^ (prefixWord ++ tailWord_6231330).sum := by decide
  have hdescent : baseEnd_6231330 < baseStart_6231330 := by decide
  rcases family_descends (prefixWord ++ tailWord_6231330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6231333 : List Nat := [1, 3, 1, 2, 4, 1, 1, 1, 3, 2, 4]
def baseStart_6231333 : Nat := 118140960795 + 6231333 * 2 ^ 59
def prefixEnd_6231333 : Nat := 4983230072969 + 3 ^ 40 * 6231333 * 2
def baseEnd_6231333 : Nat := 3199668947223173614680127

theorem tailTrace_6231333 : CollatzResearch.WordTrace tailWord_6231333 prefixEnd_6231333 3199668947223173614680127 := by
  unfold tailWord_6231333
  simp only [CollatzResearch.WordTrace]
  refine ⟨227275385933952242794074653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151516923955968161862716435 227275385933952242794074653)
  ·
    refine ⟨85228269725232091047777995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 227275385933952242794074653 85228269725232091047777995)
    ·
      refine ⟨127842404587848136571666993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85228269725232091047777995 127842404587848136571666993)
      ·
        refine ⟨95881803440886102428750245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 127842404587848136571666993 95881803440886102428750245)
        ·
          refine ⟨17977838145166144205390671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 95881803440886102428750245 17977838145166144205390671)
          ·
            refine ⟨26966757217749216308086007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17977838145166144205390671 26966757217749216308086007)
            ·
              refine ⟨40450135826623824462129011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26966757217749216308086007 40450135826623824462129011)
              ·
                refine ⟨60675203739935736693193517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40450135826623824462129011 60675203739935736693193517)
                ·
                  refine ⟨22753201402475901259947569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 60675203739935736693193517 22753201402475901259947569)
                  ·
                    refine ⟨17064901051856925944960677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22753201402475901259947569 17064901051856925944960677)
                    ·
                      refine ⟨3199668947223173614680127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17064901051856925944960677 3199668947223173614680127)
                      ·
                        rfl

theorem cell23_6231333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 1, 1, 3, 2, 4].length) (baseStart_6231333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6231333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6231333 prefixEnd_6231333 := by exact prefixLift 6231333
  have htrace : WordTrace (prefixWord ++ tailWord_6231333) baseStart_6231333 baseEnd_6231333 := by
    simpa [prefixWord, tailWord_6231333, baseEnd_6231333] using wordTrace_append hprefix tailTrace_6231333
  have hstable : (prefixWord ++ tailWord_6231333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6231333).length < 2 ^ (prefixWord ++ tailWord_6231333).sum := by decide
  have hdescent : baseEnd_6231333 < baseStart_6231333 := by decide
  rcases family_descends (prefixWord ++ tailWord_6231333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6231354 : List Nat := [3, 1, 1, 1, 4, 1, 3, 4, 1, 2, 2]
def baseStart_6231354 : Nat := 118140960795 + 6231354 * 2 ^ 59
def prefixEnd_6231354 : Nat := 4983230072969 + 3 ^ 40 * 6231354 * 2
def baseEnd_6231354 : Nat := 3199679730316918032517531

theorem tailTrace_6231354 : CollatzResearch.WordTrace tailWord_6231354 prefixEnd_6231354 3199679730316918032517531 := by
  unfold tailWord_6231354
  simp only [CollatzResearch.WordTrace]
  refine ⟨56819037966719040845147279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151517434577917442253726077 56819037966719040845147279)
  ·
    refine ⟨85228556950078561267720919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56819037966719040845147279 85228556950078561267720919)
    ·
      refine ⟨127842835425117841901581379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85228556950078561267720919 127842835425117841901581379)
      ·
        refine ⟨191764253137676762852372069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127842835425117841901581379 191764253137676762852372069)
        ·
          refine ⟨35955797463314393034819763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 191764253137676762852372069 35955797463314393034819763)
          ·
            refine ⟨53933696194971589552229645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35955797463314393034819763 53933696194971589552229645)
            ·
              refine ⟨20225136073114346082086117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53933696194971589552229645 20225136073114346082086117)
              ·
                refine ⟨3792213013708939890391147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20225136073114346082086117 3792213013708939890391147)
                ·
                  refine ⟨5688319520563409835586721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3792213013708939890391147 5688319520563409835586721)
                  ·
                    refine ⟨4266239640422557376690041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5688319520563409835586721 4266239640422557376690041)
                    ·
                      refine ⟨3199679730316918032517531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4266239640422557376690041 3199679730316918032517531)
                      ·
                        rfl

theorem cell23_6231354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 3, 4, 1, 2, 2].length) (baseStart_6231354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6231354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6231354 prefixEnd_6231354 := by exact prefixLift 6231354
  have htrace : WordTrace (prefixWord ++ tailWord_6231354) baseStart_6231354 baseEnd_6231354 := by
    simpa [prefixWord, tailWord_6231354, baseEnd_6231354] using wordTrace_append hprefix tailTrace_6231354
  have hstable : (prefixWord ++ tailWord_6231354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6231354).length < 2 ^ (prefixWord ++ tailWord_6231354).sum := by decide
  have hdescent : baseEnd_6231354 < baseStart_6231354 := by decide
  rcases family_descends (prefixWord ++ tailWord_6231354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6231397 : List Nat := [1, 3, 1, 3, 1, 2, 3, 3, 1, 3, 2]
def baseStart_6231397 : Nat := 118140960795 + 6231397 * 2 ^ 59
def prefixEnd_6231397 : Nat := 4983230072969 + 3 ^ 40 * 6231397 * 2
def baseEnd_6231397 : Nat := 3199701809985061364279833

theorem tailTrace_6231397 : CollatzResearch.WordTrace tailWord_6231397 prefixEnd_6231397 3199701809985061364279833 := by
  unfold tailWord_6231397
  simp only [CollatzResearch.WordTrace]
  refine ⟨227277720205720381724404445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151518480137146921149602963 227277720205720381724404445)
  ·
    refine ⟨85229145077145143146651667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 227277720205720381724404445 85229145077145143146651667)
    ·
      refine ⟨127843717615717714719977501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85229145077145143146651667 127843717615717714719977501)
      ·
        refine ⟨47941394105894143019991563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 127843717615717714719977501 47941394105894143019991563)
        ·
          refine ⟨71912091158841214529987345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47941394105894143019991563 71912091158841214529987345)
          ·
            refine ⟨53934068369130910897490509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71912091158841214529987345 53934068369130910897490509)
            ·
              refine ⟨20225275638424091586558941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53934068369130910897490509 20225275638424091586558941)
              ·
                refine ⟨7584478364409034344959603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20225275638424091586558941 7584478364409034344959603)
                ·
                  refine ⟨11376717546613551517439405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7584478364409034344959603 11376717546613551517439405)
                  ·
                    refine ⟨4266269079980081819039777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11376717546613551517439405 4266269079980081819039777)
                    ·
                      refine ⟨3199701809985061364279833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4266269079980081819039777 3199701809985061364279833)
                      ·
                        rfl

theorem cell23_6231397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 3, 3, 1, 3, 2].length) (baseStart_6231397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6231397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6231397 prefixEnd_6231397 := by exact prefixLift 6231397
  have htrace : WordTrace (prefixWord ++ tailWord_6231397) baseStart_6231397 baseEnd_6231397 := by
    simpa [prefixWord, tailWord_6231397, baseEnd_6231397] using wordTrace_append hprefix tailTrace_6231397
  have hstable : (prefixWord ++ tailWord_6231397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6231397).length < 2 ^ (prefixWord ++ tailWord_6231397).sum := by decide
  have hdescent : baseEnd_6231397 < baseStart_6231397 := by decide
  rcases family_descends (prefixWord ++ tailWord_6231397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6231404 : List Nat := [2, 2, 1, 1, 5, 3, 1, 2, 2, 1, 3]
def baseStart_6231404 : Nat := 118140960795 + 6231404 * 2 ^ 59
def prefixEnd_6231404 : Nat := 4983230072969 + 3 ^ 40 * 6231404 * 2
def baseEnd_6231404 : Nat := 3199705404349642836892301

theorem tailTrace_6231404 : CollatzResearch.WordTrace tailWord_6231404 prefixEnd_6231404 3199705404349642836892301 := by
  unfold tailWord_6231404
  simp only [CollatzResearch.WordTrace]
  refine ⟨113638987758347510959954633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151518650344463347946606177 113638987758347510959954633)
  ·
    refine ⟨85229240818760633219965975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113638987758347510959954633 85229240818760633219965975)
    ·
      refine ⟨127843861228140949829948963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85229240818760633219965975 127843861228140949829948963)
      ·
        refine ⟨191765791842211424744923445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127843861228140949829948963 191765791842211424744923445)
        ·
          refine ⟨17978042985207321069836573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 191765791842211424744923445 17978042985207321069836573)
          ·
            refine ⟨6741766119452745401188715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17978042985207321069836573 6741766119452745401188715)
            ·
              refine ⟨10112649179179118101783073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6741766119452745401188715 10112649179179118101783073)
              ·
                refine ⟨7584486884384338576337305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10112649179179118101783073 7584486884384338576337305)
                ·
                  refine ⟨5688365163288253932252979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7584486884384338576337305 5688365163288253932252979)
                  ·
                    refine ⟨8532547744932380898379469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5688365163288253932252979 8532547744932380898379469)
                    ·
                      refine ⟨3199705404349642836892301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8532547744932380898379469 3199705404349642836892301)
                      ·
                        rfl

theorem cell23_6231404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 2, 1, 3].length) (baseStart_6231404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6231404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6231404 prefixEnd_6231404 := by exact prefixLift 6231404
  have htrace : WordTrace (prefixWord ++ tailWord_6231404) baseStart_6231404 baseEnd_6231404 := by
    simpa [prefixWord, tailWord_6231404, baseEnd_6231404] using wordTrace_append hprefix tailTrace_6231404
  have hstable : (prefixWord ++ tailWord_6231404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6231404).length < 2 ^ (prefixWord ++ tailWord_6231404).sum := by decide
  have hdescent : baseEnd_6231404 < baseStart_6231404 := by decide
  rcases family_descends (prefixWord ++ tailWord_6231404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6231427 : List Nat := [1, 1, 1, 3, 5, 1, 3, 1, 1, 4, 2]
def baseStart_6231427 : Nat := 118140960795 + 6231427 * 2 ^ 59
def prefixEnd_6231427 : Nat := 4983230072969 + 3 ^ 40 * 6231427 * 2
def baseEnd_6231427 : Nat := 3199717214404696246904695

theorem tailTrace_6231427 : CollatzResearch.WordTrace tailWord_6231427 prefixEnd_6231427 3199717214404696246904695 := by
  unfold tailWord_6231427
  simp only [CollatzResearch.WordTrace]
  refine ⟨227278814395611696847996535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151519209597074464565331023 227278814395611696847996535)
  ·
    refine ⟨340918221593417545271994803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227278814395611696847996535 340918221593417545271994803)
    ·
      refine ⟨511377332390126317907992205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 340918221593417545271994803 511377332390126317907992205)
      ·
        refine ⟨191766499646297369215497077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 511377332390126317907992205 191766499646297369215497077)
        ·
          refine ⟨17978109341840378363952851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 191766499646297369215497077 17978109341840378363952851)
          ·
            refine ⟨26967164012760567545929277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17978109341840378363952851 26967164012760567545929277)
            ·
              refine ⟨10112686504785212829723479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26967164012760567545929277 10112686504785212829723479)
              ·
                refine ⟨15169029757177819244585219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10112686504785212829723479 15169029757177819244585219)
                ·
                  refine ⟨22753544635766728866877829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15169029757177819244585219 22753544635766728866877829)
                  ·
                    refine ⟨4266289619206261662539593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22753544635766728866877829 4266289619206261662539593)
                    ·
                      refine ⟨3199717214404696246904695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4266289619206261662539593 3199717214404696246904695)
                      ·
                        rfl

theorem cell23_6231427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 3, 1, 1, 4, 2].length) (baseStart_6231427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6231427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6231427 prefixEnd_6231427 := by exact prefixLift 6231427
  have htrace : WordTrace (prefixWord ++ tailWord_6231427) baseStart_6231427 baseEnd_6231427 := by
    simpa [prefixWord, tailWord_6231427, baseEnd_6231427] using wordTrace_append hprefix tailTrace_6231427
  have hstable : (prefixWord ++ tailWord_6231427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6231427).length < 2 ^ (prefixWord ++ tailWord_6231427).sum := by decide
  have hdescent : baseEnd_6231427 < baseStart_6231427 := by decide
  rcases family_descends (prefixWord ++ tailWord_6231427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6231444 : List Nat := [2, 4, 2, 1, 2, 1, 1, 2, 4, 2, 2]
def baseStart_6231444 : Nat := 118140960795 + 6231444 * 2 ^ 59
def prefixEnd_6231444 : Nat := 4983230072969 + 3 ^ 40 * 6231444 * 2
def baseEnd_6231444 : Nat := 3199725943575822680392117

theorem tailTrace_6231444 : CollatzResearch.WordTrace tailWord_6231444 prefixEnd_6231444 3199725943575822680392117 := by
  unfold tailWord_6231444
  simp only [CollatzResearch.WordTrace]
  refine ⟨113639717218275054375682693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151519622957700072500910257 113639717218275054375682693)
  ·
    refine ⟨21307446978426572695440505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 113639717218275054375682693 21307446978426572695440505)
    ·
      refine ⟨15980585233819929521580379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21307446978426572695440505 15980585233819929521580379)
      ·
        refine ⟨23970877850729894282370569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15980585233819929521580379 23970877850729894282370569)
        ·
          refine ⟨17978158388047420711777927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23970877850729894282370569 17978158388047420711777927)
          ·
            refine ⟨26967237582071131067666891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17978158388047420711777927 26967237582071131067666891)
            ·
              refine ⟨40450856373106696601500337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26967237582071131067666891 40450856373106696601500337)
              ·
                refine ⟨30338142279830022451125253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40450856373106696601500337 30338142279830022451125253)
                ·
                  refine ⟨5688401677468129209585985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30338142279830022451125253 5688401677468129209585985)
                  ·
                    refine ⟨4266301258101096907189489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5688401677468129209585985 4266301258101096907189489)
                    ·
                      refine ⟨3199725943575822680392117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4266301258101096907189489 3199725943575822680392117)
                      ·
                        rfl

theorem cell23_6231444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 1, 2, 4, 2, 2].length) (baseStart_6231444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6231444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6231444 prefixEnd_6231444 := by exact prefixLift 6231444
  have htrace : WordTrace (prefixWord ++ tailWord_6231444) baseStart_6231444 baseEnd_6231444 := by
    simpa [prefixWord, tailWord_6231444, baseEnd_6231444] using wordTrace_append hprefix tailTrace_6231444
  have hstable : (prefixWord ++ tailWord_6231444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6231444).length < 2 ^ (prefixWord ++ tailWord_6231444).sum := by decide
  have hdescent : baseEnd_6231444 < baseStart_6231444 := by decide
  rcases family_descends (prefixWord ++ tailWord_6231444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6231517 : List Nat := [1, 4, 3, 1, 1, 2, 2, 2, 2, 1, 4]
def baseStart_6231517 : Nat := 118140960795 + 6231517 * 2 ^ 59
def prefixEnd_6231517 : Nat := 4983230072969 + 3 ^ 40 * 6231517 * 2
def baseEnd_6231517 : Nat := 3199763427663600894779281

theorem tailTrace_6231517 : CollatzResearch.WordTrace tailWord_6231517 prefixEnd_6231517 3199763427663600894779281 := by
  unfold tailWord_6231517
  simp only [CollatzResearch.WordTrace]
  refine ⟨227282096965285642218772805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151521397976857094812515203 227282096965285642218772805)
  ·
    refine ⟨42615393180991057916019901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 227282096965285642218772805 42615393180991057916019901)
    ·
      refine ⟨15980772442871646718507463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42615393180991057916019901 15980772442871646718507463)
      ·
        refine ⟨23971158664307470077761195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15980772442871646718507463 23971158664307470077761195)
        ·
          refine ⟨35956737996461205116641793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23971158664307470077761195 35956737996461205116641793)
          ·
            refine ⟨26967553497345903837481345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35956737996461205116641793 26967553497345903837481345)
            ·
              refine ⟨20225665123009427878111009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26967553497345903837481345 20225665123009427878111009)
              ·
                refine ⟨15169248842257070908583257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20225665123009427878111009 15169248842257070908583257)
                ·
                  refine ⟨11376936631692803181437443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15169248842257070908583257 11376936631692803181437443)
                  ·
                    refine ⟨17065404947539204772156165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11376936631692803181437443 17065404947539204772156165)
                    ·
                      refine ⟨3199763427663600894779281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17065404947539204772156165 3199763427663600894779281)
                      ·
                        rfl

theorem cell23_6231517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 2, 2, 2, 1, 4].length) (baseStart_6231517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6231517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6231517 prefixEnd_6231517 := by exact prefixLift 6231517
  have htrace : WordTrace (prefixWord ++ tailWord_6231517) baseStart_6231517 baseEnd_6231517 := by
    simpa [prefixWord, tailWord_6231517, baseEnd_6231517] using wordTrace_append hprefix tailTrace_6231517
  have hstable : (prefixWord ++ tailWord_6231517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6231517).length < 2 ^ (prefixWord ++ tailWord_6231517).sum := by decide
  have hdescent : baseEnd_6231517 < baseStart_6231517 := by decide
  rcases family_descends (prefixWord ++ tailWord_6231517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6231520 : List Nat := [2, 1, 1, 3, 1, 1, 2, 3, 4, 2, 3]
def baseStart_6231520 : Nat := 118140960795 + 6231520 * 2 ^ 59
def prefixEnd_6231520 : Nat := 4983230072969 + 3 ^ 40 * 6231520 * 2
def baseEnd_6231520 : Nat := 3199764968105564383041767

theorem tailTrace_6231520 : CollatzResearch.WordTrace tailWord_6231520 prefixEnd_6231520 3199764968105564383041767 := by
  unfold tailWord_6231520
  simp only [CollatzResearch.WordTrace]
  refine ⟨113641103192137386865566007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151521470922849849154088009 113641103192137386865566007)
  ·
    refine ⟨170461654788206080298349011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113641103192137386865566007 170461654788206080298349011)
    ·
      refine ⟨255692482182309120447523517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170461654788206080298349011 255692482182309120447523517)
      ·
        refine ⟨95884680818365920167821319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 255692482182309120447523517 95884680818365920167821319)
        ·
          refine ⟨143827021227548880251731979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95884680818365920167821319 143827021227548880251731979)
          ·
            refine ⟨215740531841323320377597969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 143827021227548880251731979 215740531841323320377597969)
            ·
              refine ⟨161805398880992490283198477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 215740531841323320377597969 161805398880992490283198477)
              ·
                refine ⟨60677024580372183856199429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 161805398880992490283198477 60677024580372183856199429)
                ·
                  refine ⟨11376942108819784473037393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 60677024580372183856199429 11376942108819784473037393)
                  ·
                    refine ⟨8532706581614838354778045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11376942108819784473037393 8532706581614838354778045)
                    ·
                      refine ⟨3199764968105564383041767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8532706581614838354778045 3199764968105564383041767)
                      ·
                        rfl

theorem cell23_6231520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 3, 4, 2, 3].length) (baseStart_6231520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6231520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6231520 prefixEnd_6231520 := by exact prefixLift 6231520
  have htrace : WordTrace (prefixWord ++ tailWord_6231520) baseStart_6231520 baseEnd_6231520 := by
    simpa [prefixWord, tailWord_6231520, baseEnd_6231520] using wordTrace_append hprefix tailTrace_6231520
  have hstable : (prefixWord ++ tailWord_6231520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6231520).length < 2 ^ (prefixWord ++ tailWord_6231520).sum := by decide
  have hdescent : baseEnd_6231520 < baseStart_6231520 := by decide
  rcases family_descends (prefixWord ++ tailWord_6231520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6231543 : List Nat := [1, 1, 3, 1, 1, 1, 1, 3, 3, 2, 6]
def baseStart_6231543 : Nat := 118140960795 + 6231543 * 2 ^ 59
def prefixEnd_6231543 : Nat := 4983230072969 + 3 ^ 40 * 6231543 * 2
def baseEnd_6231543 : Nat := 3199776778160617793054161

theorem tailTrace_6231543 : CollatzResearch.WordTrace tailWord_6231543 prefixEnd_6231543 3199776778160617793054161 := by
  unfold tailWord_6231543
  simp only [CollatzResearch.WordTrace]
  refine ⟨227283045263191448659219283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151522030175460965772812855 227283045263191448659219283)
  ·
    refine ⟨340924567894787172988828925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227283045263191448659219283 340924567894787172988828925)
    ·
      refine ⟨127846712960545189870810847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 340924567894787172988828925 127846712960545189870810847)
      ·
        refine ⟨191770069440817784806216271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127846712960545189870810847 191770069440817784806216271)
        ·
          refine ⟨287655104161226677209324407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 191770069440817784806216271 287655104161226677209324407)
          ·
            refine ⟨431482656241840015813986611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 287655104161226677209324407 431482656241840015813986611)
            ·
              refine ⟨647223984362760023720979917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 431482656241840015813986611 647223984362760023720979917)
              ·
                refine ⟨242708994136035008895367469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 647223984362760023720979917 242708994136035008895367469)
                ·
                  refine ⟨91015872801013128335762801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 242708994136035008895367469 91015872801013128335762801)
                  ·
                    refine ⟨68261904600759846251822101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 91015872801013128335762801 68261904600759846251822101)
                    ·
                      refine ⟨3199776778160617793054161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 68261904600759846251822101 3199776778160617793054161)
                      ·
                        rfl

theorem cell23_6231543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 3, 3, 2, 6].length) (baseStart_6231543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6231543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6231543 prefixEnd_6231543 := by exact prefixLift 6231543
  have htrace : WordTrace (prefixWord ++ tailWord_6231543) baseStart_6231543 baseEnd_6231543 := by
    simpa [prefixWord, tailWord_6231543, baseEnd_6231543] using wordTrace_append hprefix tailTrace_6231543
  have hstable : (prefixWord ++ tailWord_6231543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6231543).length < 2 ^ (prefixWord ++ tailWord_6231543).sum := by decide
  have hdescent : baseEnd_6231543 < baseStart_6231543 := by decide
  rcases family_descends (prefixWord ++ tailWord_6231543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6231554 : List Nat := [3, 4, 1, 2, 1, 2, 1, 1, 1, 4, 3]
def baseStart_6231554 : Nat := 118140960795 + 6231554 * 2 ^ 59
def prefixEnd_6231554 : Nat := 4983230072969 + 3 ^ 40 * 6231554 * 2
def baseEnd_6231554 : Nat := 3199782426447817250016611

theorem tailTrace_6231554 : CollatzResearch.WordTrace tailWord_6231554 prefixEnd_6231554 3199782426447817250016611 := by
  unfold tailWord_6231554
  simp only [CollatzResearch.WordTrace]
  refine ⟨56820861616537899384467429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151522297644101065025246477 56820861616537899384467429)
  ·
    refine ⟨10653911553100856134587643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 56820861616537899384467429 10653911553100856134587643)
    ·
      refine ⟨15980867329651284201881465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10653911553100856134587643 15980867329651284201881465)
      ·
        refine ⟨11985650497238463151411099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15980867329651284201881465 11985650497238463151411099)
        ·
          refine ⟨17978475745857694727116649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11985650497238463151411099 17978475745857694727116649)
          ·
            refine ⟨13483856809393271045337487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17978475745857694727116649 13483856809393271045337487)
            ·
              refine ⟨20225785214089906568006231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13483856809393271045337487 20225785214089906568006231)
              ·
                refine ⟨30338677821134859852009347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20225785214089906568006231 30338677821134859852009347)
                ·
                  refine ⟨45508016731702289778014021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30338677821134859852009347 45508016731702289778014021)
                  ·
                    refine ⟨8532753137194179333377629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 45508016731702289778014021 8532753137194179333377629)
                    ·
                      refine ⟨3199782426447817250016611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8532753137194179333377629 3199782426447817250016611)
                      ·
                        rfl

theorem cell23_6231554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 1, 1, 1, 4, 3].length) (baseStart_6231554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6231554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6231554 prefixEnd_6231554 := by exact prefixLift 6231554
  have htrace : WordTrace (prefixWord ++ tailWord_6231554) baseStart_6231554 baseEnd_6231554 := by
    simpa [prefixWord, tailWord_6231554, baseEnd_6231554] using wordTrace_append hprefix tailTrace_6231554
  have hstable : (prefixWord ++ tailWord_6231554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6231554).length < 2 ^ (prefixWord ++ tailWord_6231554).sum := by decide
  have hdescent : baseEnd_6231554 < baseStart_6231554 := by decide
  rcases family_descends (prefixWord ++ tailWord_6231554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6231584 : List Nat := [2, 1, 1, 6, 1, 1, 1, 3, 3, 1, 3]
def baseStart_6231584 : Nat := 118140960795 + 6231584 * 2 ^ 59
def prefixEnd_6231584 : Nat := 4983230072969 + 3 ^ 40 * 6231584 * 2
def baseEnd_6231584 : Nat := 3199797830867452132641473

theorem tailTrace_6231584 : CollatzResearch.WordTrace tailWord_6231584 prefixEnd_6231584 3199797830867452132641473 := by
  unfold tailWord_6231584
  simp only [CollatzResearch.WordTrace]
  refine ⟨113642270328021456330730903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151523027104028608440974537 113642270328021456330730903)
  ·
    refine ⟨170463405492032184496096355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113642270328021456330730903 170463405492032184496096355)
    ·
      refine ⟨255695108238048276744144533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170463405492032184496096355 255695108238048276744144533)
      ·
        refine ⟨11985708198658512972381775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 255695108238048276744144533 11985708198658512972381775)
        ·
          refine ⟨17978562297987769458572663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11985708198658512972381775 17978562297987769458572663)
          ·
            refine ⟨26967843446981654187858995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17978562297987769458572663 26967843446981654187858995)
            ·
              refine ⟨40451765170472481281788493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26967843446981654187858995 40451765170472481281788493)
              ·
                refine ⟨15169411938927180480670685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40451765170472481281788493 15169411938927180480670685)
                ·
                  refine ⟨5688529477097692680251507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15169411938927180480670685 5688529477097692680251507)
                  ·
                    refine ⟨8532794215646539020377261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5688529477097692680251507 8532794215646539020377261)
                    ·
                      refine ⟨3199797830867452132641473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8532794215646539020377261 3199797830867452132641473)
                      ·
                        rfl

theorem cell23_6231584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 1, 3, 3, 1, 3].length) (baseStart_6231584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6231584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6231584 prefixEnd_6231584 := by exact prefixLift 6231584
  have htrace : WordTrace (prefixWord ++ tailWord_6231584) baseStart_6231584 baseEnd_6231584 := by
    simpa [prefixWord, tailWord_6231584, baseEnd_6231584] using wordTrace_append hprefix tailTrace_6231584
  have hstable : (prefixWord ++ tailWord_6231584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6231584).length < 2 ^ (prefixWord ++ tailWord_6231584).sum := by decide
  have hdescent : baseEnd_6231584 < baseStart_6231584 := by decide
  rcases family_descends (prefixWord ++ tailWord_6231584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6231607 : List Nat := [1, 1, 3, 1, 2, 4, 1, 4, 1, 1, 4]
def baseStart_6231607 : Nat := 118140960795 + 6231607 * 2 ^ 59
def prefixEnd_6231607 : Nat := 4983230072969 + 3 ^ 40 * 6231607 * 2
def baseEnd_6231607 : Nat := 3199809640922505542653867

theorem tailTrace_6231607 : CollatzResearch.WordTrace tailWord_6231607 prefixEnd_6231607 3199809640922505542653867 := by
  unfold tailWord_6231607
  simp only [CollatzResearch.WordTrace]
  refine ⟨227285379534959587589549075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151523586356639725059699383 227285379534959587589549075)
  ·
    refine ⟨340928069302439381384323613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227285379534959587589549075 340928069302439381384323613)
    ·
      refine ⟨127848025988414768019121355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 340928069302439381384323613 127848025988414768019121355)
      ·
        refine ⟨191772038982622152028682033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127848025988414768019121355 191772038982622152028682033)
        ·
          refine ⟨143829029236966614021511525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 191772038982622152028682033 143829029236966614021511525)
          ·
            refine ⟨26967942981931240129033411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 143829029236966614021511525 26967942981931240129033411)
            ·
              refine ⟨40451914472896860193550117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26967942981931240129033411 40451914472896860193550117)
              ·
                refine ⟨7584733963668161286290647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40451914472896860193550117 7584733963668161286290647)
                ·
                  refine ⟨11377100945502241929435971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7584733963668161286290647 11377100945502241929435971)
                  ·
                    refine ⟨17065651418253362894153957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11377100945502241929435971 17065651418253362894153957)
                    ·
                      refine ⟨3199809640922505542653867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17065651418253362894153957 3199809640922505542653867)
                      ·
                        rfl

theorem cell23_6231607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 1, 4, 1, 1, 4].length) (baseStart_6231607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6231607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6231607 prefixEnd_6231607 := by exact prefixLift 6231607
  have htrace : WordTrace (prefixWord ++ tailWord_6231607) baseStart_6231607 baseEnd_6231607 := by
    simpa [prefixWord, tailWord_6231607, baseEnd_6231607] using wordTrace_append hprefix tailTrace_6231607
  have hstable : (prefixWord ++ tailWord_6231607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6231607).length < 2 ^ (prefixWord ++ tailWord_6231607).sum := by decide
  have hdescent : baseEnd_6231607 < baseStart_6231607 := by decide
  rcases family_descends (prefixWord ++ tailWord_6231607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6231610 : List Nat := [3, 1, 1, 1, 3, 2, 1, 2, 3, 1, 5]
def baseStart_6231610 : Nat := 118140960795 + 6231610 * 2 ^ 59
def prefixEnd_6231610 : Nat := 4983230072969 + 3 ^ 40 * 6231610 * 2
def baseEnd_6231610 : Nat := 3199811181364469030916353

theorem tailTrace_6231610 : CollatzResearch.WordTrace tailWord_6231610 prefixEnd_6231610 3199811181364469030916353 := by
  unfold tailWord_6231610
  simp only [CollatzResearch.WordTrace]
  refine ⟨56821372238487179775477071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151523659302632479401272189 56821372238487179775477071)
  ·
    refine ⟨85232058357730769663215607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56821372238487179775477071 85232058357730769663215607)
    ·
      refine ⟨127848087536596154494823411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85232058357730769663215607 127848087536596154494823411)
      ·
        refine ⟨191772131304894231742235117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127848087536596154494823411 191772131304894231742235117)
        ·
          refine ⟨71914549239335336903338169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 191772131304894231742235117 71914549239335336903338169)
          ·
            refine ⟨53935911929501502677503627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71914549239335336903338169 53935911929501502677503627)
            ·
              refine ⟨80903867894252254016255441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53935911929501502677503627 80903867894252254016255441)
              ·
                refine ⟨60677900920689190512191581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 80903867894252254016255441 60677900920689190512191581)
                ·
                  refine ⟨22754212845258446442071843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 60677900920689190512191581 22754212845258446442071843)
                  ·
                    refine ⟨34131319267887669663107765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22754212845258446442071843 34131319267887669663107765)
                    ·
                      refine ⟨3199811181364469030916353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34131319267887669663107765 3199811181364469030916353)
                      ·
                        rfl

theorem cell23_6231610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 2, 3, 1, 5].length) (baseStart_6231610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6231610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6231610 prefixEnd_6231610 := by exact prefixLift 6231610
  have htrace : WordTrace (prefixWord ++ tailWord_6231610) baseStart_6231610 baseEnd_6231610 := by
    simpa [prefixWord, tailWord_6231610, baseEnd_6231610] using wordTrace_append hprefix tailTrace_6231610
  have hstable : (prefixWord ++ tailWord_6231610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6231610).length < 2 ^ (prefixWord ++ tailWord_6231610).sum := by decide
  have hdescent : baseEnd_6231610 < baseStart_6231610 := by decide
  rcases family_descends (prefixWord ++ tailWord_6231610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6231617 : List Nat := [1, 2, 5, 1, 1, 1, 1, 1, 6, 4]
def baseStart_6231617 : Nat := 118140960795 + 6231617 * 2 ^ 59
def prefixEnd_6231617 : Nat := 4983230072969 + 3 ^ 40 * 6231617 * 2
def baseEnd_6231617 : Nat := 1066604925243016834509607

theorem tailTrace_6231617 : CollatzResearch.WordTrace tailWord_6231617 prefixEnd_6231617 1066604925243016834509607 := by
  unfold tailWord_6231617
  simp only [CollatzResearch.WordTrace]
  refine ⟨227285744264923359297413105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151523829509948906198275403 227285744264923359297413105)
  ·
    refine ⟨170464308198692519473059829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 227285744264923359297413105 170464308198692519473059829)
    ·
      refine ⟨15981028893627423700599359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 170464308198692519473059829 15981028893627423700599359)
      ·
        refine ⟨23971543340441135550899039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15981028893627423700599359 23971543340441135550899039)
        ·
          refine ⟨35957315010661703326348559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23971543340441135550899039 35957315010661703326348559)
          ·
            refine ⟨53935972515992554989522839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35957315010661703326348559 53935972515992554989522839)
            ·
              refine ⟨80903958773988832484284259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53935972515992554989522839 80903958773988832484284259)
              ·
                refine ⟨121355938160983248726426389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 80903958773988832484284259 121355938160983248726426389)
                ·
                  refine ⟨5688559601296089784051237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 121355938160983248726426389 5688559601296089784051237)
                  ·
                    refine ⟨1066604925243016834509607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5688559601296089784051237 1066604925243016834509607)
                    ·
                      rfl

theorem cell23_6231617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 1, 6, 4].length) (baseStart_6231617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6231617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6231617 prefixEnd_6231617 := by exact prefixLift 6231617
  have htrace : WordTrace (prefixWord ++ tailWord_6231617) baseStart_6231617 baseEnd_6231617 := by
    simpa [prefixWord, tailWord_6231617, baseEnd_6231617] using wordTrace_append hprefix tailTrace_6231617
  have hstable : (prefixWord ++ tailWord_6231617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6231617).length < 2 ^ (prefixWord ++ tailWord_6231617).sum := by decide
  have hdescent : baseEnd_6231617 < baseStart_6231617 := by decide
  rcases family_descends (prefixWord ++ tailWord_6231617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6231641 : List Nat := [1, 2, 1, 2, 2, 1, 1, 8, 1, 2, 2]
def baseStart_6231641 : Nat := 118140960795 + 6231641 * 2 ^ 59
def prefixEnd_6231641 : Nat := 4983230072969 + 3 ^ 40 * 6231641 * 2
def baseEnd_6231641 : Nat := 3199827099264758409628711

theorem tailTrace_6231641 : CollatzResearch.WordTrace tailWord_6231641 prefixEnd_6231641 3199827099264758409628711 := by
  unfold tailWord_6231641
  simp only [CollatzResearch.WordTrace]
  refine ⟨227286619616836411396286777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151524413077890940930857851 227286619616836411396286777)
  ·
    refine ⟨170464964712627308547215083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 227286619616836411396286777 170464964712627308547215083)
    ·
      refine ⟨255697447068940962820822625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170464964712627308547215083 255697447068940962820822625)
      ·
        refine ⟨191773085301705722115616969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 255697447068940962820822625 191773085301705722115616969)
        ·
          refine ⟨143829813976279291586712727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 191773085301705722115616969 143829813976279291586712727)
          ·
            refine ⟨215744720964418937380069091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 143829813976279291586712727 215744720964418937380069091)
            ·
              refine ⟨323617081446628406070103637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 215744720964418937380069091 323617081446628406070103637)
              ·
                refine ⟨3792387673202676633634027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 323617081446628406070103637 3792387673202676633634027)
                ·
                  refine ⟨5688581509804014950451041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3792387673202676633634027 5688581509804014950451041)
                  ·
                    refine ⟨4266436132353011212838281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5688581509804014950451041 4266436132353011212838281)
                    ·
                      refine ⟨3199827099264758409628711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4266436132353011212838281 3199827099264758409628711)
                      ·
                        rfl

theorem cell23_6231641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 8, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 8, 1, 2, 2].length) (baseStart_6231641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6231641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6231641 prefixEnd_6231641 := by exact prefixLift 6231641
  have htrace : WordTrace (prefixWord ++ tailWord_6231641) baseStart_6231641 baseEnd_6231641 := by
    simpa [prefixWord, tailWord_6231641, baseEnd_6231641] using wordTrace_append hprefix tailTrace_6231641
  have hstable : (prefixWord ++ tailWord_6231641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6231641).length < 2 ^ (prefixWord ++ tailWord_6231641).sum := by decide
  have hdescent : baseEnd_6231641 < baseStart_6231641 := by decide
  rcases family_descends (prefixWord ++ tailWord_6231641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6231651 : List Nat := [1, 1, 1, 5, 1, 5, 2, 1, 2, 4]
def baseStart_6231651 : Nat := 118140960795 + 6231651 * 2 ^ 59
def prefixEnd_6231651 : Nat := 4983230072969 + 3 ^ 40 * 6231651 * 2
def baseEnd_6231651 : Nat := 1066610744690434456834555

theorem tailTrace_6231651 : CollatzResearch.WordTrace tailWord_6231651 prefixEnd_6231651 1066610744690434456834555 := by
  unfold tailWord_6231651
  simp only [CollatzResearch.WordTrace]
  refine ⟨227286984346800183104150807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151524656231200122069433871 227286984346800183104150807)
  ·
    refine ⟨340930476520200274656226211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227286984346800183104150807 340930476520200274656226211)
    ·
      refine ⟨511395714780300411984339317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 340930476520200274656226211 511395714780300411984339317)
      ·
        refine ⟨47943348260653163623531811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 511395714780300411984339317 47943348260653163623531811)
        ·
          refine ⟨71915022390979745435297717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47943348260653163623531811 71915022390979745435297717)
          ·
            refine ⟨6742033349154351134559161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 71915022390979745435297717 6742033349154351134559161)
            ·
              refine ⟨5056525011865763350919371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6742033349154351134559161 5056525011865763350919371)
              ·
                refine ⟨7584787517798645026379057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5056525011865763350919371 7584787517798645026379057)
                ·
                  refine ⟨5688590638348983769784293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7584787517798645026379057 5688590638348983769784293)
                  ·
                    refine ⟨1066610744690434456834555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5688590638348983769784293 1066610744690434456834555)
                    ·
                      rfl

theorem cell23_6231651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 5, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 5, 2, 1, 2, 4].length) (baseStart_6231651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6231651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6231651 prefixEnd_6231651 := by exact prefixLift 6231651
  have htrace : WordTrace (prefixWord ++ tailWord_6231651) baseStart_6231651 baseEnd_6231651 := by
    simpa [prefixWord, tailWord_6231651, baseEnd_6231651] using wordTrace_append hprefix tailTrace_6231651
  have hstable : (prefixWord ++ tailWord_6231651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6231651).length < 2 ^ (prefixWord ++ tailWord_6231651).sum := by decide
  have hdescent : baseEnd_6231651 < baseStart_6231651 := by decide
  rcases family_descends (prefixWord ++ tailWord_6231651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6231754 : List Nat := [3, 1, 2, 1, 5, 1, 2, 1, 7]
def baseStart_6231754 : Nat := 118140960795 + 6231754 * 2 ^ 59
def prefixEnd_6231754 : Nat := 4983230072969 + 3 ^ 40 * 6231754 * 2
def baseEnd_6231754 : Nat := 355542791397635163057299

theorem tailTrace_6231754 : CollatzResearch.WordTrace tailWord_6231754 prefixEnd_6231754 355542791397635163057299 := by
  unfold tailWord_6231754
  simp only [CollatzResearch.WordTrace]
  refine ⟨56822685266356757923787579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151527160710284687796766877 56822685266356757923787579)
  ·
    refine ⟨85234027899535136885681369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56822685266356757923787579 85234027899535136885681369)
    ·
      refine ⟨63925520924651352664261027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85234027899535136885681369 63925520924651352664261027)
      ·
        refine ⟨95888281386977028996391541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63925520924651352664261027 95888281386977028996391541)
        ·
          refine ⟨8989526380029096468411707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 95888281386977028996391541 8989526380029096468411707)
          ·
            refine ⟨13484289570043644702617561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8989526380029096468411707 13484289570043644702617561)
            ·
              refine ⟨10113217177532733526963171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13484289570043644702617561 10113217177532733526963171)
              ·
                refine ⟨15169825766299100290444757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10113217177532733526963171 15169825766299100290444757)
                ·
                  refine ⟨355542791397635163057299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15169825766299100290444757 355542791397635163057299)
                  ·
                    rfl

theorem cell23_6231754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 2, 1, 7].length) (baseStart_6231754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6231754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6231754 prefixEnd_6231754 := by exact prefixLift 6231754
  have htrace : WordTrace (prefixWord ++ tailWord_6231754) baseStart_6231754 baseEnd_6231754 := by
    simpa [prefixWord, tailWord_6231754, baseEnd_6231754] using wordTrace_append hprefix tailTrace_6231754
  have hstable : (prefixWord ++ tailWord_6231754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6231754).length < 2 ^ (prefixWord ++ tailWord_6231754).sum := by decide
  have hdescent : baseEnd_6231754 < baseStart_6231754 := by decide
  rcases family_descends (prefixWord ++ tailWord_6231754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6231787 : List Nat := [1, 1, 1, 1, 2, 4, 4, 1, 1, 3, 4]
def baseStart_6231787 : Nat := 118140960795 + 6231787 * 2 ^ 59
def prefixEnd_6231787 : Nat := 4983230072969 + 3 ^ 40 * 6231787 * 2
def baseEnd_6231787 : Nat := 3199902067440314838403039

theorem tailTrace_6231787 : CollatzResearch.WordTrace tailWord_6231787 prefixEnd_6231787 3199902067440314838403039 := by
  unfold tailWord_6231787
  simp only [CollatzResearch.WordTrace]
  refine ⟨227291944674307478331101615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151527963116204985554067743 227291944674307478331101615)
  ·
    refine ⟨340937917011461217496652423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227291944674307478331101615 340937917011461217496652423)
    ·
      refine ⟨511406875517191826244978635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 340937917011461217496652423 511406875517191826244978635)
      ·
        refine ⟨767110313275787739367467953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 511406875517191826244978635 767110313275787739367467953)
        ·
          refine ⟨575332734956840804525600965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 767110313275787739367467953 575332734956840804525600965)
          ·
            refine ⟨107874887804407650848550181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 575332734956840804525600965 107874887804407650848550181)
            ·
              refine ⟨20226541463326434534103159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 107874887804407650848550181 20226541463326434534103159)
              ·
                refine ⟨30339812194989651801154739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20226541463326434534103159 30339812194989651801154739)
                ·
                  refine ⟨45509718292484477701732109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30339812194989651801154739 45509718292484477701732109)
                  ·
                    refine ⟨17066144359681679138149541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 45509718292484477701732109 17066144359681679138149541)
                    ·
                      refine ⟨3199902067440314838403039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17066144359681679138149541 3199902067440314838403039)
                      ·
                        rfl

theorem cell23_6231787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 4, 1, 1, 3, 4].length) (baseStart_6231787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6231787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6231787 prefixEnd_6231787 := by exact prefixLift 6231787
  have htrace : WordTrace (prefixWord ++ tailWord_6231787) baseStart_6231787 baseEnd_6231787 := by
    simpa [prefixWord, tailWord_6231787, baseEnd_6231787] using wordTrace_append hprefix tailTrace_6231787
  have hstable : (prefixWord ++ tailWord_6231787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6231787).length < 2 ^ (prefixWord ++ tailWord_6231787).sum := by decide
  have hdescent : baseEnd_6231787 < baseStart_6231787 := by decide
  rcases family_descends (prefixWord ++ tailWord_6231787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6231804 : List Nat := [2, 2, 2, 1, 3, 1, 3, 2, 2, 1, 4]
def baseStart_6231804 : Nat := 118140960795 + 6231804 * 2 ^ 59
def prefixEnd_6231804 : Nat := 4983230072969 + 3 ^ 40 * 6231804 * 2
def baseEnd_6231804 : Nat := 3199910796611441271890461

theorem tailTrace_6231804 : CollatzResearch.WordTrace tailWord_6231804 prefixEnd_6231804 3199910796611441271890461 := by
  unfold tailWord_6231804
  simp only [CollatzResearch.WordTrace]
  refine ⟨113646282357622945117235233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151528376476830593489646977 113646282357622945117235233)
  ·
    refine ⟨85234711768217208837926425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113646282357622945117235233 85234711768217208837926425)
    ·
      refine ⟨63926033826162906628444819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85234711768217208837926425 63926033826162906628444819)
      ·
        refine ⟨95889050739244359942667229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63926033826162906628444819 95889050739244359942667229)
        ·
          refine ⟨35958394027216634978500211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 95889050739244359942667229 35958394027216634978500211)
          ·
            refine ⟨53937591040824952467750317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35958394027216634978500211 53937591040824952467750317)
            ·
              refine ⟨20226596640309357175406369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53937591040824952467750317 20226596640309357175406369)
              ·
                refine ⟨15169947480232017881554777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20226596640309357175406369 15169947480232017881554777)
                ·
                  refine ⟨11377460610174013411166083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15169947480232017881554777 11377460610174013411166083)
                  ·
                    refine ⟨17066190915261020116749125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11377460610174013411166083 17066190915261020116749125)
                    ·
                      refine ⟨3199910796611441271890461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17066190915261020116749125 3199910796611441271890461)
                      ·
                        rfl

theorem cell23_6231804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 3, 2, 2, 1, 4].length) (baseStart_6231804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6231804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6231804 prefixEnd_6231804 := by exact prefixLift 6231804
  have htrace : WordTrace (prefixWord ++ tailWord_6231804) baseStart_6231804 baseEnd_6231804 := by
    simpa [prefixWord, tailWord_6231804, baseEnd_6231804] using wordTrace_append hprefix tailTrace_6231804
  have hstable : (prefixWord ++ tailWord_6231804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6231804).length < 2 ^ (prefixWord ++ tailWord_6231804).sum := by decide
  have hdescent : baseEnd_6231804 < baseStart_6231804 := by decide
  rcases family_descends (prefixWord ++ tailWord_6231804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6231841 : List Nat := [1, 2, 3, 2, 1, 4, 2, 1, 2, 2, 3]
def baseStart_6231841 : Nat := 118140960795 + 6231841 * 2 ^ 59
def prefixEnd_6231841 : Nat := 4983230072969 + 3 ^ 40 * 6231841 * 2
def baseEnd_6231841 : Nat := 3199929795395657627127791

theorem tailTrace_6231841 : CollatzResearch.WordTrace tailWord_6231841 prefixEnd_6231841 3199929795395657627127791 := by
  unfold tailWord_6231841
  simp only [CollatzResearch.WordTrace]
  refine ⟨227293914216111845553567377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151529276144074563702378251 227293914216111845553567377)
  ·
    refine ⟨170470435662083884165175533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 227293914216111845553567377 170470435662083884165175533)
    ·
      refine ⟨63926413373281456561940825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 170470435662083884165175533 63926413373281456561940825)
      ·
        refine ⟨47944810029961092421455619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63926413373281456561940825 47944810029961092421455619)
        ·
          refine ⟨71917215044941638632183429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47944810029961092421455619 71917215044941638632183429)
          ·
            refine ⟨13484477820926557243534393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 71917215044941638632183429 13484477820926557243534393)
            ·
              refine ⟨10113358365694917932650795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13484477820926557243534393 10113358365694917932650795)
              ·
                refine ⟨15170037548542376898976193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10113358365694917932650795 15170037548542376898976193)
                ·
                  refine ⟨11377528161406782674232145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15170037548542376898976193 11377528161406782674232145)
                  ·
                    refine ⟨8533146121055087005674109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11377528161406782674232145 8533146121055087005674109)
                    ·
                      refine ⟨3199929795395657627127791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8533146121055087005674109 3199929795395657627127791)
                      ·
                        rfl

theorem cell23_6231841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 2, 1, 2, 2, 3].length) (baseStart_6231841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6231841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6231841 prefixEnd_6231841 := by exact prefixLift 6231841
  have htrace : WordTrace (prefixWord ++ tailWord_6231841) baseStart_6231841 baseEnd_6231841 := by
    simpa [prefixWord, tailWord_6231841, baseEnd_6231841] using wordTrace_append hprefix tailTrace_6231841
  have hstable : (prefixWord ++ tailWord_6231841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6231841).length < 2 ^ (prefixWord ++ tailWord_6231841).sum := by decide
  have hdescent : baseEnd_6231841 < baseStart_6231841 := by decide
  rcases family_descends (prefixWord ++ tailWord_6231841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6231861 : List Nat := [1, 3, 3, 1, 4, 1, 2, 2, 6]
def baseStart_6231861 : Nat := 118140960795 + 6231861 * 2 ^ 59
def prefixEnd_6231861 : Nat := 4983230072969 + 3 ^ 40 * 6231861 * 2
def baseEnd_6231861 : Nat := 355548896112083060986411

theorem tailTrace_6231861 : CollatzResearch.WordTrace tailWord_6231861 prefixEnd_6231861 355548896112083060986411 := by
  unfold tailWord_6231861
  simp only [CollatzResearch.WordTrace]
  refine ⟨227294643676039388969295437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151529762450692925979530291 227294643676039388969295437)
  ·
    refine ⟨85235491378514770863485789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 227294643676039388969295437 85235491378514770863485789)
    ·
      refine ⟨31963309266943039073807171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85235491378514770863485789 31963309266943039073807171)
      ·
        refine ⟨47944963900414558610710757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31963309266943039073807171 47944963900414558610710757)
        ·
          refine ⟨8989680731327729739508267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 47944963900414558610710757 8989680731327729739508267)
          ·
            refine ⟨13484521096991594609262401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8989680731327729739508267 13484521096991594609262401)
            ·
              refine ⟨10113390822743695956946801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13484521096991594609262401 10113390822743695956946801)
              ·
                refine ⟨7585043117057771967710101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10113390822743695956946801 7585043117057771967710101)
                ·
                  refine ⟨355548896112083060986411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7585043117057771967710101 355548896112083060986411)
                  ·
                    rfl

theorem cell23_6231861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 2, 2, 6].length) (baseStart_6231861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6231861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6231861 prefixEnd_6231861 := by exact prefixLift 6231861
  have htrace : WordTrace (prefixWord ++ tailWord_6231861) baseStart_6231861 baseEnd_6231861 := by
    simpa [prefixWord, tailWord_6231861, baseEnd_6231861] using wordTrace_append hprefix tailTrace_6231861
  have hstable : (prefixWord ++ tailWord_6231861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6231861).length < 2 ^ (prefixWord ++ tailWord_6231861).sum := by decide
  have hdescent : baseEnd_6231861 < baseStart_6231861 := by decide
  rcases family_descends (prefixWord ++ tailWord_6231861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6231865 : List Nat := [1, 2, 1, 7, 1, 1, 1, 4, 1, 4]
def baseStart_6231865 : Nat := 118140960795 + 6231865 * 2 ^ 59
def prefixEnd_6231865 : Nat := 4983230072969 + 3 ^ 40 * 6231865 * 2
def baseEnd_6231865 : Nat := 1066647372977121844409227

theorem tailTrace_6231865 : CollatzResearch.WordTrace tailWord_6231865 prefixEnd_6231865 1066647372977121844409227 := by
  unfold tailWord_6231865
  simp only [CollatzResearch.WordTrace]
  refine ⟨227294789568024897652441049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151529859712016598434960699 227294789568024897652441049)
  ·
    refine ⟨170471092176018673239330787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 227294789568024897652441049 170471092176018673239330787)
    ·
      refine ⟨255706638264028009858996181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170471092176018673239330787 255706638264028009858996181)
      ·
        refine ⟨5993124334313156481070223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 255706638264028009858996181 5993124334313156481070223)
        ·
          refine ⟨8989686501469734721605335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5993124334313156481070223 8989686501469734721605335)
          ·
            refine ⟨13484529752204602082408003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8989686501469734721605335 13484529752204602082408003)
            ·
              refine ⟨20226794628306903123612005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13484529752204602082408003 20226794628306903123612005)
              ·
                refine ⟨3792523992807544335677251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20226794628306903123612005 3792523992807544335677251)
                ·
                  refine ⟨5688785989211316503515877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3792523992807544335677251 5688785989211316503515877)
                  ·
                    refine ⟨1066647372977121844409227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5688785989211316503515877 1066647372977121844409227)
                    ·
                      rfl

theorem cell23_6231865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 1, 4, 1, 4].length) (baseStart_6231865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6231865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6231865 prefixEnd_6231865 := by exact prefixLift 6231865
  have htrace : WordTrace (prefixWord ++ tailWord_6231865) baseStart_6231865 baseEnd_6231865 := by
    simpa [prefixWord, tailWord_6231865, baseEnd_6231865] using wordTrace_append hprefix tailTrace_6231865
  have hstable : (prefixWord ++ tailWord_6231865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6231865).length < 2 ^ (prefixWord ++ tailWord_6231865).sum := by decide
  have hdescent : baseEnd_6231865 < baseStart_6231865 := by decide
  rcases family_descends (prefixWord ++ tailWord_6231865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6231878 : List Nat := [6, 1, 1, 2, 1, 1, 2, 3, 6]
def baseStart_6231878 : Nat := 118140960795 + 6231878 * 2 ^ 59
def prefixEnd_6231878 : Nat := 4983230072969 + 3 ^ 40 * 6231878 * 2
def baseEnd_6231878 : Nat := 355549866019985998040569

theorem tailTrace_6231878 : CollatzResearch.WordTrace tailWord_6231878 prefixEnd_6231878 355549866019985998040569 := by
  unfold tailWord_6231878
  simp only [CollatzResearch.WordTrace]
  refine ⟨7102976991155556277270759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 151530175811318533915109525 7102976991155556277270759)
  ·
    refine ⟨10654465486733334415906139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7102976991155556277270759 10654465486733334415906139)
    ·
      refine ⟨15981698230100001623859209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10654465486733334415906139 15981698230100001623859209)
      ·
        refine ⟨11986273672575001217894407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15981698230100001623859209 11986273672575001217894407)
        ·
          refine ⟨17979410508862501826841611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11986273672575001217894407 17979410508862501826841611)
          ·
            refine ⟨26969115763293752740262417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17979410508862501826841611 26969115763293752740262417)
            ·
              refine ⟨20226836822470314555196813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26969115763293752740262417 20226836822470314555196813)
              ·
                refine ⟨7585063808426367958198805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20226836822470314555196813 7585063808426367958198805)
                ·
                  refine ⟨355549866019985998040569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7585063808426367958198805 355549866019985998040569)
                  ·
                    rfl

theorem cell23_6231878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 2, 3, 6].length) (baseStart_6231878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6231878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6231878 prefixEnd_6231878 := by exact prefixLift 6231878
  have htrace : WordTrace (prefixWord ++ tailWord_6231878) baseStart_6231878 baseEnd_6231878 := by
    simpa [prefixWord, tailWord_6231878, baseEnd_6231878] using wordTrace_append hprefix tailTrace_6231878
  have hstable : (prefixWord ++ tailWord_6231878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6231878).length < 2 ^ (prefixWord ++ tailWord_6231878).sum := by decide
  have hdescent : baseEnd_6231878 < baseStart_6231878 := by decide
  rcases family_descends (prefixWord ++ tailWord_6231878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6231904 : List Nat := [2, 1, 1, 3, 3, 2, 2, 2, 1, 6]
def baseStart_6231904 : Nat := 118140960795 + 6231904 * 2 ^ 59
def prefixEnd_6231904 : Nat := 4983230072969 + 3 ^ 40 * 6231904 * 2
def baseEnd_6231904 : Nat := 1066654048225630293546667

theorem tailTrace_6231904 : CollatzResearch.WordTrace tailWord_6231904 prefixEnd_6231904 1066654048225630293546667 := by
  unfold tailWord_6231904
  simp only [CollatzResearch.WordTrace]
  refine ⟨113648106007441803656555383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151530808009922404875407177 113648106007441803656555383)
  ·
    refine ⟨170472159011162705484833075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113648106007441803656555383 170472159011162705484833075)
    ·
      refine ⟨255708238516744058227249613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170472159011162705484833075 255708238516744058227249613)
      ·
        refine ⟨95890589443779021835218605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 255708238516744058227249613 95890589443779021835218605)
        ·
          refine ⟨35958971041417133188206977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 95890589443779021835218605 35958971041417133188206977)
          ·
            refine ⟨26969228281062849891155233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35958971041417133188206977 26969228281062849891155233)
            ·
              refine ⟨20226921210797137418366425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26969228281062849891155233 20226921210797137418366425)
              ·
                refine ⟨15170190908097853063774819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20226921210797137418366425 15170190908097853063774819)
                ·
                  refine ⟨22755286362146779595662229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15170190908097853063774819 22755286362146779595662229)
                  ·
                    refine ⟨1066654048225630293546667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22755286362146779595662229 1066654048225630293546667)
                    ·
                      rfl

theorem cell23_6231904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 2, 2, 1, 6].length) (baseStart_6231904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6231904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6231904 prefixEnd_6231904 := by exact prefixLift 6231904
  have htrace : WordTrace (prefixWord ++ tailWord_6231904) baseStart_6231904 baseEnd_6231904 := by
    simpa [prefixWord, tailWord_6231904, baseEnd_6231904] using wordTrace_append hprefix tailTrace_6231904
  have hstable : (prefixWord ++ tailWord_6231904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6231904).length < 2 ^ (prefixWord ++ tailWord_6231904).sum := by decide
  have hdescent : baseEnd_6231904 < baseStart_6231904 := by decide
  rcases family_descends (prefixWord ++ tailWord_6231904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6231911 : List Nat := [1, 1, 5, 1, 2, 1, 3, 3, 1, 1, 4]
def baseStart_6231911 : Nat := 118140960795 + 6231911 * 2 ^ 59
def prefixEnd_6231911 : Nat := 4983230072969 + 3 ^ 40 * 6231911 * 2
def baseEnd_6231911 : Nat := 3199965739041472353252469

theorem tailTrace_6231911 : CollatzResearch.WordTrace tailWord_6231911 prefixEnd_6231911 3199965739041472353252469 := by
  unfold tailWord_6231911
  simp only [CollatzResearch.WordTrace]
  refine ⟨227296467325858247508615587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151530978217238831672410391 227296467325858247508615587)
  ·
    refine ⟨340944700988787371262923381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227296467325858247508615587 340944700988787371262923381)
    ·
      refine ⟨31963565717698816055899067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 340944700988787371262923381 31963565717698816055899067)
      ·
        refine ⟨47945348576548224083848601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31963565717698816055899067 47945348576548224083848601)
        ·
          refine ⟨35959011432411168062886451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47945348576548224083848601 35959011432411168062886451)
          ·
            refine ⟨53938517148616752094329677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35959011432411168062886451 53938517148616752094329677)
            ·
              refine ⟨20226943930731282035373629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53938517148616752094329677 20226943930731282035373629)
              ·
                refine ⟨7585103974024230763265111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20226943930731282035373629 7585103974024230763265111)
                ·
                  refine ⟨11377655961036346144897667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7585103974024230763265111 11377655961036346144897667)
                  ·
                    refine ⟨17066483941554519217346501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11377655961036346144897667 17066483941554519217346501)
                    ·
                      refine ⟨3199965739041472353252469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17066483941554519217346501 3199965739041472353252469)
                      ·
                        rfl

theorem cell23_6231911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 3, 3, 1, 1, 4].length) (baseStart_6231911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6231911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6231911 prefixEnd_6231911 := by exact prefixLift 6231911
  have htrace : WordTrace (prefixWord ++ tailWord_6231911) baseStart_6231911 baseEnd_6231911 := by
    simpa [prefixWord, tailWord_6231911, baseEnd_6231911] using wordTrace_append hprefix tailTrace_6231911
  have hstable : (prefixWord ++ tailWord_6231911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6231911).length < 2 ^ (prefixWord ++ tailWord_6231911).sum := by decide
  have hdescent : baseEnd_6231911 < baseStart_6231911 := by decide
  rcases family_descends (prefixWord ++ tailWord_6231911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6231927 : List Nat := [1, 1, 3, 1, 1, 2, 1, 1, 1, 4, 7]
def baseStart_6231927 : Nat := 118140960795 + 6231927 * 2 ^ 59
def prefixEnd_6231927 : Nat := 4983230072969 + 3 ^ 40 * 6231927 * 2
def baseEnd_6231927 : Nat := 3199973954731944290652395

theorem tailTrace_6231927 : CollatzResearch.WordTrace tailWord_6231927 prefixEnd_6231927 3199973954731944290652395 := by
  unfold tailWord_6231927
  simp only [CollatzResearch.WordTrace]
  refine ⟨227297050893800282241198035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151531367262533521494132023 227297050893800282241198035)
  ·
    refine ⟨340945576340700423361797053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227297050893800282241198035 340945576340700423361797053)
    ·
      refine ⟨127854591127762658760673895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 340945576340700423361797053 127854591127762658760673895)
      ·
        refine ⟨191781886691643988141010843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127854591127762658760673895 191781886691643988141010843)
        ·
          refine ⟨287672830037465982211516265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 191781886691643988141010843 287672830037465982211516265)
          ·
            refine ⟨215754622528099486658637199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 287672830037465982211516265 215754622528099486658637199)
            ·
              refine ⟨323631933792149229987955799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 215754622528099486658637199 323631933792149229987955799)
              ·
                refine ⟨485447900688223844981933699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 323631933792149229987955799 485447900688223844981933699)
                ·
                  refine ⟨728171851032335767472900549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 485447900688223844981933699 728171851032335767472900549)
                  ·
                    refine ⟨136532222068562956401168853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 728171851032335767472900549 136532222068562956401168853)
                    ·
                      refine ⟨3199973954731944290652395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 136532222068562956401168853 3199973954731944290652395)
                      ·
                        rfl

theorem cell23_6231927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 1, 1, 4, 7].length) (baseStart_6231927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6231927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6231927 prefixEnd_6231927 := by exact prefixLift 6231927
  have htrace : WordTrace (prefixWord ++ tailWord_6231927) baseStart_6231927 baseEnd_6231927 := by
    simpa [prefixWord, tailWord_6231927, baseEnd_6231927] using wordTrace_append hprefix tailTrace_6231927
  have hstable : (prefixWord ++ tailWord_6231927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6231927).length < 2 ^ (prefixWord ++ tailWord_6231927).sum := by decide
  have hdescent : baseEnd_6231927 < baseStart_6231927 := by decide
  rcases family_descends (prefixWord ++ tailWord_6231927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6231961 : List Nat := [1, 2, 1, 2, 1, 3, 3, 2, 4, 1, 3]
def baseStart_6231961 : Nat := 118140960795 + 6231961 * 2 ^ 59
def prefixEnd_6231961 : Nat := 4983230072969 + 3 ^ 40 * 6231961 * 2
def baseEnd_6231961 : Nat := 3199991413074197157627239

theorem tailTrace_6231961 : CollatzResearch.WordTrace tailWord_6231961 prefixEnd_6231961 3199991413074197157627239 := by
  unfold tailWord_6231961
  simp only [CollatzResearch.WordTrace]
  refine ⟨227298290975677106047935737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151532193983784737365290491 227298290975677106047935737)
  ·
    refine ⟨170473718231757829535951803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 227298290975677106047935737 170473718231757829535951803)
    ·
      refine ⟨255710577347636744303927705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170473718231757829535951803 255710577347636744303927705)
      ·
        refine ⟨191782933010727558227945779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 255710577347636744303927705 191782933010727558227945779)
        ·
          refine ⟨287674399516091337341918669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 191782933010727558227945779 287674399516091337341918669)
          ·
            refine ⟨107877899818534251503219501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 287674399516091337341918669 107877899818534251503219501)
            ·
              refine ⟨40454212431950344313707313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 107877899818534251503219501 40454212431950344313707313)
              ·
                refine ⟨30340659323962758235280485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40454212431950344313707313 30340659323962758235280485)
                ·
                  refine ⟨5688873623243017169115091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30340659323962758235280485 5688873623243017169115091)
                  ·
                    refine ⟨8533310434864525753672637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5688873623243017169115091 8533310434864525753672637)
                    ·
                      refine ⟨3199991413074197157627239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8533310434864525753672637 3199991413074197157627239)
                      ·
                        rfl

theorem cell23_6231961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 3, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 3, 2, 4, 1, 3].length) (baseStart_6231961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6231961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6231961 prefixEnd_6231961 := by exact prefixLift 6231961
  have htrace : WordTrace (prefixWord ++ tailWord_6231961) baseStart_6231961 baseEnd_6231961 := by
    simpa [prefixWord, tailWord_6231961, baseEnd_6231961] using wordTrace_append hprefix tailTrace_6231961
  have hstable : (prefixWord ++ tailWord_6231961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6231961).length < 2 ^ (prefixWord ++ tailWord_6231961).sum := by decide
  have hdescent : baseEnd_6231961 < baseStart_6231961 := by decide
  rcases family_descends (prefixWord ++ tailWord_6231961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6231962 : List Nat := [3, 1, 1, 4, 2, 1, 3, 3, 1, 2, 2]
def baseStart_6231962 : Nat := 118140960795 + 6231962 * 2 ^ 59
def prefixEnd_6231962 : Nat := 4983230072969 + 3 ^ 40 * 6231962 * 2
def baseEnd_6231962 : Nat := 3199991926554851653714735

theorem tailTrace_6231962 : CollatzResearch.WordTrace tailWord_6231962 prefixEnd_6231962 3199991926554851653714735 := by
  unfold tailWord_6231962
  simp only [CollatzResearch.WordTrace]
  refine ⟨56824581862168370804680535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151532218299115655479148093 56824581862168370804680535)
  ·
    refine ⟨85236872793252556207020803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56824581862168370804680535 85236872793252556207020803)
    ·
      refine ⟨127855309189878834310531205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85236872793252556207020803 127855309189878834310531205)
      ·
        refine ⟨23972870473102281433224601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 127855309189878834310531205 23972870473102281433224601)
        ·
          refine ⟨17979652854826711074918451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23972870473102281433224601 17979652854826711074918451)
          ·
            refine ⟨26969479282240066612377677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17979652854826711074918451 26969479282240066612377677)
            ·
              refine ⟨10113554730840024979641629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26969479282240066612377677 10113554730840024979641629)
              ·
                refine ⟨3792583024065009367365611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10113554730840024979641629 3792583024065009367365611)
                ·
                  refine ⟨5688874536097514051048417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3792583024065009367365611 5688874536097514051048417)
                  ·
                    refine ⟨4266655902073135538286313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5688874536097514051048417 4266655902073135538286313)
                    ·
                      refine ⟨3199991926554851653714735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4266655902073135538286313 3199991926554851653714735)
                      ·
                        rfl

theorem cell23_6231962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 3, 3, 1, 2, 2].length) (baseStart_6231962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6231962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6231962 prefixEnd_6231962 := by exact prefixLift 6231962
  have htrace : WordTrace (prefixWord ++ tailWord_6231962) baseStart_6231962 baseEnd_6231962 := by
    simpa [prefixWord, tailWord_6231962, baseEnd_6231962] using wordTrace_append hprefix tailTrace_6231962
  have hstable : (prefixWord ++ tailWord_6231962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6231962).length < 2 ^ (prefixWord ++ tailWord_6231962).sum := by decide
  have hdescent : baseEnd_6231962 < baseStart_6231962 := by decide
  rcases family_descends (prefixWord ++ tailWord_6231962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6231971 : List Nat := [1, 1, 1, 4, 1, 2, 1, 2, 5, 3, 2]
def baseStart_6231971 : Nat := 118140960795 + 6231971 * 2 ^ 59
def prefixEnd_6231971 : Nat := 4983230072969 + 3 ^ 40 * 6231971 * 2
def baseEnd_6231971 : Nat := 3199996547880742118502193

theorem tailTrace_6231971 : CollatzResearch.WordTrace tailWord_6231971 prefixEnd_6231971 3199996547880742118502193 := by
  unfold tailWord_6231971
  simp only [CollatzResearch.WordTrace]
  refine ⟨227298655705640877755799767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151532437137093918503866511 227298655705640877755799767)
  ·
    refine ⟨340947983558461316633699651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227298655705640877755799767 340947983558461316633699651)
    ·
      refine ⟨511421975337691974950549477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 340947983558461316633699651 511421975337691974950549477)
      ·
        refine ⟨95891620375817245303228027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 511421975337691974950549477 95891620375817245303228027)
        ·
          refine ⟨143837430563725867954842041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95891620375817245303228027 143837430563725867954842041)
          ·
            refine ⟨107878072922794400966131531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 143837430563725867954842041 107878072922794400966131531)
            ·
              refine ⟨161817109384191601449197297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 107878072922794400966131531 161817109384191601449197297)
              ·
                refine ⟨121362832038143701086897973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 161817109384191601449197297 121362832038143701086897973)
                ·
                  refine ⟨11377765503575971976896685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 121362832038143701086897973 11377765503575971976896685)
                  ·
                    refine ⟨4266662063840989491336257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11377765503575971976896685 4266662063840989491336257)
                    ·
                      refine ⟨3199996547880742118502193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4266662063840989491336257 3199996547880742118502193)
                      ·
                        rfl

theorem cell23_6231971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 2, 5, 3, 2].length) (baseStart_6231971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6231971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6231971 prefixEnd_6231971 := by exact prefixLift 6231971
  have htrace : WordTrace (prefixWord ++ tailWord_6231971) baseStart_6231971 baseEnd_6231971 := by
    simpa [prefixWord, tailWord_6231971, baseEnd_6231971] using wordTrace_append hprefix tailTrace_6231971
  have hstable : (prefixWord ++ tailWord_6231971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6231971).length < 2 ^ (prefixWord ++ tailWord_6231971).sum := by decide
  have hdescent : baseEnd_6231971 < baseStart_6231971 := by decide
  rcases family_descends (prefixWord ++ tailWord_6231971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6232021 : List Nat := [1, 3, 2, 3, 2, 1, 2, 1, 2, 1, 5]
def baseStart_6232021 : Nat := 118140960795 + 6232021 * 2 ^ 59
def prefixEnd_6232021 : Nat := 4983230072969 + 3 ^ 40 * 6232021 * 2
def baseEnd_6232021 : Nat := 3200022221913466922876963

theorem tailTrace_6232021 : CollatzResearch.WordTrace tailWord_6232021 prefixEnd_6232021 3200022221913466922876963 := by
  unfold tailWord_6232021
  simp only [CollatzResearch.WordTrace]
  refine ⟨227300479355459736295119917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151533652903639824196746611 227300479355459736295119917)
  ·
    refine ⟨85237679758297401110669969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 227300479355459736295119917 85237679758297401110669969)
    ·
      refine ⟨63928259818723050833002477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85237679758297401110669969 63928259818723050833002477)
      ·
        refine ⟨23973097432021144062375929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63928259818723050833002477 23973097432021144062375929)
        ·
          refine ⟨17979823074015858046781947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23973097432021144062375929 17979823074015858046781947)
          ·
            refine ⟨26969734611023787070172921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17979823074015858046781947 26969734611023787070172921)
            ·
              refine ⟨20227300958267840302629691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26969734611023787070172921 20227300958267840302629691)
              ·
                refine ⟨30340951437401760453944537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20227300958267840302629691 30340951437401760453944537)
                ·
                  refine ⟨22755713578051320340458403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30340951437401760453944537 22755713578051320340458403)
                  ·
                    refine ⟨34133570367076980510687605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22755713578051320340458403 34133570367076980510687605)
                    ·
                      refine ⟨3200022221913466922876963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34133570367076980510687605 3200022221913466922876963)
                      ·
                        rfl

theorem cell23_6232021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 2, 1, 2, 1, 5].length) (baseStart_6232021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6232021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6232021 prefixEnd_6232021 := by exact prefixLift 6232021
  have htrace : WordTrace (prefixWord ++ tailWord_6232021) baseStart_6232021 baseEnd_6232021 := by
    simpa [prefixWord, tailWord_6232021, baseEnd_6232021] using wordTrace_append hprefix tailTrace_6232021
  have hstable : (prefixWord ++ tailWord_6232021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6232021).length < 2 ^ (prefixWord ++ tailWord_6232021).sum := by decide
  have hdescent : baseEnd_6232021 < baseStart_6232021 := by decide
  rcases family_descends (prefixWord ++ tailWord_6232021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6232035 : List Nat := [1, 1, 1, 6, 1, 2, 1, 4, 2, 2, 2]
def baseStart_6232035 : Nat := 118140960795 + 6232035 * 2 ^ 59
def prefixEnd_6232035 : Nat := 4983230072969 + 3 ^ 40 * 6232035 * 2
def baseEnd_6232035 : Nat := 3200029410642629868101899

theorem tailTrace_6232035 : CollatzResearch.WordTrace tailWord_6232035 prefixEnd_6232035 3200029410642629868101899 := by
  unfold tailWord_6232035
  simp only [CollatzResearch.WordTrace]
  refine ⟨227300989977409016686129559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151533993318272677790753039 227300989977409016686129559)
  ·
    refine ⟨340951484966113525029194339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227300989977409016686129559 340951484966113525029194339)
    ·
      refine ⟨511427227449170287543791509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 340951484966113525029194339 511427227449170287543791509)
      ·
        refine ⟨23973151286679857228615227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 511427227449170287543791509 23973151286679857228615227)
        ·
          refine ⟨35959726930019785842922841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23973151286679857228615227 35959726930019785842922841)
          ·
            refine ⟨26969795197514839382192131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35959726930019785842922841 26969795197514839382192131)
            ·
              refine ⟨40454692796272259073288197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26969795197514839382192131 40454692796272259073288197)
              ·
                refine ⟨7585254899301048576241537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40454692796272259073288197 7585254899301048576241537)
                ·
                  refine ⟨5688941174475786432181153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7585254899301048576241537 5688941174475786432181153)
                  ·
                    refine ⟨4266705880856839824135865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5688941174475786432181153 4266705880856839824135865)
                    ·
                      refine ⟨3200029410642629868101899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4266705880856839824135865 3200029410642629868101899)
                      ·
                        rfl

theorem cell23_6232035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 1, 4, 2, 2, 2].length) (baseStart_6232035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6232035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6232035 prefixEnd_6232035 := by exact prefixLift 6232035
  have htrace : WordTrace (prefixWord ++ tailWord_6232035) baseStart_6232035 baseEnd_6232035 := by
    simpa [prefixWord, tailWord_6232035, baseEnd_6232035] using wordTrace_append hprefix tailTrace_6232035
  have hstable : (prefixWord ++ tailWord_6232035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6232035).length < 2 ^ (prefixWord ++ tailWord_6232035).sum := by decide
  have hdescent : baseEnd_6232035 < baseStart_6232035 := by decide
  rcases family_descends (prefixWord ++ tailWord_6232035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6232064 : List Nat := [2, 1, 1, 2, 1, 1, 1, 4, 3, 2, 5]
def baseStart_6232064 : Nat := 118140960795 + 6232064 * 2 ^ 59
def prefixEnd_6232064 : Nat := 4983230072969 + 3 ^ 40 * 6232064 * 2
def baseEnd_6232064 : Nat := 3200044301581610254639265

theorem tailTrace_6232064 : CollatzResearch.WordTrace tailWord_6232064 prefixEnd_6232064 3200044301581610254639265 := by
  unfold tailWord_6232064
  simp only [CollatzResearch.WordTrace]
  refine ⟨113651023847151977319467623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151534698462869303092623497 113651023847151977319467623)
  ·
    refine ⟨170476535770727965979201435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113651023847151977319467623 170476535770727965979201435)
    ·
      refine ⟨255714803656091948968802153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170476535770727965979201435 255714803656091948968802153)
      ·
        refine ⟨191786102742068961726601615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 255714803656091948968802153 191786102742068961726601615)
        ·
          refine ⟨287679154113103442589902423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 191786102742068961726601615 287679154113103442589902423)
          ·
            refine ⟨431518731169655163884853635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 287679154113103442589902423 431518731169655163884853635)
            ·
              refine ⟨647278096754482745827280453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 431518731169655163884853635 647278096754482745827280453)
              ·
                refine ⟨121364643141465514842615085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 647278096754482745827280453 121364643141465514842615085)
                ·
                  refine ⟨45511741178049568065980657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 121364643141465514842615085 45511741178049568065980657)
                  ·
                    refine ⟨34133805883537176049485493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 45511741178049568065980657 34133805883537176049485493)
                    ·
                      refine ⟨3200044301581610254639265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34133805883537176049485493 3200044301581610254639265)
                      ·
                        rfl

theorem cell23_6232064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 4, 3, 2, 5].length) (baseStart_6232064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6232064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6232064 prefixEnd_6232064 := by exact prefixLift 6232064
  have htrace : WordTrace (prefixWord ++ tailWord_6232064) baseStart_6232064 baseEnd_6232064 := by
    simpa [prefixWord, tailWord_6232064, baseEnd_6232064] using wordTrace_append hprefix tailTrace_6232064
  have hstable : (prefixWord ++ tailWord_6232064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6232064).length < 2 ^ (prefixWord ++ tailWord_6232064).sum := by decide
  have hdescent : baseEnd_6232064 < baseStart_6232064 := by decide
  rcases family_descends (prefixWord ++ tailWord_6232064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6232071 : List Nat := [1, 1, 4, 3, 1, 3, 1, 1, 1, 7]
def baseStart_6232071 : Nat := 118140960795 + 6232071 * 2 ^ 59
def prefixEnd_6232071 : Nat := 4983230072969 + 3 ^ 40 * 6232071 * 2
def baseEnd_6232071 : Nat := 1066682631982063909083911

theorem tailTrace_6232071 : CollatzResearch.WordTrace tailWord_6232071 prefixEnd_6232071 1066682631982063909083911 := by
  unfold tailWord_6232071
  simp only [CollatzResearch.WordTrace]
  refine ⟨227302303005278594834440067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151534868670185729889626711 227302303005278594834440067)
  ·
    refine ⟨340953454507917892251660101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227302303005278594834440067 340953454507917892251660101)
    ·
      refine ⟨63928772720234604797186269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 340953454507917892251660101 63928772720234604797186269)
      ·
        refine ⟨23973289770087976798944851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63928772720234604797186269 23973289770087976798944851)
        ·
          refine ⟨35959934655131965198417277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23973289770087976798944851 35959934655131965198417277)
          ·
            refine ⟨13484975495674486949406479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35959934655131965198417277 13484975495674486949406479)
            ·
              refine ⟨20227463243511730424109719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13484975495674486949406479 20227463243511730424109719)
              ·
                refine ⟨30341194865267595636164579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20227463243511730424109719 30341194865267595636164579)
                ·
                  refine ⟨45511792297901393454246869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30341194865267595636164579 45511792297901393454246869)
                  ·
                    refine ⟨1066682631982063909083911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 45511792297901393454246869 1066682631982063909083911)
                    ·
                      rfl

theorem cell23_6232071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 1, 1, 1, 7].length) (baseStart_6232071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6232071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6232071 prefixEnd_6232071 := by exact prefixLift 6232071
  have htrace : WordTrace (prefixWord ++ tailWord_6232071) baseStart_6232071 baseEnd_6232071 := by
    simpa [prefixWord, tailWord_6232071, baseEnd_6232071] using wordTrace_append hprefix tailTrace_6232071
  have hstable : (prefixWord ++ tailWord_6232071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6232071).length < 2 ^ (prefixWord ++ tailWord_6232071).sum := by decide
  have hdescent : baseEnd_6232071 < baseStart_6232071 := by decide
  rcases family_descends (prefixWord ++ tailWord_6232071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6232111 : List Nat := [1, 1, 2, 1, 2, 1, 1, 3, 6, 2, 3]
def baseStart_6232111 : Nat := 118140960795 + 6232111 * 2 ^ 59
def prefixEnd_6232111 : Nat := 4983230072969 + 3 ^ 40 * 6232111 * 2
def baseEnd_6232111 : Nat := 3200068435172371570751549

theorem tailTrace_6232111 : CollatzResearch.WordTrace tailWord_6232111 prefixEnd_6232111 3200068435172371570751549 := by
  unfold tailWord_6232111
  simp only [CollatzResearch.WordTrace]
  refine ⟨227303761925133681665896187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151535841283422454443930791 227303761925133681665896187)
  ·
    refine ⟨340955642887700522498844281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227303761925133681665896187 340955642887700522498844281)
    ·
      refine ⟨255716732165775391874133211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 340955642887700522498844281 255716732165775391874133211)
      ·
        refine ⟨383575098248663087811199817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 255716732165775391874133211 383575098248663087811199817)
        ·
          refine ⟨287681323686497315858399863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 383575098248663087811199817 287681323686497315858399863)
          ·
            refine ⟨431521985529745973787599795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 287681323686497315858399863 431521985529745973787599795)
            ·
              refine ⟨647282978294618960681399693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 431521985529745973787599795 647282978294618960681399693)
              ·
                refine ⟨242731116860482110255524885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 647282978294618960681399693 242731116860482110255524885)
                ·
                  refine ⟨11378021102835098918227729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 242731116860482110255524885 11378021102835098918227729)
                  ·
                    refine ⟨8533515827126324188670797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11378021102835098918227729 8533515827126324188670797)
                    ·
                      refine ⟨3200068435172371570751549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8533515827126324188670797 3200068435172371570751549)
                      ·
                        rfl

theorem cell23_6232111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 3, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 3, 6, 2, 3].length) (baseStart_6232111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6232111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6232111 prefixEnd_6232111 := by exact prefixLift 6232111
  have htrace : WordTrace (prefixWord ++ tailWord_6232111) baseStart_6232111 baseEnd_6232111 := by
    simpa [prefixWord, tailWord_6232111, baseEnd_6232111] using wordTrace_append hprefix tailTrace_6232111
  have hstable : (prefixWord ++ tailWord_6232111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6232111).length < 2 ^ (prefixWord ++ tailWord_6232111).sum := by decide
  have hdescent : baseEnd_6232111 < baseStart_6232111 := by decide
  rcases family_descends (prefixWord ++ tailWord_6232111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6232152 : List Nat := [2, 1, 2, 2, 1, 5, 3, 2, 1, 4]
def baseStart_6232152 : Nat := 118140960795 + 6232152 * 2 ^ 59
def prefixEnd_6232152 : Nat := 4983230072969 + 3 ^ 40 * 6232152 * 2
def baseEnd_6232152 : Nat := 1066696495959735303446287

theorem tailTrace_6232152 : CollatzResearch.WordTrace tailWord_6232152 prefixEnd_6232152 1066696495959735303446287 := by
  unfold tailWord_6232152
  simp only [CollatzResearch.WordTrace]
  refine ⟨113652628658992572834069355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151536838211990097112092473 113652628658992572834069355)
  ·
    refine ⟨170478942988488859251104033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113652628658992572834069355 170478942988488859251104033)
    ·
      refine ⟨127859207241366644438328025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 170478942988488859251104033 127859207241366644438328025)
      ·
        refine ⟨95894405431024983328746019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 127859207241366644438328025 95894405431024983328746019)
        ·
          refine ⟨143841608146537474993119029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95894405431024983328746019 143841608146537474993119029)
          ·
            refine ⟨13485150763737888280604909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 143841608146537474993119029 13485150763737888280604909)
            ·
              refine ⟨5056931536401708105226841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13485150763737888280604909 5056931536401708105226841)
              ·
                refine ⟨3792698652301281078920131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5056931536401708105226841 3792698652301281078920131)
                ·
                  refine ⟨5689047978451921618380197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3792698652301281078920131 5689047978451921618380197)
                  ·
                    refine ⟨1066696495959735303446287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5689047978451921618380197 1066696495959735303446287)
                    ·
                      rfl

theorem cell23_6232152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 3, 2, 1, 4].length) (baseStart_6232152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6232152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6232152 prefixEnd_6232152 := by exact prefixLift 6232152
  have htrace : WordTrace (prefixWord ++ tailWord_6232152) baseStart_6232152 baseEnd_6232152 := by
    simpa [prefixWord, tailWord_6232152, baseEnd_6232152] using wordTrace_append hprefix tailTrace_6232152
  have hstable : (prefixWord ++ tailWord_6232152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6232152).length < 2 ^ (prefixWord ++ tailWord_6232152).sum := by decide
  have hdescent : baseEnd_6232152 < baseStart_6232152 := by decide
  rcases family_descends (prefixWord ++ tailWord_6232152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6232161 : List Nat := [1, 2, 3, 1, 1, 2, 1, 4, 3, 5]
def baseStart_6232161 : Nat := 118140960795 + 6232161 * 2 ^ 59
def prefixEnd_6232161 : Nat := 4983230072969 + 3 ^ 40 * 6232161 * 2
def baseEnd_6232161 : Nat := 1066698036401698791708773

theorem tailTrace_6232161 : CollatzResearch.WordTrace tailWord_6232161 prefixEnd_6232161 1066698036401698791708773 := by
  unfold tailWord_6232161
  simp only [CollatzResearch.WordTrace]
  refine ⟨227305585574952540205216337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151537057049968360136810891 227305585574952540205216337)
  ·
    refine ⟨170479189181214405153912253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 227305585574952540205216337 170479189181214405153912253)
    ·
      refine ⟨63929695942955401932717095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 170479189181214405153912253 63929695942955401932717095)
      ·
        refine ⟨95894543914433102899075643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63929695942955401932717095 95894543914433102899075643)
        ·
          refine ⟨143841815871649654348613465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95894543914433102899075643 143841815871649654348613465)
          ·
            refine ⟨107881361903737240761460099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 143841815871649654348613465 107881361903737240761460099)
            ·
              refine ⟨161822042855605861142190149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 107881361903737240761460099 161822042855605861142190149)
              ·
                refine ⟨30341633035426098964160653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 161822042855605861142190149 30341633035426098964160653)
                ·
                  refine ⟨11378112388284787111560245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30341633035426098964160653 11378112388284787111560245)
                  ·
                    refine ⟨1066698036401698791708773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11378112388284787111560245 1066698036401698791708773)
                    ·
                      rfl

theorem cell23_6232161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 4, 3, 5].length) (baseStart_6232161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6232161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6232161 prefixEnd_6232161 := by exact prefixLift 6232161
  have htrace : WordTrace (prefixWord ++ tailWord_6232161) baseStart_6232161 baseEnd_6232161 := by
    simpa [prefixWord, tailWord_6232161, baseEnd_6232161] using wordTrace_append hprefix tailTrace_6232161
  have hstable : (prefixWord ++ tailWord_6232161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6232161).length < 2 ^ (prefixWord ++ tailWord_6232161).sum := by decide
  have hdescent : baseEnd_6232161 < baseStart_6232161 := by decide
  rcases family_descends (prefixWord ++ tailWord_6232161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6232165 : List Nat := [1, 3, 1, 3, 2, 4, 2, 1, 6]
def baseStart_6232165 : Nat := 118140960795 + 6232165 * 2 ^ 59
def prefixEnd_6232165 : Nat := 4983230072969 + 3 ^ 40 * 6232165 * 2
def baseEnd_6232165 : Nat := 355566240347523817719589

theorem tailTrace_6232165 : CollatzResearch.WordTrace tailWord_6232165 prefixEnd_6232165 355566240347523817719589 := by
  unfold tailWord_6232165
  simp only [CollatzResearch.WordTrace]
  refine ⟨227305731466938048888361949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151537154311292032592241299 227305731466938048888361949)
  ·
    refine ⟨85239649300101768333135731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 227305731466938048888361949 85239649300101768333135731)
    ·
      refine ⟨127859473950152652499703597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85239649300101768333135731 127859473950152652499703597)
      ·
        refine ⟨47947302731307244687388849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 127859473950152652499703597 47947302731307244687388849)
        ·
          refine ⟨35960477048480433515541637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47947302731307244687388849 35960477048480433515541637)
          ·
            refine ⟨6742589446590081284164057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35960477048480433515541637 6742589446590081284164057)
            ·
              refine ⟨5056942084942560963123043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6742589446590081284164057 5056942084942560963123043)
              ·
                refine ⟨7585413127413841444684565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5056942084942560963123043 7585413127413841444684565)
                ·
                  refine ⟨355566240347523817719589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7585413127413841444684565 355566240347523817719589)
                  ·
                    rfl

theorem cell23_6232165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 4, 2, 1, 6].length) (baseStart_6232165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6232165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6232165 prefixEnd_6232165 := by exact prefixLift 6232165
  have htrace : WordTrace (prefixWord ++ tailWord_6232165) baseStart_6232165 baseEnd_6232165 := by
    simpa [prefixWord, tailWord_6232165, baseEnd_6232165] using wordTrace_append hprefix tailTrace_6232165
  have hstable : (prefixWord ++ tailWord_6232165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6232165).length < 2 ^ (prefixWord ++ tailWord_6232165).sum := by decide
  have hdescent : baseEnd_6232165 < baseStart_6232165 := by decide
  rcases family_descends (prefixWord ++ tailWord_6232165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6232178 : List Nat := [3, 2, 1, 2, 2, 3, 1, 1, 3, 5]
def baseStart_6232178 : Nat := 118140960795 + 6232178 * 2 ^ 59
def prefixEnd_6232178 : Nat := 4983230072969 + 3 ^ 40 * 6232178 * 2
def baseEnd_6232178 : Nat := 1066700946125407602871247

theorem tailTrace_6232178 : CollatzResearch.WordTrace tailWord_6232178 prefixEnd_6232178 1066700946125407602871247 := by
  unfold tailWord_6232178
  simp only [CollatzResearch.WordTrace]
  refine ⟨56826551403972738027146297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151537470410593968072390125 56826551403972738027146297)
  ·
    refine ⟨42619913552979553520359723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56826551403972738027146297 42619913552979553520359723)
    ·
      refine ⟨63929870329469330280539585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42619913552979553520359723 63929870329469330280539585)
      ·
        refine ⟨47947402747101997710404689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63929870329469330280539585 47947402747101997710404689)
        ·
          refine ⟨35960552060326498282803517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47947402747101997710404689 35960552060326498282803517)
          ·
            refine ⟨13485207022622436856051319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35960552060326498282803517 13485207022622436856051319)
            ·
              refine ⟨20227810533933655284076979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13485207022622436856051319 20227810533933655284076979)
              ·
                refine ⟨30341715800900482926115469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20227810533933655284076979 30341715800900482926115469)
                ·
                  refine ⟨11378143425337681097293301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30341715800900482926115469 11378143425337681097293301)
                  ·
                    refine ⟨1066700946125407602871247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11378143425337681097293301 1066700946125407602871247)
                    ·
                      rfl

theorem cell23_6232178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 1, 1, 3, 5].length) (baseStart_6232178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6232178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6232178 prefixEnd_6232178 := by exact prefixLift 6232178
  have htrace : WordTrace (prefixWord ++ tailWord_6232178) baseStart_6232178 baseEnd_6232178 := by
    simpa [prefixWord, tailWord_6232178, baseEnd_6232178] using wordTrace_append hprefix tailTrace_6232178
  have hstable : (prefixWord ++ tailWord_6232178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6232178).length < 2 ^ (prefixWord ++ tailWord_6232178).sum := by decide
  have hdescent : baseEnd_6232178 < baseStart_6232178 := by decide
  rcases family_descends (prefixWord ++ tailWord_6232178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6232185 : List Nat := [1, 2, 1, 3, 4, 1, 1, 3, 2, 3, 2]
def baseStart_6232185 : Nat := 118140960795 + 6232185 * 2 ^ 59
def prefixEnd_6232185 : Nat := 4983230072969 + 3 ^ 40 * 6232185 * 2
def baseEnd_6232185 : Nat := 3200106432740804281226209

theorem tailTrace_6232185 : CollatzResearch.WordTrace tailWord_6232185 prefixEnd_6232185 3200106432740804281226209 := by
  unfold tailWord_6232185
  simp only [CollatzResearch.WordTrace]
  refine ⟨227306460926865592304090009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151537640617910394869393339 227306460926865592304090009)
  ·
    refine ⟨170479845695149194228067507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 227306460926865592304090009 170479845695149194228067507)
    ·
      refine ⟨255719768542723791342101261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170479845695149194228067507 255719768542723791342101261)
      ·
        refine ⟨95894913203521421753287973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 255719768542723791342101261 95894913203521421753287973)
        ·
          refine ⟨17980296225660266578741495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 95894913203521421753287973 17980296225660266578741495)
          ·
            refine ⟨26970444338490399868112243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17980296225660266578741495 26970444338490399868112243)
            ·
              refine ⟨40455666507735599802168365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26970444338490399868112243 40455666507735599802168365)
              ·
                refine ⟨15170874940400849925813137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40455666507735599802168365 15170874940400849925813137)
                ·
                  refine ⟨11378156205300637444359853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15170874940400849925813137 11378156205300637444359853)
                  ·
                    refine ⟨4266808576987739041634945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11378156205300637444359853 4266808576987739041634945)
                    ·
                      refine ⟨3200106432740804281226209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4266808576987739041634945 3200106432740804281226209)
                      ·
                        rfl

theorem cell23_6232185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 1, 3, 2, 3, 2].length) (baseStart_6232185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6232185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6232185 prefixEnd_6232185 := by exact prefixLift 6232185
  have htrace : WordTrace (prefixWord ++ tailWord_6232185) baseStart_6232185 baseEnd_6232185 := by
    simpa [prefixWord, tailWord_6232185, baseEnd_6232185] using wordTrace_append hprefix tailTrace_6232185
  have hstable : (prefixWord ++ tailWord_6232185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6232185).length < 2 ^ (prefixWord ++ tailWord_6232185).sum := by decide
  have hdescent : baseEnd_6232185 < baseStart_6232185 := by decide
  rcases family_descends (prefixWord ++ tailWord_6232185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6232195 : List Nat := [1, 1, 1, 3, 3, 4, 3, 1, 1, 5]
def baseStart_6232195 : Nat := 118140960795 + 6232195 * 2 ^ 59
def prefixEnd_6232195 : Nat := 4983230072969 + 3 ^ 40 * 6232195 * 2
def baseEnd_6232195 : Nat := 1066703855849116414033721

theorem tailTrace_6232195 : CollatzResearch.WordTrace tailWord_6232195 prefixEnd_6232195 1066703855849116414033721 := by
  unfold tailWord_6232195
  simp only [CollatzResearch.WordTrace]
  refine ⟨227306825656829364011954039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151537883771219576007969359 227306825656829364011954039)
  ·
    refine ⟨340960238485244046017931059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227306825656829364011954039 340960238485244046017931059)
    ·
      refine ⟨511440357727866069026896589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 340960238485244046017931059 511440357727866069026896589)
      ·
        refine ⟨191790134147949775885086221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 511440357727866069026896589 191790134147949775885086221)
        ·
          refine ⟨71921300305481165956907333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 191790134147949775885086221 71921300305481165956907333)
          ·
            refine ⟨13485243807277718616920125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 71921300305481165956907333 13485243807277718616920125)
            ·
              refine ⟨5056966427729144481345047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13485243807277718616920125 5056966427729144481345047)
              ·
                refine ⟨7585449641593716722017571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5056966427729144481345047 7585449641593716722017571)
                ·
                  refine ⟨11378174462390575083026357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7585449641593716722017571 11378174462390575083026357)
                  ·
                    refine ⟨1066703855849116414033721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11378174462390575083026357 1066703855849116414033721)
                    ·
                      rfl

theorem cell23_6232195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 3, 1, 1, 5].length) (baseStart_6232195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6232195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6232195 prefixEnd_6232195 := by exact prefixLift 6232195
  have htrace : WordTrace (prefixWord ++ tailWord_6232195) baseStart_6232195 baseEnd_6232195 := by
    simpa [prefixWord, tailWord_6232195, baseEnd_6232195] using wordTrace_append hprefix tailTrace_6232195
  have hstable : (prefixWord ++ tailWord_6232195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6232195).length < 2 ^ (prefixWord ++ tailWord_6232195).sum := by decide
  have hdescent : baseEnd_6232195 < baseStart_6232195 := by decide
  rcases family_descends (prefixWord ++ tailWord_6232195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6232211 : List Nat := [1, 1, 1, 2, 1, 2, 3, 1, 5, 2, 4]
def baseStart_6232211 : Nat := 118140960795 + 6232211 * 2 ^ 59
def prefixEnd_6232211 : Nat := 4983230072969 + 3 ^ 40 * 6232211 * 2
def baseEnd_6232211 : Nat := 3200119783237821179501089

theorem tailTrace_6232211 : CollatzResearch.WordTrace tailWord_6232211 prefixEnd_6232211 3200119783237821179501089 := by
  unfold tailWord_6232211
  simp only [CollatzResearch.WordTrace]
  refine ⟨227307409224771398744536487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151538272816514265829690991 227307409224771398744536487)
  ·
    refine ⟨340961113837157098116804731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227307409224771398744536487 340961113837157098116804731)
    ·
      refine ⟨511441670755735647175207097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 340961113837157098116804731 511441670755735647175207097)
      ·
        refine ⟨383581253066801735381405323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 511441670755735647175207097 383581253066801735381405323)
        ·
          refine ⟨575371879600202603072107985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 383581253066801735381405323 575371879600202603072107985)
          ·
            refine ⟨431528909700151952304080989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 575371879600202603072107985 431528909700151952304080989)
            ·
              refine ⟨161823341137556982114030371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 431528909700151952304080989 161823341137556982114030371)
              ·
                refine ⟨242735011706335473171045557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 161823341137556982114030371 242735011706335473171045557)
                ·
                  refine ⟨22756407347468950609785521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 242735011706335473171045557 22756407347468950609785521)
                  ·
                    refine ⟨17067305510601712957339141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22756407347468950609785521 17067305510601712957339141)
                    ·
                      refine ⟨3200119783237821179501089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17067305510601712957339141 3200119783237821179501089)
                      ·
                        rfl

theorem cell23_6232211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 1, 5, 2, 4].length) (baseStart_6232211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6232211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6232211 prefixEnd_6232211 := by exact prefixLift 6232211
  have htrace : WordTrace (prefixWord ++ tailWord_6232211) baseStart_6232211 baseEnd_6232211 := by
    simpa [prefixWord, tailWord_6232211, baseEnd_6232211] using wordTrace_append hprefix tailTrace_6232211
  have hstable : (prefixWord ++ tailWord_6232211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6232211).length < 2 ^ (prefixWord ++ tailWord_6232211).sum := by decide
  have hdescent : baseEnd_6232211 < baseStart_6232211 := by decide
  rcases family_descends (prefixWord ++ tailWord_6232211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6232225 : List Nat := [1, 2, 3, 3, 1, 2, 2, 3, 2, 4]
def baseStart_6232225 : Nat := 118140960795 + 6232225 * 2 ^ 59
def prefixEnd_6232225 : Nat := 4983230072969 + 3 ^ 40 * 6232225 * 2
def baseEnd_6232225 : Nat := 1066708990655661374908675

theorem tailTrace_6232225 : CollatzResearch.WordTrace tailWord_6232225 prefixEnd_6232225 1066708990655661374908675 := by
  unfold tailWord_6232225
  simp only [CollatzResearch.WordTrace]
  refine ⟨227307919846720679135546129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151538613231147119423697419 227307919846720679135546129)
  ·
    refine ⟨170480939885040509351659597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 227307919846720679135546129 170480939885040509351659597)
    ·
      refine ⟨63930352456890191006872349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 170480939885040509351659597 63930352456890191006872349)
      ·
        refine ⟨23973882171333821627577131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63930352456890191006872349 23973882171333821627577131)
        ·
          refine ⟨35960823257000732441365697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23973882171333821627577131 35960823257000732441365697)
          ·
            refine ⟨26970617442750549331024273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35960823257000732441365697 26970617442750549331024273)
            ·
              refine ⟨20227963082062911998268205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26970617442750549331024273 20227963082062911998268205)
              ·
                refine ⟨7585486155773591999350577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20227963082062911998268205 7585486155773591999350577)
                ·
                  refine ⟨5689114616830193999512933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7585486155773591999350577 5689114616830193999512933)
                  ·
                    refine ⟨1066708990655661374908675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5689114616830193999512933 1066708990655661374908675)
                    ·
                      rfl

theorem cell23_6232225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 2, 3, 2, 4].length) (baseStart_6232225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6232225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6232225 prefixEnd_6232225 := by exact prefixLift 6232225
  have htrace : WordTrace (prefixWord ++ tailWord_6232225) baseStart_6232225 baseEnd_6232225 := by
    simpa [prefixWord, tailWord_6232225, baseEnd_6232225] using wordTrace_append hprefix tailTrace_6232225
  have hstable : (prefixWord ++ tailWord_6232225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6232225).length < 2 ^ (prefixWord ++ tailWord_6232225).sum := by decide
  have hdescent : baseEnd_6232225 < baseStart_6232225 := by decide
  rcases family_descends (prefixWord ++ tailWord_6232225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6232248 : List Nat := [2, 1, 2, 1, 2, 1, 3, 4, 1, 3, 3]
def baseStart_6232248 : Nat := 118140960795 + 6232248 * 2 ^ 59
def prefixEnd_6232248 : Nat := 4983230072969 + 3 ^ 40 * 6232248 * 2
def baseEnd_6232248 : Nat := 3200138782022037534738419

theorem tailTrace_6232248 : CollatzResearch.WordTrace tailWord_6232248 prefixEnd_6232248 3200138782022037534738419 := by
  unfold tailWord_6232248
  simp only [CollatzResearch.WordTrace]
  refine ⟨113654379362818677031816699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151539172483758236042422265 113654379362818677031816699)
  ·
    refine ⟨170481569044228015547725049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113654379362818677031816699 170481569044228015547725049)
    ·
      refine ⟨127861176783171011660793787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 170481569044228015547725049 127861176783171011660793787)
      ·
        refine ⟨191791765174756517491190681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127861176783171011660793787 191791765174756517491190681)
        ·
          refine ⟨143843823881067388118393011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 191791765174756517491190681 143843823881067388118393011)
          ·
            refine ⟨215765735821601082177589517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 143843823881067388118393011 215765735821601082177589517)
            ·
              refine ⟨80912150933100405816596069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 215765735821601082177589517 80912150933100405816596069)
              ·
                refine ⟨15171028299956326090611763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 80912150933100405816596069 15171028299956326090611763)
                ·
                  refine ⟨22756542449934489135917645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15171028299956326090611763 22756542449934489135917645)
                  ·
                    refine ⟨8533703418725433425969117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22756542449934489135917645 8533703418725433425969117)
                    ·
                      refine ⟨3200138782022037534738419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8533703418725433425969117 3200138782022037534738419)
                      ·
                        rfl

theorem cell23_6232248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 4, 1, 3, 3].length) (baseStart_6232248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6232248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6232248 prefixEnd_6232248 := by exact prefixLift 6232248
  have htrace : WordTrace (prefixWord ++ tailWord_6232248) baseStart_6232248 baseEnd_6232248 := by
    simpa [prefixWord, tailWord_6232248, baseEnd_6232248] using wordTrace_append hprefix tailTrace_6232248
  have hstable : (prefixWord ++ tailWord_6232248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6232248).length < 2 ^ (prefixWord ++ tailWord_6232248).sum := by decide
  have hdescent : baseEnd_6232248 < baseStart_6232248 := by decide
  rcases family_descends (prefixWord ++ tailWord_6232248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6232249 : List Nat := [1, 2, 1, 4, 1, 2, 4, 3, 1, 2, 2]
def baseStart_6232249 : Nat := 118140960795 + 6232249 * 2 ^ 59
def prefixEnd_6232249 : Nat := 4983230072969 + 3 ^ 40 * 6232249 * 2
def baseEnd_6232249 : Nat := 3200139295502692030825915

theorem tailTrace_6232249 : CollatzResearch.WordTrace tailWord_6232249 prefixEnd_6232249 3200139295502692030825915 := by
  unfold tailWord_6232249
  simp only [CollatzResearch.WordTrace]
  refine ⟨227308795198633731234419801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151539196799089154156279867 227308795198633731234419801)
  ·
    refine ⟨170481596398975298425814851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 227308795198633731234419801 170481596398975298425814851)
    ·
      refine ⟨255722394598462947638722277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170481596398975298425814851 255722394598462947638722277)
      ·
        refine ⟨47947948987211802682260427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 255722394598462947638722277 47947948987211802682260427)
        ·
          refine ⟨71921923480817704023390641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47947948987211802682260427 71921923480817704023390641)
          ·
            refine ⟨53941442610613278017542981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71921923480817704023390641 53941442610613278017542981)
            ·
              refine ⟨10114020489489989628289309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 53941442610613278017542981 10114020489489989628289309)
              ·
                refine ⟨3792757683558746110608491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10114020489489989628289309 3792757683558746110608491)
                ·
                  refine ⟨5689136525338119165912737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3792757683558746110608491 5689136525338119165912737)
                  ·
                    refine ⟨4266852394003589374434553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5689136525338119165912737 4266852394003589374434553)
                    ·
                      refine ⟨3200139295502692030825915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4266852394003589374434553 3200139295502692030825915)
                      ·
                        rfl

theorem cell23_6232249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 4, 3, 1, 2, 2].length) (baseStart_6232249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6232249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6232249 prefixEnd_6232249 := by exact prefixLift 6232249
  have htrace : WordTrace (prefixWord ++ tailWord_6232249) baseStart_6232249 baseEnd_6232249 := by
    simpa [prefixWord, tailWord_6232249, baseEnd_6232249] using wordTrace_append hprefix tailTrace_6232249
  have hstable : (prefixWord ++ tailWord_6232249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6232249).length < 2 ^ (prefixWord ++ tailWord_6232249).sum := by decide
  have hdescent : baseEnd_6232249 < baseStart_6232249 := by decide
  rcases family_descends (prefixWord ++ tailWord_6232249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6232252 : List Nat := [2, 2, 2, 3, 3, 1, 1, 3, 1, 2, 3]
def baseStart_6232252 : Nat := 118140960795 + 6232252 * 2 ^ 59
def prefixEnd_6232252 : Nat := 4983230072969 + 3 ^ 40 * 6232252 * 2
def baseEnd_6232252 : Nat := 3200140835944655519088401

theorem tailTrace_6232252 : CollatzResearch.WordTrace tailWord_6232252 prefixEnd_6232252 3200140835944655519088401 := by
  unfold tailWord_6232252
  simp only [CollatzResearch.WordTrace]
  refine ⟨113654452308811431373389505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151539269745081908497852673 113654452308811431373389505)
  ·
    refine ⟨85240839231608573530042129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113654452308811431373389505 85240839231608573530042129)
    ·
      refine ⟨63930629423706430147531597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85240839231608573530042129 63930629423706430147531597)
      ·
        refine ⟨23973986033889911305324349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63930629423706430147531597 23973986033889911305324349)
        ·
          refine ⟨8990244762708716739496631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23973986033889911305324349 8990244762708716739496631)
          ·
            refine ⟨13485367144063075109244947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8990244762708716739496631 13485367144063075109244947)
            ·
              refine ⟨20228050716094612663867421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13485367144063075109244947 20228050716094612663867421)
              ·
                refine ⟨7585519018535479748950283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20228050716094612663867421 7585519018535479748950283)
                ·
                  refine ⟨11378278527803219623425425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7585519018535479748950283 11378278527803219623425425)
                  ·
                    refine ⟨8533708895852414717569069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11378278527803219623425425 8533708895852414717569069)
                    ·
                      refine ⟨3200140835944655519088401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8533708895852414717569069 3200140835944655519088401)
                      ·
                        rfl

theorem cell23_6232252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 1, 3, 1, 2, 3].length) (baseStart_6232252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6232252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6232252 prefixEnd_6232252 := by exact prefixLift 6232252
  have htrace : WordTrace (prefixWord ++ tailWord_6232252) baseStart_6232252 baseEnd_6232252 := by
    simpa [prefixWord, tailWord_6232252, baseEnd_6232252] using wordTrace_append hprefix tailTrace_6232252
  have hstable : (prefixWord ++ tailWord_6232252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6232252).length < 2 ^ (prefixWord ++ tailWord_6232252).sum := by decide
  have hdescent : baseEnd_6232252 < baseStart_6232252 := by decide
  rcases family_descends (prefixWord ++ tailWord_6232252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6232265 : List Nat := [1, 2, 1, 1, 2, 1, 1, 8, 2, 1, 3]
def baseStart_6232265 : Nat := 118140960795 + 6232265 * 2 ^ 59
def prefixEnd_6232265 : Nat := 4983230072969 + 3 ^ 40 * 6232265 * 2
def baseEnd_6232265 : Nat := 3200147511193163968225841

theorem tailTrace_6232265 : CollatzResearch.WordTrace tailWord_6232265 prefixEnd_6232265 3200147511193163968225841 := by
  unfold tailWord_6232265
  simp only [CollatzResearch.WordTrace]
  refine ⟨227309378766575765967002249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151539585844383843978001499 227309378766575765967002249)
  ·
    refine ⟨170482034074931824475251687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 227309378766575765967002249 170482034074931824475251687)
    ·
      refine ⟨255723051112397736712877531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170482034074931824475251687 255723051112397736712877531)
      ·
        refine ⟨383584576668596605069316297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 255723051112397736712877531 383584576668596605069316297)
        ·
          refine ⟨287688432501447453801987223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 383584576668596605069316297 287688432501447453801987223)
          ·
            refine ⟨431532648752171180702980835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 287688432501447453801987223 431532648752171180702980835)
            ·
              refine ⟨647298973128256771054471253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 431532648752171180702980835 647298973128256771054471253)
              ·
                refine ⟨7585534841346759035794585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 647298973128256771054471253 7585534841346759035794585)
                ·
                  refine ⟨5689151131010069276845939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7585534841346759035794585 5689151131010069276845939)
                  ·
                    refine ⟨8533726696515103915268909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5689151131010069276845939 8533726696515103915268909)
                    ·
                      refine ⟨3200147511193163968225841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8533726696515103915268909 3200147511193163968225841)
                      ·
                        rfl

theorem cell23_6232265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 8, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 8, 2, 1, 3].length) (baseStart_6232265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6232265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6232265 prefixEnd_6232265 := by exact prefixLift 6232265
  have htrace : WordTrace (prefixWord ++ tailWord_6232265) baseStart_6232265 baseEnd_6232265 := by
    simpa [prefixWord, tailWord_6232265, baseEnd_6232265] using wordTrace_append hprefix tailTrace_6232265
  have hstable : (prefixWord ++ tailWord_6232265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6232265).length < 2 ^ (prefixWord ++ tailWord_6232265).sum := by decide
  have hdescent : baseEnd_6232265 < baseStart_6232265 := by decide
  rcases family_descends (prefixWord ++ tailWord_6232265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6232305 : List Nat := [1, 2, 2, 2, 2, 1, 2, 4, 1, 4, 2]
def baseStart_6232305 : Nat := 118140960795 + 6232305 * 2 ^ 59
def prefixEnd_6232305 : Nat := 4983230072969 + 3 ^ 40 * 6232305 * 2
def baseEnd_6232305 : Nat := 3200168050419343811725657

theorem tailTrace_6232305 : CollatzResearch.WordTrace tailWord_6232305 prefixEnd_6232305 3200168050419343811725657 := by
  unfold tailWord_6232305
  simp only [CollatzResearch.WordTrace]
  refine ⟨227310837686430852798458369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151540558457620568532305579 227310837686430852798458369)
  ·
    refine ⟨170483128264823139598843777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 227310837686430852798458369 170483128264823139598843777)
    ·
      refine ⟨127862346198617354699132833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 170483128264823139598843777 127862346198617354699132833)
      ·
        refine ⟨95896759648963016024349625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 127862346198617354699132833 95896759648963016024349625)
        ·
          refine ⟨71922569736722262018262219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95896759648963016024349625 71922569736722262018262219)
          ·
            refine ⟨107883854605083393027393329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71922569736722262018262219 107883854605083393027393329)
            ·
              refine ⟨80912890953812544770544997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 107883854605083393027393329 80912890953812544770544997)
              ·
                refine ⟨15171167053839852144477187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 80912890953812544770544997 15171167053839852144477187)
                ·
                  refine ⟨22756750580759778216715781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15171167053839852144477187 22756750580759778216715781)
                  ·
                    refine ⟨4266890733892458415634209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22756750580759778216715781 4266890733892458415634209)
                    ·
                      refine ⟨3200168050419343811725657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4266890733892458415634209 3200168050419343811725657)
                      ·
                        rfl

theorem cell23_6232305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 4, 1, 4, 2].length) (baseStart_6232305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6232305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6232305 prefixEnd_6232305 := by exact prefixLift 6232305
  have htrace : WordTrace (prefixWord ++ tailWord_6232305) baseStart_6232305 baseEnd_6232305 := by
    simpa [prefixWord, tailWord_6232305, baseEnd_6232305] using wordTrace_append hprefix tailTrace_6232305
  have hstable : (prefixWord ++ tailWord_6232305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6232305).length < 2 ^ (prefixWord ++ tailWord_6232305).sum := by decide
  have hdescent : baseEnd_6232305 < baseStart_6232305 := by decide
  rcases family_descends (prefixWord ++ tailWord_6232305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6232382 : List Nat := [4, 2, 1, 2, 1, 2, 1, 1, 2, 5, 2]
def baseStart_6232382 : Nat := 118140960795 + 6232382 * 2 ^ 59
def prefixEnd_6232382 : Nat := 4983230072969 + 3 ^ 40 * 6232382 * 2
def baseEnd_6232382 : Nat := 3200207588429740010462803

theorem tailTrace_6232382 : CollatzResearch.WordTrace tailWord_6232382 prefixEnd_6232382 3200207588429740010462803 := by
  unfold tailWord_6232382
  simp only [CollatzResearch.WordTrace]
  refine ⟨28414205763393986868626425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 151542430738101263299340933 28414205763393986868626425)
  ·
    refine ⟨21310654322545490151469819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28414205763393986868626425 21310654322545490151469819)
    ·
      refine ⟨31965981483818235227204729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21310654322545490151469819 31965981483818235227204729)
      ·
        refine ⟨23974486112863676420403547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31965981483818235227204729 23974486112863676420403547)
        ·
          refine ⟨35961729169295514630605321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23974486112863676420403547 35961729169295514630605321)
          ·
            refine ⟨26971296876971635972953991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35961729169295514630605321 26971296876971635972953991)
            ·
              refine ⟨40456945315457453959430987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26971296876971635972953991 40456945315457453959430987)
              ·
                refine ⟨60685417973186180939146481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40456945315457453959430987 60685417973186180939146481)
                ·
                  refine ⟨45514063479889635704359861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 60685417973186180939146481 45514063479889635704359861)
                  ·
                    refine ⟨4266943451239653347283737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 45514063479889635704359861 4266943451239653347283737)
                    ·
                      refine ⟨3200207588429740010462803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4266943451239653347283737 3200207588429740010462803)
                      ·
                        rfl

theorem cell23_6232382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 1, 1, 2, 5, 2].length) (baseStart_6232382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6232382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6232382 prefixEnd_6232382 := by exact prefixLift 6232382
  have htrace : WordTrace (prefixWord ++ tailWord_6232382) baseStart_6232382 baseEnd_6232382 := by
    simpa [prefixWord, tailWord_6232382, baseEnd_6232382] using wordTrace_append hprefix tailTrace_6232382
  have hstable : (prefixWord ++ tailWord_6232382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6232382).length < 2 ^ (prefixWord ++ tailWord_6232382).sum := by decide
  have hdescent : baseEnd_6232382 < baseStart_6232382 := by decide
  rcases family_descends (prefixWord ++ tailWord_6232382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6232408 : List Nat := [2, 1, 2, 2, 1, 1, 2, 1, 1, 6, 4]
def baseStart_6232408 : Nat := 118140960795 + 6232408 * 2 ^ 59
def prefixEnd_6232408 : Nat := 4983230072969 + 3 ^ 40 * 6232408 * 2
def baseEnd_6232408 : Nat := 3200220938926756908737683

theorem tailTrace_6232408 : CollatzResearch.WordTrace tailWord_6232408 prefixEnd_6232408 3200220938926756908737683 := by
  unfold tailWord_6232408
  simp only [CollatzResearch.WordTrace]
  refine ⟨113657297202528850694728939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151543062936705134259638585 113657297202528850694728939)
  ·
    refine ⟨170485945803793276042093409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113657297202528850694728939 170485945803793276042093409)
    ·
      refine ⟨127864459352844957031570057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 170485945803793276042093409 127864459352844957031570057)
      ·
        refine ⟨95898344514633717773677543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 127864459352844957031570057 95898344514633717773677543)
        ·
          refine ⟨143847516771950576660516315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95898344514633717773677543 143847516771950576660516315)
          ·
            refine ⟨215771275157925864990774473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 143847516771950576660516315 215771275157925864990774473)
            ·
              refine ⟨161828456368444398743080855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 215771275157925864990774473 161828456368444398743080855)
              ·
                refine ⟨242742684552666598114621283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 161828456368444398743080855 242742684552666598114621283)
                ·
                  refine ⟨364114026828999897171931925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 242742684552666598114621283 364114026828999897171931925)
                  ·
                    refine ⟨17067845007609370179934309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 364114026828999897171931925 17067845007609370179934309)
                    ·
                      refine ⟨3200220938926756908737683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17067845007609370179934309 3200220938926756908737683)
                      ·
                        rfl

theorem cell23_6232408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 1, 1, 6, 4].length) (baseStart_6232408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6232408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6232408 prefixEnd_6232408 := by exact prefixLift 6232408
  have htrace : WordTrace (prefixWord ++ tailWord_6232408) baseStart_6232408 baseEnd_6232408 := by
    simpa [prefixWord, tailWord_6232408, baseEnd_6232408] using wordTrace_append hprefix tailTrace_6232408
  have hstable : (prefixWord ++ tailWord_6232408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6232408).length < 2 ^ (prefixWord ++ tailWord_6232408).sum := by decide
  have hdescent : baseEnd_6232408 < baseStart_6232408 := by decide
  rcases family_descends (prefixWord ++ tailWord_6232408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6232452 : List Nat := [2, 3, 2, 1, 1, 2, 5, 1, 6]
def baseStart_6232452 : Nat := 118140960795 + 6232452 * 2 ^ 59
def prefixEnd_6232452 : Nat := 4983230072969 + 3 ^ 40 * 6232452 * 2
def baseEnd_6232452 : Nat := 355582614675061637398609

theorem tailTrace_6232452 : CollatzResearch.WordTrace tailWord_6232452 prefixEnd_6232452 355582614675061637398609 := by
  unfold tailWord_6232452
  simp only [CollatzResearch.WordTrace]
  refine ⟨113658099608449148452029805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151544132811265531269373073 113658099608449148452029805)
  ·
    refine ⟨42621787353168430669511177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113658099608449148452029805 42621787353168430669511177)
    ·
      refine ⟨31966340514876323002133383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42621787353168430669511177 31966340514876323002133383)
      ·
        refine ⟨47949510772314484503200075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31966340514876323002133383 47949510772314484503200075)
        ·
          refine ⟨71924266158471726754800113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47949510772314484503200075 71924266158471726754800113)
          ·
            refine ⟨53943199618853795066100085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71924266158471726754800113 53943199618853795066100085)
            ·
              refine ⟨5057174964267543287446883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 53943199618853795066100085 5057174964267543287446883)
              ·
                refine ⟨7585762446401314931170325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5057174964267543287446883 7585762446401314931170325)
                ·
                  refine ⟨355582614675061637398609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7585762446401314931170325 355582614675061637398609)
                  ·
                    rfl

theorem cell23_6232452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 5, 1, 6].length) (baseStart_6232452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6232452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6232452 prefixEnd_6232452 := by exact prefixLift 6232452
  have htrace : WordTrace (prefixWord ++ tailWord_6232452) baseStart_6232452 baseEnd_6232452 := by
    simpa [prefixWord, tailWord_6232452, baseEnd_6232452] using wordTrace_append hprefix tailTrace_6232452
  have hstable : (prefixWord ++ tailWord_6232452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6232452).length < 2 ^ (prefixWord ++ tailWord_6232452).sum := by decide
  have hdescent : baseEnd_6232452 < baseStart_6232452 := by decide
  rcases family_descends (prefixWord ++ tailWord_6232452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6232482 : List Nat := [3, 3, 1, 2, 1, 1, 1, 5, 1, 5]
def baseStart_6232482 : Nat := 118140960795 + 6232482 * 2 ^ 59
def prefixEnd_6232482 : Nat := 4983230072969 + 3 ^ 40 * 6232482 * 2
def baseEnd_6232482 : Nat := 1066752978831729873070781

theorem tailTrace_6232482 : CollatzResearch.WordTrace tailWord_6232482 prefixEnd_6232482 1066752978831729873070781 := by
  unfold tailWord_6232482
  simp only [CollatzResearch.WordTrace]
  refine ⟨56829323351697403006912925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151544862271193074685101133 56829323351697403006912925)
  ·
    refine ⟨21310996256886526127592347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56829323351697403006912925 21310996256886526127592347)
    ·
      refine ⟨31966494385329789191388521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21310996256886526127592347 31966494385329789191388521)
      ·
        refine ⟨23974870788997341893541391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31966494385329789191388521 23974870788997341893541391)
        ·
          refine ⟨35962306183496012840312087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23974870788997341893541391 35962306183496012840312087)
          ·
            refine ⟨53943459275244019260468131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35962306183496012840312087 53943459275244019260468131)
            ·
              refine ⟨80915188912866028890702197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53943459275244019260468131 80915188912866028890702197)
              ·
                refine ⟨7585798960581190208503331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 80915188912866028890702197 7585798960581190208503331)
                ·
                  refine ⟨11378698440871785312754997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7585798960581190208503331 11378698440871785312754997)
                  ·
                    refine ⟨1066752978831729873070781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11378698440871785312754997 1066752978831729873070781)
                    ·
                      rfl

theorem cell23_6232482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 5, 1, 5].length) (baseStart_6232482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6232482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6232482 prefixEnd_6232482 := by exact prefixLift 6232482
  have htrace : WordTrace (prefixWord ++ tailWord_6232482) baseStart_6232482 baseEnd_6232482 := by
    simpa [prefixWord, tailWord_6232482, baseEnd_6232482] using wordTrace_append hprefix tailTrace_6232482
  have hstable : (prefixWord ++ tailWord_6232482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6232482).length < 2 ^ (prefixWord ++ tailWord_6232482).sum := by decide
  have hdescent : baseEnd_6232482 < baseStart_6232482 := by decide
  rcases family_descends (prefixWord ++ tailWord_6232482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6232490 : List Nat := [3, 1, 6, 1, 2, 1, 1, 1, 3, 4]
def baseStart_6232490 : Nat := 118140960795 + 6232490 * 2 ^ 59
def prefixEnd_6232490 : Nat := 4983230072969 + 3 ^ 40 * 6232490 * 2
def baseEnd_6232490 : Nat := 1066754348113475195970769

theorem tailTrace_6232490 : CollatzResearch.WordTrace tailWord_6232490 prefixEnd_6232490 1066754348113475195970769 := by
  unfold tailWord_6232490
  simp only [CollatzResearch.WordTrace]
  refine ⟨56829396297690157348485731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151545056793840419595961949 56829396297690157348485731)
  ·
    refine ⟨85244094446535236022728597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56829396297690157348485731 85244094446535236022728597)
    ·
      refine ⟨3995816927181339188565403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 85244094446535236022728597 3995816927181339188565403)
      ·
        refine ⟨5993725390772008782848105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3995816927181339188565403 5993725390772008782848105)
        ·
          refine ⟨4495294043079006587136079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5993725390772008782848105 4495294043079006587136079)
          ·
            refine ⟨6742941064618509880704119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4495294043079006587136079 6742941064618509880704119)
            ·
              refine ⟨10114411596927764821056179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6742941064618509880704119 10114411596927764821056179)
              ·
                refine ⟨15171617395391647231584269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10114411596927764821056179 15171617395391647231584269)
                ·
                  refine ⟨5689356523271867711844101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15171617395391647231584269 5689356523271867711844101)
                  ·
                    refine ⟨1066754348113475195970769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5689356523271867711844101 1066754348113475195970769)
                    ·
                      rfl

theorem cell23_6232490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 2, 1, 1, 1, 3, 4].length) (baseStart_6232490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6232490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6232490 prefixEnd_6232490 := by exact prefixLift 6232490
  have htrace : WordTrace (prefixWord ++ tailWord_6232490) baseStart_6232490 baseEnd_6232490 := by
    simpa [prefixWord, tailWord_6232490, baseEnd_6232490] using wordTrace_append hprefix tailTrace_6232490
  have hstable : (prefixWord ++ tailWord_6232490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6232490).length < 2 ^ (prefixWord ++ tailWord_6232490).sum := by decide
  have hdescent : baseEnd_6232490 < baseStart_6232490 := by decide
  rcases family_descends (prefixWord ++ tailWord_6232490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6232515 : List Nat := [1, 1, 1, 3, 1, 1, 3, 5, 1, 2, 4]
def baseStart_6232515 : Nat := 118140960795 + 6232515 * 2 ^ 59
def prefixEnd_6232515 : Nat := 4983230072969 + 3 ^ 40 * 6232515 * 2
def baseEnd_6232515 : Nat := 3200275881356787990099691

theorem tailTrace_6232515 : CollatzResearch.WordTrace tailWord_6232515 prefixEnd_6232515 3200275881356787990099691 := by
  unfold tailWord_6232515
  simp only [CollatzResearch.WordTrace]
  refine ⟨227318497015670058663602999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151545664677113372442401999 227318497015670058663602999)
  ·
    refine ⟨340977745523505087995404499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227318497015670058663602999 340977745523505087995404499)
    ·
      refine ⟨511466618285257631993106749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 340977745523505087995404499 511466618285257631993106749)
      ·
        refine ⟨191799981856971611997415031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 511466618285257631993106749 191799981856971611997415031)
        ·
          refine ⟨287699972785457417996122547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 191799981856971611997415031 287699972785457417996122547)
          ·
            refine ⟨431549959178186126994183821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 287699972785457417996122547 431549959178186126994183821)
            ·
              refine ⟨161831234691819797622818933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 431549959178186126994183821 161831234691819797622818933)
              ·
                refine ⟨15171678252358106027139275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 161831234691819797622818933 15171678252358106027139275)
                ·
                  refine ⟨22757517378537159040708913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15171678252358106027139275 22757517378537159040708913)
                  ·
                    refine ⟨17068138033902869280531685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22757517378537159040708913 17068138033902869280531685)
                    ·
                      refine ⟨3200275881356787990099691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17068138033902869280531685 3200275881356787990099691)
                      ·
                        rfl

theorem cell23_6232515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 5, 1, 2, 4].length) (baseStart_6232515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6232515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6232515 prefixEnd_6232515 := by exact prefixLift 6232515
  have htrace : WordTrace (prefixWord ++ tailWord_6232515) baseStart_6232515 baseEnd_6232515 := by
    simpa [prefixWord, tailWord_6232515, baseEnd_6232515] using wordTrace_append hprefix tailTrace_6232515
  have hstable : (prefixWord ++ tailWord_6232515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6232515).length < 2 ^ (prefixWord ++ tailWord_6232515).sum := by decide
  have hdescent : baseEnd_6232515 < baseStart_6232515 := by decide
  rcases family_descends (prefixWord ++ tailWord_6232515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6232516 : List Nat := [2, 3, 3, 2, 2, 2, 1, 2, 1, 5]
def baseStart_6232516 : Nat := 118140960795 + 6232516 * 2 ^ 59
def prefixEnd_6232516 : Nat := 4983230072969 + 3 ^ 40 * 6232516 * 2
def baseEnd_6232516 : Nat := 1066758798279147495395729

theorem tailTrace_6232516 : CollatzResearch.WordTrace tailWord_6232516 prefixEnd_6232516 1066758798279147495395729 := by
  unfold tailWord_6232516
  simp only [CollatzResearch.WordTrace]
  refine ⟨113659266744333217917194701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151545688992444290556259601 113659266744333217917194701)
  ·
    refine ⟨42622225029124956718948013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113659266744333217917194701 42622225029124956718948013)
    ·
      refine ⟨15983334385921858769605505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42622225029124956718948013 15983334385921858769605505)
      ·
        refine ⟨11987500789441394077204129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15983334385921858769605505 11987500789441394077204129)
        ·
          refine ⟨8990625592081045557903097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11987500789441394077204129 8990625592081045557903097)
          ·
            refine ⟨6742969194060784168427323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8990625592081045557903097 6742969194060784168427323)
            ·
              refine ⟨10114453791091176252640985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6742969194060784168427323 10114453791091176252640985)
              ·
                refine ⟨7585840343318382189480739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10114453791091176252640985 7585840343318382189480739)
                ·
                  refine ⟨11378760514977573284221109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7585840343318382189480739 11378760514977573284221109)
                  ·
                    refine ⟨1066758798279147495395729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11378760514977573284221109 1066758798279147495395729)
                    ·
                      rfl

theorem cell23_6232516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 2, 1, 2, 1, 5].length) (baseStart_6232516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6232516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6232516 prefixEnd_6232516 := by exact prefixLift 6232516
  have htrace : WordTrace (prefixWord ++ tailWord_6232516) baseStart_6232516 baseEnd_6232516 := by
    simpa [prefixWord, tailWord_6232516, baseEnd_6232516] using wordTrace_append hprefix tailTrace_6232516
  have hstable : (prefixWord ++ tailWord_6232516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6232516).length < 2 ^ (prefixWord ++ tailWord_6232516).sum := by decide
  have hdescent : baseEnd_6232516 < baseStart_6232516 := by decide
  rcases family_descends (prefixWord ++ tailWord_6232516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6232519 : List Nat := [1, 1, 4, 1, 1, 6, 1, 2, 1, 1, 4]
def baseStart_6232519 : Nat := 118140960795 + 6232519 * 2 ^ 59
def prefixEnd_6232519 : Nat := 4983230072969 + 3 ^ 40 * 6232519 * 2
def baseEnd_6232519 : Nat := 3200277935279405974449673

theorem tailTrace_6232519 : CollatzResearch.WordTrace tailWord_6232519 prefixEnd_6232519 3200277935279405974449673 := by
  unfold tailWord_6232519
  simp only [CollatzResearch.WordTrace]
  refine ⟨227318642907655567346748611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151545761938437044897832407 227318642907655567346748611)
  ·
    refine ⟨340977964361483351020122917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227318642907655567346748611 340977964361483351020122917)
    ·
      refine ⟨63933368317778128316273047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 340977964361483351020122917 63933368317778128316273047)
      ·
        refine ⟨95900052476667192474409571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63933368317778128316273047 95900052476667192474409571)
        ·
          refine ⟨143850078715000788711614357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95900052476667192474409571 143850078715000788711614357)
          ·
            refine ⟨6742972439765661970856923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 143850078715000788711614357 6742972439765661970856923)
            ·
              refine ⟨10114458659648492956285385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6742972439765661970856923 10114458659648492956285385)
              ·
                refine ⟨7585843994736369717214039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10114458659648492956285385 7585843994736369717214039)
                ·
                  refine ⟨11378765992104554575821059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7585843994736369717214039 11378765992104554575821059)
                  ·
                    refine ⟨17068148988156831863731589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11378765992104554575821059 17068148988156831863731589)
                    ·
                      refine ⟨3200277935279405974449673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17068148988156831863731589 3200277935279405974449673)
                      ·
                        rfl

theorem cell23_6232519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 6, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 6, 1, 2, 1, 1, 4].length) (baseStart_6232519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6232519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6232519 prefixEnd_6232519 := by exact prefixLift 6232519
  have htrace : WordTrace (prefixWord ++ tailWord_6232519) baseStart_6232519 baseEnd_6232519 := by
    simpa [prefixWord, tailWord_6232519, baseEnd_6232519] using wordTrace_append hprefix tailTrace_6232519
  have hstable : (prefixWord ++ tailWord_6232519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6232519).length < 2 ^ (prefixWord ++ tailWord_6232519).sum := by decide
  have hdescent : baseEnd_6232519 < baseStart_6232519 := by decide
  rcases family_descends (prefixWord ++ tailWord_6232519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6232522 : List Nat := [3, 1, 2, 1, 2, 2, 3, 1, 3, 2, 3]
def baseStart_6232522 : Nat := 118140960795 + 6232522 * 2 ^ 59
def prefixEnd_6232522 : Nat := 4983230072969 + 3 ^ 40 * 6232522 * 2
def baseEnd_6232522 : Nat := 3200279475721369462712159

theorem tailTrace_6232522 : CollatzResearch.WordTrace tailWord_6232522 prefixEnd_6232522 3200279475721369462712159 := by
  unfold tailWord_6232522
  simp only [CollatzResearch.WordTrace]
  refine ⟨56829688081661174714776955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151545834884429799239405213 56829688081661174714776955)
  ·
    refine ⟨85244532122491762072165433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56829688081661174714776955 85244532122491762072165433)
    ·
      refine ⟨63933399091868821554124075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85244532122491762072165433 63933399091868821554124075)
      ·
        refine ⟨95900098637803232331186113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63933399091868821554124075 95900098637803232331186113)
        ·
          refine ⟨71925073978352424248389585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95900098637803232331186113 71925073978352424248389585)
          ·
            refine ⟨53943805483764318186292189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71925073978352424248389585 53943805483764318186292189)
            ·
              refine ⟨20228927056411619319859571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53943805483764318186292189 20228927056411619319859571)
              ·
                refine ⟨30343390584617428979789357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20228927056411619319859571 30343390584617428979789357)
                ·
                  refine ⟨11378771469231535867421009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30343390584617428979789357 11378771469231535867421009)
                  ·
                    refine ⟨8534078601923651900565757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11378771469231535867421009 8534078601923651900565757)
                    ·
                      refine ⟨3200279475721369462712159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8534078601923651900565757 3200279475721369462712159)
                      ·
                        rfl

theorem cell23_6232522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 3, 1, 3, 2, 3].length) (baseStart_6232522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6232522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6232522 prefixEnd_6232522 := by exact prefixLift 6232522
  have htrace : WordTrace (prefixWord ++ tailWord_6232522) baseStart_6232522 baseEnd_6232522 := by
    simpa [prefixWord, tailWord_6232522, baseEnd_6232522] using wordTrace_append hprefix tailTrace_6232522
  have hstable : (prefixWord ++ tailWord_6232522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6232522).length < 2 ^ (prefixWord ++ tailWord_6232522).sum := by decide
  have hdescent : baseEnd_6232522 < baseStart_6232522 := by decide
  rcases family_descends (prefixWord ++ tailWord_6232522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6232532 : List Nat := [2, 4, 1, 2, 2, 1, 1, 1, 3, 2, 4]
def baseStart_6232532 : Nat := 118140960795 + 6232532 * 2 ^ 59
def prefixEnd_6232532 : Nat := 4983230072969 + 3 ^ 40 * 6232532 * 2
def baseEnd_6232532 : Nat := 3200284610527914423587113

theorem tailTrace_6232532 : CollatzResearch.WordTrace tailWord_6232532 prefixEnd_6232532 3200284610527914423587113 := by
  unfold tailWord_6232532
  simp only [CollatzResearch.WordTrace]
  refine ⟨113659558528304235283485925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151546078037738980377981233 113659558528304235283485925)
  ·
    refine ⟨21311167224057044115653611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 113659558528304235283485925 21311167224057044115653611)
    ·
      refine ⟨31966750836085566173480417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21311167224057044115653611 31966750836085566173480417)
      ·
        refine ⟨23975063127064174630110313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31966750836085566173480417 23975063127064174630110313)
        ·
          refine ⟨17981297345298130972582735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23975063127064174630110313 17981297345298130972582735)
          ·
            refine ⟨26971946017947196458874103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17981297345298130972582735 26971946017947196458874103)
            ·
              refine ⟨40457919026920794688311155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26971946017947196458874103 40457919026920794688311155)
              ·
                refine ⟨60686878540381192032466733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40457919026920794688311155 60686878540381192032466733)
                ·
                  refine ⟨22757579452642947012175025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 60686878540381192032466733 22757579452642947012175025)
                  ·
                    refine ⟨17068184589482210259131269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22757579452642947012175025 17068184589482210259131269)
                    ·
                      refine ⟨3200284610527914423587113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17068184589482210259131269 3200284610527914423587113)
                      ·
                        rfl

theorem cell23_6232532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 1, 1, 3, 2, 4].length) (baseStart_6232532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6232532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6232532 prefixEnd_6232532 := by exact prefixLift 6232532
  have htrace : WordTrace (prefixWord ++ tailWord_6232532) baseStart_6232532 baseEnd_6232532 := by
    simpa [prefixWord, tailWord_6232532, baseEnd_6232532] using wordTrace_append hprefix tailTrace_6232532
  have hstable : (prefixWord ++ tailWord_6232532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6232532).length < 2 ^ (prefixWord ++ tailWord_6232532).sum := by decide
  have hdescent : baseEnd_6232532 < baseStart_6232532 := by decide
  rcases family_descends (prefixWord ++ tailWord_6232532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6232536 : List Nat := [2, 1, 2, 2, 2, 1, 1, 7, 1, 2, 2]
def baseStart_6232536 : Nat := 118140960795 + 6232536 * 2 ^ 59
def prefixEnd_6232536 : Nat := 4983230072969 + 3 ^ 40 * 6232536 * 2
def baseEnd_6232536 : Nat := 3200286664450532407937095

theorem tailTrace_6232536 : CollatzResearch.WordTrace tailWord_6232536 prefixEnd_6232536 3200286664450532407937095 := by
  unfold tailWord_6232536
  simp only [CollatzResearch.WordTrace]
  refine ⟨113659631474296989625058731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151546175299062652833411641 113659631474296989625058731)
  ·
    refine ⟨170489447211445484437588097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113659631474296989625058731 170489447211445484437588097)
    ·
      refine ⟨127867085408584113328191073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 170489447211445484437588097 127867085408584113328191073)
      ·
        refine ⟨95900314056438084996143305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 127867085408584113328191073 95900314056438084996143305)
        ·
          refine ⟨71925235542328563747107479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95900314056438084996143305 71925235542328563747107479)
          ·
            refine ⟨107887853313492845620661219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71925235542328563747107479 107887853313492845620661219)
            ·
              refine ⟨161831779970239268430991829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 107887853313492845620661219 161831779970239268430991829)
              ·
                refine ⟨3792932343052482853851371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 161831779970239268430991829 3792932343052482853851371)
                ·
                  refine ⟨5689398514578724280777057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3792932343052482853851371 5689398514578724280777057)
                  ·
                    refine ⟨4267048885934043210582793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5689398514578724280777057 4267048885934043210582793)
                    ·
                      refine ⟨3200286664450532407937095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4267048885934043210582793 3200286664450532407937095)
                      ·
                        rfl

theorem cell23_6232536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 7, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 7, 1, 2, 2].length) (baseStart_6232536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6232536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6232536 prefixEnd_6232536 := by exact prefixLift 6232536
  have htrace : WordTrace (prefixWord ++ tailWord_6232536) baseStart_6232536 baseEnd_6232536 := by
    simpa [prefixWord, tailWord_6232536, baseEnd_6232536] using wordTrace_append hprefix tailTrace_6232536
  have hstable : (prefixWord ++ tailWord_6232536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6232536).length < 2 ^ (prefixWord ++ tailWord_6232536).sum := by decide
  have hdescent : baseEnd_6232536 < baseStart_6232536 := by decide
  rcases family_descends (prefixWord ++ tailWord_6232536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6232569 : List Nat := [1, 2, 1, 3, 1, 2, 4, 3, 2, 1, 3]
def baseStart_6232569 : Nat := 118140960795 + 6232569 * 2 ^ 59
def prefixEnd_6232569 : Nat := 4983230072969 + 3 ^ 40 * 6232569 * 2
def baseEnd_6232569 : Nat := 3200303609312130778824443

theorem tailTrace_6232569 : CollatzResearch.WordTrace tailWord_6232569 prefixEnd_6232569 3200303609312130778824443 := by
  unfold tailWord_6232569
  simp only [CollatzResearch.WordTrace]
  refine ⟨227320466557474425886068761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151546977704982950590712507 227320466557474425886068761)
  ·
    refine ⟨170490349918105819414551571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 227320466557474425886068761 170490349918105819414551571)
    ·
      refine ⟨255735524877158729121827357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170490349918105819414551571 255735524877158729121827357)
      ·
        refine ⟨95900821828934523420685259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 255735524877158729121827357 95900821828934523420685259)
        ·
          refine ⟨143851232743401785131027889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95900821828934523420685259 143851232743401785131027889)
          ·
            refine ⟨107888424557551338848270917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 143851232743401785131027889 107888424557551338848270917)
            ·
              refine ⟨20229079604540876034050797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 107888424557551338848270917 20229079604540876034050797)
              ·
                refine ⟨7585904851702828512769049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20229079604540876034050797 7585904851702828512769049)
                ·
                  refine ⟨5689428638777121384576787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7585904851702828512769049 5689428638777121384576787)
                  ·
                    refine ⟨8534142958165682076865181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5689428638777121384576787 8534142958165682076865181)
                    ·
                      refine ⟨3200303609312130778824443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8534142958165682076865181 3200303609312130778824443)
                      ·
                        rfl

theorem cell23_6232569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 4, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 4, 3, 2, 1, 3].length) (baseStart_6232569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6232569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6232569 prefixEnd_6232569 := by exact prefixLift 6232569
  have htrace : WordTrace (prefixWord ++ tailWord_6232569) baseStart_6232569 baseEnd_6232569 := by
    simpa [prefixWord, tailWord_6232569, baseEnd_6232569] using wordTrace_append hprefix tailTrace_6232569
  have hstable : (prefixWord ++ tailWord_6232569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6232569).length < 2 ^ (prefixWord ++ tailWord_6232569).sum := by decide
  have hdescent : baseEnd_6232569 < baseStart_6232569 := by decide
  rcases family_descends (prefixWord ++ tailWord_6232569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6232575 : List Nat := [1, 1, 2, 2, 1, 2, 3, 2, 2, 3, 4]
def baseStart_6232575 : Nat := 118140960795 + 6232575 * 2 ^ 59
def prefixEnd_6232575 : Nat := 4983230072969 + 3 ^ 40 * 6232575 * 2
def baseEnd_6232575 : Nat := 3200306690196057755349415

theorem tailTrace_6232575 : CollatzResearch.WordTrace tailWord_6232575 prefixEnd_6232575 3200306690196057755349415 := by
  unfold tailWord_6232575
  simp only [CollatzResearch.WordTrace]
  refine ⟨227320685395452688910787179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151547123596968459273858119 227320685395452688910787179)
  ·
    refine ⟨340981028093179033366180769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227320685395452688910787179 340981028093179033366180769)
    ·
      refine ⟨255735771069884275024635577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 340981028093179033366180769 255735771069884275024635577)
      ·
        refine ⟨191801828302413206268476683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 255735771069884275024635577 191801828302413206268476683)
        ·
          refine ⟨287702742453619809402715025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 191801828302413206268476683 287702742453619809402715025)
          ·
            refine ⟨215777056840214857052036269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 287702742453619809402715025 215777056840214857052036269)
            ·
              refine ⟨80916396315080571394513601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 215777056840214857052036269 80916396315080571394513601)
              ·
                refine ⟨60687297236310428545885201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 80916396315080571394513601 60687297236310428545885201)
                ·
                  refine ⟨45515472927232821409413901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 60687297236310428545885201 45515472927232821409413901)
                  ·
                    refine ⟨17068302347712308028530213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 45515472927232821409413901 17068302347712308028530213)
                    ·
                      refine ⟨3200306690196057755349415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17068302347712308028530213 3200306690196057755349415)
                      ·
                        rfl

theorem cell23_6232575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 2, 2, 3, 4].length) (baseStart_6232575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6232575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6232575 prefixEnd_6232575 := by exact prefixLift 6232575
  have htrace : WordTrace (prefixWord ++ tailWord_6232575) baseStart_6232575 baseEnd_6232575 := by
    simpa [prefixWord, tailWord_6232575, baseEnd_6232575] using wordTrace_append hprefix tailTrace_6232575
  have hstable : (prefixWord ++ tailWord_6232575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6232575).length < 2 ^ (prefixWord ++ tailWord_6232575).sum := by decide
  have hdescent : baseEnd_6232575 < baseStart_6232575 := by decide
  rcases family_descends (prefixWord ++ tailWord_6232575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6232579 : List Nat := [1, 1, 1, 3, 2, 1, 4, 4, 1, 3, 2]
def baseStart_6232579 : Nat := 118140960795 + 6232579 * 2 ^ 59
def prefixEnd_6232579 : Nat := 4983230072969 + 3 ^ 40 * 6232579 * 2
def baseEnd_6232579 : Nat := 3200308744118675739699397

theorem tailTrace_6232579 : CollatzResearch.WordTrace tailWord_6232579 prefixEnd_6232579 3200308744118675739699397 := by
  unfold tailWord_6232579
  simp only [CollatzResearch.WordTrace]
  refine ⟨227320831287438197593932791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151547220858292131729288527 227320831287438197593932791)
  ·
    refine ⟨340981246931157296390899187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227320831287438197593932791 340981246931157296390899187)
    ·
      refine ⟨511471870396735944586348781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 340981246931157296390899187 511471870396735944586348781)
      ·
        refine ⟨191801951398775979219880793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 511471870396735944586348781 191801951398775979219880793)
        ·
          refine ⟨143851463549081984414910595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 191801951398775979219880793 143851463549081984414910595)
          ·
            refine ⟨215777195323622976622365893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 143851463549081984414910595 215777195323622976622365893)
            ·
              refine ⟨40458224123179308116693605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 215777195323622976622365893 40458224123179308116693605)
              ·
                refine ⟨7585917023096120271880051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40458224123179308116693605 7585917023096120271880051)
                ·
                  refine ⟨11378875534644180407820077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7585917023096120271880051 11378875534644180407820077)
                  ·
                    refine ⟨4267078325491567652932529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11378875534644180407820077 4267078325491567652932529)
                    ·
                      refine ⟨3200308744118675739699397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4267078325491567652932529 3200308744118675739699397)
                      ·
                        rfl

theorem cell23_6232579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 4, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 4, 4, 1, 3, 2].length) (baseStart_6232579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6232579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6232579 prefixEnd_6232579 := by exact prefixLift 6232579
  have htrace : WordTrace (prefixWord ++ tailWord_6232579) baseStart_6232579 baseEnd_6232579 := by
    simpa [prefixWord, tailWord_6232579, baseEnd_6232579] using wordTrace_append hprefix tailTrace_6232579
  have hstable : (prefixWord ++ tailWord_6232579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6232579).length < 2 ^ (prefixWord ++ tailWord_6232579).sum := by decide
  have hdescent : baseEnd_6232579 < baseStart_6232579 := by decide
  rcases family_descends (prefixWord ++ tailWord_6232579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6232592 : List Nat := [2, 1, 1, 1, 1, 1, 1, 2, 7, 4, 2]
def baseStart_6232592 : Nat := 118140960795 + 6232592 * 2 ^ 59
def prefixEnd_6232592 : Nat := 4983230072969 + 3 ^ 40 * 6232592 * 2
def baseEnd_6232592 : Nat := 3200315419367184188836837

theorem tailTrace_6232592 : CollatzResearch.WordTrace tailWord_6232592 prefixEnd_6232592 3200315419367184188836837 := by
  unfold tailWord_6232592
  simp only [CollatzResearch.WordTrace]
  refine ⟨113660652718195550407078015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151547536957594067209437353 113660652718195550407078015)
  ·
    refine ⟨170490979077293325610617023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113660652718195550407078015 170490979077293325610617023)
    ·
      refine ⟨255736468615939988415925535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170490979077293325610617023 255736468615939988415925535)
      ·
        refine ⟨383604702923909982623888303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 255736468615939988415925535 383604702923909982623888303)
        ·
          refine ⟨575407054385864973935832455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 383604702923909982623888303 575407054385864973935832455)
          ·
            refine ⟨863110581578797460903748683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 575407054385864973935832455 863110581578797460903748683)
            ·
              refine ⟨1294665872368196191355623025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 863110581578797460903748683 1294665872368196191355623025)
              ·
                refine ⟨970999404276147143516717269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1294665872368196191355623025 970999404276147143516717269)
                ·
                  refine ⟨22757798537722198676173061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 970999404276147143516717269 22757798537722198676173061)
                  ·
                    refine ⟨4267087225822912251782449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22757798537722198676173061 4267087225822912251782449)
                    ·
                      refine ⟨3200315419367184188836837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4267087225822912251782449 3200315419367184188836837)
                      ·
                        rfl

theorem cell23_6232592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 7, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 7, 4, 2].length) (baseStart_6232592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6232592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6232592 prefixEnd_6232592 := by exact prefixLift 6232592
  have htrace : WordTrace (prefixWord ++ tailWord_6232592) baseStart_6232592 baseEnd_6232592 := by
    simpa [prefixWord, tailWord_6232592, baseEnd_6232592] using wordTrace_append hprefix tailTrace_6232592
  have hstable : (prefixWord ++ tailWord_6232592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6232592).length < 2 ^ (prefixWord ++ tailWord_6232592).sum := by decide
  have hdescent : baseEnd_6232592 < baseStart_6232592 := by decide
  rcases family_descends (prefixWord ++ tailWord_6232592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6232595 : List Nat := [1, 1, 1, 2, 1, 5, 2, 1, 1, 3, 5]
def baseStart_6232595 : Nat := 118140960795 + 6232595 * 2 ^ 59
def prefixEnd_6232595 : Nat := 4983230072969 + 3 ^ 40 * 6232595 * 2
def baseEnd_6232595 : Nat := 3200316959809147677099323

theorem tailTrace_6232595 : CollatzResearch.WordTrace tailWord_6232595 prefixEnd_6232595 3200316959809147677099323 := by
  unfold tailWord_6232595
  simp only [CollatzResearch.WordTrace]
  refine ⟨227321414855380232326515239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151547609903586821551010159 227321414855380232326515239)
  ·
    refine ⟨340982122283070348489772859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227321414855380232326515239 340982122283070348489772859)
    ·
      refine ⟨511473183424605522734659289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 340982122283070348489772859 511473183424605522734659289)
      ·
        refine ⟨383604887568454142050994467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 511473183424605522734659289 383604887568454142050994467)
        ·
          refine ⟨575407331352681213076491701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 383604887568454142050994467 575407331352681213076491701)
          ·
            refine ⟨53944437314313863725921097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 575407331352681213076491701 53944437314313863725921097)
            ·
              refine ⟨40458327985735397794440823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53944437314313863725921097 40458327985735397794440823)
              ·
                refine ⟨60687491978603096691661235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40458327985735397794440823 60687491978603096691661235)
                ·
                  refine ⟨91031237967904645037491853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 60687491978603096691661235 91031237967904645037491853)
                  ·
                    refine ⟨34136714237964241889059445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 91031237967904645037491853 34136714237964241889059445)
                    ·
                      refine ⟨3200316959809147677099323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34136714237964241889059445 3200316959809147677099323)
                      ·
                        rfl

theorem cell23_6232595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 2, 1, 1, 3, 5].length) (baseStart_6232595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6232595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6232595 prefixEnd_6232595 := by exact prefixLift 6232595
  have htrace : WordTrace (prefixWord ++ tailWord_6232595) baseStart_6232595 baseEnd_6232595 := by
    simpa [prefixWord, tailWord_6232595, baseEnd_6232595] using wordTrace_append hprefix tailTrace_6232595
  have hstable : (prefixWord ++ tailWord_6232595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6232595).length < 2 ^ (prefixWord ++ tailWord_6232595).sum := by decide
  have hdescent : baseEnd_6232595 < baseStart_6232595 := by decide
  rcases family_descends (prefixWord ++ tailWord_6232595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6232626 : List Nat := [3, 2, 1, 1, 2, 1, 2, 5, 2, 2, 2]
def baseStart_6232626 : Nat := 118140960795 + 6232626 * 2 ^ 59
def prefixEnd_6232626 : Nat := 4983230072969 + 3 ^ 40 * 6232626 * 2
def baseEnd_6232626 : Nat := 3200332877709437055811681

theorem tailTrace_6232626 : CollatzResearch.WordTrace tailWord_6232626 prefixEnd_6232626 3200332877709437055811681 := by
  unfold tailWord_6232626
  simp only [CollatzResearch.WordTrace]
  refine ⟨56830636379566981155223433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151548363678845283080595821 56830636379566981155223433)
  ·
    refine ⟨42622977284675235866417575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56830636379566981155223433 42622977284675235866417575)
    ·
      refine ⟨63934465927012853799626363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42622977284675235866417575 63934465927012853799626363)
      ·
        refine ⟨95901698890519280699439545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63934465927012853799626363 95901698890519280699439545)
        ·
          refine ⟨71926274167889460524579659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95901698890519280699439545 71926274167889460524579659)
          ·
            refine ⟨107889411251834190786869489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71926274167889460524579659 107889411251834190786869489)
            ·
              refine ⟨80917058438875643090152117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 107889411251834190786869489 80917058438875643090152117)
              ·
                refine ⟨7585974228644591539701761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 80917058438875643090152117 7585974228644591539701761)
                ·
                  refine ⟨5689480671483443654776321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7585974228644591539701761 5689480671483443654776321)
                  ·
                    refine ⟨4267110503612582741082241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5689480671483443654776321 4267110503612582741082241)
                    ·
                      refine ⟨3200332877709437055811681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4267110503612582741082241 3200332877709437055811681)
                      ·
                        rfl

theorem cell23_6232626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 5, 2, 2, 2].length) (baseStart_6232626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6232626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6232626 prefixEnd_6232626 := by exact prefixLift 6232626
  have htrace : WordTrace (prefixWord ++ tailWord_6232626) baseStart_6232626 baseEnd_6232626 := by
    simpa [prefixWord, tailWord_6232626, baseEnd_6232626] using wordTrace_append hprefix tailTrace_6232626
  have hstable : (prefixWord ++ tailWord_6232626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6232626).length < 2 ^ (prefixWord ++ tailWord_6232626).sum := by decide
  have hdescent : baseEnd_6232626 < baseStart_6232626 := by decide
  rcases family_descends (prefixWord ++ tailWord_6232626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6232646 : List Nat := [6, 1, 1, 1, 2, 2, 1, 1, 2, 1, 5]
def baseStart_6232646 : Nat := 118140960795 + 6232646 * 2 ^ 59
def prefixEnd_6232646 : Nat := 4983230072969 + 3 ^ 40 * 6232646 * 2
def baseEnd_6232646 : Nat := 3200343147322526977561589

theorem tailTrace_6232646 : CollatzResearch.WordTrace tailWord_6232646 prefixEnd_6232646 3200343147322526977561589 := by
  unfold tailWord_6232646
  simp only [CollatzResearch.WordTrace]
  refine ⟨7103852343068608376144431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 151548849985463645357747861 7103852343068608376144431)
  ·
    refine ⟨10655778514602912564216647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7103852343068608376144431 10655778514602912564216647)
    ·
      refine ⟨15983667771904368846324971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10655778514602912564216647 15983667771904368846324971)
      ·
        refine ⟨23975501657856553269487457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15983667771904368846324971 23975501657856553269487457)
        ·
          refine ⟨17981626243392414952115593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23975501657856553269487457 17981626243392414952115593)
          ·
            refine ⟨13486219682544311214086695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17981626243392414952115593 13486219682544311214086695)
            ·
              refine ⟨20229329523816466821130043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13486219682544311214086695 20229329523816466821130043)
              ·
                refine ⟨30343994285724700231695065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20229329523816466821130043 30343994285724700231695065)
                ·
                  refine ⟨22757995714293525173771299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30343994285724700231695065 22757995714293525173771299)
                  ·
                    refine ⟨34136993571440287760656949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22757995714293525173771299 34136993571440287760656949)
                    ·
                      refine ⟨3200343147322526977561589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34136993571440287760656949 3200343147322526977561589)
                      ·
                        rfl

theorem cell23_6232646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 1, 1, 2, 1, 5].length) (baseStart_6232646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6232646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6232646 prefixEnd_6232646 := by exact prefixLift 6232646
  have htrace : WordTrace (prefixWord ++ tailWord_6232646) baseStart_6232646 baseEnd_6232646 := by
    simpa [prefixWord, tailWord_6232646, baseEnd_6232646] using wordTrace_append hprefix tailTrace_6232646
  have hstable : (prefixWord ++ tailWord_6232646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6232646).length < 2 ^ (prefixWord ++ tailWord_6232646).sum := by decide
  have hdescent : baseEnd_6232646 < baseStart_6232646 := by decide
  rcases family_descends (prefixWord ++ tailWord_6232646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6232665 : List Nat := [1, 2, 1, 2, 2, 1, 1, 1, 2, 2, 8]
def baseStart_6232665 : Nat := 118140960795 + 6232665 * 2 ^ 59
def prefixEnd_6232665 : Nat := 4983230072969 + 3 ^ 40 * 6232665 * 2
def baseEnd_6232665 : Nat := 3200352903454962403224001

theorem tailTrace_6232665 : CollatzResearch.WordTrace tailWord_6232665 prefixEnd_6232665 3200352903454962403224001 := by
  unfold tailWord_6232665
  simp only [CollatzResearch.WordTrace]
  refine ⟨227323967965126634281563449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151549311976751089521042299 227323967965126634281563449)
  ·
    refine ⟨170492975973844975711172587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 227323967965126634281563449 170492975973844975711172587)
    ·
      refine ⟨255739463960767463566758881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170492975973844975711172587 255739463960767463566758881)
      ·
        refine ⟨191804597970575597675069161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 255739463960767463566758881 191804597970575597675069161)
        ·
          refine ⟨143853448477931698256301871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 191804597970575597675069161 143853448477931698256301871)
          ·
            refine ⟨215780172716897547384452807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 143853448477931698256301871 215780172716897547384452807)
            ·
              refine ⟨323670259075346321076679211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 215780172716897547384452807 323670259075346321076679211)
              ·
                refine ⟨485505388613019481615018817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 323670259075346321076679211 485505388613019481615018817)
                ·
                  refine ⟨364129041459764611211264113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 485505388613019481615018817 364129041459764611211264113)
                  ·
                    refine ⟨273096781094823458408448085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 364129041459764611211264113 273096781094823458408448085)
                    ·
                      refine ⟨3200352903454962403224001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 273096781094823458408448085 3200352903454962403224001)
                      ·
                        rfl

theorem cell23_6232665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 1, 2, 2, 8].length) (baseStart_6232665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6232665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6232665 prefixEnd_6232665 := by exact prefixLift 6232665
  have htrace : WordTrace (prefixWord ++ tailWord_6232665) baseStart_6232665 baseEnd_6232665 := by
    simpa [prefixWord, tailWord_6232665, baseEnd_6232665] using wordTrace_append hprefix tailTrace_6232665
  have hstable : (prefixWord ++ tailWord_6232665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6232665).length < 2 ^ (prefixWord ++ tailWord_6232665).sum := by decide
  have hdescent : baseEnd_6232665 < baseStart_6232665 := by decide
  rcases family_descends (prefixWord ++ tailWord_6232665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6232677 : List Nat := [1, 3, 1, 3, 5, 1, 2, 1, 2, 2, 2]
def baseStart_6232677 : Nat := 118140960795 + 6232677 * 2 ^ 59
def prefixEnd_6232677 : Nat := 4983230072969 + 3 ^ 40 * 6232677 * 2
def baseEnd_6232677 : Nat := 3200359065222816356273947

theorem tailTrace_6232677 : CollatzResearch.WordTrace tailWord_6232677 prefixEnd_6232677 3200359065222816356273947 := by
  unfold tailWord_6232677
  simp only [CollatzResearch.WordTrace]
  refine ⟨227324405641083160331000285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151549603760722106887333523 227324405641083160331000285)
  ·
    refine ⟨85246652115406185124125107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 227324405641083160331000285 85246652115406185124125107)
    ·
      refine ⟨127869978173109277686187661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85246652115406185124125107 127869978173109277686187661)
      ·
        refine ⟨47951241814915979132320373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 127869978173109277686187661 47951241814915979132320373)
        ·
          refine ⟨4495428920148373043655035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 47951241814915979132320373 4495428920148373043655035)
          ·
            refine ⟨6743143380222559565482553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4495428920148373043655035 6743143380222559565482553)
            ·
              refine ⟨5057357535166919674111915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6743143380222559565482553 5057357535166919674111915)
              ·
                refine ⟨7586036302750379511167873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5057357535166919674111915 7586036302750379511167873)
                ·
                  refine ⟨5689527227062784633375905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7586036302750379511167873 5689527227062784633375905)
                  ·
                    refine ⟨4267145420297088475031929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5689527227062784633375905 4267145420297088475031929)
                    ·
                      refine ⟨3200359065222816356273947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4267145420297088475031929 3200359065222816356273947)
                      ·
                        rfl

theorem cell23_6232677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 5, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 5, 1, 2, 1, 2, 2, 2].length) (baseStart_6232677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6232677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6232677 prefixEnd_6232677 := by exact prefixLift 6232677
  have htrace : WordTrace (prefixWord ++ tailWord_6232677) baseStart_6232677 baseEnd_6232677 := by
    simpa [prefixWord, tailWord_6232677, baseEnd_6232677] using wordTrace_append hprefix tailTrace_6232677
  have hstable : (prefixWord ++ tailWord_6232677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6232677).length < 2 ^ (prefixWord ++ tailWord_6232677).sum := by decide
  have hdescent : baseEnd_6232677 < baseStart_6232677 := by decide
  rcases family_descends (prefixWord ++ tailWord_6232677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6232743 : List Nat := [1, 1, 6, 3, 1, 1, 1, 2, 3, 4]
def baseStart_6232743 : Nat := 118140960795 + 6232743 * 2 ^ 59
def prefixEnd_6232743 : Nat := 4983230072969 + 3 ^ 40 * 6232743 * 2
def baseEnd_6232743 : Nat := 1066797651648671032682881

theorem tailTrace_6232743 : CollatzResearch.WordTrace tailWord_6232743 prefixEnd_6232743 1066797651648671032682881 := by
  unfold tailWord_6232743
  simp only [CollatzResearch.WordTrace]
  refine ⟨227326812858844053602902883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151551208572562702401935255 227326812858844053602902883)
  ·
    refine ⟨340990219288266080404354325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227326812858844053602902883 340990219288266080404354325)
    ·
      refine ⟨15983916529137472518954109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 340990219288266080404354325 15983916529137472518954109)
      ·
        refine ⟨5993968698426552194607791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15983916529137472518954109 5993968698426552194607791)
        ·
          refine ⟨8990953047639828291911687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5993968698426552194607791 8990953047639828291911687)
          ·
            refine ⟨13486429571459742437867531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8990953047639828291911687 13486429571459742437867531)
            ·
              refine ⟨20229644357189613656801297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13486429571459742437867531 20229644357189613656801297)
              ·
                refine ⟨15172233267892210242600973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20229644357189613656801297 15172233267892210242600973)
                ·
                  refine ⟨5689587475459578840975365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15172233267892210242600973 5689587475459578840975365)
                  ·
                    refine ⟨1066797651648671032682881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5689587475459578840975365 1066797651648671032682881)
                    ·
                      rfl

theorem cell23_6232743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 1, 2, 3, 4].length) (baseStart_6232743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6232743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6232743 prefixEnd_6232743 := by exact prefixLift 6232743
  have htrace : WordTrace (prefixWord ++ tailWord_6232743) baseStart_6232743 baseEnd_6232743 := by
    simpa [prefixWord, tailWord_6232743, baseEnd_6232743] using wordTrace_append hprefix tailTrace_6232743
  have hstable : (prefixWord ++ tailWord_6232743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6232743).length < 2 ^ (prefixWord ++ tailWord_6232743).sum := by decide
  have hdescent : baseEnd_6232743 < baseStart_6232743 := by decide
  rcases family_descends (prefixWord ++ tailWord_6232743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6232766 : List Nat := [4, 2, 1, 1, 2, 1, 1, 2, 5, 1, 3]
def baseStart_6232766 : Nat := 118140960795 + 6232766 * 2 ^ 59
def prefixEnd_6232766 : Nat := 4983230072969 + 3 ^ 40 * 6232766 * 2
def baseEnd_6232766 : Nat := 3200404765001066508061037

theorem tailTrace_6232766 : CollatzResearch.WordTrace tailWord_6232766 prefixEnd_6232766 3200404765001066508061037 := by
  unfold tailWord_6232766
  simp only [CollatzResearch.WordTrace]
  refine ⟨28415956467220091066373769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 151551767825173819020660101 28415956467220091066373769)
  ·
    refine ⟨21311967350415068299780327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28415956467220091066373769 21311967350415068299780327)
    ·
      refine ⟨31967951025622602449670491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21311967350415068299780327 31967951025622602449670491)
      ·
        refine ⟨47951926538433903674505737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31967951025622602449670491 47951926538433903674505737)
        ·
          refine ⟨35963944903825427755879303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47951926538433903674505737 35963944903825427755879303)
          ·
            refine ⟨53945917355738141633818955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35963944903825427755879303 53945917355738141633818955)
            ·
              refine ⟨80918876033607212450728433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53945917355738141633818955 80918876033607212450728433)
              ·
                refine ⟨60689157025205409338046325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 80918876033607212450728433 60689157025205409338046325)
                ·
                  refine ⟨5689608471113007125441843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 60689157025205409338046325 5689608471113007125441843)
                  ·
                    refine ⟨8534412706669510688162765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5689608471113007125441843 8534412706669510688162765)
                    ·
                      refine ⟨3200404765001066508061037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8534412706669510688162765 3200404765001066508061037)
                      ·
                        rfl

theorem cell23_6232766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 2, 5, 1, 3].length) (baseStart_6232766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6232766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6232766 prefixEnd_6232766 := by exact prefixLift 6232766
  have htrace : WordTrace (prefixWord ++ tailWord_6232766) baseStart_6232766 baseEnd_6232766 := by
    simpa [prefixWord, tailWord_6232766, baseEnd_6232766] using wordTrace_append hprefix tailTrace_6232766
  have hstable : (prefixWord ++ tailWord_6232766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6232766).length < 2 ^ (prefixWord ++ tailWord_6232766).sum := by decide
  have hdescent : baseEnd_6232766 < baseStart_6232766 := by decide
  rcases family_descends (prefixWord ++ tailWord_6232766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6232799 : List Nat := [1, 1, 2, 3, 2, 3, 3, 1, 1, 6]
def baseStart_6232799 : Nat := 118140960795 + 6232799 * 2 ^ 59
def prefixEnd_6232799 : Nat := 4983230072969 + 3 ^ 40 * 6232799 * 2
def baseEnd_6232799 : Nat := 1066807236620888292982795

theorem tailTrace_6232799 : CollatzResearch.WordTrace tailWord_6232799 prefixEnd_6232799 1066807236620888292982795 := by
  unfold tailWord_6232799
  simp only [CollatzResearch.WordTrace]
  refine ⟨227328855346641175166941451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151552570231094116777960967 227328855346641175166941451)
  ·
    refine ⟨340993283019961762750412177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227328855346641175166941451 340993283019961762750412177)
    ·
      refine ⟨255744962264971322062809133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 340993283019961762750412177 255744962264971322062809133)
      ·
        refine ⟨95904360849364245773553425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 255744962264971322062809133 95904360849364245773553425)
        ·
          refine ⟨71928270637023184330165069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95904360849364245773553425 71928270637023184330165069)
          ·
            refine ⟨26973101488883694123811901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 71928270637023184330165069 26973101488883694123811901)
            ·
              refine ⟨10114913058331385296429463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26973101488883694123811901 10114913058331385296429463)
              ·
                refine ⟨15172369587497077944644195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10114913058331385296429463 15172369587497077944644195)
                ·
                  refine ⟨22758554381245616916966293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15172369587497077944644195 22758554381245616916966293)
                  ·
                    refine ⟨1066807236620888292982795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22758554381245616916966293 1066807236620888292982795)
                    ·
                      rfl

theorem cell23_6232799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 3, 1, 1, 6].length) (baseStart_6232799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6232799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6232799 prefixEnd_6232799 := by exact prefixLift 6232799
  have htrace : WordTrace (prefixWord ++ tailWord_6232799) baseStart_6232799 baseEnd_6232799 := by
    simpa [prefixWord, tailWord_6232799, baseEnd_6232799] using wordTrace_append hprefix tailTrace_6232799
  have hstable : (prefixWord ++ tailWord_6232799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6232799).length < 2 ^ (prefixWord ++ tailWord_6232799).sum := by decide
  have hdescent : baseEnd_6232799 < baseStart_6232799 := by decide
  rcases family_descends (prefixWord ++ tailWord_6232799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6232809 : List Nat := [1, 2, 1, 1, 1, 2, 4, 3, 3, 2, 3]
def baseStart_6232809 : Nat := 118140960795 + 6232809 * 2 ^ 59
def prefixEnd_6232809 : Nat := 4983230072969 + 3 ^ 40 * 6232809 * 2
def baseEnd_6232809 : Nat := 3200426844669209839823339

theorem tailTrace_6232809 : CollatzResearch.WordTrace tailWord_6232809 prefixEnd_6232809 3200426844669209839823339 := by
  unfold tailWord_6232809
  simp only [CollatzResearch.WordTrace]
  refine ⟨227329220076604946874805481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151552813384403297916536987 227329220076604946874805481)
  ·
    refine ⟨170496915057453710156104111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 227329220076604946874805481 170496915057453710156104111)
    ·
      refine ⟨255745372586180565234156167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170496915057453710156104111 255745372586180565234156167)
      ·
        refine ⟨383618058879270847851234251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 255745372586180565234156167 383618058879270847851234251)
        ·
          refine ⟨575427088318906271776851377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 383618058879270847851234251 575427088318906271776851377)
          ·
            refine ⟨431570316239179703832638533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 575427088318906271776851377 431570316239179703832638533)
            ·
              refine ⟨80919434294846194468619725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 431570316239179703832638533 80919434294846194468619725)
              ·
                refine ⟨30344787860567322925732397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 80919434294846194468619725 30344787860567322925732397)
                ·
                  refine ⟨11379295447712746097149649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30344787860567322925732397 11379295447712746097149649)
                  ·
                    refine ⟨8534471585784559572862237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11379295447712746097149649 8534471585784559572862237)
                    ·
                      refine ⟨3200426844669209839823339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8534471585784559572862237 3200426844669209839823339)
                      ·
                        rfl

theorem cell23_6232809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 3, 3, 2, 3].length) (baseStart_6232809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6232809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6232809 prefixEnd_6232809 := by exact prefixLift 6232809
  have htrace : WordTrace (prefixWord ++ tailWord_6232809) baseStart_6232809 baseEnd_6232809 := by
    simpa [prefixWord, tailWord_6232809, baseEnd_6232809] using wordTrace_append hprefix tailTrace_6232809
  have hstable : (prefixWord ++ tailWord_6232809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6232809).length < 2 ^ (prefixWord ++ tailWord_6232809).sum := by decide
  have hdescent : baseEnd_6232809 < baseStart_6232809 := by decide
  rcases family_descends (prefixWord ++ tailWord_6232809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6232826 : List Nat := [3, 1, 1, 1, 1, 3, 4, 3, 1, 2, 3]
def baseStart_6232826 : Nat := 118140960795 + 6232826 * 2 ^ 59
def prefixEnd_6232826 : Nat := 4983230072969 + 3 ^ 40 * 6232826 * 2
def baseEnd_6232826 : Nat := 3200435573840336273310761

theorem tailTrace_6232826 : CollatzResearch.WordTrace tailWord_6232826 prefixEnd_6232826 3200435573840336273310761 := by
  unfold tailWord_6232826
  simp only [CollatzResearch.WordTrace]
  refine ⟨56832460029385839694543583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151553226745028905852116221 56832460029385839694543583)
  ·
    refine ⟨85248690044078759541815375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56832460029385839694543583 85248690044078759541815375)
    ·
      refine ⟨127873035066118139312723063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85248690044078759541815375 127873035066118139312723063)
      ·
        refine ⟨191809552599177208969084595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127873035066118139312723063 191809552599177208969084595)
        ·
          refine ⟨287714328898765813453626893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 191809552599177208969084595 287714328898765813453626893)
          ·
            refine ⟨107892873337037180045110085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 287714328898765813453626893 107892873337037180045110085)
            ·
              refine ⟨20229913750694471258458141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 107892873337037180045110085 20229913750694471258458141)
              ·
                refine ⟨7586217656510426721921803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20229913750694471258458141 7586217656510426721921803)
                ·
                  refine ⟨11379326484765640082882705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7586217656510426721921803 11379326484765640082882705)
                  ·
                    refine ⟨8534494863574230062162029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11379326484765640082882705 8534494863574230062162029)
                    ·
                      refine ⟨3200435573840336273310761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8534494863574230062162029 3200435573840336273310761)
                      ·
                        rfl

theorem cell23_6232826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 4, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 4, 3, 1, 2, 3].length) (baseStart_6232826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6232826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6232826 prefixEnd_6232826 := by exact prefixLift 6232826
  have htrace : WordTrace (prefixWord ++ tailWord_6232826) baseStart_6232826 baseEnd_6232826 := by
    simpa [prefixWord, tailWord_6232826, baseEnd_6232826] using wordTrace_append hprefix tailTrace_6232826
  have hstable : (prefixWord ++ tailWord_6232826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6232826).length < 2 ^ (prefixWord ++ tailWord_6232826).sum := by decide
  have hdescent : baseEnd_6232826 < baseStart_6232826 := by decide
  rcases family_descends (prefixWord ++ tailWord_6232826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6232832 : List Nat := [2, 1, 1, 2, 1, 1, 2, 1, 4, 2, 6]
def baseStart_6232832 : Nat := 118140960795 + 6232832 * 2 ^ 59
def prefixEnd_6232832 : Nat := 4983230072969 + 3 ^ 40 * 6232832 * 2
def baseEnd_6232832 : Nat := 3200438654724263249835733

theorem tailTrace_6232832 : CollatzResearch.WordTrace tailWord_6232832 prefixEnd_6232832 3200438654724263249835733 := by
  unfold tailWord_6232832
  simp only [CollatzResearch.WordTrace]
  refine ⟨113665029477760810901446375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151553372637014414535261833 113665029477760810901446375)
  ·
    refine ⟨170497544216641216352169563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113665029477760810901446375 170497544216641216352169563)
    ·
      refine ⟨255746316324961824528254345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170497544216641216352169563 255746316324961824528254345)
      ·
        refine ⟨191809737243721368396190759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 255746316324961824528254345 191809737243721368396190759)
        ·
          refine ⟨287714605865582052594286139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 191809737243721368396190759 287714605865582052594286139)
          ·
            refine ⟨431571908798373078891429209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 287714605865582052594286139 431571908798373078891429209)
            ·
              refine ⟨323678931598779809168571907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 431571908798373078891429209 323678931598779809168571907)
              ·
                refine ⟨485518397398169713752857861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 323678931598779809168571907 485518397398169713752857861)
                ·
                  refine ⟨91034699512156821328660849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 485518397398169713752857861 91034699512156821328660849)
                  ·
                    refine ⟨68276024634117615996495637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 91034699512156821328660849 68276024634117615996495637)
                    ·
                      refine ⟨3200438654724263249835733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 68276024634117615996495637 3200438654724263249835733)
                      ·
                        rfl

theorem cell23_6232832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 1, 4, 2, 6].length) (baseStart_6232832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6232832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6232832 prefixEnd_6232832 := by exact prefixLift 6232832
  have htrace : WordTrace (prefixWord ++ tailWord_6232832) baseStart_6232832 baseEnd_6232832 := by
    simpa [prefixWord, tailWord_6232832, baseEnd_6232832] using wordTrace_append hprefix tailTrace_6232832
  have hstable : (prefixWord ++ tailWord_6232832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6232832).length < 2 ^ (prefixWord ++ tailWord_6232832).sum := by decide
  have hdescent : baseEnd_6232832 < baseStart_6232832 := by decide
  rcases family_descends (prefixWord ++ tailWord_6232832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6232840 : List Nat := [2, 1, 3, 2, 2, 4, 1, 1, 3, 2, 2]
def baseStart_6232840 : Nat := 118140960795 + 6232840 * 2 ^ 59
def prefixEnd_6232840 : Nat := 4983230072969 + 3 ^ 40 * 6232840 * 2
def baseEnd_6232840 : Nat := 3200442762569499218535697

theorem tailTrace_6232840 : CollatzResearch.WordTrace tailWord_6232840 prefixEnd_6232840 3200442762569499218535697 := by
  unfold tailWord_6232840
  simp only [CollatzResearch.WordTrace]
  refine ⟨113665175369746319584591987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151553567159661759446122649 113665175369746319584591987)
  ·
    refine ⟨170497763054619479376887981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113665175369746319584591987 170497763054619479376887981)
    ·
      refine ⟨63936661145482304766332993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 170497763054619479376887981 63936661145482304766332993)
      ·
        refine ⟨47952495859111728574749745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63936661145482304766332993 47952495859111728574749745)
        ·
          refine ⟨35964371894333796431062309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47952495859111728574749745 35964371894333796431062309)
          ·
            refine ⟨6743319730187586830824183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35964371894333796431062309 6743319730187586830824183)
            ·
              refine ⟨10114979595281380246236275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6743319730187586830824183 10114979595281380246236275)
              ·
                refine ⟨15172469392922070369354413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10114979595281380246236275 15172469392922070369354413)
                ·
                  refine ⟨5689676022345776388507905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15172469392922070369354413 5689676022345776388507905)
                  ·
                    refine ⟨4267257016759332291380929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5689676022345776388507905 4267257016759332291380929)
                    ·
                      refine ⟨3200442762569499218535697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4267257016759332291380929 3200442762569499218535697)
                      ·
                        rfl

theorem cell23_6232840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 4, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 4, 1, 1, 3, 2, 2].length) (baseStart_6232840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6232840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6232840 prefixEnd_6232840 := by exact prefixLift 6232840
  have htrace : WordTrace (prefixWord ++ tailWord_6232840) baseStart_6232840 baseEnd_6232840 := by
    simpa [prefixWord, tailWord_6232840, baseEnd_6232840] using wordTrace_append hprefix tailTrace_6232840
  have hstable : (prefixWord ++ tailWord_6232840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6232840).length < 2 ^ (prefixWord ++ tailWord_6232840).sum := by decide
  have hdescent : baseEnd_6232840 < baseStart_6232840 := by decide
  rcases family_descends (prefixWord ++ tailWord_6232840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6232850 : List Nat := [3, 2, 4, 1, 2, 1, 1, 3, 2, 4]
def baseStart_6232850 : Nat := 118140960795 + 6232850 * 2 ^ 59
def prefixEnd_6232850 : Nat := 4983230072969 + 3 ^ 40 * 6232850 * 2
def baseEnd_6232850 : Nat := 1066815965792014726470217

theorem tailTrace_6232850 : CollatzResearch.WordTrace tailWord_6232850 prefixEnd_6232850 1066815965792014726470217 := by
  unfold tailWord_6232850
  simp only [CollatzResearch.WordTrace]
  refine ⟨56832678867364102719262001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151553810312970940584698669 56832678867364102719262001)
  ·
    refine ⟨42624509150523077039446501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56832678867364102719262001 42624509150523077039446501)
    ·
      refine ⟨7992095465723076944896219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 42624509150523077039446501 7992095465723076944896219)
      ·
        refine ⟨11988143198584615417344329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7992095465723076944896219 11988143198584615417344329)
        ·
          refine ⟨8991107398938461563008247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11988143198584615417344329 8991107398938461563008247)
          ·
            refine ⟨13486661098407692344512371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8991107398938461563008247 13486661098407692344512371)
            ·
              refine ⟨20229991647611538516768557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13486661098407692344512371 20229991647611538516768557)
              ·
                refine ⟨7586246867854326943788209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20229991647611538516768557 7586246867854326943788209)
                ·
                  refine ⟨5689685150890745207841157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7586246867854326943788209 5689685150890745207841157)
                  ·
                    refine ⟨1066815965792014726470217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5689685150890745207841157 1066815965792014726470217)
                    ·
                      rfl

theorem cell23_6232850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 1, 3, 2, 4].length) (baseStart_6232850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6232850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6232850 prefixEnd_6232850 := by exact prefixLift 6232850
  have htrace : WordTrace (prefixWord ++ tailWord_6232850) baseStart_6232850 baseEnd_6232850 := by
    simpa [prefixWord, tailWord_6232850, baseEnd_6232850] using wordTrace_append hprefix tailTrace_6232850
  have hstable : (prefixWord ++ tailWord_6232850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6232850).length < 2 ^ (prefixWord ++ tailWord_6232850).sum := by decide
  have hdescent : baseEnd_6232850 < baseStart_6232850 := by decide
  rcases family_descends (prefixWord ++ tailWord_6232850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6232877 : List Nat := [1, 5, 3, 2, 2, 1, 1, 1, 1, 1, 5]
def baseStart_6232877 : Nat := 118140960795 + 6232877 * 2 ^ 59
def prefixEnd_6232877 : Nat := 4983230072969 + 3 ^ 40 * 6232877 * 2
def baseEnd_6232877 : Nat := 3200461761353715573773027

theorem tailTrace_6232877 : CollatzResearch.WordTrace tailWord_6232877 prefixEnd_6232877 3200461761353715573773027 := by
  unfold tailWord_6232877
  simp only [CollatzResearch.WordTrace]
  refine ⟨227331700240358594488280885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151554466826905729658853923 227331700240358594488280885)
  ·
    refine ⟨21312346897533618233276333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 227331700240358594488280885 21312346897533618233276333)
    ·
      refine ⟨7992130086575106837478625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21312346897533618233276333 7992130086575106837478625)
      ·
        refine ⟨5994097564931330128108969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7992130086575106837478625 5994097564931330128108969)
        ·
          refine ⟨4495573173698497596081727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5994097564931330128108969 4495573173698497596081727)
          ·
            refine ⟨6743359760547746394122591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4495573173698497596081727 6743359760547746394122591)
            ·
              refine ⟨10115039640821619591183887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6743359760547746394122591 10115039640821619591183887)
              ·
                refine ⟨15172559461232429386775831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10115039640821619591183887 15172559461232429386775831)
                ·
                  refine ⟨22758839191848644080163747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15172559461232429386775831 22758839191848644080163747)
                  ·
                    refine ⟨34138258787772966120245621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22758839191848644080163747 34138258787772966120245621)
                    ·
                      refine ⟨3200461761353715573773027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34138258787772966120245621 3200461761353715573773027)
                      ·
                        rfl

theorem cell23_6232877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 2, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 2, 1, 1, 1, 1, 1, 5].length) (baseStart_6232877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6232877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6232877 prefixEnd_6232877 := by exact prefixLift 6232877
  have htrace : WordTrace (prefixWord ++ tailWord_6232877) baseStart_6232877 baseEnd_6232877 := by
    simpa [prefixWord, tailWord_6232877, baseEnd_6232877] using wordTrace_append hprefix tailTrace_6232877
  have hstable : (prefixWord ++ tailWord_6232877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6232877).length < 2 ^ (prefixWord ++ tailWord_6232877).sum := by decide
  have hdescent : baseEnd_6232877 < baseStart_6232877 := by decide
  rcases family_descends (prefixWord ++ tailWord_6232877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6232890 : List Nat := [3, 1, 1, 1, 6, 1, 2, 2, 2, 1, 3]
def baseStart_6232890 : Nat := 118140960795 + 6232890 * 2 ^ 59
def prefixEnd_6232890 : Nat := 4983230072969 + 3 ^ 40 * 6232890 * 2
def baseEnd_6232890 : Nat := 3200468436602224022910467

theorem tailTrace_6232890 : CollatzResearch.WordTrace tailWord_6232890 prefixEnd_6232890 3200468436602224022910467 := by
  unfold tailWord_6232890
  simp only [CollatzResearch.WordTrace]
  refine ⟨56833043597327874427126031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151554782926207665139002749 56833043597327874427126031)
  ·
    refine ⟨85249565395991811640689047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56833043597327874427126031 85249565395991811640689047)
    ·
      refine ⟨127874348093987717461033571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85249565395991811640689047 127874348093987717461033571)
      ·
        refine ⟨191811522140981576191550357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127874348093987717461033571 191811522140981576191550357)
        ·
          refine ⟨8991165100358511383978923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 191811522140981576191550357 8991165100358511383978923)
          ·
            refine ⟨13486747650537767075968385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8991165100358511383978923 13486747650537767075968385)
            ·
              refine ⟨10115060737903325306976289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13486747650537767075968385 10115060737903325306976289)
              ·
                refine ⟨7586295553427493980232217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10115060737903325306976289 7586295553427493980232217)
                ·
                  refine ⟨5689721665070620485174163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7586295553427493980232217 5689721665070620485174163)
                  ·
                    refine ⟨8534582497605930727761245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5689721665070620485174163 8534582497605930727761245)
                    ·
                      refine ⟨3200468436602224022910467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8534582497605930727761245 3200468436602224022910467)
                      ·
                        rfl

theorem cell23_6232890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 2, 2, 2, 1, 3].length) (baseStart_6232890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6232890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6232890 prefixEnd_6232890 := by exact prefixLift 6232890
  have htrace : WordTrace (prefixWord ++ tailWord_6232890) baseStart_6232890 baseEnd_6232890 := by
    simpa [prefixWord, tailWord_6232890, baseEnd_6232890] using wordTrace_append hprefix tailTrace_6232890
  have hstable : (prefixWord ++ tailWord_6232890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6232890).length < 2 ^ (prefixWord ++ tailWord_6232890).sum := by decide
  have hdescent : baseEnd_6232890 < baseStart_6232890 := by decide
  rcases family_descends (prefixWord ++ tailWord_6232890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6232899 : List Nat := [1, 1, 1, 3, 1, 4, 1, 1, 1, 6, 3]
def baseStart_6232899 : Nat := 118140960795 + 6232899 * 2 ^ 59
def prefixEnd_6232899 : Nat := 4983230072969 + 3 ^ 40 * 6232899 * 2
def baseEnd_6232899 : Nat := 3200473057928114487697925

theorem tailTrace_6232899 : CollatzResearch.WordTrace tailWord_6232899 prefixEnd_6232899 3200473057928114487697925 := by
  unfold tailWord_6232899
  simp only [CollatzResearch.WordTrace]
  refine ⟨227332502646278892245581751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151555001764185928163721167 227332502646278892245581751)
  ·
    refine ⟨340998753969418338368372627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227332502646278892245581751 340998753969418338368372627)
    ·
      refine ⟨511498130954127507552558941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 340998753969418338368372627 511498130954127507552558941)
      ·
        refine ⟨191811799107797815332209603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 511498130954127507552558941 191811799107797815332209603)
        ·
          refine ⟨287717698661696722998314405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 191811799107797815332209603 287717698661696722998314405)
          ·
            refine ⟨53947068499068135562183951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 287717698661696722998314405 53947068499068135562183951)
            ·
              refine ⟨80920602748602203343275927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53947068499068135562183951 80920602748602203343275927)
              ·
                refine ⟨121380904122903305014913891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 80920602748602203343275927 121380904122903305014913891)
                ·
                  refine ⟨182071356184354957522370837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 121380904122903305014913891 182071356184354957522370837)
                  ·
                    refine ⟨8534594821141638633861133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 182071356184354957522370837 8534594821141638633861133)
                    ·
                      refine ⟨3200473057928114487697925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8534594821141638633861133 3200473057928114487697925)
                      ·
                        rfl

theorem cell23_6232899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 1, 1, 6, 3].length) (baseStart_6232899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6232899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6232899 prefixEnd_6232899 := by exact prefixLift 6232899
  have htrace : WordTrace (prefixWord ++ tailWord_6232899) baseStart_6232899 baseEnd_6232899 := by
    simpa [prefixWord, tailWord_6232899, baseEnd_6232899] using wordTrace_append hprefix tailTrace_6232899
  have hstable : (prefixWord ++ tailWord_6232899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6232899).length < 2 ^ (prefixWord ++ tailWord_6232899).sum := by decide
  have hdescent : baseEnd_6232899 < baseStart_6232899 := by decide
  rcases family_descends (prefixWord ++ tailWord_6232899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6232919 : List Nat := [1, 1, 3, 2, 4, 1, 1, 1, 9]
def baseStart_6232919 : Nat := 118140960795 + 6232919 * 2 ^ 59
def prefixEnd_6232919 : Nat := 4983230072969 + 3 ^ 40 * 6232919 * 2
def baseEnd_6232919 : Nat := 355609258615689378827537

theorem tailTrace_6232919 : CollatzResearch.WordTrace tailWord_6232919 prefixEnd_6232919 355609258615689378827537 := by
  unfold tailWord_6232919
  simp only [CollatzResearch.WordTrace]
  refine ⟨227333232106206435661309811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151555488070804290440873207 227333232106206435661309811)
  ·
    refine ⟨340999848159309653491964717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227333232106206435661309811 340999848159309653491964717)
    ·
      refine ⟨127874943059741120059486769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 340999848159309653491964717 127874943059741120059486769)
      ·
        refine ⟨95906207294805840044615077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 127874943059741120059486769 95906207294805840044615077)
        ·
          refine ⟨17982413867776095008365327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 95906207294805840044615077 17982413867776095008365327)
          ·
            refine ⟨26973620801664142512547991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17982413867776095008365327 26973620801664142512547991)
            ·
              refine ⟨40460431202496213768821987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26973620801664142512547991 40460431202496213768821987)
              ·
                refine ⟨60690646803744320653232981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40460431202496213768821987 60690646803744320653232981)
                ·
                  refine ⟨355609258615689378827537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 60690646803744320653232981 355609258615689378827537)
                  ·
                    rfl

theorem cell23_6232919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 1, 1, 9].length) (baseStart_6232919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6232919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6232919 prefixEnd_6232919 := by exact prefixLift 6232919
  have htrace : WordTrace (prefixWord ++ tailWord_6232919) baseStart_6232919 baseEnd_6232919 := by
    simpa [prefixWord, tailWord_6232919, baseEnd_6232919] using wordTrace_append hprefix tailTrace_6232919
  have hstable : (prefixWord ++ tailWord_6232919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6232919).length < 2 ^ (prefixWord ++ tailWord_6232919).sum := by decide
  have hdescent : baseEnd_6232919 < baseStart_6232919 := by decide
  rcases family_descends (prefixWord ++ tailWord_6232919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6232946 : List Nat := [3, 2, 1, 2, 1, 1, 3, 2, 2, 3, 3]
def baseStart_6232946 : Nat := 118140960795 + 6232946 * 2 ^ 59
def prefixEnd_6232946 : Nat := 4983230072969 + 3 ^ 40 * 6232946 * 2
def baseEnd_6232946 : Nat := 3200497191518875803810209

theorem tailTrace_6232946 : CollatzResearch.WordTrace tailWord_6232946 prefixEnd_6232946 3200497191518875803810209 := by
  unfold tailWord_6232946
  simp only [CollatzResearch.WordTrace]
  refine ⟨56833554219277154818135673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151556144584739079515028461 56833554219277154818135673)
  ·
    refine ⟨42625165664457866113601755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56833554219277154818135673 42625165664457866113601755)
    ·
      refine ⟨63937748496686799170402633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42625165664457866113601755 63937748496686799170402633)
      ·
        refine ⟨47953311372515099377801975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63937748496686799170402633 47953311372515099377801975)
        ·
          refine ⟨71929967058772649066702963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47953311372515099377801975 71929967058772649066702963)
          ·
            refine ⟨107894950588158973600054445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71929967058772649066702963 107894950588158973600054445)
            ·
              refine ⟨40460606470559615100020417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 107894950588158973600054445 40460606470559615100020417)
              ·
                refine ⟨30345454852919711325015313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40460606470559615100020417 30345454852919711325015313)
                ·
                  refine ⟨22759091139689783493761485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30345454852919711325015313 22759091139689783493761485)
                  ·
                    refine ⟨8534659177383668810160557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22759091139689783493761485 8534659177383668810160557)
                    ·
                      refine ⟨3200497191518875803810209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8534659177383668810160557 3200497191518875803810209)
                      ·
                        rfl

theorem cell23_6232946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 3, 2, 2, 3, 3].length) (baseStart_6232946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6232946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6232946 prefixEnd_6232946 := by exact prefixLift 6232946
  have htrace : WordTrace (prefixWord ++ tailWord_6232946) baseStart_6232946 baseEnd_6232946 := by
    simpa [prefixWord, tailWord_6232946, baseEnd_6232946] using wordTrace_append hprefix tailTrace_6232946
  have hstable : (prefixWord ++ tailWord_6232946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6232946).length < 2 ^ (prefixWord ++ tailWord_6232946).sum := by decide
  have hdescent : baseEnd_6232946 < baseStart_6232946 := by decide
  rcases family_descends (prefixWord ++ tailWord_6232946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6232956 : List Nat := [2, 2, 2, 1, 1, 1, 1, 3, 1, 7, 2]
def baseStart_6232956 : Nat := 118140960795 + 6232956 * 2 ^ 59
def prefixEnd_6232956 : Nat := 4983230072969 + 3 ^ 40 * 6232956 * 2
def baseEnd_6232956 : Nat := 3200502326325420764685163

theorem tailTrace_6232956 : CollatzResearch.WordTrace tailWord_6232956 prefixEnd_6232956 3200502326325420764685163 := by
  unfold tailWord_6232956
  simp only [CollatzResearch.WordTrace]
  refine ⟨113667290803536195490203361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151556387738048260653604481 113667290803536195490203361)
  ·
    refine ⟨85250468102652146617652521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113667290803536195490203361 85250468102652146617652521)
    ·
      refine ⟨63937851076989109963239391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85250468102652146617652521 63937851076989109963239391)
      ·
        refine ⟨95906776615483664944859087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63937851076989109963239391 95906776615483664944859087)
        ·
          refine ⟨143860164923225497417288631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95906776615483664944859087 143860164923225497417288631)
          ·
            refine ⟨215790247384838246125932947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 143860164923225497417288631 215790247384838246125932947)
            ·
              refine ⟨323685371077257369188899421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 215790247384838246125932947 323685371077257369188899421)
              ·
                refine ⟨121382014153971513445837283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 323685371077257369188899421 121382014153971513445837283)
                ·
                  refine ⟨182073021230957270168755925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 121382014153971513445837283 182073021230957270168755925)
                  ·
                    refine ⟨4267336435100561019580217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 182073021230957270168755925 4267336435100561019580217)
                    ·
                      refine ⟨3200502326325420764685163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4267336435100561019580217 3200502326325420764685163)
                      ·
                        rfl

theorem cell23_6232956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 3, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 3, 1, 7, 2].length) (baseStart_6232956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6232956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6232956 prefixEnd_6232956 := by exact prefixLift 6232956
  have htrace : WordTrace (prefixWord ++ tailWord_6232956) baseStart_6232956 baseEnd_6232956 := by
    simpa [prefixWord, tailWord_6232956, baseEnd_6232956] using wordTrace_append hprefix tailTrace_6232956
  have hstable : (prefixWord ++ tailWord_6232956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6232956).length < 2 ^ (prefixWord ++ tailWord_6232956).sum := by decide
  have hdescent : baseEnd_6232956 < baseStart_6232956 := by decide
  rcases family_descends (prefixWord ++ tailWord_6232956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6232959 : List Nat := [1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 5]
def baseStart_6232959 : Nat := 118140960795 + 6232959 * 2 ^ 59
def prefixEnd_6232959 : Nat := 4983230072969 + 3 ^ 40 * 6232959 * 2
def baseEnd_6232959 : Nat := 3200503866767384252947649

theorem tailTrace_6232959 : CollatzResearch.WordTrace tailWord_6232959 prefixEnd_6232959 3200503866767384252947649 := by
  unfold tailWord_6232959
  simp only [CollatzResearch.WordTrace]
  refine ⟨227334691026061522492765931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151556460684041014995177287 227334691026061522492765931)
  ·
    refine ⟨341002036539092283739148897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227334691026061522492765931 341002036539092283739148897)
    ·
      refine ⟨255751527404319212804361673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 341002036539092283739148897 255751527404319212804361673)
      ·
        refine ⟨191813645553239409603271255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 255751527404319212804361673 191813645553239409603271255)
        ·
          refine ⟨287720468329859114404906883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 191813645553239409603271255 287720468329859114404906883)
          ·
            refine ⟨431580702494788671607360325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 287720468329859114404906883 431580702494788671607360325)
            ·
              refine ⟨80921381717772875926380061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 431580702494788671607360325 80921381717772875926380061)
              ·
                refine ⟨30345518144164828472392523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 80921381717772875926380061 30345518144164828472392523)
                ·
                  refine ⟨45518277216247242708588785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30345518144164828472392523 45518277216247242708588785)
                  ·
                    refine ⟨34138707912185432031441589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 45518277216247242708588785 34138707912185432031441589)
                    ·
                      refine ⟨3200503866767384252947649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34138707912185432031441589 3200503866767384252947649)
                      ·
                        rfl

theorem cell23_6232959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 5].length) (baseStart_6232959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6232959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6232959 prefixEnd_6232959 := by exact prefixLift 6232959
  have htrace : WordTrace (prefixWord ++ tailWord_6232959) baseStart_6232959 baseEnd_6232959 := by
    simpa [prefixWord, tailWord_6232959, baseEnd_6232959] using wordTrace_append hprefix tailTrace_6232959
  have hstable : (prefixWord ++ tailWord_6232959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6232959).length < 2 ^ (prefixWord ++ tailWord_6232959).sum := by decide
  have hdescent : baseEnd_6232959 < baseStart_6232959 := by decide
  rcases family_descends (prefixWord ++ tailWord_6232959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6233029 : List Nat := [1, 3, 1, 1, 1, 1, 1, 2, 3, 1, 8]
def baseStart_6233029 : Nat := 118140960795 + 6233029 * 2 ^ 59
def prefixEnd_6233029 : Nat := 4983230072969 + 3 ^ 40 * 6233029 * 2
def baseEnd_6233029 : Nat := 3200539810413198979072327

theorem tailTrace_6233029 : CollatzResearch.WordTrace tailWord_6233029 prefixEnd_6233029 3200539810413198979072327 := by
  unfold tailWord_6233029
  simp only [CollatzResearch.WordTrace]
  refine ⟨227337244135807924447814141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151558162757205282965209427 227337244135807924447814141)
  ·
    refine ⟨85251466550927971667930303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 227337244135807924447814141 85251466550927971667930303)
    ·
      refine ⟨127877199826391957501895455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85251466550927971667930303 127877199826391957501895455)
      ·
        refine ⟨191815799739587936252843183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127877199826391957501895455 191815799739587936252843183)
        ·
          refine ⟨287723699609381904379264775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 191815799739587936252843183 287723699609381904379264775)
          ·
            refine ⟨431585549414072856568897163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 287723699609381904379264775 431585549414072856568897163)
            ·
              refine ⟨647378324121109284853345745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 431585549414072856568897163 647378324121109284853345745)
              ·
                refine ⟨485533743090831963640009309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 647378324121109284853345745 485533743090831963640009309)
                ·
                  refine ⟨182075153659061986365003491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 485533743090831963640009309 182075153659061986365003491)
                  ·
                    refine ⟨273112730488592979547505237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 182075153659061986365003491 273112730488592979547505237)
                    ·
                      refine ⟨3200539810413198979072327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 273112730488592979547505237 3200539810413198979072327)
                      ·
                        rfl

theorem cell23_6233029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 2, 3, 1, 8].length) (baseStart_6233029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6233029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6233029 prefixEnd_6233029 := by exact prefixLift 6233029
  have htrace : WordTrace (prefixWord ++ tailWord_6233029) baseStart_6233029 baseEnd_6233029 := by
    simpa [prefixWord, tailWord_6233029, baseEnd_6233029] using wordTrace_append hprefix tailTrace_6233029
  have hstable : (prefixWord ++ tailWord_6233029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6233029).length < 2 ^ (prefixWord ++ tailWord_6233029).sum := by decide
  have hdescent : baseEnd_6233029 < baseStart_6233029 := by decide
  rcases family_descends (prefixWord ++ tailWord_6233029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6233093 : List Nat := [1, 3, 1, 1, 2, 3, 2, 4, 1, 1, 4]
def baseStart_6233093 : Nat := 118140960795 + 6233093 * 2 ^ 59
def prefixEnd_6233093 : Nat := 4983230072969 + 3 ^ 40 * 6233093 * 2
def baseEnd_6233093 : Nat := 3200572673175086728672033

theorem tailTrace_6233093 : CollatzResearch.WordTrace tailWord_6233093 prefixEnd_6233093 3200572673175086728672033 := by
  unfold tailWord_6233093
  simp only [CollatzResearch.WordTrace]
  refine ⟨227339578407576063378143933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151559718938384042252095955 227339578407576063378143933)
  ·
    refine ⟨85252341902841023766803975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 227339578407576063378143933 85252341902841023766803975)
    ·
      refine ⟨127878512854261535650205963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85252341902841023766803975 127878512854261535650205963)
      ·
        refine ⟨191817769281392303475308945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127878512854261535650205963 191817769281392303475308945)
        ·
          refine ⟨143863326961044227606481709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 191817769281392303475308945 143863326961044227606481709)
          ·
            refine ⟨53948747610391585352430641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 143863326961044227606481709 53948747610391585352430641)
            ·
              refine ⟨40461560707793689014322981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53948747610391585352430641 40461560707793689014322981)
              ·
                refine ⟨7586542632711316690185559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40461560707793689014322981 7586542632711316690185559)
                ·
                  refine ⟨11379813949066975035278339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7586542632711316690185559 11379813949066975035278339)
                  ·
                    refine ⟨17069720923600462552917509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11379813949066975035278339 17069720923600462552917509)
                    ·
                      refine ⟨3200572673175086728672033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17069720923600462552917509 3200572673175086728672033)
                      ·
                        rfl

theorem cell23_6233093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 2, 4, 1, 1, 4].length) (baseStart_6233093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6233093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6233093 prefixEnd_6233093 := by exact prefixLift 6233093
  have htrace : WordTrace (prefixWord ++ tailWord_6233093) baseStart_6233093 baseEnd_6233093 := by
    simpa [prefixWord, tailWord_6233093, baseEnd_6233093] using wordTrace_append hprefix tailTrace_6233093
  have hstable : (prefixWord ++ tailWord_6233093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6233093).length < 2 ^ (prefixWord ++ tailWord_6233093).sum := by decide
  have hdescent : baseEnd_6233093 < baseStart_6233093 := by decide
  rcases family_descends (prefixWord ++ tailWord_6233093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6233130 : List Nat := [3, 1, 4, 1, 3, 1, 1, 2, 1, 1, 5]
def baseStart_6233130 : Nat := 118140960795 + 6233130 * 2 ^ 59
def prefixEnd_6233130 : Nat := 4983230072969 + 3 ^ 40 * 6233130 * 2
def baseEnd_6233130 : Nat := 3200591671959303083909363

theorem tailTrace_6233130 : CollatzResearch.WordTrace tailWord_6233130 prefixEnd_6233130 3200591671959303083909363 := by
  unfold tailWord_6233130
  simp only [CollatzResearch.WordTrace]
  refine ⟨56835231977110504674310211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151560618605628012464827229 56835231977110504674310211)
  ·
    refine ⟨85252847965665757011465317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56835231977110504674310211 85252847965665757011465317)
    ·
      refine ⟨15984908993562329439649747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 85252847965665757011465317 15984908993562329439649747)
      ·
        refine ⟨23977363490343494159474621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15984908993562329439649747 23977363490343494159474621)
        ·
          refine ⟨8991511308878810309802983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23977363490343494159474621 8991511308878810309802983)
          ·
            refine ⟨13487266963318215464704475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8991511308878810309802983 13487266963318215464704475)
            ·
              refine ⟨20230900444977323197056713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13487266963318215464704475 20230900444977323197056713)
              ·
                refine ⟨15173175333732992397792535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20230900444977323197056713 15173175333732992397792535)
                ·
                  refine ⟨22759763000599488596688803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15173175333732992397792535 22759763000599488596688803)
                  ·
                    refine ⟨34139644500899232895033205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22759763000599488596688803 34139644500899232895033205)
                    ·
                      refine ⟨3200591671959303083909363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34139644500899232895033205 3200591671959303083909363)
                      ·
                        rfl

theorem cell23_6233130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 1, 2, 1, 1, 5].length) (baseStart_6233130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6233130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6233130 prefixEnd_6233130 := by exact prefixLift 6233130
  have htrace : WordTrace (prefixWord ++ tailWord_6233130) baseStart_6233130 baseEnd_6233130 := by
    simpa [prefixWord, tailWord_6233130, baseEnd_6233130] using wordTrace_append hprefix tailTrace_6233130
  have hstable : (prefixWord ++ tailWord_6233130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6233130).length < 2 ^ (prefixWord ++ tailWord_6233130).sum := by decide
  have hdescent : baseEnd_6233130 < baseStart_6233130 := by decide
  rcases family_descends (prefixWord ++ tailWord_6233130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6233140 : List Nat := [2, 5, 1, 2, 1, 2, 1, 1, 1, 1, 6]
def baseStart_6233140 : Nat := 118140960795 + 6233140 * 2 ^ 59
def prefixEnd_6233140 : Nat := 4983230072969 + 3 ^ 40 * 6233140 * 2
def baseEnd_6233140 : Nat := 3200596806765848044784317

theorem tailTrace_6233140 : CollatzResearch.WordTrace tailWord_6233140 prefixEnd_6233140 3200596806765848044784317 := by
  unfold tailWord_6233140
  simp only [CollatzResearch.WordTrace]
  refine ⟨113670646319202895202552437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151560861758937193603403249 113670646319202895202552437)
  ·
    refine ⟨10656623092425271425239291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 113670646319202895202552437 10656623092425271425239291)
    ·
      refine ⟨15984934638637907137858937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10656623092425271425239291 15984934638637907137858937)
      ·
        refine ⟨11988700978978430353394203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15984934638637907137858937 11988700978978430353394203)
        ·
          refine ⟨17983051468467645530091305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11988700978978430353394203 17983051468467645530091305)
          ·
            refine ⟨13487288601350734147568479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17983051468467645530091305 13487288601350734147568479)
            ·
              refine ⟨20230932902026101221352719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13487288601350734147568479 20230932902026101221352719)
              ·
                refine ⟨30346399353039151832029079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20230932902026101221352719 30346399353039151832029079)
                ·
                  refine ⟨45519599029558727748043619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30346399353039151832029079 45519599029558727748043619)
                  ·
                    refine ⟨68279398544338091622065429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 45519599029558727748043619 68279398544338091622065429)
                    ·
                      refine ⟨3200596806765848044784317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 68279398544338091622065429 3200596806765848044784317)
                      ·
                        rfl

theorem cell23_6233140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 1, 1, 1, 1, 6].length) (baseStart_6233140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6233140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6233140 prefixEnd_6233140 := by exact prefixLift 6233140
  have htrace : WordTrace (prefixWord ++ tailWord_6233140) baseStart_6233140 baseEnd_6233140 := by
    simpa [prefixWord, tailWord_6233140, baseEnd_6233140] using wordTrace_append hprefix tailTrace_6233140
  have hstable : (prefixWord ++ tailWord_6233140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6233140).length < 2 ^ (prefixWord ++ tailWord_6233140).sum := by decide
  have hdescent : baseEnd_6233140 < baseStart_6233140 := by decide
  rcases family_descends (prefixWord ++ tailWord_6233140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6233146 : List Nat := [3, 1, 1, 1, 3, 1, 2, 2, 2, 7]
def baseStart_6233146 : Nat := 118140960795 + 6233146 * 2 ^ 59
def prefixEnd_6233146 : Nat := 4983230072969 + 3 ^ 40 * 6233146 * 2
def baseEnd_6233146 : Nat := 1066866629216591673769763

theorem tailTrace_6233146 : CollatzResearch.WordTrace tailWord_6233146 prefixEnd_6233146 1066866629216591673769763 := by
  unfold tailWord_6233146
  simp only [CollatzResearch.WordTrace]
  refine ⟨56835377869096013357455823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151561007650922702286548861 56835377869096013357455823)
  ·
    refine ⟨85253066803644020036183735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56835377869096013357455823 85253066803644020036183735)
    ·
      refine ⟨127879600205466030054275603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85253066803644020036183735 127879600205466030054275603)
      ·
        refine ⟨191819400308199045081413405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127879600205466030054275603 191819400308199045081413405)
        ·
          refine ⟨71932275115574641905530027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 191819400308199045081413405 71932275115574641905530027)
          ·
            refine ⟨107898412673361962858295041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71932275115574641905530027 107898412673361962858295041)
            ·
              refine ⟨80923809505021472143721281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 107898412673361962858295041 80923809505021472143721281)
              ·
                refine ⟨60692857128766104107790961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 80923809505021472143721281 60692857128766104107790961)
                ·
                  refine ⟨45519642846574578080843221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 60692857128766104107790961 45519642846574578080843221)
                  ·
                    refine ⟨1066866629216591673769763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 45519642846574578080843221 1066866629216591673769763)
                    ·
                      rfl

theorem cell23_6233146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 2, 2, 7].length) (baseStart_6233146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6233146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6233146 prefixEnd_6233146 := by exact prefixLift 6233146
  have htrace : WordTrace (prefixWord ++ tailWord_6233146) baseStart_6233146 baseEnd_6233146 := by
    simpa [prefixWord, tailWord_6233146, baseEnd_6233146] using wordTrace_append hprefix tailTrace_6233146
  have hstable : (prefixWord ++ tailWord_6233146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6233146).length < 2 ^ (prefixWord ++ tailWord_6233146).sum := by decide
  have hdescent : baseEnd_6233146 < baseStart_6233146 := by decide
  rcases family_descends (prefixWord ++ tailWord_6233146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6233150 : List Nat := [4, 2, 1, 3, 1, 1, 4, 7]
def baseStart_6233150 : Nat := 118140960795 + 6233150 * 2 ^ 59
def prefixEnd_6233150 : Nat := 4983230072969 + 3 ^ 40 * 6233150 * 2
def baseEnd_6233150 : Nat := 118540812650829370579973

theorem tailTrace_6233150 : CollatzResearch.WordTrace tailWord_6233150 prefixEnd_6233150 118540812650829370579973 := by
  unfold tailWord_6233150
  simp only [CollatzResearch.WordTrace]
  refine ⟨28417707171046195264121113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 151561104912246374741979269 28417707171046195264121113)
  ·
    refine ⟨21313280378284646448090835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28417707171046195264121113 21313280378284646448090835)
    ·
      refine ⟨31969920567426969672136253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21313280378284646448090835 31969920567426969672136253)
      ·
        refine ⟨11988720212785113627051095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31969920567426969672136253 11988720212785113627051095)
        ·
          refine ⟨17983080319177670440576643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11988720212785113627051095 17983080319177670440576643)
          ·
            refine ⟨26974620478766505660864965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17983080319177670440576643 26974620478766505660864965)
            ·
              refine ⟨5057741339768719811412181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26974620478766505660864965 5057741339768719811412181)
              ·
                refine ⟨118540812650829370579973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5057741339768719811412181 118540812650829370579973)
                ·
                  rfl

theorem cell23_6233150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 4, 7].length) (baseStart_6233150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6233150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6233150 prefixEnd_6233150 := by exact prefixLift 6233150
  have htrace : WordTrace (prefixWord ++ tailWord_6233150) baseStart_6233150 baseEnd_6233150 := by
    simpa [prefixWord, tailWord_6233150, baseEnd_6233150] using wordTrace_append hprefix tailTrace_6233150
  have hstable : (prefixWord ++ tailWord_6233150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6233150).length < 2 ^ (prefixWord ++ tailWord_6233150).sum := by decide
  have hdescent : baseEnd_6233150 < baseStart_6233150 := by decide
  rcases family_descends (prefixWord ++ tailWord_6233150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6233194 : List Nat := [3, 1, 3, 2, 2, 1, 4, 1, 2, 1, 3]
def baseStart_6233194 : Nat := 118140960795 + 6233194 * 2 ^ 59
def prefixEnd_6233194 : Nat := 4983230072969 + 3 ^ 40 * 6233194 * 2
def baseEnd_6233194 : Nat := 3200624534721190833509069

theorem tailTrace_6233194 : CollatzResearch.WordTrace tailWord_6233194 prefixEnd_6233194 3200624534721190833509069 := by
  unfold tailWord_6233194
  simp only [CollatzResearch.WordTrace]
  refine ⟨56835815545052539406892659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151562174786806771751713757 56835815545052539406892659)
  ·
    refine ⟨85253723317578809110338989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56835815545052539406892659 85253723317578809110338989)
    ·
      refine ⟨31970146244092053416377121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85253723317578809110338989 31970146244092053416377121)
      ·
        refine ⟨23977609683069040062282841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31970146244092053416377121 23977609683069040062282841)
        ·
          refine ⟨17983207262301780046712131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23977609683069040062282841 17983207262301780046712131)
          ·
            refine ⟨26974810893452670070068197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17983207262301780046712131 26974810893452670070068197)
            ·
              refine ⟨5057777042522375638137787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26974810893452670070068197 5057777042522375638137787)
              ·
                refine ⟨7586665563783563457206681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5057777042522375638137787 7586665563783563457206681)
                ·
                  refine ⟨5689999172837672592905011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7586665563783563457206681 5689999172837672592905011)
                  ·
                    refine ⟨8534998759256508889357517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5689999172837672592905011 8534998759256508889357517)
                    ·
                      refine ⟨3200624534721190833509069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8534998759256508889357517 3200624534721190833509069)
                      ·
                        rfl

theorem cell23_6233194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 4, 1, 2, 1, 3].length) (baseStart_6233194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6233194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6233194 prefixEnd_6233194 := by exact prefixLift 6233194
  have htrace : WordTrace (prefixWord ++ tailWord_6233194) baseStart_6233194 baseEnd_6233194 := by
    simpa [prefixWord, tailWord_6233194, baseEnd_6233194] using wordTrace_append hprefix tailTrace_6233194
  have hstable : (prefixWord ++ tailWord_6233194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6233194).length < 2 ^ (prefixWord ++ tailWord_6233194).sum := by decide
  have hdescent : baseEnd_6233194 < baseStart_6233194 := by decide
  rcases family_descends (prefixWord ++ tailWord_6233194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6233200 : List Nat := [2, 1, 1, 1, 5, 1, 2, 3, 1, 4, 2]
def baseStart_6233200 : Nat := 118140960795 + 6233200 * 2 ^ 59
def prefixEnd_6233200 : Nat := 4983230072969 + 3 ^ 40 * 6233200 * 2
def baseEnd_6233200 : Nat := 3200627615605117810034041

theorem tailTrace_6233200 : CollatzResearch.WordTrace tailWord_6233200 prefixEnd_6233200 3200627615605117810034041 := by
  unfold tailWord_6233200
  simp only [CollatzResearch.WordTrace]
  refine ⟨113671740509094210326144527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151562320678792280434859369 113671740509094210326144527)
  ·
    refine ⟨170507610763641315489216791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113671740509094210326144527 170507610763641315489216791)
    ·
      refine ⟨255761416145461973233825187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170507610763641315489216791 255761416145461973233825187)
      ·
        refine ⟨383642124218192959850737781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 255761416145461973233825187 383642124218192959850737781)
        ·
          refine ⟨35966449145455589986006667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 383642124218192959850737781 35966449145455589986006667)
          ·
            refine ⟨53949673718183384979010001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35966449145455589986006667 53949673718183384979010001)
            ·
              refine ⟨40462255288637538734257501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53949673718183384979010001 40462255288637538734257501)
              ·
                refine ⟨15173345733239077025346563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40462255288637538734257501 15173345733239077025346563)
                ·
                  refine ⟨22760018599858615538019845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15173345733239077025346563 22760018599858615538019845)
                  ·
                    refine ⟨4267503487473490413378721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22760018599858615538019845 4267503487473490413378721)
                    ·
                      refine ⟨3200627615605117810034041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4267503487473490413378721 3200627615605117810034041)
                      ·
                        rfl

theorem cell23_6233200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 2, 3, 1, 4, 2].length) (baseStart_6233200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6233200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6233200 prefixEnd_6233200 := by exact prefixLift 6233200
  have htrace : WordTrace (prefixWord ++ tailWord_6233200) baseStart_6233200 baseEnd_6233200 := by
    simpa [prefixWord, tailWord_6233200, baseEnd_6233200] using wordTrace_append hprefix tailTrace_6233200
  have hstable : (prefixWord ++ tailWord_6233200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6233200).length < 2 ^ (prefixWord ++ tailWord_6233200).sum := by decide
  have hdescent : baseEnd_6233200 < baseStart_6233200 := by decide
  rcases family_descends (prefixWord ++ tailWord_6233200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6233217 : List Nat := [1, 2, 4, 2, 2, 2, 1, 2, 1, 4, 2]
def baseStart_6233217 : Nat := 118140960795 + 6233217 * 2 ^ 59
def prefixEnd_6233217 : Nat := 4983230072969 + 3 ^ 40 * 6233217 * 2
def baseEnd_6233217 : Nat := 3200636344776244243521463

theorem tailTrace_6233217 : CollatzResearch.WordTrace tailWord_6233217 prefixEnd_6233217 3200636344776244243521463 := by
  unfold tailWord_6233217
  simp only [CollatzResearch.WordTrace]
  refine ⟨227344101059126832555657905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151562734039417888370438603 227344101059126832555657905)
  ·
    refine ⟨170508075794345124416743429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 227344101059126832555657905 170508075794345124416743429)
    ·
      refine ⟨31970264211439710828139393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 170508075794345124416743429 31970264211439710828139393)
      ·
        refine ⟨23977698158579783121104545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31970264211439710828139393 23977698158579783121104545)
        ·
          refine ⟨17983273618934837340828409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23977698158579783121104545 17983273618934837340828409)
          ·
            refine ⟨13487455214201128005621307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17983273618934837340828409 13487455214201128005621307)
            ·
              refine ⟨20231182821301692008431961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13487455214201128005621307 20231182821301692008431961)
              ·
                refine ⟨15173387115976269006323971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20231182821301692008431961 15173387115976269006323971)
                ·
                  refine ⟨22760080673964403509485957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15173387115976269006323971 22760080673964403509485957)
                  ·
                    refine ⟨4267515126368325658028617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22760080673964403509485957 4267515126368325658028617)
                    ·
                      refine ⟨3200636344776244243521463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4267515126368325658028617 3200636344776244243521463)
                      ·
                        rfl

theorem cell23_6233217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 1, 2, 1, 4, 2].length) (baseStart_6233217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6233217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6233217 prefixEnd_6233217 := by exact prefixLift 6233217
  have htrace : WordTrace (prefixWord ++ tailWord_6233217) baseStart_6233217 baseEnd_6233217 := by
    simpa [prefixWord, tailWord_6233217, baseEnd_6233217] using wordTrace_append hprefix tailTrace_6233217
  have hstable : (prefixWord ++ tailWord_6233217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6233217).length < 2 ^ (prefixWord ++ tailWord_6233217).sum := by decide
  have hdescent : baseEnd_6233217 < baseStart_6233217 := by decide
  rcases family_descends (prefixWord ++ tailWord_6233217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6233234 : List Nat := [3, 2, 3, 1, 1, 2, 1, 4, 2, 2, 2]
def baseStart_6233234 : Nat := 118140960795 + 6233234 * 2 ^ 59
def prefixEnd_6233234 : Nat := 4983230072969 + 3 ^ 40 * 6233234 * 2
def baseEnd_6233234 : Nat := 3200645073947370677008885

theorem tailTrace_6233234 : CollatzResearch.WordTrace tailWord_6233234 prefixEnd_6233234 3200645073947370677008885 := by
  unfold tailWord_6233234
  simp only [CollatzResearch.WordTrace]
  refine ⟨56836180275016311114756689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151563147400043496306017837 56836180275016311114756689)
  ·
    refine ⟨42627135206262233336067517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56836180275016311114756689 42627135206262233336067517)
    ·
      refine ⟨15985175702348337501025319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42627135206262233336067517 15985175702348337501025319)
      ·
        refine ⟨23977763553522506251537979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15985175702348337501025319 23977763553522506251537979)
        ·
          refine ⟨35966645330283759377306969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23977763553522506251537979 35966645330283759377306969)
          ·
            refine ⟨26974983997712819532980227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35966645330283759377306969 26974983997712819532980227)
            ·
              refine ⟨40462475996569229299470341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26974983997712819532980227 40462475996569229299470341)
              ·
                refine ⟨7586714249356730493650689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40462475996569229299470341 7586714249356730493650689)
                ·
                  refine ⟨5690035687017547870238017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7586714249356730493650689 5690035687017547870238017)
                  ·
                    refine ⟨4267526765263160902678513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5690035687017547870238017 4267526765263160902678513)
                    ·
                      refine ⟨3200645073947370677008885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4267526765263160902678513 3200645073947370677008885)
                      ·
                        rfl

theorem cell23_6233234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 1, 4, 2, 2, 2].length) (baseStart_6233234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6233234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6233234 prefixEnd_6233234 := by exact prefixLift 6233234
  have htrace : WordTrace (prefixWord ++ tailWord_6233234) baseStart_6233234 baseEnd_6233234 := by
    simpa [prefixWord, tailWord_6233234, baseEnd_6233234] using wordTrace_append hprefix tailTrace_6233234
  have hstable : (prefixWord ++ tailWord_6233234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6233234).length < 2 ^ (prefixWord ++ tailWord_6233234).sum := by decide
  have hdescent : baseEnd_6233234 < baseStart_6233234 := by decide
  rcases family_descends (prefixWord ++ tailWord_6233234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6233363 : List Nat := [1, 1, 1, 2, 1, 3, 1, 1, 1, 7, 4]
def baseStart_6233363 : Nat := 118140960795 + 6233363 * 2 ^ 59
def prefixEnd_6233363 : Nat := 4983230072969 + 3 ^ 40 * 6233363 * 2
def baseEnd_6233363 : Nat := 3200711312951800672295791

theorem tailTrace_6233363 : CollatzResearch.WordTrace tailWord_6233363 prefixEnd_6233363 3200711312951800672295791 := by
  unfold tailWord_6233363
  simp only [CollatzResearch.WordTrace]
  refine ⟨227349426116597899490472743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151566284077731932993648495 227349426116597899490472743)
  ·
    refine ⟨341024139174896849235709115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227349426116597899490472743 341024139174896849235709115)
    ·
      refine ⟨511536208762345273853563673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 341024139174896849235709115 511536208762345273853563673)
      ·
        refine ⟨383652156571758955390172755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 511536208762345273853563673 383652156571758955390172755)
        ·
          refine ⟨575478234857638433085259133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 383652156571758955390172755 575478234857638433085259133)
          ·
            refine ⟨215804338071614412406972175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 575478234857638433085259133 215804338071614412406972175)
            ·
              refine ⟨323706507107421618610458263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 215804338071614412406972175 323706507107421618610458263)
              ·
                refine ⟨485559760661132427915687395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 323706507107421618610458263 485559760661132427915687395)
                ·
                  refine ⟨728339640991698641873531093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 485559760661132427915687395 728339640991698641873531093)
                  ·
                    refine ⟨17070460335742936918910885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 728339640991698641873531093 17070460335742936918910885)
                    ·
                      refine ⟨3200711312951800672295791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17070460335742936918910885 3200711312951800672295791)
                      ·
                        rfl

theorem cell23_6233363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 1, 1, 7, 4].length) (baseStart_6233363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6233363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6233363 prefixEnd_6233363 := by exact prefixLift 6233363
  have htrace : WordTrace (prefixWord ++ tailWord_6233363) baseStart_6233363 baseEnd_6233363 := by
    simpa [prefixWord, tailWord_6233363, baseEnd_6233363] using wordTrace_append hprefix tailTrace_6233363
  have hstable : (prefixWord ++ tailWord_6233363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6233363).length < 2 ^ (prefixWord ++ tailWord_6233363).sum := by decide
  have hdescent : baseEnd_6233363 < baseStart_6233363 := by decide
  rcases family_descends (prefixWord ++ tailWord_6233363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6233367 : List Nat := [1, 1, 3, 4, 1, 1, 1, 2, 4, 3, 2]
def baseStart_6233367 : Nat := 118140960795 + 6233367 * 2 ^ 59
def prefixEnd_6233367 : Nat := 4983230072969 + 3 ^ 40 * 6233367 * 2
def baseEnd_6233367 : Nat := 3200713366874418656645773

theorem tailTrace_6233367 : CollatzResearch.WordTrace tailWord_6233367 prefixEnd_6233367 3200713366874418656645773 := by
  unfold tailWord_6233367
  simp only [CollatzResearch.WordTrace]
  refine ⟨227349572008583408173618355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151566381339055605449078903 227349572008583408173618355)
  ·
    refine ⟨341024358012875112260427533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227349572008583408173618355 341024358012875112260427533)
    ·
      refine ⟨127884134254828167097660325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 341024358012875112260427533 127884134254828167097660325)
      ·
        refine ⟨23978275172780281330811311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 127884134254828167097660325 23978275172780281330811311)
        ·
          refine ⟨35967412759170421996216967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23978275172780281330811311 35967412759170421996216967)
          ·
            refine ⟨53951119138755632994325451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35967412759170421996216967 53951119138755632994325451)
            ·
              refine ⟨80926678708133449491488177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53951119138755632994325451 80926678708133449491488177)
              ·
                refine ⟨60695009031100087118616133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 80926678708133449491488177 60695009031100087118616133)
                ·
                  refine ⟨11380314193331266334740525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 60695009031100087118616133 11380314193331266334740525)
                  ·
                    refine ⟨4267617822499224875527697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11380314193331266334740525 4267617822499224875527697)
                    ·
                      refine ⟨3200713366874418656645773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4267617822499224875527697 3200713366874418656645773)
                      ·
                        rfl

theorem cell23_6233367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 2, 4, 3, 2].length) (baseStart_6233367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6233367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6233367 prefixEnd_6233367 := by exact prefixLift 6233367
  have htrace : WordTrace (prefixWord ++ tailWord_6233367) baseStart_6233367 baseEnd_6233367 := by
    simpa [prefixWord, tailWord_6233367, baseEnd_6233367] using wordTrace_append hprefix tailTrace_6233367
  have hstable : (prefixWord ++ tailWord_6233367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6233367).length < 2 ^ (prefixWord ++ tailWord_6233367).sum := by decide
  have hdescent : baseEnd_6233367 < baseStart_6233367 := by decide
  rcases family_descends (prefixWord ++ tailWord_6233367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6233384 : List Nat := [2, 1, 5, 1, 2, 1, 1, 3, 2, 3, 2]
def baseStart_6233384 : Nat := 118140960795 + 6233384 * 2 ^ 59
def prefixEnd_6233384 : Nat := 4983230072969 + 3 ^ 40 * 6233384 * 2
def baseEnd_6233384 : Nat := 3200722096045545090133195

theorem tailTrace_6233384 : CollatzResearch.WordTrace tailWord_6233384 prefixEnd_6233384 3200722096045545090133195 := by
  unfold tailWord_6233384
  simp only [CollatzResearch.WordTrace]
  refine ⟨113675096024760910038493603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151566794699681213384658137 113675096024760910038493603)
  ·
    refine ⟨170512644037141365057740405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113675096024760910038493603 170512644037141365057740405)
    ·
      refine ⟨15985560378482002974163163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 170512644037141365057740405 15985560378482002974163163)
      ·
        refine ⟨23978340567723004461244745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15985560378482002974163163 23978340567723004461244745)
        ·
          refine ⟨17983755425792253345933559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23978340567723004461244745 17983755425792253345933559)
          ·
            refine ⟨26975633138688380018900339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17983755425792253345933559 26975633138688380018900339)
            ·
              refine ⟨40463449708032570028350509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26975633138688380018900339 40463449708032570028350509)
              ·
                refine ⟨15173793640512213760631441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40463449708032570028350509 15173793640512213760631441)
                ·
                  refine ⟨11380345230384160320473581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15173793640512213760631441 11380345230384160320473581)
                  ·
                    refine ⟨4267629461394060120177593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11380345230384160320473581 4267629461394060120177593)
                    ·
                      refine ⟨3200722096045545090133195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4267629461394060120177593 3200722096045545090133195)
                      ·
                        rfl

theorem cell23_6233384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 1, 3, 2, 3, 2].length) (baseStart_6233384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6233384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6233384 prefixEnd_6233384 := by exact prefixLift 6233384
  have htrace : WordTrace (prefixWord ++ tailWord_6233384) baseStart_6233384 baseEnd_6233384 := by
    simpa [prefixWord, tailWord_6233384, baseEnd_6233384] using wordTrace_append hprefix tailTrace_6233384
  have hstable : (prefixWord ++ tailWord_6233384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6233384).length < 2 ^ (prefixWord ++ tailWord_6233384).sum := by decide
  have hdescent : baseEnd_6233384 < baseStart_6233384 := by decide
  rcases family_descends (prefixWord ++ tailWord_6233384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6233394 : List Nat := [3, 2, 1, 1, 4, 2, 3, 1, 1, 5]
def baseStart_6233394 : Nat := 118140960795 + 6233394 * 2 ^ 59
def prefixEnd_6233394 : Nat := 4983230072969 + 3 ^ 40 * 6233394 * 2
def baseEnd_6233394 : Nat := 1066909076950696683669383

theorem tailTrace_6233394 : CollatzResearch.WordTrace tailWord_6233394 prefixEnd_6233394 1066909076950696683669383 := by
  unfold tailWord_6233394
  simp only [CollatzResearch.WordTrace]
  refine ⟨56837639194871397946212809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151567037852990394523234157 56837639194871397946212809)
  ·
    refine ⟨42628229396153548459659607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56837639194871397946212809 42628229396153548459659607)
    ·
      refine ⟨63942344094230322689489411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42628229396153548459659607 63942344094230322689489411)
      ·
        refine ⟨95913516141345484034234117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63942344094230322689489411 95913516141345484034234117)
        ·
          refine ⟨17983784276502278256418897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 95913516141345484034234117 17983784276502278256418897)
          ·
            refine ⟨13487838207376708692314173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17983784276502278256418897 13487838207376708692314173)
            ·
              refine ⟨5057939327766265759617815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13487838207376708692314173 5057939327766265759617815)
              ·
                refine ⟨7586908991649398639426723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5057939327766265759617815 7586908991649398639426723)
                ·
                  refine ⟨11380363487474097959140085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7586908991649398639426723 11380363487474097959140085)
                  ·
                    refine ⟨1066909076950696683669383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11380363487474097959140085 1066909076950696683669383)
                    ·
                      rfl

theorem cell23_6233394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 3, 1, 1, 5].length) (baseStart_6233394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6233394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6233394 prefixEnd_6233394 := by exact prefixLift 6233394
  have htrace : WordTrace (prefixWord ++ tailWord_6233394) baseStart_6233394 baseEnd_6233394 := by
    simpa [prefixWord, tailWord_6233394, baseEnd_6233394] using wordTrace_append hprefix tailTrace_6233394
  have hstable : (prefixWord ++ tailWord_6233394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6233394).length < 2 ^ (prefixWord ++ tailWord_6233394).sum := by decide
  have hdescent : baseEnd_6233394 < baseStart_6233394 := by decide
  rcases family_descends (prefixWord ++ tailWord_6233394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6233407 : List Nat := [1, 1, 2, 2, 4, 2, 1, 4, 2, 4]
def baseStart_6233407 : Nat := 118140960795 + 6233407 * 2 ^ 59
def prefixEnd_6233407 : Nat := 4983230072969 + 3 ^ 40 * 6233407 * 2
def baseEnd_6233407 : Nat := 1066911302033532833381863

theorem tailTrace_6233407 : CollatzResearch.WordTrace tailWord_6233407 prefixEnd_6233407 1066911302033532833381863 := by
  unfold tailWord_6233407
  simp only [CollatzResearch.WordTrace]
  refine ⟨227351030928438495005074475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151567353952292330003382983 227351030928438495005074475)
  ·
    refine ⟨341026546392657742507611713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227351030928438495005074475 341026546392657742507611713)
    ·
      refine ⟨255769909794493306880708785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 341026546392657742507611713 255769909794493306880708785)
      ·
        refine ⟨191827432345869980160531589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 255769909794493306880708785 191827432345869980160531589)
        ·
          refine ⟨35967643564850621280099673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 191827432345869980160531589 35967643564850621280099673)
          ·
            refine ⟨26975732673637965960074755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35967643564850621280099673 26975732673637965960074755)
            ·
              refine ⟨40463599010456948940112133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26975732673637965960074755 40463599010456948940112133)
              ·
                refine ⟨7586924814460677926271025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40463599010456948940112133 7586924814460677926271025)
                ·
                  refine ⟨5690193610845508444703269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7586924814460677926271025 5690193610845508444703269)
                  ·
                    refine ⟨1066911302033532833381863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5690193610845508444703269 1066911302033532833381863)
                    ·
                      rfl

theorem cell23_6233407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 1, 4, 2, 4].length) (baseStart_6233407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6233407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6233407 prefixEnd_6233407 := by exact prefixLift 6233407
  have htrace : WordTrace (prefixWord ++ tailWord_6233407) baseStart_6233407 baseEnd_6233407 := by
    simpa [prefixWord, tailWord_6233407, baseEnd_6233407] using wordTrace_append hprefix tailTrace_6233407
  have hstable : (prefixWord ++ tailWord_6233407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6233407).length < 2 ^ (prefixWord ++ tailWord_6233407).sum := by decide
  have hdescent : baseEnd_6233407 < baseStart_6233407 := by decide
  rcases family_descends (prefixWord ++ tailWord_6233407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6233420 : List Nat := [2, 2, 1, 3, 2, 2, 3, 8]
def baseStart_6233420 : Nat := 118140960795 + 6233420 * 2 ^ 59
def prefixEnd_6233420 : Nat := 4983230072969 + 3 ^ 40 * 6233420 * 2
def baseEnd_6233420 : Nat := 118545947457374331454927

theorem tailTrace_6233420 : CollatzResearch.WordTrace tailWord_6233420 prefixEnd_6233420 118545947457374331454927 := by
  unfold tailWord_6233420
  simp only [CollatzResearch.WordTrace]
  refine ⟨113675752538695699112648857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151567670051594265483531809 113675752538695699112648857)
  ·
    refine ⟨85256814404021774334486643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113675752538695699112648857 85256814404021774334486643)
    ·
      refine ⟨127885221606032661501729965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85256814404021774334486643 127885221606032661501729965)
      ·
        refine ⟨47956958102262248063148737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 127885221606032661501729965 47956958102262248063148737)
        ·
          refine ⟨35967718576696686047361553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47956958102262248063148737 35967718576696686047361553)
          ·
            refine ⟨26975788932522514535521165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35967718576696686047361553 26975788932522514535521165)
            ·
              refine ⟨10115920849695942950820437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26975788932522514535521165 10115920849695942950820437)
              ·
                refine ⟨118545947457374331454927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10115920849695942950820437 118545947457374331454927)
                ·
                  rfl

theorem cell23_6233420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 3, 8].length) (baseStart_6233420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6233420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6233420 prefixEnd_6233420 := by exact prefixLift 6233420
  have htrace : WordTrace (prefixWord ++ tailWord_6233420) baseStart_6233420 baseEnd_6233420 := by
    simpa [prefixWord, tailWord_6233420, baseEnd_6233420] using wordTrace_append hprefix tailTrace_6233420
  have hstable : (prefixWord ++ tailWord_6233420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6233420).length < 2 ^ (prefixWord ++ tailWord_6233420).sum := by decide
  have hdescent : baseEnd_6233420 < baseStart_6233420 := by decide
  rcases family_descends (prefixWord ++ tailWord_6233420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6233448 : List Nat := [2, 1, 4, 2, 4, 1, 2, 1, 1, 1, 4]
def baseStart_6233448 : Nat := 118140960795 + 6233448 * 2 ^ 59
def prefixEnd_6233448 : Nat := 4983230072969 + 3 ^ 40 * 6233448 * 2
def baseEnd_6233448 : Nat := 3200754958807432839732901

theorem tailTrace_6233448 : CollatzResearch.WordTrace tailWord_6233448 prefixEnd_6233448 3200754958807432839732901 := by
  unfold tailWord_6233448
  simp only [CollatzResearch.WordTrace]
  refine ⟨113676263160644979503658499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151568350880859972671544665 113676263160644979503658499)
  ·
    refine ⟨170514394740967469255487749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113676263160644979503658499 170514394740967469255487749)
    ·
      refine ⟨31971449013931400485403953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 170514394740967469255487749 31971449013931400485403953)
      ·
        refine ⟨23978586760448550364052965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31971449013931400485403953 23978586760448550364052965)
        ·
          refine ⟨4495985017584103193259931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23978586760448550364052965 4495985017584103193259931)
          ·
            refine ⟨6743977526376154789889897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4495985017584103193259931 6743977526376154789889897)
            ·
              refine ⟨5057983144782116092417423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6743977526376154789889897 5057983144782116092417423)
              ·
                refine ⟨7586974717173174138626135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5057983144782116092417423 7586974717173174138626135)
                ·
                  refine ⟨11380462075759761207939203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7586974717173174138626135 11380462075759761207939203)
                  ·
                    refine ⟨17070693113639641811908805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11380462075759761207939203 17070693113639641811908805)
                    ·
                      refine ⟨3200754958807432839732901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17070693113639641811908805 3200754958807432839732901)
                      ·
                        rfl

theorem cell23_6233448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 4, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 4, 1, 2, 1, 1, 1, 4].length) (baseStart_6233448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6233448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6233448 prefixEnd_6233448 := by exact prefixLift 6233448
  have htrace : WordTrace (prefixWord ++ tailWord_6233448) baseStart_6233448 baseEnd_6233448 := by
    simpa [prefixWord, tailWord_6233448, baseEnd_6233448] using wordTrace_append hprefix tailTrace_6233448
  have hstable : (prefixWord ++ tailWord_6233448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6233448).length < 2 ^ (prefixWord ++ tailWord_6233448).sum := by decide
  have hdescent : baseEnd_6233448 < baseStart_6233448 := by decide
  rcases family_descends (prefixWord ++ tailWord_6233448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6233481 : List Nat := [1, 2, 1, 1, 8, 1, 1, 1, 1, 3, 3]
def baseStart_6233481 : Nat := 118140960795 + 6233481 * 2 ^ 59
def prefixEnd_6233481 : Nat := 4983230072969 + 3 ^ 40 * 6233481 * 2
def baseEnd_6233481 : Nat := 3200771903669031210620249

theorem tailTrace_6233481 : CollatzResearch.WordTrace tailWord_6233481 prefixEnd_6233481 3200771903669031210620249 := by
  unfold tailWord_6233481
  simp only [CollatzResearch.WordTrace]
  refine ⟨227353729930170405643268297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151569153286780270428845531 227353729930170405643268297)
  ·
    refine ⟨170515297447627804232451223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 227353729930170405643268297 170515297447627804232451223)
    ·
      refine ⟨255772946171441706348676835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170515297447627804232451223 255772946171441706348676835)
      ·
        refine ⟨383659419257162559523015253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 255772946171441706348676835 383659419257162559523015253)
        ·
          refine ⟨4496008819419873744410335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 383659419257162559523015253 4496008819419873744410335)
          ·
            refine ⟨6744013229129810616615503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4496008819419873744410335 6744013229129810616615503)
            ·
              refine ⟨10116019843694715924923255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6744013229129810616615503 10116019843694715924923255)
              ·
                refine ⟨15174029765542073887384883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10116019843694715924923255 15174029765542073887384883)
                ·
                  refine ⟨22761044648313110831077325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15174029765542073887384883 22761044648313110831077325)
                  ·
                    refine ⟨8535391743117416561653997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22761044648313110831077325 8535391743117416561653997)
                    ·
                      refine ⟨3200771903669031210620249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8535391743117416561653997 3200771903669031210620249)
                      ·
                        rfl

theorem cell23_6233481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 8, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 8, 1, 1, 1, 1, 3, 3].length) (baseStart_6233481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6233481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6233481 prefixEnd_6233481 := by exact prefixLift 6233481
  have htrace : WordTrace (prefixWord ++ tailWord_6233481) baseStart_6233481 baseEnd_6233481 := by
    simpa [prefixWord, tailWord_6233481, baseEnd_6233481] using wordTrace_append hprefix tailTrace_6233481
  have hstable : (prefixWord ++ tailWord_6233481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6233481).length < 2 ^ (prefixWord ++ tailWord_6233481).sum := by decide
  have hdescent : baseEnd_6233481 < baseStart_6233481 := by decide
  rcases family_descends (prefixWord ++ tailWord_6233481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6233504 : List Nat := [2, 1, 1, 4, 1, 2, 1, 1, 6, 2, 2]
def baseStart_6233504 : Nat := 118140960795 + 6233504 * 2 ^ 59
def prefixEnd_6233504 : Nat := 4983230072969 + 3 ^ 40 * 6233504 * 2
def baseEnd_6233504 : Nat := 3200783713724084620632643

theorem tailTrace_6233504 : CollatzResearch.WordTrace tailWord_6233504 prefixEnd_6233504 3200783713724084620632643 := by
  unfold tailWord_6233504
  simp only [CollatzResearch.WordTrace]
  refine ⟨113677284404543540285677783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151569712539391387047570377 113677284404543540285677783)
  ·
    refine ⟨170515926606815310428516675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113677284404543540285677783 170515926606815310428516675)
    ·
      refine ⟨255773889910222965642775013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170515926606815310428516675 255773889910222965642775013)
      ·
        refine ⟨47957604358166806058020315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 255773889910222965642775013 47957604358166806058020315)
        ·
          refine ⟨71936406537250209087030473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47957604358166806058020315 71936406537250209087030473)
          ·
            refine ⟨53952304902937656815272855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71936406537250209087030473 53952304902937656815272855)
            ·
              refine ⟨80928457354406485222909283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53952304902937656815272855 80928457354406485222909283)
              ·
                refine ⟨121392686031609727834363925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 80928457354406485222909283 121392686031609727834363925)
                ·
                  refine ⟨5690282157731705992235809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 121392686031609727834363925 5690282157731705992235809)
                  ·
                    refine ⟨4267711618298779494176857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5690282157731705992235809 4267711618298779494176857)
                    ·
                      refine ⟨3200783713724084620632643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4267711618298779494176857 3200783713724084620632643)
                      ·
                        rfl

theorem cell23_6233504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 1, 6, 2, 2].length) (baseStart_6233504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6233504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6233504 prefixEnd_6233504 := by exact prefixLift 6233504
  have htrace : WordTrace (prefixWord ++ tailWord_6233504) baseStart_6233504 baseEnd_6233504 := by
    simpa [prefixWord, tailWord_6233504, baseEnd_6233504] using wordTrace_append hprefix tailTrace_6233504
  have hstable : (prefixWord ++ tailWord_6233504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6233504).length < 2 ^ (prefixWord ++ tailWord_6233504).sum := by decide
  have hdescent : baseEnd_6233504 < baseStart_6233504 := by decide
  rcases family_descends (prefixWord ++ tailWord_6233504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6233521 : List Nat := [1, 2, 2, 4, 1, 1, 2, 4, 2, 2, 2]
def baseStart_6233521 : Nat := 118140960795 + 6233521 * 2 ^ 59
def prefixEnd_6233521 : Nat := 4983230072969 + 3 ^ 40 * 6233521 * 2
def baseEnd_6233521 : Nat := 3200792442895211054120065

theorem tailTrace_6233521 : CollatzResearch.WordTrace tailWord_6233521 prefixEnd_6233521 3200792442895211054120065 := by
  unfold tailWord_6233521
  simp only [CollatzResearch.WordTrace]
  refine ⟨227355188850025492474724417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151570125900016994983149611 227355188850025492474724417)
  ·
    refine ⟨170516391637519119356043313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 227355188850025492474724417 170516391637519119356043313)
    ·
      refine ⟨127887293728139339517032485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 170516391637519119356043313 127887293728139339517032485)
      ·
        refine ⟨23978867574026126159443591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 127887293728139339517032485 23978867574026126159443591)
        ·
          refine ⟨35968301361039189239165387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23978867574026126159443591 35968301361039189239165387)
          ·
            refine ⟨53952452041558783858748081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35968301361039189239165387 53952452041558783858748081)
            ·
              refine ⟨40464339031169087894061061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53952452041558783858748081 40464339031169087894061061)
              ·
                refine ⟨7587063568344203980136449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40464339031169087894061061 7587063568344203980136449)
                ·
                  refine ⟨5690297676258152985102337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7587063568344203980136449 5690297676258152985102337)
                  ·
                    refine ⟨4267723257193614738826753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5690297676258152985102337 4267723257193614738826753)
                    ·
                      refine ⟨3200792442895211054120065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4267723257193614738826753 3200792442895211054120065)
                      ·
                        rfl

theorem cell23_6233521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 2, 4, 2, 2, 2].length) (baseStart_6233521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6233521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6233521 prefixEnd_6233521 := by exact prefixLift 6233521
  have htrace : WordTrace (prefixWord ++ tailWord_6233521) baseStart_6233521 baseEnd_6233521 := by
    simpa [prefixWord, tailWord_6233521, baseEnd_6233521] using wordTrace_append hprefix tailTrace_6233521
  have hstable : (prefixWord ++ tailWord_6233521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6233521).length < 2 ^ (prefixWord ++ tailWord_6233521).sum := by decide
  have hdescent : baseEnd_6233521 < baseStart_6233521 := by decide
  rcases family_descends (prefixWord ++ tailWord_6233521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6233578 : List Nat := [3, 1, 3, 1, 4, 2, 2, 2, 5]
def baseStart_6233578 : Nat := 118140960795 + 6233578 * 2 ^ 59
def prefixEnd_6233578 : Nat := 4983230072969 + 3 ^ 40 * 6233578 * 2
def baseEnd_6233578 : Nat := 355646856810279703456367

theorem tailTrace_6233578 : CollatzResearch.WordTrace tailWord_6233578 prefixEnd_6233578 355646856810279703456367 := by
  unfold tailWord_6233578
  simp only [CollatzResearch.WordTrace]
  refine ⟨56839316952704747802387347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151571511873879327473032925 56839316952704747802387347)
  ·
    refine ⟨85258975429057121703581021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56839316952704747802387347 85258975429057121703581021)
    ·
      refine ⟨31972115785896420638842883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85258975429057121703581021 31972115785896420638842883)
      ·
        refine ⟨47958173678844630958264325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31972115785896420638842883 47958173678844630958264325)
        ·
          refine ⟨8992157564783368304674561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 47958173678844630958264325 8992157564783368304674561)
          ·
            refine ⟨6744118173587526228505921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8992157564783368304674561 6744118173587526228505921)
            ·
              refine ⟨5058088630190644671379441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6744118173587526228505921 5058088630190644671379441)
              ·
                refine ⟨3793566472642983503534581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5058088630190644671379441 3793566472642983503534581)
                ·
                  refine ⟨355646856810279703456367, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3793566472642983503534581 355646856810279703456367)
                  ·
                    rfl

theorem cell23_6233578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 2, 2, 2, 5].length) (baseStart_6233578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6233578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6233578 prefixEnd_6233578 := by exact prefixLift 6233578
  have htrace : WordTrace (prefixWord ++ tailWord_6233578) baseStart_6233578 baseEnd_6233578 := by
    simpa [prefixWord, tailWord_6233578, baseEnd_6233578] using wordTrace_append hprefix tailTrace_6233578
  have hstable : (prefixWord ++ tailWord_6233578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6233578).length < 2 ^ (prefixWord ++ tailWord_6233578).sum := by decide
  have hdescent : baseEnd_6233578 < baseStart_6233578 := by decide
  rcases family_descends (prefixWord ++ tailWord_6233578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6233594 : List Nat := [3, 1, 1, 1, 1, 2, 5, 1, 2, 4, 2]
def baseStart_6233594 : Nat := 118140960795 + 6233594 * 2 ^ 59
def prefixEnd_6233594 : Nat := 4983230072969 + 3 ^ 40 * 6233594 * 2
def baseEnd_6233594 : Nat := 3200829926982989268507229

theorem tailTrace_6233594 : CollatzResearch.WordTrace tailWord_6233594 prefixEnd_6233594 3200829926982989268507229 := by
  unfold tailWord_6233594
  simp only [CollatzResearch.WordTrace]
  refine ⟨56839462844690256485532959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151571900919174017294754557 56839462844690256485532959)
  ·
    refine ⟨85259194267035384728299439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56839462844690256485532959 85259194267035384728299439)
    ·
      refine ⟨127888791400553077092449159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85259194267035384728299439 127888791400553077092449159)
      ·
        refine ⟨191833187100829615638673739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127888791400553077092449159 191833187100829615638673739)
        ·
          refine ⟨287749780651244423458010609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 191833187100829615638673739 287749780651244423458010609)
          ·
            refine ⟨215812335488433317593507957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 287749780651244423458010609 215812335488433317593507957)
            ·
              refine ⟨20232406452040623524391371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 215812335488433317593507957 20232406452040623524391371)
              ·
                refine ⟨30348609678060935286587057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20232406452040623524391371 30348609678060935286587057)
                ·
                  refine ⟨22761457258545701464940293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30348609678060935286587057 22761457258545701464940293)
                  ·
                    refine ⟨4267773235977319024676305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22761457258545701464940293 4267773235977319024676305)
                    ·
                      refine ⟨3200829926982989268507229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4267773235977319024676305 3200829926982989268507229)
                      ·
                        rfl

theorem cell23_6233594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 5, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 5, 1, 2, 4, 2].length) (baseStart_6233594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6233594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6233594 prefixEnd_6233594 := by exact prefixLift 6233594
  have htrace : WordTrace (prefixWord ++ tailWord_6233594) baseStart_6233594 baseEnd_6233594 := by
    simpa [prefixWord, tailWord_6233594, baseEnd_6233594] using wordTrace_append hprefix tailTrace_6233594
  have hstable : (prefixWord ++ tailWord_6233594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6233594).length < 2 ^ (prefixWord ++ tailWord_6233594).sum := by decide
  have hdescent : baseEnd_6233594 < baseStart_6233594 := by decide
  rcases family_descends (prefixWord ++ tailWord_6233594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6233611 : List Nat := [1, 1, 1, 1, 8, 2, 1, 1, 2, 1, 4]
def baseStart_6233611 : Nat := 118140960795 + 6233611 * 2 ^ 59
def prefixEnd_6233611 : Nat := 4983230072969 + 3 ^ 40 * 6233611 * 2
def baseEnd_6233611 : Nat := 3200838656154115701994651

theorem tailTrace_6233611 : CollatzResearch.WordTrace tailWord_6233611 prefixEnd_6233611 3200838656154115701994651 := by
  unfold tailWord_6233611
  simp only [CollatzResearch.WordTrace]
  refine ⟨227358471419699437845500687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151572314279799625230333791 227358471419699437845500687)
  ·
    refine ⟨341037707129549156768251031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227358471419699437845500687 341037707129549156768251031)
    ·
      refine ⟨511556560694323735152376547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 341037707129549156768251031 511556560694323735152376547)
      ·
        refine ⟨767334841041485602728564821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 511556560694323735152376547 767334841041485602728564821)
        ·
          refine ⟨8992205168454909406975369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 767334841041485602728564821 8992205168454909406975369)
          ·
            refine ⟨6744153876341182055231527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8992205168454909406975369 6744153876341182055231527)
            ·
              refine ⟨10116230814511773082847291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6744153876341182055231527 10116230814511773082847291)
              ·
                refine ⟨15174346221767659624270937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10116230814511773082847291 15174346221767659624270937)
                ·
                  refine ⟨11380759666325744718203203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15174346221767659624270937 11380759666325744718203203)
                  ·
                    refine ⟨17071139499488617077304805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11380759666325744718203203 17071139499488617077304805)
                    ·
                      refine ⟨3200838656154115701994651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17071139499488617077304805 3200838656154115701994651)
                      ·
                        rfl

theorem cell23_6233611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 2, 1, 1, 2, 1, 4].length) (baseStart_6233611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6233611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6233611 prefixEnd_6233611 := by exact prefixLift 6233611
  have htrace : WordTrace (prefixWord ++ tailWord_6233611) baseStart_6233611 baseEnd_6233611 := by
    simpa [prefixWord, tailWord_6233611, baseEnd_6233611] using wordTrace_append hprefix tailTrace_6233611
  have hstable : (prefixWord ++ tailWord_6233611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6233611).length < 2 ^ (prefixWord ++ tailWord_6233611).sum := by decide
  have hdescent : baseEnd_6233611 < baseStart_6233611 := by decide
  rcases family_descends (prefixWord ++ tailWord_6233611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6233621 : List Nat := [1, 3, 2, 1, 3, 2, 1, 5, 1, 4]
def baseStart_6233621 : Nat := 118140960795 + 6233621 * 2 ^ 59
def prefixEnd_6233621 : Nat := 4983230072969 + 3 ^ 40 * 6233621 * 2
def baseEnd_6233621 : Nat := 1066947930320220220956535

theorem tailTrace_6233621 : CollatzResearch.WordTrace tailWord_6233621 prefixEnd_6233621 1066947930320220220956535 := by
  unfold tailWord_6233621
  simp only [CollatzResearch.WordTrace]
  refine ⟨227358836149663209553364717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151572557433108806368909811 227358836149663209553364717)
  ·
    refine ⟨85259563556123703582511769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 227358836149663209553364717 85259563556123703582511769)
    ·
      refine ⟨63944672667092777686883827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85259563556123703582511769 63944672667092777686883827)
      ·
        refine ⟨95917009000639166530325741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63944672667092777686883827 95917009000639166530325741)
        ·
          refine ⟨35968878375239687448872153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 95917009000639166530325741 35968878375239687448872153)
          ·
            refine ⟨26976658781429765586654115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35968878375239687448872153 26976658781429765586654115)
            ·
              refine ⟨40464988172144648379981173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26976658781429765586654115 40464988172144648379981173)
              ·
                refine ⟨3793592641138560785623235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 40464988172144648379981173 3793592641138560785623235)
                ·
                  refine ⟨5690388961707841178434853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3793592641138560785623235 5690388961707841178434853)
                  ·
                    refine ⟨1066947930320220220956535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5690388961707841178434853 1066947930320220220956535)
                    ·
                      rfl

theorem cell23_6233621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 1, 5, 1, 4].length) (baseStart_6233621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6233621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6233621 prefixEnd_6233621 := by exact prefixLift 6233621
  have htrace : WordTrace (prefixWord ++ tailWord_6233621) baseStart_6233621 baseEnd_6233621 := by
    simpa [prefixWord, tailWord_6233621, baseEnd_6233621] using wordTrace_append hprefix tailTrace_6233621
  have hstable : (prefixWord ++ tailWord_6233621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6233621).length < 2 ^ (prefixWord ++ tailWord_6233621).sum := by decide
  have hdescent : baseEnd_6233621 < baseStart_6233621 := by decide
  rcases family_descends (prefixWord ++ tailWord_6233621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6233634 : List Nat := [3, 3, 1, 1, 1, 1, 5, 2, 6]
def baseStart_6233634 : Nat := 118140960795 + 6233634 * 2 ^ 59
def prefixEnd_6233634 : Nat := 4983230072969 + 3 ^ 40 * 6233634 * 2
def baseEnd_6233634 : Nat := 355650051801018790223005

theorem tailTrace_6233634 : CollatzResearch.WordTrace tailWord_6233634 prefixEnd_6233634 355650051801018790223005 := by
  unfold tailWord_6233634
  simp only [CollatzResearch.WordTrace]
  refine ⟨56839827574654028193396989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151572873532410741849058637 56839827574654028193396989)
  ·
    refine ⟨21314935340495260572523871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56839827574654028193396989 21314935340495260572523871)
    ·
      refine ⟨31972403010742890858785807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21314935340495260572523871 31972403010742890858785807)
      ·
        refine ⟨47958604516114336288178711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31972403010742890858785807 47958604516114336288178711)
        ·
          refine ⟨71937906774171504432268067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47958604516114336288178711 71937906774171504432268067)
          ·
            refine ⟨107906860161257256648402101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71937906774171504432268067 107906860161257256648402101)
            ·
              refine ⟨10116268140117867810787697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 107906860161257256648402101 10116268140117867810787697)
              ·
                refine ⟨7587201105088400858090773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10116268140117867810787697 7587201105088400858090773)
                ·
                  refine ⟨355650051801018790223005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7587201105088400858090773 355650051801018790223005)
                  ·
                    rfl

theorem cell23_6233634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 5, 2, 6].length) (baseStart_6233634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6233634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6233634 prefixEnd_6233634 := by exact prefixLift 6233634
  have htrace : WordTrace (prefixWord ++ tailWord_6233634) baseStart_6233634 baseEnd_6233634 := by
    simpa [prefixWord, tailWord_6233634, baseEnd_6233634] using wordTrace_append hprefix tailTrace_6233634
  have hstable : (prefixWord ++ tailWord_6233634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6233634).length < 2 ^ (prefixWord ++ tailWord_6233634).sum := by decide
  have hdescent : baseEnd_6233634 < baseStart_6233634 := by decide
  rcases family_descends (prefixWord ++ tailWord_6233634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6233697 : List Nat := [1, 2, 3, 1, 1, 3, 1, 1, 3, 1, 6]
def baseStart_6233697 : Nat := 118140960795 + 6233697 * 2 ^ 59
def prefixEnd_6233697 : Nat := 4983230072969 + 3 ^ 40 * 6233697 * 2
def baseEnd_6233697 : Nat := 3200882815490402365519255

theorem tailTrace_6233697 : CollatzResearch.WordTrace tailWord_6233697 prefixEnd_6233697 3200882815490402365519255 := by
  unfold tailWord_6233697
  simp only [CollatzResearch.WordTrace]
  refine ⟨227361608097387874533131345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151574405398258583022087563 227361608097387874533131345)
  ·
    refine ⟨170521206073040905899848509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 227361608097387874533131345 170521206073040905899848509)
    ·
      refine ⟨63945452277390339712443191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 170521206073040905899848509 63945452277390339712443191)
      ·
        refine ⟨95918178416085509568664787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63945452277390339712443191 95918178416085509568664787)
        ·
          refine ⟨143877267624128264352997181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95918178416085509568664787 143877267624128264352997181)
          ·
            refine ⟨53953975359048099132373943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 143877267624128264352997181 53953975359048099132373943)
            ·
              refine ⟨80930963038572148698560915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53953975359048099132373943 80930963038572148698560915)
              ·
                refine ⟨121396444557858223047841373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 80930963038572148698560915 121396444557858223047841373)
                ·
                  refine ⟨45523666709196833642940515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 121396444557858223047841373 45523666709196833642940515)
                  ·
                    refine ⟨68285500063795250464410773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 45523666709196833642940515 68285500063795250464410773)
                    ·
                      refine ⟨3200882815490402365519255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 68285500063795250464410773 3200882815490402365519255)
                      ·
                        rfl

theorem cell23_6233697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 1, 3, 1, 6].length) (baseStart_6233697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6233697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6233697 prefixEnd_6233697 := by exact prefixLift 6233697
  have htrace : WordTrace (prefixWord ++ tailWord_6233697) baseStart_6233697 baseEnd_6233697 := by
    simpa [prefixWord, tailWord_6233697, baseEnd_6233697] using wordTrace_append hprefix tailTrace_6233697
  have hstable : (prefixWord ++ tailWord_6233697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6233697).length < 2 ^ (prefixWord ++ tailWord_6233697).sum := by decide
  have hdescent : baseEnd_6233697 < baseStart_6233697 := by decide
  rcases family_descends (prefixWord ++ tailWord_6233697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6233714 : List Nat := [3, 2, 1, 2, 3, 1, 2, 1, 1, 1, 6]
def baseStart_6233714 : Nat := 118140960795 + 6233714 * 2 ^ 59
def prefixEnd_6233714 : Nat := 4983230072969 + 3 ^ 40 * 6233714 * 2
def baseEnd_6233714 : Nat := 3200891544661528799006677

theorem tailTrace_6233714 : CollatzResearch.WordTrace tailWord_6233714 prefixEnd_6233714 3200891544661528799006677 := by
  unfold tailWord_6233714
  simp only [CollatzResearch.WordTrace]
  refine ⟨56840557034581571609125049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151574818758884190957666797 56840557034581571609125049)
  ·
    refine ⟨42630417775936178706843787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56840557034581571609125049 42630417775936178706843787)
    ·
      refine ⟨63945626663904268060265681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42630417775936178706843787 63945626663904268060265681)
      ·
        refine ⟨47959219997928201045199261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63945626663904268060265681 47959219997928201045199261)
        ·
          refine ⟨17984707499223075391949723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47959219997928201045199261 17984707499223075391949723)
          ·
            refine ⟨26977061248834613087924585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17984707499223075391949723 26977061248834613087924585)
            ·
              refine ⟨20232795936625959815943439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26977061248834613087924585 20232795936625959815943439)
              ·
                refine ⟨30349193904938939723915159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20232795936625959815943439 30349193904938939723915159)
                ·
                  refine ⟨45523790857408409585872739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30349193904938939723915159 45523790857408409585872739)
                  ·
                    refine ⟨68285686286112614378809109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 45523790857408409585872739 68285686286112614378809109)
                    ·
                      refine ⟨3200891544661528799006677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 68285686286112614378809109 3200891544661528799006677)
                      ·
                        rfl

theorem cell23_6233714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 2, 1, 1, 1, 6].length) (baseStart_6233714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6233714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6233714 prefixEnd_6233714 := by exact prefixLift 6233714
  have htrace : WordTrace (prefixWord ++ tailWord_6233714) baseStart_6233714 baseEnd_6233714 := by
    simpa [prefixWord, tailWord_6233714, baseEnd_6233714] using wordTrace_append hprefix tailTrace_6233714
  have hstable : (prefixWord ++ tailWord_6233714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6233714).length < 2 ^ (prefixWord ++ tailWord_6233714).sum := by decide
  have hdescent : baseEnd_6233714 < baseStart_6233714 := by decide
  rcases family_descends (prefixWord ++ tailWord_6233714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6233718 : List Nat := [5, 1, 1, 2, 2, 1, 3, 2, 1, 1, 4]
def baseStart_6233718 : Nat := 118140960795 + 6233718 * 2 ^ 59
def prefixEnd_6233718 : Nat := 4983230072969 + 3 ^ 40 * 6233718 * 2
def baseEnd_6233718 : Nat := 3200893598584146783356659

theorem tailTrace_6233718 : CollatzResearch.WordTrace tailWord_6233718 prefixEnd_6233718 3200893598584146783356659 := by
  unfold tailWord_6233718
  simp only [CollatzResearch.WordTrace]
  refine ⟨14210148376894487194977863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 151574916020207863413097205 14210148376894487194977863)
  ·
    refine ⟨21315222565341730792466795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14210148376894487194977863 21315222565341730792466795)
    ·
      refine ⟨31972833848012596188700193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21315222565341730792466795 31972833848012596188700193)
      ·
        refine ⟨23979625386009447141525145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31972833848012596188700193 23979625386009447141525145)
        ·
          refine ⟨17984719039507085356143859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23979625386009447141525145 17984719039507085356143859)
          ·
            refine ⟨26977078559260628034215789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17984719039507085356143859 26977078559260628034215789)
            ·
              refine ⟨10116404459722735512830921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26977078559260628034215789 10116404459722735512830921)
              ·
                refine ⟨7587303344792051634623191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10116404459722735512830921 7587303344792051634623191)
                ·
                  refine ⟨11380955017188077451934787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7587303344792051634623191 11380955017188077451934787)
                  ·
                    refine ⟨17071432525782116177902181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11380955017188077451934787 17071432525782116177902181)
                    ·
                      refine ⟨3200893598584146783356659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17071432525782116177902181 3200893598584146783356659)
                      ·
                        rfl

theorem cell23_6233718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 3, 2, 1, 1, 4].length) (baseStart_6233718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6233718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6233718 prefixEnd_6233718 := by exact prefixLift 6233718
  have htrace : WordTrace (prefixWord ++ tailWord_6233718) baseStart_6233718 baseEnd_6233718 := by
    simpa [prefixWord, tailWord_6233718, baseEnd_6233718] using wordTrace_append hprefix tailTrace_6233718
  have hstable : (prefixWord ++ tailWord_6233718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6233718).length < 2 ^ (prefixWord ++ tailWord_6233718).sum := by decide
  have hdescent : baseEnd_6233718 < baseStart_6233718 := by decide
  rcases family_descends (prefixWord ++ tailWord_6233718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6233752 : List Nat := [2, 1, 2, 4, 1, 2, 4, 2, 1, 2, 2]
def baseStart_6233752 : Nat := 118140960795 + 6233752 * 2 ^ 59
def prefixEnd_6233752 : Nat := 4983230072969 + 3 ^ 40 * 6233752 * 2
def baseEnd_6233752 : Nat := 3200911056926399650331503

theorem tailTrace_6233752 : CollatzResearch.WordTrace tailWord_6233752 prefixEnd_6233752 3200911056926399650331503 := by
  unfold tailWord_6233752
  simp only [CollatzResearch.WordTrace]
  refine ⟨113681807056094309463191755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151575742741459079284255673 113681807056094309463191755)
  ·
    refine ⟨170522710584141464194787633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113681807056094309463191755 170522710584141464194787633)
    ·
      refine ⟨127892032938106098146090725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 170522710584141464194787633 127892032938106098146090725)
      ·
        refine ⟨23979756175894893402392011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 127892032938106098146090725 23979756175894893402392011)
        ·
          refine ⟨35969634263842340103588017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23979756175894893402392011 35969634263842340103588017)
          ·
            refine ⟨26977225697881755077691013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35969634263842340103588017 26977225697881755077691013)
            ·
              refine ⟨5058229818352829077067065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26977225697881755077691013 5058229818352829077067065)
              ·
                refine ⟨3793672363764621807800299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5058229818352829077067065 3793672363764621807800299)
                ·
                  refine ⟨5690508545646932711700449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3793672363764621807800299 5690508545646932711700449)
                  ·
                    refine ⟨4267881409235199533775337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5690508545646932711700449 4267881409235199533775337)
                    ·
                      refine ⟨3200911056926399650331503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4267881409235199533775337 3200911056926399650331503)
                      ·
                        rfl

theorem cell23_6233752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 4, 2, 1, 2, 2].length) (baseStart_6233752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6233752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6233752 prefixEnd_6233752 := by exact prefixLift 6233752
  have htrace : WordTrace (prefixWord ++ tailWord_6233752) baseStart_6233752 baseEnd_6233752 := by
    simpa [prefixWord, tailWord_6233752, baseEnd_6233752] using wordTrace_append hprefix tailTrace_6233752
  have hstable : (prefixWord ++ tailWord_6233752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6233752).length < 2 ^ (prefixWord ++ tailWord_6233752).sum := by decide
  have hdescent : baseEnd_6233752 < baseStart_6233752 := by decide
  rcases family_descends (prefixWord ++ tailWord_6233752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6233791 : List Nat := [1, 1, 2, 2, 2, 3, 1, 4, 1, 4, 2]
def baseStart_6233791 : Nat := 118140960795 + 6233791 * 2 ^ 59
def prefixEnd_6233791 : Nat := 4983230072969 + 3 ^ 40 * 6233791 * 2
def baseEnd_6233791 : Nat := 3200931082671924997743823

theorem tailTrace_6233791 : CollatzResearch.WordTrace tailWord_6233791 prefixEnd_6233791 3200931082671924997743823 := by
  unfold tailWord_6233791
  simp only [CollatzResearch.WordTrace]
  refine ⟨227365036559047328587053227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151576691039364885724702151 227365036559047328587053227)
  ·
    refine ⟨341047554838570992880579841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227365036559047328587053227 341047554838570992880579841)
    ·
      refine ⟨255785666128928244660434881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 341047554838570992880579841 255785666128928244660434881)
      ·
        refine ⟨191839249596696183495326161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 255785666128928244660434881 191839249596696183495326161)
        ·
          refine ⟨143879437197522137621494621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 191839249596696183495326161 143879437197522137621494621)
          ·
            refine ⟨53954788949070801608060483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 143879437197522137621494621 53954788949070801608060483)
            ·
              refine ⟨80932183423606202412090725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53954788949070801608060483 80932183423606202412090725)
              ·
                refine ⟨15174784391926162952267011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 80932183423606202412090725 15174784391926162952267011)
                ·
                  refine ⟨22762176587889244428400517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15174784391926162952267011 22762176587889244428400517)
                  ·
                    refine ⟨4267908110229233330325097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22762176587889244428400517 4267908110229233330325097)
                    ·
                      refine ⟨3200931082671924997743823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4267908110229233330325097 3200931082671924997743823)
                      ·
                        rfl

theorem cell23_6233791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 4, 1, 4, 2].length) (baseStart_6233791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6233791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6233791 prefixEnd_6233791 := by exact prefixLift 6233791
  have htrace : WordTrace (prefixWord ++ tailWord_6233791) baseStart_6233791 baseEnd_6233791 := by
    simpa [prefixWord, tailWord_6233791, baseEnd_6233791] using wordTrace_append hprefix tailTrace_6233791
  have hstable : (prefixWord ++ tailWord_6233791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6233791).length < 2 ^ (prefixWord ++ tailWord_6233791).sum := by decide
  have hdescent : baseEnd_6233791 < baseStart_6233791 := by decide
  rcases family_descends (prefixWord ++ tailWord_6233791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6233802 : List Nat := [3, 1, 2, 1, 6, 1, 1, 2, 2, 1, 3]
def baseStart_6233802 : Nat := 118140960795 + 6233802 * 2 ^ 59
def prefixEnd_6233802 : Nat := 4983230072969 + 3 ^ 40 * 6233802 * 2
def baseEnd_6233802 : Nat := 3200936730959124454706273

theorem tailTrace_6233802 : CollatzResearch.WordTrace tailWord_6233802 prefixEnd_6233802 3200936730959124454706273 := by
  unfold tailWord_6233802
  simp only [CollatzResearch.WordTrace]
  refine ⟨56841359440501869366425915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151576958508004984977135773 56841359440501869366425915)
  ·
    refine ⟨85262039160752804049638873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56841359440501869366425915 85262039160752804049638873)
    ·
      refine ⟨63946529370564603037229155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85262039160752804049638873 63946529370564603037229155)
      ·
        refine ⟨95919794055846904555843733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63946529370564603037229155 95919794055846904555843733)
        ·
          refine ⟨4496240346367823651055175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 95919794055846904555843733 4496240346367823651055175)
          ·
            refine ⟨6744360519551735476582763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4496240346367823651055175 6744360519551735476582763)
            ·
              refine ⟨10116540779327603214874145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6744360519551735476582763 10116540779327603214874145)
              ·
                refine ⟨7587405584495702411155609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10116540779327603214874145 7587405584495702411155609)
                ·
                  refine ⟨5690554188371776808366707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7587405584495702411155609 5690554188371776808366707)
                  ·
                    refine ⟨8535831282557665212550061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5690554188371776808366707 8535831282557665212550061)
                    ·
                      refine ⟨3200936730959124454706273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8535831282557665212550061 3200936730959124454706273)
                      ·
                        rfl

theorem cell23_6233802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 6, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 6, 1, 1, 2, 2, 1, 3].length) (baseStart_6233802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6233802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6233802 prefixEnd_6233802 := by exact prefixLift 6233802
  have htrace : WordTrace (prefixWord ++ tailWord_6233802) baseStart_6233802 baseEnd_6233802 := by
    simpa [prefixWord, tailWord_6233802, baseEnd_6233802] using wordTrace_append hprefix tailTrace_6233802
  have hstable : (prefixWord ++ tailWord_6233802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6233802).length < 2 ^ (prefixWord ++ tailWord_6233802).sum := by decide
  have hdescent : baseEnd_6233802 < baseStart_6233802 := by decide
  rcases family_descends (prefixWord ++ tailWord_6233802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6233808 : List Nat := [2, 1, 1, 1, 1, 2, 1, 8, 2, 2, 2]
def baseStart_6233808 : Nat := 118140960795 + 6233808 * 2 ^ 59
def prefixEnd_6233808 : Nat := 4983230072969 + 3 ^ 40 * 6233808 * 2
def baseEnd_6233808 : Nat := 3200939811843051431231245

theorem tailTrace_6233808 : CollatzResearch.WordTrace tailWord_6233808 prefixEnd_6233808 3200939811843051431231245 := by
  unfold tailWord_6233808
  simp only [CollatzResearch.WordTrace]
  refine ⟨113682828299992870245211039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151577104399990493660281385 113682828299992870245211039)
  ·
    refine ⟨170524242449989305367816559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113682828299992870245211039 170524242449989305367816559)
    ·
      refine ⟨255786363674983958051724839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170524242449989305367816559 255786363674983958051724839)
      ·
        refine ⟨383679545512475937077587259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 255786363674983958051724839 383679545512475937077587259)
        ·
          refine ⟨575519318268713905616380889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 383679545512475937077587259 575519318268713905616380889)
          ·
            refine ⟨431639488701535429212285667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 575519318268713905616380889 431639488701535429212285667)
            ·
              refine ⟨647459233052303143818428501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 431639488701535429212285667 647459233052303143818428501)
              ·
                refine ⟨7587412887331677466622209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 647459233052303143818428501 7587412887331677466622209)
                ·
                  refine ⟨5690559665498758099966657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7587412887331677466622209 5690559665498758099966657)
                  ·
                    refine ⟨4267919749124068574974993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5690559665498758099966657 4267919749124068574974993)
                    ·
                      refine ⟨3200939811843051431231245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4267919749124068574974993 3200939811843051431231245)
                      ·
                        rfl

theorem cell23_6233808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 8, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 8, 2, 2, 2].length) (baseStart_6233808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6233808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6233808 prefixEnd_6233808 := by exact prefixLift 6233808
  have htrace : WordTrace (prefixWord ++ tailWord_6233808) baseStart_6233808 baseEnd_6233808 := by
    simpa [prefixWord, tailWord_6233808, baseEnd_6233808] using wordTrace_append hprefix tailTrace_6233808
  have hstable : (prefixWord ++ tailWord_6233808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6233808).length < 2 ^ (prefixWord ++ tailWord_6233808).sum := by decide
  have hdescent : baseEnd_6233808 < baseStart_6233808 := by decide
  rcases family_descends (prefixWord ++ tailWord_6233808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6233825 : List Nat := [1, 2, 3, 1, 5, 2, 1, 1, 1, 4, 2]
def baseStart_6233825 : Nat := 118140960795 + 6233825 * 2 ^ 59
def prefixEnd_6233825 : Nat := 4983230072969 + 3 ^ 40 * 6233825 * 2
def baseEnd_6233825 : Nat := 3200948541014177864718667

theorem tailTrace_6233825 : CollatzResearch.WordTrace tailWord_6233825 prefixEnd_6233825 3200948541014177864718667 := by
  unfold tailWord_6233825
  simp only [CollatzResearch.WordTrace]
  refine ⟨227366276640924152393790929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151577517760616101595860619 227366276640924152393790929)
  ·
    refine ⟨170524707480693114295343197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 227366276640924152393790929 170524707480693114295343197)
    ·
      refine ⟨63946765305259917860753699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 170524707480693114295343197 63946765305259917860753699)
      ·
        refine ⟨95920147957889876791130549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63946765305259917860753699 95920147957889876791130549)
        ·
          refine ⟨8992513871052175949168489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 95920147957889876791130549 8992513871052175949168489)
          ·
            refine ⟨6744385403289131961876367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8992513871052175949168489 6744385403289131961876367)
            ·
              refine ⟨10116578104933697942814551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6744385403289131961876367 10116578104933697942814551)
              ·
                refine ⟨15174867157400546914221827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10116578104933697942814551 15174867157400546914221827)
                ·
                  refine ⟨22762300736100820371332741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15174867157400546914221827 22762300736100820371332741)
                  ·
                    refine ⟨4267931388018903819624889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22762300736100820371332741 4267931388018903819624889)
                    ·
                      refine ⟨3200948541014177864718667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4267931388018903819624889 3200948541014177864718667)
                      ·
                        rfl

theorem cell23_6233825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 2, 1, 1, 1, 4, 2].length) (baseStart_6233825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6233825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6233825 prefixEnd_6233825 := by exact prefixLift 6233825
  have htrace : WordTrace (prefixWord ++ tailWord_6233825) baseStart_6233825 baseEnd_6233825 := by
    simpa [prefixWord, tailWord_6233825, baseEnd_6233825] using wordTrace_append hprefix tailTrace_6233825
  have hstable : (prefixWord ++ tailWord_6233825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6233825).length < 2 ^ (prefixWord ++ tailWord_6233825).sum := by decide
  have hdescent : baseEnd_6233825 < baseStart_6233825 := by decide
  rcases family_descends (prefixWord ++ tailWord_6233825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6233876 : List Nat := [2, 4, 4, 1, 1, 1, 1, 3, 2, 2, 2]
def baseStart_6233876 : Nat := 118140960795 + 6233876 * 2 ^ 59
def prefixEnd_6233876 : Nat := 4983230072969 + 3 ^ 40 * 6233876 * 2
def baseEnd_6233876 : Nat := 3200974728527557165180933

theorem tailTrace_6233876 : CollatzResearch.WordTrace tailWord_6233876 prefixEnd_6233876 3200974728527557165180933 := by
  unfold tailWord_6233876
  simp only [CollatzResearch.WordTrace]
  refine ⟨113684068381869694051948741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151578757842492925402598321 113684068381869694051948741)
  ·
    refine ⟨21315762821600567634740389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 113684068381869694051948741 21315762821600567634740389)
    ·
      refine ⟨3996705529050106431513823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21315762821600567634740389 3996705529050106431513823)
      ·
        refine ⟨5995058293575159647270735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3996705529050106431513823 5995058293575159647270735)
        ·
          refine ⟨8992587440362739470906103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5995058293575159647270735 8992587440362739470906103)
          ·
            refine ⟨13488881160544109206359155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8992587440362739470906103 13488881160544109206359155)
            ·
              refine ⟨20233321740816163809538733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13488881160544109206359155 20233321740816163809538733)
              ·
                refine ⟨7587495652806061428577025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20233321740816163809538733 7587495652806061428577025)
                ·
                  refine ⟨5690621739604546071432769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7587495652806061428577025 5690621739604546071432769)
                  ·
                    refine ⟨4267966304703409553574577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5690621739604546071432769 4267966304703409553574577)
                    ·
                      refine ⟨3200974728527557165180933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4267966304703409553574577 3200974728527557165180933)
                      ·
                        rfl

theorem cell23_6233876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 1, 3, 2, 2, 2].length) (baseStart_6233876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6233876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6233876 prefixEnd_6233876 := by exact prefixLift 6233876
  have htrace : WordTrace (prefixWord ++ tailWord_6233876) baseStart_6233876 baseEnd_6233876 := by
    simpa [prefixWord, tailWord_6233876, baseEnd_6233876] using wordTrace_append hprefix tailTrace_6233876
  have hstable : (prefixWord ++ tailWord_6233876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6233876).length < 2 ^ (prefixWord ++ tailWord_6233876).sum := by decide
  have hdescent : baseEnd_6233876 < baseStart_6233876 := by decide
  rcases family_descends (prefixWord ++ tailWord_6233876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6233881 : List Nat := [1, 2, 1, 2, 1, 1, 1, 2, 6, 4, 2]
def baseStart_6233881 : Nat := 118140960795 + 6233881 * 2 ^ 59
def prefixEnd_6233881 : Nat := 4983230072969 + 3 ^ 40 * 6233881 * 2
def baseEnd_6233881 : Nat := 3200977295930829645618409

theorem tailTrace_6233881 : CollatzResearch.WordTrace tailWord_6233881 prefixEnd_6233881 3200977295930829645618409 := by
  unfold tailWord_6233881
  simp only [CollatzResearch.WordTrace]
  refine ⟨227368319128721273957829497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151578879419147515971886331 227368319128721273957829497)
  ·
    refine ⟨170526239346540955468372123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 227368319128721273957829497 170526239346540955468372123)
    ·
      refine ⟨255789359019811433202558185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170526239346540955468372123 255789359019811433202558185)
      ·
        refine ⟨191842019264858574901918639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 255789359019811433202558185 191842019264858574901918639)
        ·
          refine ⟨287763028897287862352877959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 191842019264858574901918639 287763028897287862352877959)
          ·
            refine ⟨431644543345931793529316939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 287763028897287862352877959 431644543345931793529316939)
            ·
              refine ⟨647466815018897690293975409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 431644543345931793529316939 647466815018897690293975409)
              ·
                refine ⟨485600111264173267720481557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 647466815018897690293975409 485600111264173267720481557)
                ·
                  refine ⟨22762505215508121924397573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 485600111264173267720481557 22762505215508121924397573)
                  ·
                    refine ⟨4267969727907772860824545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22762505215508121924397573 4267969727907772860824545)
                    ·
                      refine ⟨3200977295930829645618409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4267969727907772860824545 3200977295930829645618409)
                      ·
                        rfl

theorem cell23_6233881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 2, 6, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 2, 6, 4, 2].length) (baseStart_6233881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6233881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6233881 prefixEnd_6233881 := by exact prefixLift 6233881
  have htrace : WordTrace (prefixWord ++ tailWord_6233881) baseStart_6233881 baseEnd_6233881 := by
    simpa [prefixWord, tailWord_6233881, baseEnd_6233881] using wordTrace_append hprefix tailTrace_6233881
  have hstable : (prefixWord ++ tailWord_6233881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6233881).length < 2 ^ (prefixWord ++ tailWord_6233881).sum := by decide
  have hdescent : baseEnd_6233881 < baseStart_6233881 := by decide
  rcases family_descends (prefixWord ++ tailWord_6233881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6233891 : List Nat := [1, 1, 1, 4, 2, 1, 2, 4, 3, 4]
def baseStart_6233891 : Nat := 118140960795 + 6233891 * 2 ^ 59
def prefixEnd_6233891 : Nat := 4983230072969 + 3 ^ 40 * 6233891 * 2
def baseEnd_6233891 : Nat := 1066994143579124868831121

theorem tailTrace_6233891 : CollatzResearch.WordTrace tailWord_6233891 prefixEnd_6233891 1066994143579124868831121 := by
  unfold tailWord_6233891
  simp only [CollatzResearch.WordTrace]
  refine ⟨227368683858685045665693527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151579122572456697110462351 227368683858685045665693527)
  ·
    refine ⟨341053025788027568498540291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227368683858685045665693527 341053025788027568498540291)
    ·
      refine ⟨511579538682041352747810437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 341053025788027568498540291 511579538682041352747810437)
      ·
        refine ⟨95921163502882753640214457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 511579538682041352747810437 95921163502882753640214457)
        ·
          refine ⟨71940872627162065230160843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95921163502882753640214457 71940872627162065230160843)
          ·
            refine ⟨107911308940743097845241265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71940872627162065230160843 107911308940743097845241265)
            ·
              refine ⟨80933481705557323383930949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 107911308940743097845241265 80933481705557323383930949)
              ·
                refine ⟨15175027819791998134487053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 80933481705557323383930949 15175027819791998134487053)
                ·
                  refine ⟨5690635432421999300432645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15175027819791998134487053 5690635432421999300432645)
                  ·
                    refine ⟨1066994143579124868831121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5690635432421999300432645 1066994143579124868831121)
                    ·
                      rfl

theorem cell23_6233891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 4, 3, 4].length) (baseStart_6233891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6233891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6233891 prefixEnd_6233891 := by exact prefixLift 6233891
  have htrace : WordTrace (prefixWord ++ tailWord_6233891) baseStart_6233891 baseEnd_6233891 := by
    simpa [prefixWord, tailWord_6233891, baseEnd_6233891] using wordTrace_append hprefix tailTrace_6233891
  have hstable : (prefixWord ++ tailWord_6233891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6233891).length < 2 ^ (prefixWord ++ tailWord_6233891).sum := by decide
  have hdescent : baseEnd_6233891 < baseStart_6233891 := by decide
  rcases family_descends (prefixWord ++ tailWord_6233891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6233951 : List Nat := [1, 1, 2, 3, 1, 4, 2, 1, 3, 5]
def baseStart_6233951 : Nat := 118140960795 + 6233951 * 2 ^ 59
def prefixEnd_6233951 : Nat := 4983230072969 + 3 ^ 40 * 6233951 * 2
def baseEnd_6233951 : Nat := 1067004413192214790581029

theorem tailTrace_6233951 : CollatzResearch.WordTrace tailWord_6233951 prefixEnd_6233951 1067004413192214790581029 := by
  unfold tailWord_6233951
  simp only [CollatzResearch.WordTrace]
  refine ⟨227370872238467675912877707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151580581492311783941918471 227370872238467675912877707)
  ·
    refine ⟨341056308357701513869316561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227370872238467675912877707 341056308357701513869316561)
    ·
      refine ⟨255792231268276135401987421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 341056308357701513869316561 255792231268276135401987421)
      ·
        refine ⟨95922086725603550775745283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 255792231268276135401987421 95922086725603550775745283)
        ·
          refine ⟨143883130088405326163617925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95922086725603550775745283 143883130088405326163617925)
          ·
            refine ⟨26978086891575998655678361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 143883130088405326163617925 26978086891575998655678361)
            ·
              refine ⟨20233565168681998991758771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26978086891575998655678361 20233565168681998991758771)
              ·
                refine ⟨30350347753022998487638157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20233565168681998991758771 30350347753022998487638157)
                ·
                  refine ⟨11381380407383624432864309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30350347753022998487638157 11381380407383624432864309)
                  ·
                    refine ⟨1067004413192214790581029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11381380407383624432864309 1067004413192214790581029)
                    ·
                      rfl

theorem cell23_6233951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 2, 1, 3, 5].length) (baseStart_6233951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6233951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6233951 prefixEnd_6233951 := by exact prefixLift 6233951
  have htrace : WordTrace (prefixWord ++ tailWord_6233951) baseStart_6233951 baseEnd_6233951 := by
    simpa [prefixWord, tailWord_6233951, baseEnd_6233951] using wordTrace_append hprefix tailTrace_6233951
  have hstable : (prefixWord ++ tailWord_6233951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6233951).length < 2 ^ (prefixWord ++ tailWord_6233951).sum := by decide
  have hdescent : baseEnd_6233951 < baseStart_6233951 := by decide
  rcases family_descends (prefixWord ++ tailWord_6233951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6233982 : List Nat := [4, 2, 3, 1, 1, 1, 1, 3, 3, 1, 3]
def baseStart_6233982 : Nat := 118140960795 + 6233982 * 2 ^ 59
def prefixEnd_6233982 : Nat := 4983230072969 + 3 ^ 40 * 6233982 * 2
def baseEnd_6233982 : Nat := 3201029157476933750455445

theorem tailTrace_6233982 : CollatzResearch.WordTrace tailWord_6233982 prefixEnd_6233982 3201029157476933750455445 := by
  unfold tailWord_6233982
  simp only [CollatzResearch.WordTrace]
  refine ⟨28421500362669421025907025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 151581335267570245471504133 28421500362669421025907025)
  ·
    refine ⟨21316125272002065769430269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28421500362669421025907025 21316125272002065769430269)
    ·
      refine ⟨7993546977000774663536351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21316125272002065769430269 7993546977000774663536351)
      ·
        refine ⟨11990320465501161995304527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7993546977000774663536351 11990320465501161995304527)
        ·
          refine ⟨17985480698251742992956791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11990320465501161995304527 17985480698251742992956791)
          ·
            refine ⟨26978221047377614489435187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17985480698251742992956791 26978221047377614489435187)
            ·
              refine ⟨40467331571066421734152781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26978221047377614489435187 40467331571066421734152781)
              ·
                refine ⟨15175249339149908150307293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40467331571066421734152781 15175249339149908150307293)
                ·
                  refine ⟨5690718502181215556365235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15175249339149908150307293 5690718502181215556365235)
                  ·
                    refine ⟨8536077753271823334547853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5690718502181215556365235 8536077753271823334547853)
                    ·
                      refine ⟨3201029157476933750455445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8536077753271823334547853 3201029157476933750455445)
                      ·
                        rfl

theorem cell23_6233982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 1, 3, 3, 1, 3].length) (baseStart_6233982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6233982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6233982 prefixEnd_6233982 := by exact prefixLift 6233982
  have htrace : WordTrace (prefixWord ++ tailWord_6233982) baseStart_6233982 baseEnd_6233982 := by
    simpa [prefixWord, tailWord_6233982, baseEnd_6233982] using wordTrace_append hprefix tailTrace_6233982
  have hstable : (prefixWord ++ tailWord_6233982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6233982).length < 2 ^ (prefixWord ++ tailWord_6233982).sum := by decide
  have hdescent : baseEnd_6233982 < baseStart_6233982 := by decide
  rcases family_descends (prefixWord ++ tailWord_6233982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6234005 : List Nat := [1, 3, 2, 1, 1, 3, 1, 4, 3, 2, 2]
def baseStart_6234005 : Nat := 118140960795 + 6234005 * 2 ^ 59
def prefixEnd_6234005 : Nat := 4983230072969 + 3 ^ 40 * 6234005 * 2
def baseEnd_6234005 : Nat := 3201040967531987160467839

theorem tailTrace_6234005 : CollatzResearch.WordTrace tailWord_6234005 prefixEnd_6234005 3201040967531987160467839 := by
  unfold tailWord_6234005
  simp only [CollatzResearch.WordTrace]
  refine ⟨227372841780272043135343469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151581894520181362090228979 227372841780272043135343469)
  ·
    refine ⟨85264815667602016175753801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 227372841780272043135343469 85264815667602016175753801)
    ·
      refine ⟨63948611750701512131815351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85264815667602016175753801 63948611750701512131815351)
      ·
        refine ⟨95922917626052268197723027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63948611750701512131815351 95922917626052268197723027)
        ·
          refine ⟨143884376439078402296584541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95922917626052268197723027 143884376439078402296584541)
          ·
            refine ⟨53956641164654400861219203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 143884376439078402296584541 53956641164654400861219203)
            ·
              refine ⟨80934961746981601291828805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53956641164654400861219203 80934961746981601291828805)
              ·
                refine ⟨15175305327559050242217901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 80934961746981601291828805 15175305327559050242217901)
                ·
                  refine ⟨5690739497834643840831713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15175305327559050242217901 5690739497834643840831713)
                  ·
                    refine ⟨4268054623375982880623785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5690739497834643840831713 4268054623375982880623785)
                    ·
                      refine ⟨3201040967531987160467839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4268054623375982880623785 3201040967531987160467839)
                      ·
                        rfl

theorem cell23_6234005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 4, 3, 2, 2].length) (baseStart_6234005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6234005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6234005 prefixEnd_6234005 := by exact prefixLift 6234005
  have htrace : WordTrace (prefixWord ++ tailWord_6234005) baseStart_6234005 baseEnd_6234005 := by
    simpa [prefixWord, tailWord_6234005, baseEnd_6234005] using wordTrace_append hprefix tailTrace_6234005
  have hstable : (prefixWord ++ tailWord_6234005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6234005).length < 2 ^ (prefixWord ++ tailWord_6234005).sum := by decide
  have hdescent : baseEnd_6234005 < baseStart_6234005 := by decide
  rcases family_descends (prefixWord ++ tailWord_6234005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6234041 : List Nat := [1, 2, 1, 4, 2, 1, 2, 1, 2, 7]
def baseStart_6234041 : Nat := 118140960795 + 6234041 * 2 ^ 59
def prefixEnd_6234041 : Nat := 4983230072969 + 3 ^ 40 * 6234041 * 2
def baseEnd_6234041 : Nat := 1067019817611849673205891

theorem tailTrace_6234041 : CollatzResearch.WordTrace tailWord_6234041 prefixEnd_6234041 1067019817611849673205891 := by
  unfold tailWord_6234041
  simp only [CollatzResearch.WordTrace]
  refine ⟨227374154808141621283653977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151582769872094414189102651 227374154808141621283653977)
  ·
    refine ⟨170530616106106215962740483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 227374154808141621283653977 170530616106106215962740483)
    ·
      refine ⟨255795924159159323944110725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170530616106106215962740483 255795924159159323944110725)
      ·
        refine ⟨47961735779842373239520761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 255795924159159323944110725 47961735779842373239520761)
        ·
          refine ⟨35971301834881779929640571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47961735779842373239520761 35971301834881779929640571)
          ·
            refine ⟨53956952752322669894460857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35971301834881779929640571 53956952752322669894460857)
            ·
              refine ⟨40467714564242002420845643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53956952752322669894460857 40467714564242002420845643)
              ·
                refine ⟨60701571846363003631268465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40467714564242002420845643 60701571846363003631268465)
                ·
                  refine ⟨45526178884772252723451349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 60701571846363003631268465 45526178884772252723451349)
                  ·
                    refine ⟨1067019817611849673205891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 45526178884772252723451349 1067019817611849673205891)
                    ·
                      rfl

theorem cell23_6234041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 2, 1, 2, 7].length) (baseStart_6234041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6234041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6234041 prefixEnd_6234041 := by exact prefixLift 6234041
  have htrace : WordTrace (prefixWord ++ tailWord_6234041) baseStart_6234041 baseEnd_6234041 := by
    simpa [prefixWord, tailWord_6234041, baseEnd_6234041] using wordTrace_append hprefix tailTrace_6234041
  have hstable : (prefixWord ++ tailWord_6234041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6234041).length < 2 ^ (prefixWord ++ tailWord_6234041).sum := by decide
  have hdescent : baseEnd_6234041 < baseStart_6234041 := by decide
  rcases family_descends (prefixWord ++ tailWord_6234041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6234065 : List Nat := [1, 2, 2, 1, 2, 1, 2, 6, 1, 3, 2]
def baseStart_6234065 : Nat := 118140960795 + 6234065 * 2 ^ 59
def prefixEnd_6234065 : Nat := 4983230072969 + 3 ^ 40 * 6234065 * 2
def baseEnd_6234065 : Nat := 3201071776371256925717563

theorem tailTrace_6234065 : CollatzResearch.WordTrace tailWord_6234065 prefixEnd_6234065 3201071776371256925717563 := by
  unfold tailWord_6234065
  simp only [CollatzResearch.WordTrace]
  refine ⟨227375030160054673382527649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151583353440036448921685099 227375030160054673382527649)
  ·
    refine ⟨170531272620041005036895737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 227375030160054673382527649 170531272620041005036895737)
    ·
      refine ⟨127898454465030753777671803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 170531272620041005036895737 127898454465030753777671803)
      ·
        refine ⟨191847681697546130666507705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127898454465030753777671803 191847681697546130666507705)
        ·
          refine ⟨143885761273159597999880779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 191847681697546130666507705 143885761273159597999880779)
          ·
            refine ⟨215828641909739396999821169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 143885761273159597999880779 215828641909739396999821169)
            ·
              refine ⟨161871481432304547749865877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 215828641909739396999821169 161871481432304547749865877)
              ·
                refine ⟨7587725692139275675774963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 161871481432304547749865877 7587725692139275675774963)
                ·
                  refine ⟨11381588538208913513662445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7587725692139275675774963 11381588538208913513662445)
                  ·
                    refine ⟨4268095701828342567623417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11381588538208913513662445 4268095701828342567623417)
                    ·
                      refine ⟨3201071776371256925717563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4268095701828342567623417 3201071776371256925717563)
                      ·
                        rfl

theorem cell23_6234065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 6, 1, 3, 2].length) (baseStart_6234065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6234065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6234065 prefixEnd_6234065 := by exact prefixLift 6234065
  have htrace : WordTrace (prefixWord ++ tailWord_6234065) baseStart_6234065 baseEnd_6234065 := by
    simpa [prefixWord, tailWord_6234065, baseEnd_6234065] using wordTrace_append hprefix tailTrace_6234065
  have hstable : (prefixWord ++ tailWord_6234065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6234065).length < 2 ^ (prefixWord ++ tailWord_6234065).sum := by decide
  have hdescent : baseEnd_6234065 < baseStart_6234065 := by decide
  rcases family_descends (prefixWord ++ tailWord_6234065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6234076 : List Nat := [2, 2, 6, 1, 2, 1, 1, 1, 1, 1, 5]
def baseStart_6234076 : Nat := 118140960795 + 6234076 * 2 ^ 59
def prefixEnd_6234076 : Nat := 4983230072969 + 3 ^ 40 * 6234076 * 2
def baseEnd_6234076 : Nat := 3201077424658456382680013

theorem tailTrace_6234076 : CollatzResearch.WordTrace tailWord_6234076 prefixEnd_6234076 3201077424658456382680013 := by
  unfold tailWord_6234076
  simp only [CollatzResearch.WordTrace]
  refine ⟨113687715681507411130589041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151583620908676548174118721 113687715681507411130589041)
  ·
    refine ⟨85265786761130558347941781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113687715681507411130589041 85265786761130558347941781)
    ·
      refine ⟨3996833754427994922559771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 85265786761130558347941781 3996833754427994922559771)
      ·
        refine ⟨5995250631641992383839657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3996833754427994922559771 5995250631641992383839657)
        ·
          refine ⟨4496437973731494287879743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5995250631641992383839657 4496437973731494287879743)
          ·
            refine ⟨6744656960597241431819615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4496437973731494287879743 6744656960597241431819615)
            ·
              refine ⟨10116985440895862147729423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6744656960597241431819615 10116985440895862147729423)
              ·
                refine ⟨15175478161343793221594135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10116985440895862147729423 15175478161343793221594135)
                ·
                  refine ⟨22763217242015689832391203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15175478161343793221594135 22763217242015689832391203)
                  ·
                    refine ⟨34144825863023534748586805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22763217242015689832391203 34144825863023534748586805)
                    ·
                      refine ⟨3201077424658456382680013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34144825863023534748586805 3201077424658456382680013)
                      ·
                        rfl

theorem cell23_6234076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 2, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 2, 1, 1, 1, 1, 1, 5].length) (baseStart_6234076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6234076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6234076 prefixEnd_6234076 := by exact prefixLift 6234076
  have htrace : WordTrace (prefixWord ++ tailWord_6234076) baseStart_6234076 baseEnd_6234076 := by
    simpa [prefixWord, tailWord_6234076, baseEnd_6234076] using wordTrace_append hprefix tailTrace_6234076
  have hstable : (prefixWord ++ tailWord_6234076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6234076).length < 2 ^ (prefixWord ++ tailWord_6234076).sum := by decide
  have hdescent : baseEnd_6234076 < baseStart_6234076 := by decide
  rcases family_descends (prefixWord ++ tailWord_6234076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6234091 : List Nat := [1, 1, 1, 1, 2, 3, 1, 2, 3, 4, 4]
def baseStart_6234091 : Nat := 118140960795 + 6234091 * 2 ^ 59
def prefixEnd_6234091 : Nat := 4983230072969 + 3 ^ 40 * 6234091 * 2
def baseEnd_6234091 : Nat := 3201085126868273823992443

theorem tailTrace_6234091 : CollatzResearch.WordTrace tailWord_6234091 prefixEnd_6234091 3201085126868273823992443 := by
  unfold tailWord_6234091
  simp only [CollatzResearch.WordTrace]
  refine ⟨227375978457960479822974127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151583985638640319881982751 227375978457960479822974127)
  ·
    refine ⟨341063967686940719734461191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227375978457960479822974127 341063967686940719734461191)
    ·
      refine ⟨511595951530411079601691787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 341063967686940719734461191 511595951530411079601691787)
      ·
        refine ⟨767393927295616619402537681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 511595951530411079601691787 767393927295616619402537681)
        ·
          refine ⟨575545445471712464551903261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 767393927295616619402537681 575545445471712464551903261)
          ·
            refine ⟨215829542051892174206963723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 575545445471712464551903261 215829542051892174206963723)
            ·
              refine ⟨323744313077838261310445585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 215829542051892174206963723 323744313077838261310445585)
              ·
                refine ⟨242808234808378695982834189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 323744313077838261310445585 242808234808378695982834189)
                ·
                  refine ⟨91053088053142010993562821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 242808234808378695982834189 91053088053142010993562821)
                  ·
                    refine ⟨17072454009964127061293029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 91053088053142010993562821 17072454009964127061293029)
                    ·
                      refine ⟨3201085126868273823992443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17072454009964127061293029 3201085126868273823992443)
                      ·
                        rfl

theorem cell23_6234091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 2, 3, 4, 4].length) (baseStart_6234091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6234091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6234091 prefixEnd_6234091 := by exact prefixLift 6234091
  have htrace : WordTrace (prefixWord ++ tailWord_6234091) baseStart_6234091 baseEnd_6234091 := by
    simpa [prefixWord, tailWord_6234091, baseEnd_6234091] using wordTrace_append hprefix tailTrace_6234091
  have hstable : (prefixWord ++ tailWord_6234091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6234091).length < 2 ^ (prefixWord ++ tailWord_6234091).sum := by decide
  have hdescent : baseEnd_6234091 < baseStart_6234091 := by decide
  rcases family_descends (prefixWord ++ tailWord_6234091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6234108 : List Nat := [2, 2, 2, 1, 2, 2, 3, 1, 2, 2, 4]
def baseStart_6234108 : Nat := 118140960795 + 6234108 * 2 ^ 59
def prefixEnd_6234108 : Nat := 4983230072969 + 3 ^ 40 * 6234108 * 2
def baseEnd_6234108 : Nat := 3201093856039400257479865

theorem tailTrace_6234108 : CollatzResearch.WordTrace tailWord_6234108 prefixEnd_6234108 3201093856039400257479865 := by
  unfold tailWord_6234108
  simp only [CollatzResearch.WordTrace]
  refine ⟨113688299249449445863171489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151584398999265927817561985 113688299249449445863171489)
  ·
    refine ⟨85266224437087084397378617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113688299249449445863171489 85266224437087084397378617)
    ·
      refine ⟨63949668327815313298033963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85266224437087084397378617 63949668327815313298033963)
      ·
        refine ⟨95924502491722969947050945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63949668327815313298033963 95924502491722969947050945)
        ·
          refine ⟨71943376868792227460288209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95924502491722969947050945 71943376868792227460288209)
          ·
            refine ⟨53957532651594170595216157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71943376868792227460288209 53957532651594170595216157)
            ·
              refine ⟨20234074744347813973206059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53957532651594170595216157 20234074744347813973206059)
              ·
                refine ⟨30351112116521720959809089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20234074744347813973206059 30351112116521720959809089)
                ·
                  refine ⟨22763334087391290719856817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30351112116521720959809089 22763334087391290719856817)
                  ·
                    refine ⟨17072500565543468039892613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22763334087391290719856817 17072500565543468039892613)
                    ·
                      refine ⟨3201093856039400257479865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17072500565543468039892613 3201093856039400257479865)
                      ·
                        rfl

theorem cell23_6234108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 3, 1, 2, 2, 4].length) (baseStart_6234108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6234108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6234108 prefixEnd_6234108 := by exact prefixLift 6234108
  have htrace : WordTrace (prefixWord ++ tailWord_6234108) baseStart_6234108 baseEnd_6234108 := by
    simpa [prefixWord, tailWord_6234108, baseEnd_6234108] using wordTrace_append hprefix tailTrace_6234108
  have hstable : (prefixWord ++ tailWord_6234108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6234108).length < 2 ^ (prefixWord ++ tailWord_6234108).sum := by decide
  have hdescent : baseEnd_6234108 < baseStart_6234108 := by decide
  rcases family_descends (prefixWord ++ tailWord_6234108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6234152 : List Nat := [2, 1, 5, 3, 1, 1, 2, 1, 7]
def baseStart_6234152 : Nat := 118140960795 + 6234152 * 2 ^ 59
def prefixEnd_6234152 : Nat := 4983230072969 + 3 ^ 40 * 6234152 * 2
def baseEnd_6234152 : Nat := 355679605465355342814407

theorem tailTrace_6234152 : CollatzResearch.WordTrace tailWord_6234152 prefixEnd_6234152 355679605465355342814407 := by
  unfold tailWord_6234152
  simp only [CollatzResearch.WordTrace]
  refine ⟨113689101655369743620472355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151585468873826324827296473 113689101655369743620472355)
  ·
    refine ⟨170533652483054615430708533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113689101655369743620472355 170533652483054615430708533)
    ·
      refine ⟨15987529920286370196628925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 170533652483054615430708533 15987529920286370196628925)
      ·
        refine ⟨5995323720107388823735847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15987529920286370196628925 5995323720107388823735847)
        ·
          refine ⟨8992985580161083235603771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5995323720107388823735847 8992985580161083235603771)
          ·
            refine ⟨13489478370241624853405657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8992985580161083235603771 13489478370241624853405657)
            ·
              refine ⟨10117108777681218640054243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13489478370241624853405657 10117108777681218640054243)
              ·
                refine ⟨15175663166521827960081365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10117108777681218640054243 15175663166521827960081365)
                ·
                  refine ⟨355679605465355342814407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15175663166521827960081365 355679605465355342814407)
                  ·
                    rfl

theorem cell23_6234152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 2, 1, 7].length) (baseStart_6234152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6234152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6234152 prefixEnd_6234152 := by exact prefixLift 6234152
  have htrace : WordTrace (prefixWord ++ tailWord_6234152) baseStart_6234152 baseEnd_6234152 := by
    simpa [prefixWord, tailWord_6234152, baseEnd_6234152] using wordTrace_append hprefix tailTrace_6234152
  have hstable : (prefixWord ++ tailWord_6234152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6234152).length < 2 ^ (prefixWord ++ tailWord_6234152).sum := by decide
  have hdescent : baseEnd_6234152 < baseStart_6234152 := by decide
  rcases family_descends (prefixWord ++ tailWord_6234152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
