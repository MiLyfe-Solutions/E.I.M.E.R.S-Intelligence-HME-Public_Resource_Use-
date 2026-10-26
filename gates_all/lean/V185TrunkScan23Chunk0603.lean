import V185TrunkScan23Chunk0602

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_3566159 : List Nat := [1, 1, 2, 1, 1, 2, 5, 2, 2, 1, 5]
def baseStart_3566159 : Nat := 118140960795 + 3566159 * 2 ^ 59
def prefixEnd_3566159 : Nat := 4983230072969 + 3 ^ 40 * 3566159 * 2
def baseEnd_3566159 : Nat := 1831153657357218120212039

theorem tailTrace_3566159 : CollatzResearch.WordTrace tailWord_3566159 prefixEnd_3566159 1831153657357218120212039 := by
  unfold tailWord_3566159
  simp only [CollatzResearch.WordTrace]
  refine ⟨130068504287422469313245531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86712336191614979542163687 130068504287422469313245531)
  ·
    refine ⟨195102756431133703969868297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130068504287422469313245531 195102756431133703969868297)
    ·
      refine ⟨146327067323350277977401223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 195102756431133703969868297 146327067323350277977401223)
      ·
        refine ⟨219490600985025416966101835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146327067323350277977401223 219490600985025416966101835)
        ·
          refine ⟨329235901477538125449152753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 219490600985025416966101835 329235901477538125449152753)
          ·
            refine ⟨246926926108153594086864565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 329235901477538125449152753 246926926108153594086864565)
            ·
              refine ⟨23149399322639399445643553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 246926926108153594086864565 23149399322639399445643553)
              ·
                refine ⟨17362049491979549584232665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23149399322639399445643553 17362049491979549584232665)
                ·
                  refine ⟨13021537118984662188174499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17362049491979549584232665 13021537118984662188174499)
                  ·
                    refine ⟨19532305678476993282261749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13021537118984662188174499 19532305678476993282261749)
                    ·
                      refine ⟨1831153657357218120212039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19532305678476993282261749 1831153657357218120212039)
                      ·
                        rfl

theorem cell23_3566159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 5, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 5, 2, 2, 1, 5].length) (baseStart_3566159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3566159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3566159 prefixEnd_3566159 := by exact prefixLift 3566159
  have htrace : WordTrace (prefixWord ++ tailWord_3566159) baseStart_3566159 baseEnd_3566159 := by
    simpa [prefixWord, tailWord_3566159, baseEnd_3566159] using wordTrace_append hprefix tailTrace_3566159
  have hstable : (prefixWord ++ tailWord_3566159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3566159).length < 2 ^ (prefixWord ++ tailWord_3566159).sum := by decide
  have hdescent : baseEnd_3566159 < baseStart_3566159 := by decide
  rcases family_descends (prefixWord ++ tailWord_3566159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3566169 : List Nat := [1, 2, 1, 2, 2, 1, 1, 1, 6, 2, 4]
def baseStart_3566169 : Nat := 118140960795 + 3566169 * 2 ^ 59
def prefixEnd_3566169 : Nat := 4983230072969 + 3 ^ 40 * 3566169 * 2
def baseEnd_3566169 : Nat := 1831158792163763081086993

theorem tailTrace_3566169 : CollatzResearch.WordTrace tailWord_3566169 prefixEnd_3566169 1831158792163763081086993 := by
  unfold tailWord_3566169
  simp only [CollatzResearch.WordTrace]
  refine ⟨130068869017386241021109561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86712579344924160680739707 130068869017386241021109561)
  ·
    refine ⟨97551651763039680765832171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130068869017386241021109561 97551651763039680765832171)
    ·
      refine ⟨146327477644559521148748257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97551651763039680765832171 146327477644559521148748257)
      ·
        refine ⟨109745608233419640861561193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146327477644559521148748257 109745608233419640861561193)
        ·
          refine ⟨82309206175064730646170895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109745608233419640861561193 82309206175064730646170895)
          ·
            refine ⟨123463809262597095969256343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82309206175064730646170895 123463809262597095969256343)
            ·
              refine ⟨185195713893895643953884515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 123463809262597095969256343 185195713893895643953884515)
              ·
                refine ⟨277793570840843465930826773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 185195713893895643953884515 277793570840843465930826773)
                ·
                  refine ⟨13021573633164537465507505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 277793570840843465930826773 13021573633164537465507505)
                  ·
                    refine ⟨9766180224873403099130629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13021573633164537465507505 9766180224873403099130629)
                    ·
                      refine ⟨1831158792163763081086993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9766180224873403099130629 1831158792163763081086993)
                      ·
                        rfl

theorem cell23_3566169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 1, 6, 2, 4].length) (baseStart_3566169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3566169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3566169 prefixEnd_3566169 := by exact prefixLift 3566169
  have htrace : WordTrace (prefixWord ++ tailWord_3566169) baseStart_3566169 baseEnd_3566169 := by
    simpa [prefixWord, tailWord_3566169, baseEnd_3566169] using wordTrace_append hprefix tailTrace_3566169
  have hstable : (prefixWord ++ tailWord_3566169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3566169).length < 2 ^ (prefixWord ++ tailWord_3566169).sum := by decide
  have hdescent : baseEnd_3566169 < baseStart_3566169 := by decide
  rcases family_descends (prefixWord ++ tailWord_3566169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3566186 : List Nat := [3, 1, 3, 2, 1, 1, 2, 2, 2, 2, 4]
def baseStart_3566186 : Nat := 118140960795 + 3566186 * 2 ^ 59
def prefixEnd_3566186 : Nat := 4983230072969 + 3 ^ 40 * 3566186 * 2
def baseEnd_3566186 : Nat := 1831167521334889514574415

theorem tailTrace_3566186 : CollatzResearch.WordTrace tailWord_3566186 prefixEnd_3566186 1831167521334889514574415 := by
  unfold tailWord_3566186
  simp only [CollatzResearch.WordTrace]
  refine ⟨32517372264581163231119603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86712992705549768616318941 32517372264581163231119603)
  ·
    refine ⟨48776058396871744846679405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32517372264581163231119603 48776058396871744846679405)
    ·
      refine ⟨18291021898826904317504777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48776058396871744846679405 18291021898826904317504777)
      ·
        refine ⟨13718266424120178238128583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18291021898826904317504777 13718266424120178238128583)
        ·
          refine ⟨20577399636180267357192875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13718266424120178238128583 20577399636180267357192875)
          ·
            refine ⟨30866099454270401035789313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20577399636180267357192875 30866099454270401035789313)
            ·
              refine ⟨23149574590702800776841985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30866099454270401035789313 23149574590702800776841985)
              ·
                refine ⟨17362180943027100582631489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23149574590702800776841985 17362180943027100582631489)
                ·
                  refine ⟨13021635707270325436973617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17362180943027100582631489 13021635707270325436973617)
                  ·
                    refine ⟨9766226780452744077730213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13021635707270325436973617 9766226780452744077730213)
                    ·
                      refine ⟨1831167521334889514574415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9766226780452744077730213 1831167521334889514574415)
                      ·
                        rfl

theorem cell23_3566186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 2, 2, 2, 2, 4].length) (baseStart_3566186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3566186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3566186 prefixEnd_3566186 := by exact prefixLift 3566186
  have htrace : WordTrace (prefixWord ++ tailWord_3566186) baseStart_3566186 baseEnd_3566186 := by
    simpa [prefixWord, tailWord_3566186, baseEnd_3566186] using wordTrace_append hprefix tailTrace_3566186
  have hstable : (prefixWord ++ tailWord_3566186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3566186).length < 2 ^ (prefixWord ++ tailWord_3566186).sum := by decide
  have hdescent : baseEnd_3566186 < baseStart_3566186 := by decide
  rcases family_descends (prefixWord ++ tailWord_3566186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3566219 : List Nat := [1, 1, 1, 1, 4, 1, 2, 2, 3, 2, 5]
def baseStart_3566219 : Nat := 118140960795 + 3566219 * 2 ^ 59
def prefixEnd_3566219 : Nat := 4983230072969 + 3 ^ 40 * 3566219 * 2
def baseEnd_3566219 : Nat := 1831184466196487885461763

theorem tailTrace_3566219 : CollatzResearch.WordTrace tailWord_3566219 prefixEnd_3566219 1831184466196487885461763 := by
  unfold tailWord_3566219
  simp only [CollatzResearch.WordTrace]
  refine ⟨130070692667205099560429711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86713795111470066373619807 130070692667205099560429711)
  ·
    refine ⟨195106039000807649340644567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130070692667205099560429711 195106039000807649340644567)
    ·
      refine ⟨292659058501211474010966851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195106039000807649340644567 292659058501211474010966851)
      ·
        refine ⟨438988587751817211016450277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 292659058501211474010966851 438988587751817211016450277)
        ·
          refine ⟨82310360203465727065584427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 438988587751817211016450277 82310360203465727065584427)
          ·
            refine ⟨123465540305198590598376641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82310360203465727065584427 123465540305198590598376641)
            ·
              refine ⟨92599155228898942948782481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 123465540305198590598376641 92599155228898942948782481)
              ·
                refine ⟨69449366421674207211586861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 92599155228898942948782481 69449366421674207211586861)
                ·
                  refine ⟨26043512408127827704345073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 69449366421674207211586861 26043512408127827704345073)
                  ·
                    refine ⟨19532634306095870778258805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26043512408127827704345073 19532634306095870778258805)
                    ·
                      refine ⟨1831184466196487885461763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19532634306095870778258805 1831184466196487885461763)
                      ·
                        rfl

theorem cell23_3566219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 2, 3, 2, 5].length) (baseStart_3566219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3566219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3566219 prefixEnd_3566219 := by exact prefixLift 3566219
  have htrace : WordTrace (prefixWord ++ tailWord_3566219) baseStart_3566219 baseEnd_3566219 := by
    simpa [prefixWord, tailWord_3566219, baseEnd_3566219] using wordTrace_append hprefix tailTrace_3566219
  have hstable : (prefixWord ++ tailWord_3566219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3566219).length < 2 ^ (prefixWord ++ tailWord_3566219).sum := by decide
  have hdescent : baseEnd_3566219 < baseStart_3566219 := by decide
  rcases family_descends (prefixWord ++ tailWord_3566219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3566249 : List Nat := [1, 2, 1, 1, 1, 1, 2, 3, 1, 5, 5]
def baseStart_3566249 : Nat := 118140960795 + 3566249 * 2 ^ 59
def prefixEnd_3566249 : Nat := 4983230072969 + 3 ^ 40 * 3566249 * 2
def baseEnd_3566249 : Nat := 1831199870616122768086625

theorem tailTrace_3566249 : CollatzResearch.WordTrace tailWord_3566249 prefixEnd_3566249 1831199870616122768086625 := by
  unfold tailWord_3566249
  simp only [CollatzResearch.WordTrace]
  refine ⟨130071786857096414684021801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86714524571397609789347867 130071786857096414684021801)
  ·
    refine ⟨97553840142822311013016351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130071786857096414684021801 97553840142822311013016351)
    ·
      refine ⟨146330760214233466519524527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97553840142822311013016351 146330760214233466519524527)
      ·
        refine ⟨219496140321350199779286791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146330760214233466519524527 219496140321350199779286791)
        ·
          refine ⟨329244210482025299668930187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 219496140321350199779286791 329244210482025299668930187)
          ·
            refine ⟨493866315723037949503395281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 329244210482025299668930187 493866315723037949503395281)
            ·
              refine ⟨370399736792278462127546461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 493866315723037949503395281 370399736792278462127546461)
              ·
                refine ⟨138899901297104423297829923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 370399736792278462127546461 138899901297104423297829923)
                ·
                  refine ⟨208349851945656634946744885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 138899901297104423297829923 208349851945656634946744885)
                  ·
                    refine ⟨19532798619905309526257333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 208349851945656634946744885 19532798619905309526257333)
                    ·
                      refine ⟨1831199870616122768086625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19532798619905309526257333 1831199870616122768086625)
                      ·
                        rfl

theorem cell23_3566249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 3, 1, 5, 5].length) (baseStart_3566249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3566249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3566249 prefixEnd_3566249 := by exact prefixLift 3566249
  have htrace : WordTrace (prefixWord ++ tailWord_3566249) baseStart_3566249 baseEnd_3566249 := by
    simpa [prefixWord, tailWord_3566249, baseEnd_3566249] using wordTrace_append hprefix tailTrace_3566249
  have hstable : (prefixWord ++ tailWord_3566249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3566249).length < 2 ^ (prefixWord ++ tailWord_3566249).sum := by decide
  have hdescent : baseEnd_3566249 < baseStart_3566249 := by decide
  rcases family_descends (prefixWord ++ tailWord_3566249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3566266 : List Nat := [3, 1, 1, 1, 2, 3, 1, 1, 3, 4, 3]
def baseStart_3566266 : Nat := 118140960795 + 3566266 * 2 ^ 59
def prefixEnd_3566266 : Nat := 4983230072969 + 3 ^ 40 * 3566266 * 2
def baseEnd_3566266 : Nat := 1831208599787249201574047

theorem tailTrace_3566266 : CollatzResearch.WordTrace tailWord_3566266 prefixEnd_3566266 1831208599787249201574047 := by
  unfold tailWord_3566266
  simp only [CollatzResearch.WordTrace]
  refine ⟨32518101724508706646847663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86714937932023217724927101 32518101724508706646847663)
  ·
    refine ⟨48777152586763059970271495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32518101724508706646847663 48777152586763059970271495)
    ·
      refine ⟨73165728880144589955407243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48777152586763059970271495 73165728880144589955407243)
      ·
        refine ⟨109748593320216884933110865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73165728880144589955407243 109748593320216884933110865)
        ·
          refine ⟨82311444990162663699833149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109748593320216884933110865 82311444990162663699833149)
          ·
            refine ⟨30866791871310998887437431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 82311444990162663699833149 30866791871310998887437431)
            ·
              refine ⟨46300187806966498331156147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30866791871310998887437431 46300187806966498331156147)
              ·
                refine ⟨69450281710449747496734221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46300187806966498331156147 69450281710449747496734221)
                ·
                  refine ⟨26043855641418655311275333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 69450281710449747496734221 26043855641418655311275333)
                  ·
                    refine ⟨4883222932765997870864125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26043855641418655311275333 4883222932765997870864125)
                    ·
                      refine ⟨1831208599787249201574047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4883222932765997870864125 1831208599787249201574047)
                      ·
                        rfl

theorem cell23_3566266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 1, 3, 4, 3].length) (baseStart_3566266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3566266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3566266 prefixEnd_3566266 := by exact prefixLift 3566266
  have htrace : WordTrace (prefixWord ++ tailWord_3566266) baseStart_3566266 baseEnd_3566266 := by
    simpa [prefixWord, tailWord_3566266, baseEnd_3566266] using wordTrace_append hprefix tailTrace_3566266
  have hstable : (prefixWord ++ tailWord_3566266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3566266).length < 2 ^ (prefixWord ++ tailWord_3566266).sum := by decide
  have hdescent : baseEnd_3566266 < baseStart_3566266 := by decide
  rcases family_descends (prefixWord ++ tailWord_3566266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3566286 : List Nat := [4, 1, 1, 1, 3, 2, 1, 2, 8]
def baseStart_3566286 : Nat := 118140960795 + 3566286 * 2 ^ 59
def prefixEnd_3566286 : Nat := 4983230072969 + 3 ^ 40 * 3566286 * 2
def baseEnd_3566286 : Nat := 203468763266704347035995

theorem tailTrace_3566286 : CollatzResearch.WordTrace tailWord_3566286 prefixEnd_3566286 203468763266704347035995 := by
  unfold tailWord_3566286
  simp only [CollatzResearch.WordTrace]
  refine ⟨16259142044745296250389839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 86715424238641580002079141 16259142044745296250389839)
  ·
    refine ⟨24388713067117944375584759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16259142044745296250389839 24388713067117944375584759)
    ·
      refine ⟨36583069600676916563377139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24388713067117944375584759 36583069600676916563377139)
      ·
        refine ⟨54874604401015374845065709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36583069600676916563377139 54874604401015374845065709)
        ·
          refine ⟨20577976650380765566899641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54874604401015374845065709 20577976650380765566899641)
          ·
            refine ⟨15433482487785574175174731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20577976650380765566899641 15433482487785574175174731)
            ·
              refine ⟨23150223731678361262762097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15433482487785574175174731 23150223731678361262762097)
              ·
                refine ⟨17362667798758770947071573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23150223731678361262762097 17362667798758770947071573)
                ·
                  refine ⟨203468763266704347035995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 17362667798758770947071573 203468763266704347035995)
                  ·
                    rfl

theorem cell23_3566286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 1, 2, 8].length) (baseStart_3566286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3566286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3566286 prefixEnd_3566286 := by exact prefixLift 3566286
  have htrace : WordTrace (prefixWord ++ tailWord_3566286) baseStart_3566286 baseEnd_3566286 := by
    simpa [prefixWord, tailWord_3566286, baseEnd_3566286] using wordTrace_append hprefix tailTrace_3566286
  have hstable : (prefixWord ++ tailWord_3566286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3566286).length < 2 ^ (prefixWord ++ tailWord_3566286).sum := by decide
  have hdescent : baseEnd_3566286 < baseStart_3566286 := by decide
  rcases family_descends (prefixWord ++ tailWord_3566286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3566300 : List Nat := [2, 2, 5, 1, 1, 1, 1, 1, 4, 2, 3]
def baseStart_3566300 : Nat := 118140960795 + 3566300 * 2 ^ 59
def prefixEnd_3566300 : Nat := 4983230072969 + 3 ^ 40 * 3566300 * 2
def baseEnd_3566300 : Nat := 1831226058129502068548891

theorem tailTrace_3566300 : CollatzResearch.WordTrace tailWord_3566300 prefixEnd_3566300 1831226058129502068548891 := by
  unfold tailWord_3566300
  simp only [CollatzResearch.WordTrace]
  refine ⟨65036823489955825197064177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86715764653274433596085569 65036823489955825197064177)
  ·
    refine ⟨48777617617466868897798133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65036823489955825197064177 48777617617466868897798133)
    ·
      refine ⟨4572901651637518959168575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 48777617617466868897798133 4572901651637518959168575)
      ·
        refine ⟨6859352477456278438752863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4572901651637518959168575 6859352477456278438752863)
        ·
          refine ⟨10289028716184417658129295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6859352477456278438752863 10289028716184417658129295)
          ·
            refine ⟨15433543074276626487193943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10289028716184417658129295 15433543074276626487193943)
            ·
              refine ⟨23150314611414939730790915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15433543074276626487193943 23150314611414939730790915)
              ·
                refine ⟨34725471917122409596186373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23150314611414939730790915 34725471917122409596186373)
                ·
                  refine ⟨6511025984460451799284945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34725471917122409596186373 6511025984460451799284945)
                  ·
                    refine ⟨4883269488345338849463709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6511025984460451799284945 4883269488345338849463709)
                    ·
                      refine ⟨1831226058129502068548891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4883269488345338849463709 1831226058129502068548891)
                      ·
                        rfl

theorem cell23_3566300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 1, 1, 4, 2, 3].length) (baseStart_3566300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3566300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3566300 prefixEnd_3566300 := by exact prefixLift 3566300
  have htrace : WordTrace (prefixWord ++ tailWord_3566300) baseStart_3566300 baseEnd_3566300 := by
    simpa [prefixWord, tailWord_3566300, baseEnd_3566300] using wordTrace_append hprefix tailTrace_3566300
  have hstable : (prefixWord ++ tailWord_3566300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3566300).length < 2 ^ (prefixWord ++ tailWord_3566300).sum := by decide
  have hdescent : baseEnd_3566300 < baseStart_3566300 := by decide
  rcases family_descends (prefixWord ++ tailWord_3566300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3566316 : List Nat := [2, 2, 1, 1, 2, 2, 1, 4, 3, 5]
def baseStart_3566316 : Nat := 118140960795 + 3566316 * 2 ^ 59
def prefixEnd_3566316 : Nat := 4983230072969 + 3 ^ 40 * 3566316 * 2
def baseEnd_3566316 : Nat := 610411424606658001982939

theorem tailTrace_3566316 : CollatzResearch.WordTrace tailWord_3566316 prefixEnd_3566316 610411424606658001982939 := by
  unfold tailWord_3566316
  simp only [CollatzResearch.WordTrace]
  refine ⟨65037115273926842563355401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86716153698569123417807201 65037115273926842563355401)
  ·
    refine ⟨48777836455445131922516551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65037115273926842563355401 48777836455445131922516551)
    ·
      refine ⟨73166754683167697883774827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48777836455445131922516551 73166754683167697883774827)
      ·
        refine ⟨109750132024751546825662241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73166754683167697883774827 109750132024751546825662241)
        ·
          refine ⟨82312599018563660119246681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109750132024751546825662241 82312599018563660119246681)
          ·
            refine ⟨61734449263922745089435011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82312599018563660119246681 61734449263922745089435011)
            ·
              refine ⟨92601673895884117634152517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61734449263922745089435011 92601673895884117634152517)
              ·
                refine ⟨17362813855478272056403597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 92601673895884117634152517 17362813855478272056403597)
                ·
                  refine ⟨6511055195804352021151349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17362813855478272056403597 6511055195804352021151349)
                  ·
                    refine ⟨610411424606658001982939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6511055195804352021151349 610411424606658001982939)
                    ·
                      rfl

theorem cell23_3566316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 5].length) (baseStart_3566316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3566316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3566316 prefixEnd_3566316 := by exact prefixLift 3566316
  have htrace : WordTrace (prefixWord ++ tailWord_3566316) baseStart_3566316 baseEnd_3566316 := by
    simpa [prefixWord, tailWord_3566316, baseEnd_3566316] using wordTrace_append hprefix tailTrace_3566316
  have hstable : (prefixWord ++ tailWord_3566316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3566316).length < 2 ^ (prefixWord ++ tailWord_3566316).sum := by decide
  have hdescent : baseEnd_3566316 < baseStart_3566316 := by decide
  rcases family_descends (prefixWord ++ tailWord_3566316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3566323 : List Nat := [1, 1, 1, 2, 2, 3, 1, 1, 6, 3, 2]
def baseStart_3566323 : Nat := 118140960795 + 3566323 * 2 ^ 59
def prefixEnd_3566323 : Nat := 4983230072969 + 3 ^ 40 * 3566323 * 2
def baseEnd_3566323 : Nat := 1831237868184555478561285

theorem tailTrace_3566323 : CollatzResearch.WordTrace tailWord_3566323 prefixEnd_3566323 1831237868184555478561285 := by
  unfold tailWord_3566323
  simp only [CollatzResearch.WordTrace]
  refine ⟨130074485858828325322215623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86716323905885550214810415 130074485858828325322215623)
  ·
    refine ⟨195111728788242487983323435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130074485858828325322215623 195111728788242487983323435)
    ·
      refine ⟨292667593182363731974985153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195111728788242487983323435 292667593182363731974985153)
      ·
        refine ⟨219500694886772798981238865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 292667593182363731974985153 219500694886772798981238865)
        ·
          refine ⟨164625521165079599235929149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 219500694886772798981238865 164625521165079599235929149)
          ·
            refine ⟨61734570436904849713473431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 164625521165079599235929149 61734570436904849713473431)
            ·
              refine ⟨92601855655357274570210147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61734570436904849713473431 92601855655357274570210147)
              ·
                refine ⟨138902783483035911855315221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92601855655357274570210147 138902783483035911855315221)
                ·
                  refine ⟨6511067975767308368217901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 138902783483035911855315221 6511067975767308368217901)
                  ·
                    refine ⟨2441650490912740638081713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6511067975767308368217901 2441650490912740638081713)
                    ·
                      refine ⟨1831237868184555478561285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2441650490912740638081713 1831237868184555478561285)
                      ·
                        rfl

theorem cell23_3566323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 1, 6, 3, 2].length) (baseStart_3566323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3566323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3566323 prefixEnd_3566323 := by exact prefixLift 3566323
  have htrace : WordTrace (prefixWord ++ tailWord_3566323) baseStart_3566323 baseEnd_3566323 := by
    simpa [prefixWord, tailWord_3566323, baseEnd_3566323] using wordTrace_append hprefix tailTrace_3566323
  have hstable : (prefixWord ++ tailWord_3566323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3566323).length < 2 ^ (prefixWord ++ tailWord_3566323).sum := by decide
  have hdescent : baseEnd_3566323 < baseStart_3566323 := by decide
  rcases family_descends (prefixWord ++ tailWord_3566323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3566353 : List Nat := [1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 4]
def baseStart_3566353 : Nat := 118140960795 + 3566353 * 2 ^ 59
def prefixEnd_3566353 : Nat := 4983230072969 + 3 ^ 40 * 3566353 * 2
def baseEnd_3566353 : Nat := 1831253272604190361186147

theorem tailTrace_3566353 : CollatzResearch.WordTrace tailWord_3566353 prefixEnd_3566353 1831253272604190361186147 := by
  unfold tailWord_3566353
  simp only [CollatzResearch.WordTrace]
  refine ⟨130075580048719640445807713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86717053365813093630538475 130075580048719640445807713)
  ·
    refine ⟨97556685036539730334355785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130075580048719640445807713 97556685036539730334355785)
    ·
      refine ⟨73167513777404797750766839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97556685036539730334355785 73167513777404797750766839)
      ·
        refine ⟨109751270666107196626150259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73167513777404797750766839 109751270666107196626150259)
        ·
          refine ⟨164626905999160794939225389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109751270666107196626150259 164626905999160794939225389)
          ·
            refine ⟨61735089749685298102209521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 164626905999160794939225389 61735089749685298102209521)
            ·
              refine ⟨46301317312263973576657141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61735089749685298102209521 46301317312263973576657141)
              ·
                refine ⟨4340748498024747522811607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 46301317312263973576657141 4340748498024747522811607)
                ·
                  refine ⟨6511122747037121284217411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4340748498024747522811607 6511122747037121284217411)
                  ·
                    refine ⟨9766684120555681926326117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6511122747037121284217411 9766684120555681926326117)
                    ·
                      refine ⟨1831253272604190361186147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9766684120555681926326117 1831253272604190361186147)
                      ·
                        rfl

theorem cell23_3566353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 4].length) (baseStart_3566353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3566353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3566353 prefixEnd_3566353 := by exact prefixLift 3566353
  have htrace : WordTrace (prefixWord ++ tailWord_3566353) baseStart_3566353 baseEnd_3566353 := by
    simpa [prefixWord, tailWord_3566353, baseEnd_3566353] using wordTrace_append hprefix tailTrace_3566353
  have hstable : (prefixWord ++ tailWord_3566353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3566353).length < 2 ^ (prefixWord ++ tailWord_3566353).sum := by decide
  have hdescent : baseEnd_3566353 < baseStart_3566353 := by decide
  rcases family_descends (prefixWord ++ tailWord_3566353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3566364 : List Nat := [2, 2, 3, 1, 1, 3, 4, 2, 1, 1, 3]
def baseStart_3566364 : Nat := 118140960795 + 3566364 * 2 ^ 59
def prefixEnd_3566364 : Nat := 4983230072969 + 3 ^ 40 * 3566364 * 2
def baseEnd_3566364 : Nat := 1831258920891389818148597

theorem tailTrace_3566364 : CollatzResearch.WordTrace tailWord_3566364 prefixEnd_3566364 1831258920891389818148597 := by
  unfold tailWord_3566364
  simp only [CollatzResearch.WordTrace]
  refine ⟨65037990625839894662229073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86717320834453192882972097 65037990625839894662229073)
  ·
    refine ⟨48778492969379920996671805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65037990625839894662229073 48778492969379920996671805)
    ·
      refine ⟨18291934863517470373751927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48778492969379920996671805 18291934863517470373751927)
      ·
        refine ⟨27437902295276205560627891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18291934863517470373751927 27437902295276205560627891)
        ·
          refine ⟨41156853442914308340941837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27437902295276205560627891 41156853442914308340941837)
          ·
            refine ⟨15433820041092865627853189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41156853442914308340941837 15433820041092865627853189)
            ·
              refine ⟨2893841257704912305222473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15433820041092865627853189 2893841257704912305222473)
              ·
                refine ⟨2170380943278684228916855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2893841257704912305222473 2170380943278684228916855)
                ·
                  refine ⟨3255571414918026343375283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2170380943278684228916855 3255571414918026343375283)
                  ·
                    refine ⟨4883357122377039515062925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3255571414918026343375283 4883357122377039515062925)
                    ·
                      refine ⟨1831258920891389818148597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4883357122377039515062925 1831258920891389818148597)
                      ·
                        rfl

theorem cell23_3566364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 4, 2, 1, 1, 3].length) (baseStart_3566364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3566364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3566364 prefixEnd_3566364 := by exact prefixLift 3566364
  have htrace : WordTrace (prefixWord ++ tailWord_3566364) baseStart_3566364 baseEnd_3566364 := by
    simpa [prefixWord, tailWord_3566364, baseEnd_3566364] using wordTrace_append hprefix tailTrace_3566364
  have hstable : (prefixWord ++ tailWord_3566364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3566364).length < 2 ^ (prefixWord ++ tailWord_3566364).sum := by decide
  have hdescent : baseEnd_3566364 < baseStart_3566364 := by decide
  rcases family_descends (prefixWord ++ tailWord_3566364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3566373 : List Nat := [1, 3, 1, 2, 3, 1, 1, 1, 5, 2, 3]
def baseStart_3566373 : Nat := 118140960795 + 3566373 * 2 ^ 59
def prefixEnd_3566373 : Nat := 4983230072969 + 3 ^ 40 * 3566373 * 2
def baseEnd_3566373 : Nat := 1831263542217280282936055

theorem tailTrace_3566373 : CollatzResearch.WordTrace tailWord_3566373 prefixEnd_3566373 1831263542217280282936055 := by
  unfold tailWord_3566373
  simp only [CollatzResearch.WordTrace]
  refine ⟨130076309508647183861535773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86717539672431455907690515 130076309508647183861535773)
  ·
    refine ⟨48778616065742693948075915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130076309508647183861535773 48778616065742693948075915)
    ·
      refine ⟨73167924098614040922113873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48778616065742693948075915 73167924098614040922113873)
      ·
        refine ⟨54875943073960530691585405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73167924098614040922113873 54875943073960530691585405)
        ·
          refine ⟨20578478652735199009344527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54875943073960530691585405 20578478652735199009344527)
          ·
            refine ⟨30867717979102798514016791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20578478652735199009344527 30867717979102798514016791)
            ·
              refine ⟨46301576968654197771025187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30867717979102798514016791 46301576968654197771025187)
              ·
                refine ⟨69452365452981296656537781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46301576968654197771025187 69452365452981296656537781)
                ·
                  refine ⟨6511159261216996561550417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 69452365452981296656537781 6511159261216996561550417)
                  ·
                    refine ⟨4883369445912747421162813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6511159261216996561550417 4883369445912747421162813)
                    ·
                      refine ⟨1831263542217280282936055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4883369445912747421162813 1831263542217280282936055)
                      ·
                        rfl

theorem cell23_3566373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 1, 5, 2, 3].length) (baseStart_3566373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3566373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3566373 prefixEnd_3566373 := by exact prefixLift 3566373
  have htrace : WordTrace (prefixWord ++ tailWord_3566373) baseStart_3566373 baseEnd_3566373 := by
    simpa [prefixWord, tailWord_3566373, baseEnd_3566373] using wordTrace_append hprefix tailTrace_3566373
  have hstable : (prefixWord ++ tailWord_3566373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3566373).length < 2 ^ (prefixWord ++ tailWord_3566373).sum := by decide
  have hdescent : baseEnd_3566373 < baseStart_3566373 := by decide
  rcases family_descends (prefixWord ++ tailWord_3566373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3566387 : List Nat := [1, 1, 1, 2, 6, 2, 1, 2, 3, 2, 2]
def baseStart_3566387 : Nat := 118140960795 + 3566387 * 2 ^ 59
def prefixEnd_3566387 : Nat := 4983230072969 + 3 ^ 40 * 3566387 * 2
def baseEnd_3566387 : Nat := 1831270730946443228160991

theorem tailTrace_3566387 : CollatzResearch.WordTrace tailWord_3566387 prefixEnd_3566387 1831270730946443228160991 := by
  unfold tailWord_3566387
  simp only [CollatzResearch.WordTrace]
  refine ⟨130076820130596464252545415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86717880087064309501696943 130076820130596464252545415)
  ·
    refine ⟨195115230195894696378818123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130076820130596464252545415 195115230195894696378818123)
    ·
      refine ⟨292672845293842044568227185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195115230195894696378818123 292672845293842044568227185)
      ·
        refine ⟨219504633970381533426170389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 292672845293842044568227185 219504633970381533426170389)
        ·
          refine ⟨10289279717361634379351737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 219504633970381533426170389 10289279717361634379351737)
          ·
            refine ⟨7716959788021225784513803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10289279717361634379351737 7716959788021225784513803)
            ·
              refine ⟨11575439682031838676770705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7716959788021225784513803 11575439682031838676770705)
              ·
                refine ⟨8681579761523879007578029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11575439682031838676770705 8681579761523879007578029)
                ·
                  refine ⟨3255592410571454627841761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8681579761523879007578029 3255592410571454627841761)
                  ·
                    refine ⟨2441694307928590970881321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3255592410571454627841761 2441694307928590970881321)
                    ·
                      refine ⟨1831270730946443228160991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2441694307928590970881321 1831270730946443228160991)
                      ·
                        rfl

theorem cell23_3566387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 1, 2, 3, 2, 2].length) (baseStart_3566387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3566387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3566387 prefixEnd_3566387 := by exact prefixLift 3566387
  have htrace : WordTrace (prefixWord ++ tailWord_3566387) baseStart_3566387 baseEnd_3566387 := by
    simpa [prefixWord, tailWord_3566387, baseEnd_3566387] using wordTrace_append hprefix tailTrace_3566387
  have hstable : (prefixWord ++ tailWord_3566387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3566387).length < 2 ^ (prefixWord ++ tailWord_3566387).sum := by decide
  have hdescent : baseEnd_3566387 < baseStart_3566387 := by decide
  rcases family_descends (prefixWord ++ tailWord_3566387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3566401 : List Nat := [1, 2, 5, 3, 2, 1, 2, 1, 1, 5]
def baseStart_3566401 : Nat := 118140960795 + 3566401 * 2 ^ 59
def prefixEnd_3566401 : Nat := 4983230072969 + 3 ^ 40 * 3566401 * 2
def baseEnd_3566401 : Nat := 610425973225202057795309

theorem tailTrace_3566401 : CollatzResearch.WordTrace tailWord_3566401 prefixEnd_3566401 610425973225202057795309 := by
  unfold tailWord_3566401
  simp only [CollatzResearch.WordTrace]
  refine ⟨130077330752545744643555057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86718220501697163095703371 130077330752545744643555057)
  ·
    refine ⟨97557998064409308482666293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130077330752545744643555057 97557998064409308482666293)
    ·
      refine ⟨9146062318538372670249965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 97557998064409308482666293 9146062318538372670249965)
      ·
        refine ⟨3429773369451889751343737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9146062318538372670249965 3429773369451889751343737)
        ·
          refine ⟨2572330027088917313507803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3429773369451889751343737 2572330027088917313507803)
          ·
            refine ⟨3858495040633375970261705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2572330027088917313507803 3858495040633375970261705)
            ·
              refine ⟨2893871280475031977696279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3858495040633375970261705 2893871280475031977696279)
              ·
                refine ⟨4340806920712547966544419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2893871280475031977696279 4340806920712547966544419)
                ·
                  refine ⟨6511210381068821949816629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4340806920712547966544419 6511210381068821949816629)
                  ·
                    refine ⟨610425973225202057795309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6511210381068821949816629 610425973225202057795309)
                    ·
                      rfl

theorem cell23_3566401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 2, 1, 2, 1, 1, 5].length) (baseStart_3566401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3566401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3566401 prefixEnd_3566401 := by exact prefixLift 3566401
  have htrace : WordTrace (prefixWord ++ tailWord_3566401) baseStart_3566401 baseEnd_3566401 := by
    simpa [prefixWord, tailWord_3566401, baseEnd_3566401] using wordTrace_append hprefix tailTrace_3566401
  have hstable : (prefixWord ++ tailWord_3566401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3566401).length < 2 ^ (prefixWord ++ tailWord_3566401).sum := by decide
  have hdescent : baseEnd_3566401 < baseStart_3566401 := by decide
  rcases family_descends (prefixWord ++ tailWord_3566401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3566403 : List Nat := [1, 1, 1, 3, 1, 4, 1, 4, 1, 3, 3]
def baseStart_3566403 : Nat := 118140960795 + 3566403 * 2 ^ 59
def prefixEnd_3566403 : Nat := 4983230072969 + 3 ^ 40 * 3566403 * 2
def baseEnd_3566403 : Nat := 1831278946636915165560917

theorem tailTrace_3566403 : CollatzResearch.WordTrace tailWord_3566403 prefixEnd_3566403 1831278946636915165560917 := by
  unfold tailWord_3566403
  simp only [CollatzResearch.WordTrace]
  refine ⟨130077403698538498985127863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86718269132358999323418575 130077403698538498985127863)
  ·
    refine ⟨195116105547807748477691795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130077403698538498985127863 195116105547807748477691795)
    ·
      refine ⟨292674158321711622716537693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195116105547807748477691795 292674158321711622716537693)
      ·
        refine ⟨109752809370641858518701635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 292674158321711622716537693 109752809370641858518701635)
        ·
          refine ⟨164629214055962787778052453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109752809370641858518701635 164629214055962787778052453)
          ·
            refine ⟨30867977635493022708384835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 164629214055962787778052453 30867977635493022708384835)
            ·
              refine ⟨46301966453239534062577253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30867977635493022708384835 46301966453239534062577253)
              ·
                refine ⟨8681618709982412636733235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46301966453239534062577253 8681618709982412636733235)
                ·
                  refine ⟨13022428064973618955099853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8681618709982412636733235 13022428064973618955099853)
                  ·
                    refine ⟨4883410524365107108162445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13022428064973618955099853 4883410524365107108162445)
                    ·
                      refine ⟨1831278946636915165560917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4883410524365107108162445 1831278946636915165560917)
                      ·
                        rfl

theorem cell23_3566403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 4, 1, 3, 3].length) (baseStart_3566403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3566403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3566403 prefixEnd_3566403 := by exact prefixLift 3566403
  have htrace : WordTrace (prefixWord ++ tailWord_3566403) baseStart_3566403 baseEnd_3566403 := by
    simpa [prefixWord, tailWord_3566403, baseEnd_3566403] using wordTrace_append hprefix tailTrace_3566403
  have hstable : (prefixWord ++ tailWord_3566403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3566403).length < 2 ^ (prefixWord ++ tailWord_3566403).sum := by decide
  have hdescent : baseEnd_3566403 < baseStart_3566403 := by decide
  rcases family_descends (prefixWord ++ tailWord_3566403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3566404 : List Nat := [2, 3, 4, 2, 1, 1, 1, 3, 1, 1, 4]
def baseStart_3566404 : Nat := 118140960795 + 3566404 * 2 ^ 59
def prefixEnd_3566404 : Nat := 4983230072969 + 3 ^ 40 * 3566404 * 2
def baseEnd_3566404 : Nat := 1831279460117569661648413

theorem tailTrace_3566404 : CollatzResearch.WordTrace tailWord_3566404 prefixEnd_3566404 1831279460117569661648413 := by
  unfold tailWord_3566404
  simp only [CollatzResearch.WordTrace]
  refine ⟨65038720085767438077957133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86718293447689917437276177 65038720085767438077957133)
  ·
    refine ⟨24389520032162789279233925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65038720085767438077957133 24389520032162789279233925)
    ·
      refine ⟨4573035006030522989856361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24389520032162789279233925 4573035006030522989856361)
      ·
        refine ⟨3429776254522892242392271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4573035006030522989856361 3429776254522892242392271)
        ·
          refine ⟨5144664381784338363588407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3429776254522892242392271 5144664381784338363588407)
          ·
            refine ⟨7716996572676507545382611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5144664381784338363588407 7716996572676507545382611)
            ·
              refine ⟨11575494859014761318073917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7716996572676507545382611 11575494859014761318073917)
              ·
                refine ⟨4340810572130535494277719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11575494859014761318073917 4340810572130535494277719)
                ·
                  refine ⟨6511215858195803241416579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4340810572130535494277719 6511215858195803241416579)
                  ·
                    refine ⟨9766823787293704862124869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6511215858195803241416579 9766823787293704862124869)
                    ·
                      refine ⟨1831279460117569661648413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9766823787293704862124869 1831279460117569661648413)
                      ·
                        rfl

theorem cell23_3566404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 1, 3, 1, 1, 4].length) (baseStart_3566404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3566404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3566404 prefixEnd_3566404 := by exact prefixLift 3566404
  have htrace : WordTrace (prefixWord ++ tailWord_3566404) baseStart_3566404 baseEnd_3566404 := by
    simpa [prefixWord, tailWord_3566404, baseEnd_3566404] using wordTrace_append hprefix tailTrace_3566404
  have hstable : (prefixWord ++ tailWord_3566404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3566404).length < 2 ^ (prefixWord ++ tailWord_3566404).sum := by decide
  have hdescent : baseEnd_3566404 < baseStart_3566404 := by decide
  rcases family_descends (prefixWord ++ tailWord_3566404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3566434 : List Nat := [3, 3, 2, 1, 4, 1, 1, 1, 1, 2, 4]
def baseStart_3566434 : Nat := 118140960795 + 3566434 * 2 ^ 59
def prefixEnd_3566434 : Nat := 4983230072969 + 3 ^ 40 * 3566434 * 2
def baseEnd_3566434 : Nat := 1831294864537204544273275

theorem tailTrace_3566434 : CollatzResearch.WordTrace tailWord_3566434 prefixEnd_3566434 1831294864537204544273275 := by
  unfold tailWord_3566434
  simp only [CollatzResearch.WordTrace]
  refine ⟨32519633590356547819876589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86719022907617460853004237 32519633590356547819876589)
  ·
    refine ⟨12194862596383705432453721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32519633590356547819876589 12194862596383705432453721)
    ·
      refine ⟨9146146947287779074340291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12194862596383705432453721 9146146947287779074340291)
      ·
        refine ⟨13719220420931668611510437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9146146947287779074340291 13719220420931668611510437)
        ·
          refine ⟨2572353828924687864658207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13719220420931668611510437 2572353828924687864658207)
          ·
            refine ⟨3858530743387031796987311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2572353828924687864658207 3858530743387031796987311)
            ·
              refine ⟨5787796115080547695480967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3858530743387031796987311 5787796115080547695480967)
              ·
                refine ⟨8681694172620821543221451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5787796115080547695480967 8681694172620821543221451)
                ·
                  refine ⟨13022541258931232314832177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8681694172620821543221451 13022541258931232314832177)
                  ·
                    refine ⟨9766905944198424236124133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13022541258931232314832177 9766905944198424236124133)
                    ·
                      refine ⟨1831294864537204544273275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9766905944198424236124133 1831294864537204544273275)
                      ·
                        rfl

theorem cell23_3566434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 4, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 4, 1, 1, 1, 1, 2, 4].length) (baseStart_3566434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3566434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3566434 prefixEnd_3566434 := by exact prefixLift 3566434
  have htrace : WordTrace (prefixWord ++ tailWord_3566434) baseStart_3566434 baseEnd_3566434 := by
    simpa [prefixWord, tailWord_3566434, baseEnd_3566434] using wordTrace_append hprefix tailTrace_3566434
  have hstable : (prefixWord ++ tailWord_3566434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3566434).length < 2 ^ (prefixWord ++ tailWord_3566434).sum := by decide
  have hdescent : baseEnd_3566434 < baseStart_3566434 := by decide
  rcases family_descends (prefixWord ++ tailWord_3566434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3566460 : List Nat := [2, 2, 2, 1, 1, 1, 1, 6, 1, 4, 2]
def baseStart_3566460 : Nat := 118140960795 + 3566460 * 2 ^ 59
def prefixEnd_3566460 : Nat := 4983230072969 + 3 ^ 40 * 3566460 * 2
def baseEnd_3566460 : Nat := 1831308215034221442548155

theorem tailTrace_3566460 : CollatzResearch.WordTrace tailWord_3566460 prefixEnd_3566460 1831308215034221442548155 := by
  unfold tailWord_3566460
  simp only [CollatzResearch.WordTrace]
  refine ⟨65039741329665998859976417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86719655106221331813301889 65039741329665998859976417)
  ·
    refine ⟨48779805997249499144982313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65039741329665998859976417 48779805997249499144982313)
    ·
      refine ⟨36584854497937124358736735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48779805997249499144982313 36584854497937124358736735)
      ·
        refine ⟨54877281746905686538105103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36584854497937124358736735 54877281746905686538105103)
        ·
          refine ⟨82315922620358529807157655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54877281746905686538105103 82315922620358529807157655)
          ·
            refine ⟨123473883930537794710736483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82315922620358529807157655 123473883930537794710736483)
            ·
              refine ⟨185210825895806692066104725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 123473883930537794710736483 185210825895806692066104725)
              ·
                refine ⟨8681757463865938690598659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 185210825895806692066104725 8681757463865938690598659)
                ·
                  refine ⟨13022636195798908035897989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8681757463865938690598659 13022636195798908035897989)
                  ·
                    refine ⟨2441744286712295256730873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13022636195798908035897989 2441744286712295256730873)
                    ·
                      refine ⟨1831308215034221442548155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2441744286712295256730873 1831308215034221442548155)
                      ·
                        rfl

theorem cell23_3566460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 6, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 6, 1, 4, 2].length) (baseStart_3566460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3566460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3566460 prefixEnd_3566460 := by exact prefixLift 3566460
  have htrace : WordTrace (prefixWord ++ tailWord_3566460) baseStart_3566460 baseEnd_3566460 := by
    simpa [prefixWord, tailWord_3566460, baseEnd_3566460] using wordTrace_append hprefix tailTrace_3566460
  have hstable : (prefixWord ++ tailWord_3566460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3566460).length < 2 ^ (prefixWord ++ tailWord_3566460).sum := by decide
  have hdescent : baseEnd_3566460 < baseStart_3566460 := by decide
  rcases family_descends (prefixWord ++ tailWord_3566460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3566541 : List Nat := [1, 6, 3, 1, 1, 1, 1, 1, 2, 2, 4]
def baseStart_3566541 : Nat := 118140960795 + 3566541 * 2 ^ 59
def prefixEnd_3566541 : Nat := 4983230072969 + 3 ^ 40 * 3566541 * 2
def baseEnd_3566541 : Nat := 1831349806967235625635283

theorem tailTrace_3566541 : CollatzResearch.WordTrace tailWord_3566541 prefixEnd_3566541 1831349806967235625635283 := by
  unfold tailWord_3566541
  simp only [CollatzResearch.WordTrace]
  refine ⟨130082436972038548553651477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86721624648025699035767651 130082436972038548553651477)
  ·
    refine ⟨6097614233064306963452413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 130082436972038548553651477 6097614233064306963452413)
    ·
      refine ⟨2286605337399115111294655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6097614233064306963452413 2286605337399115111294655)
      ·
        refine ⟨3429908006098672666941983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2286605337399115111294655 3429908006098672666941983)
        ·
          refine ⟨5144862009148009000412975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3429908006098672666941983 5144862009148009000412975)
          ·
            refine ⟨7717293013722013500619463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5144862009148009000412975 7717293013722013500619463)
            ·
              refine ⟨11575939520583020250929195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7717293013722013500619463 11575939520583020250929195)
              ·
                refine ⟨17363909280874530376393793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11575939520583020250929195 17363909280874530376393793)
                ·
                  refine ⟨13022931960655897782295345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17363909280874530376393793 13022931960655897782295345)
                  ·
                    refine ⟨9767198970491923336721509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13022931960655897782295345 9767198970491923336721509)
                    ·
                      refine ⟨1831349806967235625635283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9767198970491923336721509 1831349806967235625635283)
                      ·
                        rfl

theorem cell23_3566541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 1, 1, 2, 2, 4].length) (baseStart_3566541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3566541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3566541 prefixEnd_3566541 := by exact prefixLift 3566541
  have htrace : WordTrace (prefixWord ++ tailWord_3566541) baseStart_3566541 baseEnd_3566541 := by
    simpa [prefixWord, tailWord_3566541, baseEnd_3566541] using wordTrace_append hprefix tailTrace_3566541
  have hstable : (prefixWord ++ tailWord_3566541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3566541).length < 2 ^ (prefixWord ++ tailWord_3566541).sum := by decide
  have hdescent : baseEnd_3566541 < baseStart_3566541 := by decide
  rcases family_descends (prefixWord ++ tailWord_3566541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3566567 : List Nat := [1, 1, 5, 2, 2, 1, 3, 1, 2, 1, 4]
def baseStart_3566567 : Nat := 118140960795 + 3566567 * 2 ^ 59
def prefixEnd_3566567 : Nat := 4983230072969 + 3 ^ 40 * 3566567 * 2
def baseEnd_3566567 : Nat := 1831363157464252523910163

theorem tailTrace_3566567 : CollatzResearch.WordTrace tailWord_3566567 prefixEnd_3566567 1831363157464252523910163 := by
  unfold tailWord_3566567
  simp only [CollatzResearch.WordTrace]
  refine ⟨130083385269944354994097955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86722256846629569996065303 130083385269944354994097955)
  ·
    refine ⟨195125077904916532491146933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130083385269944354994097955 195125077904916532491146933)
    ·
      refine ⟨18292976053585924921045025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 195125077904916532491146933 18292976053585924921045025)
      ·
        refine ⟨13719732040189443690783769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18292976053585924921045025 13719732040189443690783769)
        ·
          refine ⟨10289799030142082768087827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13719732040189443690783769 10289799030142082768087827)
          ·
            refine ⟨15434698545213124152131741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10289799030142082768087827 15434698545213124152131741)
            ·
              refine ⟨5788011954454921557049403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15434698545213124152131741 5788011954454921557049403)
              ·
                refine ⟨8682017931682382335574105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5788011954454921557049403 8682017931682382335574105)
                ·
                  refine ⟨6511513448761786751680579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8682017931682382335574105 6511513448761786751680579)
                  ·
                    refine ⟨9767270173142680127520869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6511513448761786751680579 9767270173142680127520869)
                    ·
                      refine ⟨1831363157464252523910163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9767270173142680127520869 1831363157464252523910163)
                      ·
                        rfl

theorem cell23_3566567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 3, 1, 2, 1, 4].length) (baseStart_3566567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3566567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3566567 prefixEnd_3566567 := by exact prefixLift 3566567
  have htrace : WordTrace (prefixWord ++ tailWord_3566567) baseStart_3566567 baseEnd_3566567 := by
    simpa [prefixWord, tailWord_3566567, baseEnd_3566567] using wordTrace_append hprefix tailTrace_3566567
  have hstable : (prefixWord ++ tailWord_3566567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3566567).length < 2 ^ (prefixWord ++ tailWord_3566567).sum := by decide
  have hdescent : baseEnd_3566567 < baseStart_3566567 := by decide
  rcases family_descends (prefixWord ++ tailWord_3566567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3566617 : List Nat := [1, 2, 1, 2, 1, 1, 6, 2, 3, 1, 3]
def baseStart_3566617 : Nat := 118140960795 + 3566617 * 2 ^ 59
def prefixEnd_3566617 : Nat := 4983230072969 + 3 ^ 40 * 3566617 * 2
def baseEnd_3566617 : Nat := 1831388831496977328284933

theorem tailTrace_3566617 : CollatzResearch.WordTrace tailWord_3566617 prefixEnd_3566617 1831388831496977328284933 := by
  unfold tailWord_3566617
  simp only [CollatzResearch.WordTrace]
  refine ⟨130085208919763213533418105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86723472613175475688945403 130085208919763213533418105)
  ·
    refine ⟨97563906689822410150063579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130085208919763213533418105 97563906689822410150063579)
    ·
      refine ⟨146345860034733615225095369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97563906689822410150063579 146345860034733615225095369)
      ·
        refine ⟨109759395026050211418821527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146345860034733615225095369 109759395026050211418821527)
        ·
          refine ⟨164639092539075317128232291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109759395026050211418821527 164639092539075317128232291)
          ·
            refine ⟨246958638808612975692348437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 164639092539075317128232291 246958638808612975692348437)
            ·
              refine ⟨11576186194153733235578833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 246958638808612975692348437 11576186194153733235578833)
              ·
                refine ⟨8682139645615299926684125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11576186194153733235578833 8682139645615299926684125)
                ·
                  refine ⟨3255802367105737472506547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8682139645615299926684125 3255802367105737472506547)
                  ·
                    refine ⟨4883703550658606208759821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3255802367105737472506547 4883703550658606208759821)
                    ·
                      refine ⟨1831388831496977328284933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4883703550658606208759821 1831388831496977328284933)
                      ·
                        rfl

theorem cell23_3566617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 6, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 6, 2, 3, 1, 3].length) (baseStart_3566617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3566617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3566617 prefixEnd_3566617 := by exact prefixLift 3566617
  have htrace : WordTrace (prefixWord ++ tailWord_3566617) baseStart_3566617 baseEnd_3566617 := by
    simpa [prefixWord, tailWord_3566617, baseEnd_3566617] using wordTrace_append hprefix tailTrace_3566617
  have hstable : (prefixWord ++ tailWord_3566617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3566617).length < 2 ^ (prefixWord ++ tailWord_3566617).sum := by decide
  have hdescent : baseEnd_3566617 < baseStart_3566617 := by decide
  rcases family_descends (prefixWord ++ tailWord_3566617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3566627 : List Nat := [1, 1, 1, 4, 3, 2, 2, 1, 1, 5, 2]
def baseStart_3566627 : Nat := 118140960795 + 3566627 * 2 ^ 59
def prefixEnd_3566627 : Nat := 4983230072969 + 3 ^ 40 * 3566627 * 2
def baseEnd_3566627 : Nat := 1831393966303522289159887

theorem tailTrace_3566627 : CollatzResearch.WordTrace tailWord_3566627 prefixEnd_3566627 1831393966303522289159887 := by
  unfold tailWord_3566627
  simp only [CollatzResearch.WordTrace]
  refine ⟨130085573649726985241282135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86723715766484656827521423 130085573649726985241282135)
  ·
    refine ⟨195128360474590477861923203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130085573649726985241282135 195128360474590477861923203)
    ·
      refine ⟨292692540711885716792884805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195128360474590477861923203 292692540711885716792884805)
      ·
        refine ⟨54879851383478571898665901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 292692540711885716792884805 54879851383478571898665901)
        ·
          refine ⟨20579944268804464461999713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54879851383478571898665901 20579944268804464461999713)
          ·
            refine ⟨15434958201603348346499785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20579944268804464461999713 15434958201603348346499785)
            ·
              refine ⟨11576218651202511259874839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15434958201603348346499785 11576218651202511259874839)
              ·
                refine ⟨17364327976803766889812259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11576218651202511259874839 17364327976803766889812259)
                ·
                  refine ⟨26046491965205650334718389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17364327976803766889812259 26046491965205650334718389)
                  ·
                    refine ⟨2441858621738029718879849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 26046491965205650334718389 2441858621738029718879849)
                    ·
                      refine ⟨1831393966303522289159887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2441858621738029718879849 1831393966303522289159887)
                      ·
                        rfl

theorem cell23_3566627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 2, 1, 1, 5, 2].length) (baseStart_3566627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3566627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3566627 prefixEnd_3566627 := by exact prefixLift 3566627
  have htrace : WordTrace (prefixWord ++ tailWord_3566627) baseStart_3566627 baseEnd_3566627 := by
    simpa [prefixWord, tailWord_3566627, baseEnd_3566627] using wordTrace_append hprefix tailTrace_3566627
  have hstable : (prefixWord ++ tailWord_3566627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3566627).length < 2 ^ (prefixWord ++ tailWord_3566627).sum := by decide
  have hdescent : baseEnd_3566627 < baseStart_3566627 := by decide
  rcases family_descends (prefixWord ++ tailWord_3566627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3566670 : List Nat := [4, 1, 1, 1, 1, 3, 1, 3, 1, 1, 6]
def baseStart_3566670 : Nat := 118140960795 + 3566670 * 2 ^ 59
def prefixEnd_3566670 : Nat := 4983230072969 + 3 ^ 40 * 3566670 * 2
def baseEnd_3566670 : Nat := 1831416045971665620922189

theorem tailTrace_3566670 : CollatzResearch.WordTrace tailWord_3566670 prefixEnd_3566670 1831416045971665620922189 := by
  unfold tailWord_3566670
  simp only [CollatzResearch.WordTrace]
  refine ⟨16260892748571400448137183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 86724761325714135723398309 16260892748571400448137183)
  ·
    refine ⟨24391339122857100672205775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16260892748571400448137183 24391339122857100672205775)
    ·
      refine ⟨36587008684285651008308663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24391339122857100672205775 36587008684285651008308663)
      ·
        refine ⟨54880513026428476512462995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36587008684285651008308663 54880513026428476512462995)
        ·
          refine ⟨82320769539642714768694493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54880513026428476512462995 82320769539642714768694493)
          ·
            refine ⟨30870288577366018038260435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 82320769539642714768694493 30870288577366018038260435)
            ·
              refine ⟨46305432866049027057390653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30870288577366018038260435 46305432866049027057390653)
              ·
                refine ⟨17364537324768385146521495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46305432866049027057390653 17364537324768385146521495)
                ·
                  refine ⟨26046805987152577719782243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17364537324768385146521495 26046805987152577719782243)
                  ·
                    refine ⟨39070208980728866579673365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26046805987152577719782243 39070208980728866579673365)
                    ·
                      refine ⟨1831416045971665620922189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 39070208980728866579673365 1831416045971665620922189)
                      ·
                        rfl

theorem cell23_3566670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 3, 1, 1, 6].length) (baseStart_3566670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3566670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3566670 prefixEnd_3566670 := by exact prefixLift 3566670
  have htrace : WordTrace (prefixWord ++ tailWord_3566670) baseStart_3566670 baseEnd_3566670 := by
    simpa [prefixWord, tailWord_3566670, baseEnd_3566670] using wordTrace_append hprefix tailTrace_3566670
  have hstable : (prefixWord ++ tailWord_3566670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3566670).length < 2 ^ (prefixWord ++ tailWord_3566670).sum := by decide
  have hdescent : baseEnd_3566670 < baseStart_3566670 := by decide
  rcases family_descends (prefixWord ++ tailWord_3566670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3566674 : List Nat := [3, 2, 2, 1, 3, 1, 3, 2, 1, 1, 4]
def baseStart_3566674 : Nat := 118140960795 + 3566674 * 2 ^ 59
def prefixEnd_3566674 : Nat := 4983230072969 + 3 ^ 40 * 3566674 * 2
def baseEnd_3566674 : Nat := 1831418099894283605272171

theorem tailTrace_3566674 : CollatzResearch.WordTrace tailWord_3566674 prefixEnd_3566674 1831418099894283605272171 := by
  unfold tailWord_3566674
  simp only [CollatzResearch.WordTrace]
  refine ⟨32521821970139178067060769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86724858587037808178828717 32521821970139178067060769)
  ·
    refine ⟨24391366477604383550295577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32521821970139178067060769 24391366477604383550295577)
    ·
      refine ⟨18293524858203287662721683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24391366477604383550295577 18293524858203287662721683)
      ·
        refine ⟨27440287287304931494082525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18293524858203287662721683 27440287287304931494082525)
        ·
          refine ⟨10290107732739349310280947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27440287287304931494082525 10290107732739349310280947)
          ·
            refine ⟨15435161599109023965421421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10290107732739349310280947 15435161599109023965421421)
            ·
              refine ⟨5788185599665883987033033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15435161599109023965421421 5788185599665883987033033)
              ·
                refine ⟨4341139199749412990274775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5788185599665883987033033 4341139199749412990274775)
                ·
                  refine ⟨6511708799624119485412163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4341139199749412990274775 6511708799624119485412163)
                  ·
                    refine ⟨9767563199436179228118245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6511708799624119485412163 9767563199436179228118245)
                    ·
                      refine ⟨1831418099894283605272171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9767563199436179228118245 1831418099894283605272171)
                      ·
                        rfl

theorem cell23_3566674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 3, 2, 1, 1, 4].length) (baseStart_3566674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3566674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3566674 prefixEnd_3566674 := by exact prefixLift 3566674
  have htrace : WordTrace (prefixWord ++ tailWord_3566674) baseStart_3566674 baseEnd_3566674 := by
    simpa [prefixWord, tailWord_3566674, baseEnd_3566674] using wordTrace_append hprefix tailTrace_3566674
  have hstable : (prefixWord ++ tailWord_3566674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3566674).length < 2 ^ (prefixWord ++ tailWord_3566674).sum := by decide
  have hdescent : baseEnd_3566674 < baseStart_3566674 := by decide
  rcases family_descends (prefixWord ++ tailWord_3566674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3566677 : List Nat := [1, 3, 2, 2, 1, 2, 3, 1, 3, 2, 3]
def baseStart_3566677 : Nat := 118140960795 + 3566677 * 2 ^ 59
def prefixEnd_3566677 : Nat := 4983230072969 + 3 ^ 40 * 3566677 * 2
def baseEnd_3566677 : Nat := 1831419640336247093534657

theorem tailTrace_3566677 : CollatzResearch.WordTrace tailWord_3566677 prefixEnd_3566677 1831419640336247093534657 := by
  unfold tailWord_3566677
  simp only [CollatzResearch.WordTrace]
  refine ⟨130087397299545843780602285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86724931533030562520401523 130087397299545843780602285)
  ·
    refine ⟨48782773987329691417725857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130087397299545843780602285 48782773987329691417725857)
    ·
      refine ⟨36587080490497268563294393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48782773987329691417725857 36587080490497268563294393)
      ·
        refine ⟨27440310367872951422470795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36587080490497268563294393 27440310367872951422470795)
        ·
          refine ⟨41160465551809427133706193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27440310367872951422470795 41160465551809427133706193)
          ·
            refine ⟨30870349163857070350279645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41160465551809427133706193 30870349163857070350279645)
            ·
              refine ⟨11576380936446401381354867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30870349163857070350279645 11576380936446401381354867)
              ·
                refine ⟨17364571404669602072032301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11576380936446401381354867 17364571404669602072032301)
                ·
                  refine ⟨6511714276751100777012113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17364571404669602072032301 6511714276751100777012113)
                  ·
                    refine ⟨4883785707563325582759085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6511714276751100777012113 4883785707563325582759085)
                    ·
                      refine ⟨1831419640336247093534657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4883785707563325582759085 1831419640336247093534657)
                      ·
                        rfl

theorem cell23_3566677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 3, 1, 3, 2, 3].length) (baseStart_3566677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3566677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3566677 prefixEnd_3566677 := by exact prefixLift 3566677
  have htrace : WordTrace (prefixWord ++ tailWord_3566677) baseStart_3566677 baseEnd_3566677 := by
    simpa [prefixWord, tailWord_3566677, baseEnd_3566677] using wordTrace_append hprefix tailTrace_3566677
  have hstable : (prefixWord ++ tailWord_3566677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3566677).length < 2 ^ (prefixWord ++ tailWord_3566677).sum := by decide
  have hdescent : baseEnd_3566677 < baseStart_3566677 := by decide
  rcases family_descends (prefixWord ++ tailWord_3566677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3566691 : List Nat := [1, 1, 1, 5, 1, 1, 1, 7, 1, 2, 2]
def baseStart_3566691 : Nat := 118140960795 + 3566691 * 2 ^ 59
def prefixEnd_3566691 : Nat := 4983230072969 + 3 ^ 40 * 3566691 * 2
def baseEnd_3566691 : Nat := 1831426829065410038759593

theorem tailTrace_3566691 : CollatzResearch.WordTrace tailWord_3566691 prefixEnd_3566691 1831426829065410038759593 := by
  unfold tailWord_3566691
  simp only [CollatzResearch.WordTrace]
  refine ⟨130087907921495124171611927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86725271947663416114407951 130087907921495124171611927)
  ·
    refine ⟨195131861882242686257417891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130087907921495124171611927 195131861882242686257417891)
    ·
      refine ⟨292697792823364029386126837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195131861882242686257417891 292697792823364029386126837)
      ·
        refine ⟨27440418077190377754949391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 292697792823364029386126837 27440418077190377754949391)
        ·
          refine ⟨41160627115785566632424087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27440418077190377754949391 41160627115785566632424087)
          ·
            refine ⟨61740940673678349948636131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41160627115785566632424087 61740940673678349948636131)
            ·
              refine ⟨92611411010517524922954197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61740940673678349948636131 92611411010517524922954197)
              ·
                refine ⟨2170579945559004490381739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 92611411010517524922954197 2170579945559004490381739)
                ·
                  refine ⟨3255869918338506735572609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2170579945559004490381739 3255869918338506735572609)
                  ·
                    refine ⟨2441902438753880051679457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3255869918338506735572609 2441902438753880051679457)
                    ·
                      refine ⟨1831426829065410038759593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2441902438753880051679457 1831426829065410038759593)
                      ·
                        rfl

theorem cell23_3566691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 7, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 7, 1, 2, 2].length) (baseStart_3566691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3566691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3566691 prefixEnd_3566691 := by exact prefixLift 3566691
  have htrace : WordTrace (prefixWord ++ tailWord_3566691) baseStart_3566691 baseEnd_3566691 := by
    simpa [prefixWord, tailWord_3566691, baseEnd_3566691] using wordTrace_append hprefix tailTrace_3566691
  have hstable : (prefixWord ++ tailWord_3566691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3566691).length < 2 ^ (prefixWord ++ tailWord_3566691).sum := by decide
  have hdescent : baseEnd_3566691 < baseStart_3566691 := by decide
  rcases family_descends (prefixWord ++ tailWord_3566691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3566718 : List Nat := [4, 2, 4, 1, 1, 1, 2, 1, 1, 6]
def baseStart_3566718 : Nat := 118140960795 + 3566718 * 2 ^ 59
def prefixEnd_3566718 : Nat := 4983230072969 + 3 ^ 40 * 3566718 * 2
def baseEnd_3566718 : Nat := 610480231014360477707323

theorem tailTrace_3566718 : CollatzResearch.WordTrace tailWord_3566718 prefixEnd_3566718 610480231014360477707323 := by
  unfold tailWord_3566718
  simp only [CollatzResearch.WordTrace]
  refine ⟨16261111586549663472855601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 86725928461598205188563205 16261111586549663472855601)
  ·
    refine ⟨12195833689912247604641701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16261111586549663472855601 12195833689912247604641701)
    ·
      refine ⟨2286718816858546425870319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12195833689912247604641701 2286718816858546425870319)
      ·
        refine ⟨3430078225287819638805479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2286718816858546425870319 3430078225287819638805479)
        ·
          refine ⟨5145117337931729458208219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3430078225287819638805479 5145117337931729458208219)
          ·
            refine ⟨7717676006897594187312329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5145117337931729458208219 7717676006897594187312329)
            ·
              refine ⟨5788257005173195640484247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7717676006897594187312329 5788257005173195640484247)
              ·
                refine ⟨8682385507759793460726371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5788257005173195640484247 8682385507759793460726371)
                ·
                  refine ⟨13023578261639690191089557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8682385507759793460726371 13023578261639690191089557)
                  ·
                    refine ⟨610480231014360477707323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13023578261639690191089557 610480231014360477707323)
                    ·
                      rfl

theorem cell23_3566718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 2, 1, 1, 6].length) (baseStart_3566718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3566718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3566718 prefixEnd_3566718 := by exact prefixLift 3566718
  have htrace : WordTrace (prefixWord ++ tailWord_3566718) baseStart_3566718 baseEnd_3566718 := by
    simpa [prefixWord, tailWord_3566718, baseEnd_3566718] using wordTrace_append hprefix tailTrace_3566718
  have hstable : (prefixWord ++ tailWord_3566718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3566718).length < 2 ^ (prefixWord ++ tailWord_3566718).sum := by decide
  have hdescent : baseEnd_3566718 < baseStart_3566718 := by decide
  rcases family_descends (prefixWord ++ tailWord_3566718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3566724 : List Nat := [2, 3, 2, 1, 2, 3, 2, 1, 1, 3, 3]
def baseStart_3566724 : Nat := 118140960795 + 3566724 * 2 ^ 59
def prefixEnd_3566724 : Nat := 4983230072969 + 3 ^ 40 * 3566724 * 2
def baseEnd_3566724 : Nat := 1831443773927008409646941

theorem tailTrace_3566724 : CollatzResearch.WordTrace tailWord_3566724 prefixEnd_3566724 1831443773927008409646941 := by
  unfold tailWord_3566724
  simp only [CollatzResearch.WordTrace]
  refine ⟨65044555765187785403781613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86726074353583713871708817 65044555765187785403781613)
  ·
    refine ⟨24391708411945419526418105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65044555765187785403781613 24391708411945419526418105)
    ·
      refine ⟨18293781308959064644813579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24391708411945419526418105 18293781308959064644813579)
      ·
        refine ⟨27440671963438596967220369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18293781308959064644813579 27440671963438596967220369)
        ·
          refine ⟨20580503972578947725415277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27440671963438596967220369 20580503972578947725415277)
          ·
            refine ⟨7717688989717105397030729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20580503972578947725415277 7717688989717105397030729)
            ·
              refine ⟨5788266742287829047773047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7717688989717105397030729 5788266742287829047773047)
              ·
                refine ⟨8682400113431743571659571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5788266742287829047773047 8682400113431743571659571)
                ·
                  refine ⟨13023600170147615357489357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8682400113431743571659571 13023600170147615357489357)
                  ·
                    refine ⟨4883850063805355759058509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13023600170147615357489357 4883850063805355759058509)
                    ·
                      refine ⟨1831443773927008409646941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4883850063805355759058509 1831443773927008409646941)
                      ·
                        rfl

theorem cell23_3566724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 2, 1, 1, 3, 3].length) (baseStart_3566724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3566724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3566724 prefixEnd_3566724 := by exact prefixLift 3566724
  have htrace : WordTrace (prefixWord ++ tailWord_3566724) baseStart_3566724 baseEnd_3566724 := by
    simpa [prefixWord, tailWord_3566724, baseEnd_3566724] using wordTrace_append hprefix tailTrace_3566724
  have hstable : (prefixWord ++ tailWord_3566724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3566724).length < 2 ^ (prefixWord ++ tailWord_3566724).sum := by decide
  have hdescent : baseEnd_3566724 < baseStart_3566724 := by decide
  rcases family_descends (prefixWord ++ tailWord_3566724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3566777 : List Nat := [1, 2, 1, 4, 1, 3, 2, 1, 2, 2, 4]
def baseStart_3566777 : Nat := 118140960795 + 3566777 * 2 ^ 59
def prefixEnd_3566777 : Nat := 4983230072969 + 3 ^ 40 * 3566777 * 2
def baseEnd_3566777 : Nat := 1831470988401696702284197

theorem tailTrace_3566777 : CollatzResearch.WordTrace tailWord_3566777 prefixEnd_3566777 1831470988401696702284197 := by
  unfold tailWord_3566777
  simp only [CollatzResearch.WordTrace]
  refine ⟨130091044599183560859242585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86727363066122373906161723 130091044599183560859242585)
  ·
    refine ⟨97568283449387670644431939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130091044599183560859242585 97568283449387670644431939)
    ·
      refine ⟨146352425174081505966647909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97568283449387670644431939 146352425174081505966647909)
      ·
        refine ⟨27441079720140282368746483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 146352425174081505966647909 27441079720140282368746483)
        ·
          refine ⟨41161619580210423553119725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27441079720140282368746483 41161619580210423553119725)
          ·
            refine ⟨15435607342578908832419897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41161619580210423553119725 15435607342578908832419897)
            ·
              refine ⟨11576705506934181624314923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15435607342578908832419897 11576705506934181624314923)
              ·
                refine ⟨17365058260401272436472385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11576705506934181624314923 17365058260401272436472385)
                ·
                  refine ⟨13023793695300954327354289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17365058260401272436472385 13023793695300954327354289)
                  ·
                    refine ⟨9767845271475715745515717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13023793695300954327354289 9767845271475715745515717)
                    ·
                      refine ⟨1831470988401696702284197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9767845271475715745515717 1831470988401696702284197)
                      ·
                        rfl

theorem cell23_3566777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 2, 1, 2, 2, 4].length) (baseStart_3566777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3566777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3566777 prefixEnd_3566777 := by exact prefixLift 3566777
  have htrace : WordTrace (prefixWord ++ tailWord_3566777) baseStart_3566777 baseEnd_3566777 := by
    simpa [prefixWord, tailWord_3566777, baseEnd_3566777] using wordTrace_append hprefix tailTrace_3566777
  have hstable : (prefixWord ++ tailWord_3566777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3566777).length < 2 ^ (prefixWord ++ tailWord_3566777).sum := by decide
  have hdescent : baseEnd_3566777 < baseStart_3566777 := by decide
  rcases family_descends (prefixWord ++ tailWord_3566777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3566781 : List Nat := [1, 4, 1, 2, 1, 1, 2, 5, 2, 2, 2]
def baseStart_3566781 : Nat := 118140960795 + 3566781 * 2 ^ 59
def prefixEnd_3566781 : Nat := 4983230072969 + 3 ^ 40 * 3566781 * 2
def baseEnd_3566781 : Nat := 1831473042324314686634179

theorem tailTrace_3566781 : CollatzResearch.WordTrace tailWord_3566781 prefixEnd_3566781 1831473042324314686634179 := by
  unfold tailWord_3566781
  simp only [CollatzResearch.WordTrace]
  refine ⟨130091190491169069542388197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86727460327446046361592131 130091190491169069542388197)
  ·
    refine ⟨24392098217094200539197787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 130091190491169069542388197 24392098217094200539197787)
    ·
      refine ⟨36588147325641300808796681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24392098217094200539197787 36588147325641300808796681)
      ·
        refine ⟨27441110494230975606597511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36588147325641300808796681 27441110494230975606597511)
        ·
          refine ⟨41161665741346463409896267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27441110494230975606597511 41161665741346463409896267)
          ·
            refine ⟨61742498612019695114844401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41161665741346463409896267 61742498612019695114844401)
            ·
              refine ⟨46306873959014771336133301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61742498612019695114844401 46306873959014771336133301)
              ·
                refine ⟨4341269433657634812762497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 46306873959014771336133301 4341269433657634812762497)
                ·
                  refine ⟨3255952075243226109571873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4341269433657634812762497 3255952075243226109571873)
                  ·
                    refine ⟨2441964056432419582178905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3255952075243226109571873 2441964056432419582178905)
                    ·
                      refine ⟨1831473042324314686634179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2441964056432419582178905 1831473042324314686634179)
                      ·
                        rfl

theorem cell23_3566781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 5, 2, 2, 2].length) (baseStart_3566781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3566781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3566781 prefixEnd_3566781 := by exact prefixLift 3566781
  have htrace : WordTrace (prefixWord ++ tailWord_3566781) baseStart_3566781 baseEnd_3566781 := by
    simpa [prefixWord, tailWord_3566781, baseEnd_3566781] using wordTrace_append hprefix tailTrace_3566781
  have hstable : (prefixWord ++ tailWord_3566781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3566781).length < 2 ^ (prefixWord ++ tailWord_3566781).sum := by decide
  have hdescent : baseEnd_3566781 < baseStart_3566781 := by decide
  rcases family_descends (prefixWord ++ tailWord_3566781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3566817 : List Nat := [1, 2, 3, 1, 3, 2, 1, 1, 4, 5]
def baseStart_3566817 : Nat := 118140960795 + 3566817 * 2 ^ 59
def prefixEnd_3566817 : Nat := 4983230072969 + 3 ^ 40 * 3566817 * 2
def baseEnd_3566817 : Nat := 610497175875958848594671

theorem tailTrace_3566817 : CollatzResearch.WordTrace tailWord_3566817 prefixEnd_3566817 610497175875958848594671 := by
  unfold tailWord_3566817
  simp only [CollatzResearch.WordTrace]
  refine ⟨130092503519038647690698705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86728335679359098460465803 130092503519038647690698705)
  ·
    refine ⟨97569377639278985768024029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130092503519038647690698705 97569377639278985768024029)
    ·
      refine ⟨36588516614729619663009011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 97569377639278985768024029 36588516614729619663009011)
      ·
        refine ⟨54882774922094429494513517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36588516614729619663009011 54882774922094429494513517)
        ·
          refine ⟨20581040595785411060442569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54882774922094429494513517 20581040595785411060442569)
          ·
            refine ⟨15435780446839058295331927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20581040595785411060442569 15435780446839058295331927)
            ·
              refine ⟨23153670670258587442997891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15435780446839058295331927 23153670670258587442997891)
              ·
                refine ⟨34730506005387881164496837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23153670670258587442997891 34730506005387881164496837)
                ·
                  refine ⟨6511969876010227718343157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34730506005387881164496837 6511969876010227718343157)
                  ·
                    refine ⟨610497175875958848594671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6511969876010227718343157 610497175875958848594671)
                    ·
                      rfl

theorem cell23_3566817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 1, 1, 4, 5].length) (baseStart_3566817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3566817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3566817 prefixEnd_3566817 := by exact prefixLift 3566817
  have htrace : WordTrace (prefixWord ++ tailWord_3566817) baseStart_3566817 baseEnd_3566817 := by
    simpa [prefixWord, tailWord_3566817, baseEnd_3566817] using wordTrace_append hprefix tailTrace_3566817
  have hstable : (prefixWord ++ tailWord_3566817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3566817).length < 2 ^ (prefixWord ++ tailWord_3566817).sum := by decide
  have hdescent : baseEnd_3566817 < baseStart_3566817 := by decide
  rcases family_descends (prefixWord ++ tailWord_3566817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3566821 : List Nat := [1, 3, 1, 4, 4, 1, 1, 1, 7]
def baseStart_3566821 : Nat := 118140960795 + 3566821 * 2 ^ 59
def prefixEnd_3566821 : Nat := 4983230072969 + 3 ^ 40 * 3566821 * 2
def baseEnd_3566821 : Nat := 203499286838943836681555

theorem tailTrace_3566821 : CollatzResearch.WordTrace tailWord_3566821 prefixEnd_3566821 203499286838943836681555 := by
  unfold tailWord_3566821
  simp only [CollatzResearch.WordTrace]
  refine ⟨130092649411024156373844317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86728432940682770915896211 130092649411024156373844317)
  ·
    refine ⟨48784743529134058640191619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130092649411024156373844317 48784743529134058640191619)
    ·
      refine ⟨73177115293701087960287429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48784743529134058640191619 73177115293701087960287429)
      ·
        refine ⟨13720709117568953992553893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 73177115293701087960287429 13720709117568953992553893)
        ·
          refine ⟨2572632959544178873603855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13720709117568953992553893 2572632959544178873603855)
          ·
            refine ⟨3858949439316268310405783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2572632959544178873603855 3858949439316268310405783)
            ·
              refine ⟨5788424158974402465608675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3858949439316268310405783 5788424158974402465608675)
              ·
                refine ⟨8682636238461603698413013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5788424158974402465608675 8682636238461603698413013)
                ·
                  refine ⟨203499286838943836681555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8682636238461603698413013 203499286838943836681555)
                  ·
                    rfl

theorem cell23_3566821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 4, 1, 1, 1, 7].length) (baseStart_3566821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3566821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3566821 prefixEnd_3566821 := by exact prefixLift 3566821
  have htrace : WordTrace (prefixWord ++ tailWord_3566821) baseStart_3566821 baseEnd_3566821 := by
    simpa [prefixWord, tailWord_3566821, baseEnd_3566821] using wordTrace_append hprefix tailTrace_3566821
  have hstable : (prefixWord ++ tailWord_3566821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3566821).length < 2 ^ (prefixWord ++ tailWord_3566821).sum := by decide
  have hdescent : baseEnd_3566821 < baseStart_3566821 := by decide
  rcases family_descends (prefixWord ++ tailWord_3566821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3566824 : List Nat := [2, 1, 4, 1, 2, 1, 2, 1, 2, 5, 2]
def baseStart_3566824 : Nat := 118140960795 + 3566824 * 2 ^ 59
def prefixEnd_3566824 : Nat := 4983230072969 + 3 ^ 40 * 3566824 * 2
def baseEnd_3566824 : Nat := 1831495121992458018396481

theorem tailTrace_3566824 : CollatzResearch.WordTrace tailWord_3566824 prefixEnd_3566824 1831495121992458018396481 := by
  unfold tailWord_3566824
  simp only [CollatzResearch.WordTrace]
  refine ⟨65046379415006643943101763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86728505886675525257469017 65046379415006643943101763)
  ·
    refine ⟨97569569122509965914652645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65046379415006643943101763 97569569122509965914652645)
    ·
      refine ⟨18294294210470618608997371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 97569569122509965914652645 18294294210470618608997371)
      ·
        refine ⟨27441441315705927913496057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18294294210470618608997371 27441441315705927913496057)
        ·
          refine ⟨20581080986779445935122043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27441441315705927913496057 20581080986779445935122043)
          ·
            refine ⟨30871621480169168902683065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20581080986779445935122043 30871621480169168902683065)
            ·
              refine ⟨23153716110126876677012299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30871621480169168902683065 23153716110126876677012299)
              ·
                refine ⟨34730574165190315015518449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23153716110126876677012299 34730574165190315015518449)
                ·
                  refine ⟨26047930623892736261638837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34730574165190315015518449 26047930623892736261638837)
                  ·
                    refine ⟨2441993495989944024528641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 26047930623892736261638837 2441993495989944024528641)
                    ·
                      refine ⟨1831495121992458018396481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2441993495989944024528641 1831495121992458018396481)
                      ·
                        rfl

theorem cell23_3566824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 2, 1, 2, 5, 2].length) (baseStart_3566824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3566824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3566824 prefixEnd_3566824 := by exact prefixLift 3566824
  have htrace : WordTrace (prefixWord ++ tailWord_3566824) baseStart_3566824 baseEnd_3566824 := by
    simpa [prefixWord, tailWord_3566824, baseEnd_3566824] using wordTrace_append hprefix tailTrace_3566824
  have hstable : (prefixWord ++ tailWord_3566824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3566824).length < 2 ^ (prefixWord ++ tailWord_3566824).sum := by decide
  have hdescent : baseEnd_3566824 < baseStart_3566824 := by decide
  rcases family_descends (prefixWord ++ tailWord_3566824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3566827 : List Nat := [1, 1, 1, 1, 2, 7, 1, 1, 1, 2, 5]
def baseStart_3566827 : Nat := 118140960795 + 3566827 * 2 ^ 59
def prefixEnd_3566827 : Nat := 4983230072969 + 3 ^ 40 * 3566827 * 2
def baseEnd_3566827 : Nat := 1831496662434421506658967

theorem tailTrace_3566827 : CollatzResearch.WordTrace tailWord_3566827 prefixEnd_3566827 1831496662434421506658967 := by
  unfold tailWord_3566827
  simp only [CollatzResearch.WordTrace]
  refine ⟨130092868249002419398562735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86728578832668279599041823 130092868249002419398562735)
  ·
    refine ⟨195139302373503629097844103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130092868249002419398562735 195139302373503629097844103)
    ·
      refine ⟨292708953560255443646766155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195139302373503629097844103 292708953560255443646766155)
      ·
        refine ⟨439063430340383165470149233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 292708953560255443646766155 439063430340383165470149233)
        ·
          refine ⟨329297572755287374102611925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 439063430340383165470149233 329297572755287374102611925)
          ·
            refine ⟨7717911861452047830529967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 329297572755287374102611925 7717911861452047830529967)
            ·
              refine ⟨11576867792178071745794951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7717911861452047830529967 11576867792178071745794951)
              ·
                refine ⟨17365301688267107618692427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11576867792178071745794951 17365301688267107618692427)
                ·
                  refine ⟨26047952532400661428038641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17365301688267107618692427 26047952532400661428038641)
                  ·
                    refine ⟨19535964399300496071028981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26047952532400661428038641 19535964399300496071028981)
                    ·
                      refine ⟨1831496662434421506658967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19535964399300496071028981 1831496662434421506658967)
                      ·
                        rfl

theorem cell23_3566827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 1, 1, 1, 2, 5].length) (baseStart_3566827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3566827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3566827 prefixEnd_3566827 := by exact prefixLift 3566827
  have htrace : WordTrace (prefixWord ++ tailWord_3566827) baseStart_3566827 baseEnd_3566827 := by
    simpa [prefixWord, tailWord_3566827, baseEnd_3566827] using wordTrace_append hprefix tailTrace_3566827
  have hstable : (prefixWord ++ tailWord_3566827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3566827).length < 2 ^ (prefixWord ++ tailWord_3566827).sum := by decide
  have hdescent : baseEnd_3566827 < baseStart_3566827 := by decide
  rcases family_descends (prefixWord ++ tailWord_3566827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3566937 : List Nat := [1, 2, 1, 2, 2, 2, 2, 2, 3, 6]
def baseStart_3566937 : Nat := 118140960795 + 3566937 * 2 ^ 59
def prefixEnd_3566937 : Nat := 4983230072969 + 3 ^ 40 * 3566937 * 2
def baseEnd_3566937 : Nat := 610517715102138692094487

theorem tailTrace_3566937 : CollatzResearch.WordTrace tailWord_3566937 prefixEnd_3566937 610517715102138692094487 := by
  unfold tailWord_3566937
  simp only [CollatzResearch.WordTrace]
  refine ⟨130096880278603908185067065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86731253519069272123378043 130096880278603908185067065)
  ·
    refine ⟨97572660208952931138800299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130096880278603908185067065 97572660208952931138800299)
    ·
      refine ⟨146358990313429396708200449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97572660208952931138800299 146358990313429396708200449)
      ·
        refine ⟨109769242735072047531150337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146358990313429396708200449 109769242735072047531150337)
        ·
          refine ⟨82326932051304035648362753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109769242735072047531150337 82326932051304035648362753)
          ·
            refine ⟨61745199038478026736272065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82326932051304035648362753 61745199038478026736272065)
            ·
              refine ⟨46308899278858520052204049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61745199038478026736272065 46308899278858520052204049)
              ·
                refine ⟨34731674459143890039153037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46308899278858520052204049 34731674459143890039153037)
                ·
                  refine ⟨13024377922178958764682389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34731674459143890039153037 13024377922178958764682389)
                  ·
                    refine ⟨610517715102138692094487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13024377922178958764682389 610517715102138692094487)
                    ·
                      rfl

theorem cell23_3566937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 2, 3, 6].length) (baseStart_3566937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3566937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3566937 prefixEnd_3566937 := by exact prefixLift 3566937
  have htrace : WordTrace (prefixWord ++ tailWord_3566937) baseStart_3566937 baseEnd_3566937 := by
    simpa [prefixWord, tailWord_3566937, baseEnd_3566937] using wordTrace_append hprefix tailTrace_3566937
  have hstable : (prefixWord ++ tailWord_3566937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3566937).length < 2 ^ (prefixWord ++ tailWord_3566937).sum := by decide
  have hdescent : baseEnd_3566937 < baseStart_3566937 := by decide
  rcases family_descends (prefixWord ++ tailWord_3566937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3566938 : List Nat := [3, 1, 1, 2, 1, 2, 4, 4, 1, 1, 3]
def baseStart_3566938 : Nat := 118140960795 + 3566938 * 2 ^ 59
def prefixEnd_3566938 : Nat := 4983230072969 + 3 ^ 40 * 3566938 * 2
def baseEnd_3566938 : Nat := 1831553658787070572370957

theorem tailTrace_3566938 : CollatzResearch.WordTrace tailWord_3566938 prefixEnd_3566938 1831553658787070572370957 := by
  unfold tailWord_3566938
  simp only [CollatzResearch.WordTrace]
  refine ⟨32524229187900071338963367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86731277834400190237235645 32524229187900071338963367)
  ·
    refine ⟨48786343781850107008445051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32524229187900071338963367 48786343781850107008445051)
    ·
      refine ⟨73179515672775160512667577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48786343781850107008445051 73179515672775160512667577)
      ·
        refine ⟨54884636754581370384500683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73179515672775160512667577 54884636754581370384500683)
        ·
          refine ⟨82326955131872055576751025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54884636754581370384500683 82326955131872055576751025)
          ·
            refine ⟨61745216348904041682563269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82326955131872055576751025 61745216348904041682563269)
            ·
              refine ⟨11577228065419507815480613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 61745216348904041682563269 11577228065419507815480613)
              ·
                refine ⟨2170730262266157715402615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11577228065419507815480613 2170730262266157715402615)
                ·
                  refine ⟨3256095393399236573103923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2170730262266157715402615 3256095393399236573103923)
                  ·
                    refine ⟨4884143090098854859655885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3256095393399236573103923 4884143090098854859655885)
                    ·
                      refine ⟨1831553658787070572370957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4884143090098854859655885 1831553658787070572370957)
                      ·
                        rfl

theorem cell23_3566938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 4, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 4, 4, 1, 1, 3].length) (baseStart_3566938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3566938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3566938 prefixEnd_3566938 := by exact prefixLift 3566938
  have htrace : WordTrace (prefixWord ++ tailWord_3566938) baseStart_3566938 baseEnd_3566938 := by
    simpa [prefixWord, tailWord_3566938, baseEnd_3566938] using wordTrace_append hprefix tailTrace_3566938
  have hstable : (prefixWord ++ tailWord_3566938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3566938).length < 2 ^ (prefixWord ++ tailWord_3566938).sum := by decide
  have hdescent : baseEnd_3566938 < baseStart_3566938 := by decide
  rcases family_descends (prefixWord ++ tailWord_3566938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3566967 : List Nat := [1, 1, 3, 1, 1, 2, 5, 9]
def baseStart_3566967 : Nat := 118140960795 + 3566967 * 2 ^ 59
def prefixEnd_3566967 : Nat := 4983230072969 + 3 ^ 40 * 3566967 * 2
def baseEnd_3566967 : Nat := 67835872212075961441049

theorem tailTrace_3566967 : CollatzResearch.WordTrace tailWord_3566967 prefixEnd_3566967 67835872212075961441049 := by
  unfold tailWord_3566967
  simp only [CollatzResearch.WordTrace]
  refine ⟨130097974468495223308659155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86731982978996815539106103 130097974468495223308659155)
  ·
    refine ⟨195146961702742834962988733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130097974468495223308659155 195146961702742834962988733)
    ·
      refine ⟨73180110638528563111120775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 195146961702742834962988733 73180110638528563111120775)
      ·
        refine ⟨109770165957792844666681163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73180110638528563111120775 109770165957792844666681163)
        ·
          refine ⟨164655248936689267000021745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109770165957792844666681163 164655248936689267000021745)
          ·
            refine ⟨123491436702516950250016309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 164655248936689267000021745 123491436702516950250016309)
            ·
              refine ⟨11577322190860964085939029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 123491436702516950250016309 11577322190860964085939029)
              ·
                refine ⟨67835872212075961441049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 11577322190860964085939029 67835872212075961441049)
                ·
                  rfl

theorem cell23_3566967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 5, 9].length) (baseStart_3566967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3566967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3566967 prefixEnd_3566967 := by exact prefixLift 3566967
  have htrace : WordTrace (prefixWord ++ tailWord_3566967) baseStart_3566967 baseEnd_3566967 := by
    simpa [prefixWord, tailWord_3566967, baseEnd_3566967] using wordTrace_append hprefix tailTrace_3566967
  have hstable : (prefixWord ++ tailWord_3566967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3566967).length < 2 ^ (prefixWord ++ tailWord_3566967).sum := by decide
  have hdescent : baseEnd_3566967 < baseStart_3566967 := by decide
  rcases family_descends (prefixWord ++ tailWord_3566967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3566981 : List Nat := [1, 3, 1, 1, 3, 1, 4, 3, 1, 2, 3]
def baseStart_3566981 : Nat := 118140960795 + 3566981 * 2 ^ 59
def prefixEnd_3566981 : Nat := 4983230072969 + 3 ^ 40 * 3566981 * 2
def baseEnd_3566981 : Nat := 1831575738455213904133259

theorem tailTrace_3566981 : CollatzResearch.WordTrace tailWord_3566981 prefixEnd_3566981 1831575738455213904133259 := by
  unfold tailWord_3566981
  simp only [CollatzResearch.WordTrace]
  refine ⟨130098485090444503699668797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86732323393629669133112531 130098485090444503699668797)
  ·
    refine ⟨48786931908916688887375799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130098485090444503699668797 48786931908916688887375799)
    ·
      refine ⟨73180397863375033331063699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48786931908916688887375799 73180397863375033331063699)
      ·
        refine ⟨109770596795062549996595549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73180397863375033331063699 109770596795062549996595549)
        ·
          refine ⟨41163973798148456248723331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 109770596795062549996595549 41163973798148456248723331)
          ·
            refine ⟨61745960697222684373084997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41163973798148456248723331 61745960697222684373084997)
            ·
              refine ⟨11577367630729253319953437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 61745960697222684373084997 11577367630729253319953437)
              ·
                refine ⟨4341512861523469994982539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11577367630729253319953437 4341512861523469994982539)
                ·
                  refine ⟨6512269292285204992473809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4341512861523469994982539 6512269292285204992473809)
                  ·
                    refine ⟨4884201969213903744355357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6512269292285204992473809 4884201969213903744355357)
                    ·
                      refine ⟨1831575738455213904133259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4884201969213903744355357 1831575738455213904133259)
                      ·
                        rfl

theorem cell23_3566981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 4, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 4, 3, 1, 2, 3].length) (baseStart_3566981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3566981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3566981 prefixEnd_3566981 := by exact prefixLift 3566981
  have htrace : WordTrace (prefixWord ++ tailWord_3566981) baseStart_3566981 baseEnd_3566981 := by
    simpa [prefixWord, tailWord_3566981, baseEnd_3566981] using wordTrace_append hprefix tailTrace_3566981
  have hstable : (prefixWord ++ tailWord_3566981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3566981).length < 2 ^ (prefixWord ++ tailWord_3566981).sum := by decide
  have hdescent : baseEnd_3566981 < baseStart_3566981 := by decide
  rcases family_descends (prefixWord ++ tailWord_3566981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3566984 : List Nat := [2, 1, 3, 3, 1, 4, 9]
def baseStart_3566984 : Nat := 118140960795 + 3566984 * 2 ^ 59
def prefixEnd_3566984 : Nat := 4983230072969 + 3 ^ 40 * 3566984 * 2
def baseEnd_3566984 : Nat := 22612065171570091264145

theorem tailTrace_3566984 : CollatzResearch.WordTrace tailWord_3566984 prefixEnd_3566984 22612065171570091264145 := by
  unfold tailWord_3566984
  simp only [CollatzResearch.WordTrace]
  refine ⟨65049297254716817606014003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86732396339622423474685337 65049297254716817606014003)
  ·
    refine ⟨97573945882075226409021005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65049297254716817606014003 97573945882075226409021005)
    ·
      refine ⟨36590229705778209903382877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 97573945882075226409021005 36590229705778209903382877)
      ·
        refine ⟨13721336139666828713768579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36590229705778209903382877 13721336139666828713768579)
        ·
          refine ⟨20582004209500243070652869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13721336139666828713768579 20582004209500243070652869)
          ·
            refine ⟨3859125789281295575747413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20582004209500243070652869 3859125789281295575747413)
            ·
              refine ⟨22612065171570091264145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3859125789281295575747413 22612065171570091264145)
              ·
                rfl

theorem cell23_3566984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 4, 9].length) (baseStart_3566984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3566984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3566984 prefixEnd_3566984 := by exact prefixLift 3566984
  have htrace : WordTrace (prefixWord ++ tailWord_3566984) baseStart_3566984 baseEnd_3566984 := by
    simpa [prefixWord, tailWord_3566984, baseEnd_3566984] using wordTrace_append hprefix tailTrace_3566984
  have hstable : (prefixWord ++ tailWord_3566984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3566984).length < 2 ^ (prefixWord ++ tailWord_3566984).sum := by decide
  have hdescent : baseEnd_3566984 < baseStart_3566984 := by decide
  rcases family_descends (prefixWord ++ tailWord_3566984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3567005 : List Nat := [1, 4, 2, 1, 3, 3, 2, 1, 2, 4]
def baseStart_3567005 : Nat := 118140960795 + 3567005 * 2 ^ 59
def prefixEnd_3567005 : Nat := 4983230072969 + 3 ^ 40 * 3567005 * 2
def baseEnd_3567005 : Nat := 610529353996973936744383

theorem tailTrace_3567005 : CollatzResearch.WordTrace tailWord_3567005 prefixEnd_3567005 610529353996973936744383 := by
  unfold tailWord_3567005
  simp only [CollatzResearch.WordTrace]
  refine ⟨130099360442357555798542469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86732906961571703865694979 130099360442357555798542469)
  ·
    refine ⟨24393630082942041712226713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 130099360442357555798542469 24393630082942041712226713)
    ·
      refine ⟨18295222562206531284170035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24393630082942041712226713 18295222562206531284170035)
      ·
        refine ⟨27442833843309796926255053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18295222562206531284170035 27442833843309796926255053)
        ·
          refine ⟨10291062691241173847345645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27442833843309796926255053 10291062691241173847345645)
          ·
            refine ⟨3859148509215440192754617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10291062691241173847345645 3859148509215440192754617)
            ·
              refine ⟨2894361381911580144565963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3859148509215440192754617 2894361381911580144565963)
              ·
                refine ⟨4341542072867370216848945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2894361381911580144565963 4341542072867370216848945)
                ·
                  refine ⟨3256156554650527662636709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4341542072867370216848945 3256156554650527662636709)
                  ·
                    refine ⟨610529353996973936744383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3256156554650527662636709 610529353996973936744383)
                    ·
                      rfl

theorem cell23_3567005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 3, 2, 1, 2, 4].length) (baseStart_3567005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3567005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3567005 prefixEnd_3567005 := by exact prefixLift 3567005
  have htrace : WordTrace (prefixWord ++ tailWord_3567005) baseStart_3567005 baseEnd_3567005 := by
    simpa [prefixWord, tailWord_3567005, baseEnd_3567005] using wordTrace_append hprefix tailTrace_3567005
  have hstable : (prefixWord ++ tailWord_3567005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3567005).length < 2 ^ (prefixWord ++ tailWord_3567005).sum := by decide
  have hdescent : baseEnd_3567005 < baseStart_3567005 := by decide
  rcases family_descends (prefixWord ++ tailWord_3567005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3567017 : List Nat := [1, 2, 1, 1, 1, 1, 3, 1, 1, 1, 10]
def baseStart_3567017 : Nat := 118140960795 + 3567017 * 2 ^ 59
def prefixEnd_3567017 : Nat := 4983230072969 + 3 ^ 40 * 3567017 * 2
def baseEnd_3567017 : Nat := 1831594223758775763283093

theorem tailTrace_3567017 : CollatzResearch.WordTrace tailWord_3567017 prefixEnd_3567017 1831594223758775763283093 := by
  unfold tailWord_3567017
  simp only [CollatzResearch.WordTrace]
  refine ⟨130099798118314081847979305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86733198745542721231986203 130099798118314081847979305)
  ·
    refine ⟨97574848588735561385984479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130099798118314081847979305 97574848588735561385984479)
    ·
      refine ⟨146362272883103342078976719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97574848588735561385984479 146362272883103342078976719)
      ·
        refine ⟨219543409324655013118465079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146362272883103342078976719 219543409324655013118465079)
        ·
          refine ⟨329315113986982519677697619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 219543409324655013118465079 329315113986982519677697619)
          ·
            refine ⟨493972670980473779516546429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 329315113986982519677697619 493972670980473779516546429)
            ·
              refine ⟨185239751617677667318704911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 493972670980473779516546429 185239751617677667318704911)
              ·
                refine ⟨277859627426516500978057367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 185239751617677667318704911 277859627426516500978057367)
                ·
                  refine ⟨416789441139774751467086051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 277859627426516500978057367 416789441139774751467086051)
                  ·
                    refine ⟨625184161709662127200629077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 416789441139774751467086051 625184161709662127200629077)
                    ·
                      refine ⟨1831594223758775763283093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 10 625184161709662127200629077 1831594223758775763283093)
                      ·
                        rfl

theorem cell23_3567017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 1, 1, 1, 10].length) (baseStart_3567017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3567017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3567017 prefixEnd_3567017 := by exact prefixLift 3567017
  have htrace : WordTrace (prefixWord ++ tailWord_3567017) baseStart_3567017 baseEnd_3567017 := by
    simpa [prefixWord, tailWord_3567017, baseEnd_3567017] using wordTrace_append hprefix tailTrace_3567017
  have hstable : (prefixWord ++ tailWord_3567017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3567017).length < 2 ^ (prefixWord ++ tailWord_3567017).sum := by decide
  have hdescent : baseEnd_3567017 < baseStart_3567017 := by decide
  rcases family_descends (prefixWord ++ tailWord_3567017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3567054 : List Nat := [4, 1, 1, 1, 2, 1, 2, 2, 1, 3, 5]
def baseStart_3567054 : Nat := 118140960795 + 3567054 * 2 ^ 59
def prefixEnd_3567054 : Nat := 4983230072969 + 3 ^ 40 * 3567054 * 2
def baseEnd_3567054 : Nat := 1831613222542992118520423

theorem tailTrace_3567054 : CollatzResearch.WordTrace tailWord_3567054 prefixEnd_3567054 1831613222542992118520423 := by
  unfold tailWord_3567054
  simp only [CollatzResearch.WordTrace]
  refine ⟨16262643452397504645884527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 86734098412786691444717477 16262643452397504645884527)
  ·
    refine ⟨24393965178596256968826791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16262643452397504645884527 24393965178596256968826791)
    ·
      refine ⟨36590947767894385453240187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24393965178596256968826791 36590947767894385453240187)
      ·
        refine ⟨54886421651841578179860281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36590947767894385453240187 54886421651841578179860281)
        ·
          refine ⟨41164816238881183634895211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54886421651841578179860281 41164816238881183634895211)
          ·
            refine ⟨61747224358321775452342817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41164816238881183634895211 61747224358321775452342817)
            ·
              refine ⟨46310418268741331589257113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61747224358321775452342817 46310418268741331589257113)
              ·
                refine ⟨34732813701555998691942835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46310418268741331589257113 34732813701555998691942835)
                ·
                  refine ⟨52099220552333998037914253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34732813701555998691942835 52099220552333998037914253)
                  ·
                    refine ⟨19537207707125249264217845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 52099220552333998037914253 19537207707125249264217845)
                    ·
                      refine ⟨1831613222542992118520423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19537207707125249264217845 1831613222542992118520423)
                      ·
                        rfl

theorem cell23_3567054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 2, 1, 3, 5].length) (baseStart_3567054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3567054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3567054 prefixEnd_3567054 := by exact prefixLift 3567054
  have htrace : WordTrace (prefixWord ++ tailWord_3567054) baseStart_3567054 baseEnd_3567054 := by
    simpa [prefixWord, tailWord_3567054, baseEnd_3567054] using wordTrace_append hprefix tailTrace_3567054
  have hstable : (prefixWord ++ tailWord_3567054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3567054).length < 2 ^ (prefixWord ++ tailWord_3567054).sum := by decide
  have hdescent : baseEnd_3567054 < baseStart_3567054 := by decide
  rcases family_descends (prefixWord ++ tailWord_3567054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3567064 : List Nat := [2, 1, 2, 2, 2, 1, 3, 1, 1, 4, 4]
def baseStart_3567064 : Nat := 118140960795 + 3567064 * 2 ^ 59
def prefixEnd_3567064 : Nat := 4983230072969 + 3 ^ 40 * 3567064 * 2
def baseEnd_3567064 : Nat := 1831618357349537079395377

theorem tailTrace_3567064 : CollatzResearch.WordTrace tailWord_3567064 prefixEnd_3567064 1831618357349537079395377 := by
  unfold tailWord_3567064
  simp only [CollatzResearch.WordTrace]
  refine ⟨65050756174571904437470123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86734341566095872583293497 65050756174571904437470123)
  ·
    refine ⟨97576134261857856656205185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65050756174571904437470123 97576134261857856656205185)
    ·
      refine ⟨73182100696393392492153889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97576134261857856656205185 73182100696393392492153889)
      ·
        refine ⟨54886575522295044369115417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73182100696393392492153889 54886575522295044369115417)
        ·
          refine ⟨41164931641721283276836563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54886575522295044369115417 41164931641721283276836563)
          ·
            refine ⟨61747397462581924915254845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41164931641721283276836563 61747397462581924915254845)
            ·
              refine ⟨23155274048468221843220567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61747397462581924915254845 23155274048468221843220567)
              ·
                refine ⟨34732911072702332764830851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23155274048468221843220567 34732911072702332764830851)
                ·
                  refine ⟨52099366609053499147246277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34732911072702332764830851 52099366609053499147246277)
                  ·
                    refine ⟨9768631239197531090108677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 52099366609053499147246277 9768631239197531090108677)
                    ·
                      refine ⟨1831618357349537079395377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9768631239197531090108677 1831618357349537079395377)
                      ·
                        rfl

theorem cell23_3567064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 3, 1, 1, 4, 4].length) (baseStart_3567064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3567064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3567064 prefixEnd_3567064 := by exact prefixLift 3567064
  have htrace : WordTrace (prefixWord ++ tailWord_3567064) baseStart_3567064 baseEnd_3567064 := by
    simpa [prefixWord, tailWord_3567064, baseEnd_3567064] using wordTrace_append hprefix tailTrace_3567064
  have hstable : (prefixWord ++ tailWord_3567064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3567064).length < 2 ^ (prefixWord ++ tailWord_3567064).sum := by decide
  have hdescent : baseEnd_3567064 < baseStart_3567064 := by decide
  rcases family_descends (prefixWord ++ tailWord_3567064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3567101 : List Nat := [1, 4, 1, 1, 1, 4, 1, 2, 2, 3, 3]
def baseStart_3567101 : Nat := 118140960795 + 3567101 * 2 ^ 59
def prefixEnd_3567101 : Nat := 4983230072969 + 3 ^ 40 * 3567101 * 2
def baseEnd_3567101 : Nat := 1831637356133753434632707

theorem tailTrace_3567101 : CollatzResearch.WordTrace tailWord_3567101 prefixEnd_3567101 1831637356133753434632707 := by
  unfold tailWord_3567101
  simp only [CollatzResearch.WordTrace]
  refine ⟨130102861850009764194037157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86735241233339842796024771 130102861850009764194037157)
  ·
    refine ⟨24394286596876830786381967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 130102861850009764194037157 24394286596876830786381967)
    ·
      refine ⟨36591429895315246179572951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24394286596876830786381967 36591429895315246179572951)
      ·
        refine ⟨54887144842972869269359427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36591429895315246179572951 54887144842972869269359427)
        ·
          refine ⟨82330717264459303904039141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54887144842972869269359427 82330717264459303904039141)
          ·
            refine ⟨15437009487086119482007339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 82330717264459303904039141 15437009487086119482007339)
            ·
              refine ⟨23155514230629179223011009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15437009487086119482007339 23155514230629179223011009)
              ·
                refine ⟨17366635672971884417258257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23155514230629179223011009 17366635672971884417258257)
                ·
                  refine ⟨13024976754728913312943693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17366635672971884417258257 13024976754728913312943693)
                  ·
                    refine ⟨4884366283023342492353885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13024976754728913312943693 4884366283023342492353885)
                    ·
                      refine ⟨1831637356133753434632707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4884366283023342492353885 1831637356133753434632707)
                      ·
                        rfl

theorem cell23_3567101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 1, 2, 2, 3, 3].length) (baseStart_3567101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3567101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3567101 prefixEnd_3567101 := by exact prefixLift 3567101
  have htrace : WordTrace (prefixWord ++ tailWord_3567101) baseStart_3567101 baseEnd_3567101 := by
    simpa [prefixWord, tailWord_3567101, baseEnd_3567101] using wordTrace_append hprefix tailTrace_3567101
  have hstable : (prefixWord ++ tailWord_3567101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3567101).length < 2 ^ (prefixWord ++ tailWord_3567101).sum := by decide
  have hdescent : baseEnd_3567101 < baseStart_3567101 := by decide
  rcases family_descends (prefixWord ++ tailWord_3567101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3567108 : List Nat := [2, 3, 2, 3, 2, 1, 2, 1, 7]
def baseStart_3567108 : Nat := 118140960795 + 3567108 * 2 ^ 59
def prefixEnd_3567108 : Nat := 4983230072969 + 3 ^ 40 * 3567108 * 2
def baseEnd_3567108 : Nat := 203515661166481656360575

theorem tailTrace_3567108 : CollatzResearch.WordTrace tailWord_3567108 prefixEnd_3567108 203515661166481656360575 := by
  unfold tailWord_3567108
  simp only [CollatzResearch.WordTrace]
  refine ⟨65051558580492202194770989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86735411440656269593027985 65051558580492202194770989)
  ·
    refine ⟨24394334467684575823039121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65051558580492202194770989 24394334467684575823039121)
    ·
      refine ⟨18295750850763431867279341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24394334467684575823039121 18295750850763431867279341)
      ·
        refine ⟨6860906569036286950229753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18295750850763431867279341 6860906569036286950229753)
        ·
          refine ⟨5145679926777215212672315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6860906569036286950229753 5145679926777215212672315)
          ·
            refine ⟨7718519890165822819008473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5145679926777215212672315 7718519890165822819008473)
            ·
              refine ⟨5788889917624367114256355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7718519890165822819008473 5788889917624367114256355)
              ·
                refine ⟨8683334876436550671384533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5788889917624367114256355 8683334876436550671384533)
                ·
                  refine ⟨203515661166481656360575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8683334876436550671384533 203515661166481656360575)
                  ·
                    rfl

theorem cell23_3567108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 2, 1, 7].length) (baseStart_3567108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3567108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3567108 prefixEnd_3567108 := by exact prefixLift 3567108
  have htrace : WordTrace (prefixWord ++ tailWord_3567108) baseStart_3567108 baseEnd_3567108 := by
    simpa [prefixWord, tailWord_3567108, baseEnd_3567108] using wordTrace_append hprefix tailTrace_3567108
  have hstable : (prefixWord ++ tailWord_3567108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3567108).length < 2 ^ (prefixWord ++ tailWord_3567108).sum := by decide
  have hdescent : baseEnd_3567108 < baseStart_3567108 := by decide
  rcases family_descends (prefixWord ++ tailWord_3567108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3567141 : List Nat := [1, 3, 1, 2, 2, 1, 1, 5, 2, 1, 4]
def baseStart_3567141 : Nat := 118140960795 + 3567141 * 2 ^ 59
def prefixEnd_3567141 : Nat := 4983230072969 + 3 ^ 40 * 3567141 * 2
def baseEnd_3567141 : Nat := 1831657895359933278132523

theorem tailTrace_3567141 : CollatzResearch.WordTrace tailWord_3567141 prefixEnd_3567141 1831657895359933278132523 := by
  unfold tailWord_3567141
  simp only [CollatzResearch.WordTrace]
  refine ⟨130104320769864851025493277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86736213846576567350328851 130104320769864851025493277)
  ·
    refine ⟨48789120288699319134559979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130104320769864851025493277 48789120288699319134559979)
    ·
      refine ⟨73183680433048978701839969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48789120288699319134559979 73183680433048978701839969)
      ·
        refine ⟨54887760324786734026379977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73183680433048978701839969 54887760324786734026379977)
        ·
          refine ⟨41165820243590050519784983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54887760324786734026379977 41165820243590050519784983)
          ·
            refine ⟨61748730365385075779677475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41165820243590050519784983 61748730365385075779677475)
            ·
              refine ⟨92623095548077613669516213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61748730365385075779677475 92623095548077613669516213)
              ·
                refine ⟨8683415207632276281517145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 92623095548077613669516213 8683415207632276281517145)
                ·
                  refine ⟨6512561405724207211137859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8683415207632276281517145 6512561405724207211137859)
                  ·
                    refine ⟨9768842108586310816706789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6512561405724207211137859 9768842108586310816706789)
                    ·
                      refine ⟨1831657895359933278132523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9768842108586310816706789 1831657895359933278132523)
                      ·
                        rfl

theorem cell23_3567141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 5, 2, 1, 4].length) (baseStart_3567141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3567141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3567141 prefixEnd_3567141 := by exact prefixLift 3567141
  have htrace : WordTrace (prefixWord ++ tailWord_3567141) baseStart_3567141 baseEnd_3567141 := by
    simpa [prefixWord, tailWord_3567141, baseEnd_3567141] using wordTrace_append hprefix tailTrace_3567141
  have hstable : (prefixWord ++ tailWord_3567141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3567141).length < 2 ^ (prefixWord ++ tailWord_3567141).sum := by decide
  have hdescent : baseEnd_3567141 < baseStart_3567141 := by decide
  rcases family_descends (prefixWord ++ tailWord_3567141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3567241 : List Nat := [1, 2, 1, 1, 4, 1, 3, 3, 1, 6]
def baseStart_3567241 : Nat := 118140960795 + 3567241 * 2 ^ 59
def prefixEnd_3567241 : Nat := 4983230072969 + 3 ^ 40 * 3567241 * 2
def baseEnd_3567241 : Nat := 610569747808460962294021

theorem tailTrace_3567241 : CollatzResearch.WordTrace tailWord_3567241 prefixEnd_3567241 610569747808460962294021 := by
  unfold tailWord_3567241
  simp only [CollatzResearch.WordTrace]
  refine ⟨130107968069502568104133577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86738645379668378736089051 130107968069502568104133577)
  ·
    refine ⟨97580976052126926078100183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130107968069502568104133577 97580976052126926078100183)
    ·
      refine ⟨146371464078190389117150275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97580976052126926078100183 146371464078190389117150275)
      ·
        refine ⟨219557196117285583675725413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146371464078190389117150275 219557196117285583675725413)
        ·
          refine ⟨41166974271991046939198515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 219557196117285583675725413 41166974271991046939198515)
          ·
            refine ⟨61750461407986570408797773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41166974271991046939198515 61750461407986570408797773)
            ·
              refine ⟨23156423027994963903299165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61750461407986570408797773 23156423027994963903299165)
              ·
                refine ⟨8683658635498111463737187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23156423027994963903299165 8683658635498111463737187)
                ·
                  refine ⟨13025487953247167195605781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8683658635498111463737187 13025487953247167195605781)
                  ·
                    refine ⟨610569747808460962294021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13025487953247167195605781 610569747808460962294021)
                    ·
                      rfl

theorem cell23_3567241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 3, 3, 1, 6].length) (baseStart_3567241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3567241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3567241 prefixEnd_3567241 := by exact prefixLift 3567241
  have htrace : WordTrace (prefixWord ++ tailWord_3567241) baseStart_3567241 baseEnd_3567241 := by
    simpa [prefixWord, tailWord_3567241, baseEnd_3567241] using wordTrace_append hprefix tailTrace_3567241
  have hstable : (prefixWord ++ tailWord_3567241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3567241).length < 2 ^ (prefixWord ++ tailWord_3567241).sum := by decide
  have hdescent : baseEnd_3567241 < baseStart_3567241 := by decide
  rcases family_descends (prefixWord ++ tailWord_3567241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3567252 : List Nat := [2, 4, 2, 2, 2, 1, 1, 1, 1, 5, 2]
def baseStart_3567252 : Nat := 118140960795 + 3567252 * 2 ^ 59
def prefixEnd_3567252 : Nat := 4983230072969 + 3 ^ 40 * 3567252 * 2
def baseEnd_3567252 : Nat := 1831714891712582343844513

theorem tailTrace_3567252 : CollatzResearch.WordTrace tailWord_3567252 prefixEnd_3567252 1831714891712582343844513 := by
  unfold tailWord_3567252
  simp only [CollatzResearch.WordTrace]
  refine ⟨65054184636231358491392005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86738912848308477988522673 65054184636231358491392005)
  ·
    refine ⟨12197659619293379717136001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 65054184636231358491392005 12197659619293379717136001)
    ·
      refine ⟨9148244714470034787852001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12197659619293379717136001 9148244714470034787852001)
      ·
        refine ⟨6861183535852526090889001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9148244714470034787852001 6861183535852526090889001)
        ·
          refine ⟨5145887651889394568166751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6861183535852526090889001 5145887651889394568166751)
          ·
            refine ⟨7718831477834091852250127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5145887651889394568166751 7718831477834091852250127)
            ·
              refine ⟨11578247216751137778375191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7718831477834091852250127 11578247216751137778375191)
              ·
                refine ⟨17367370825126706667562787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11578247216751137778375191 17367370825126706667562787)
                ·
                  refine ⟨26051056237690060001344181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17367370825126706667562787 26051056237690060001344181)
                  ·
                    refine ⟨2442286522283443125126017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 26051056237690060001344181 2442286522283443125126017)
                    ·
                      refine ⟨1831714891712582343844513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2442286522283443125126017 1831714891712582343844513)
                      ·
                        rfl

theorem cell23_3567252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 1, 1, 1, 5, 2].length) (baseStart_3567252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3567252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3567252 prefixEnd_3567252 := by exact prefixLift 3567252
  have htrace : WordTrace (prefixWord ++ tailWord_3567252) baseStart_3567252 baseEnd_3567252 := by
    simpa [prefixWord, tailWord_3567252, baseEnd_3567252] using wordTrace_append hprefix tailTrace_3567252
  have hstable : (prefixWord ++ tailWord_3567252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3567252).length < 2 ^ (prefixWord ++ tailWord_3567252).sum := by decide
  have hdescent : baseEnd_3567252 < baseStart_3567252 := by decide
  rcases family_descends (prefixWord ++ tailWord_3567252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3567261 : List Nat := [1, 4, 2, 1, 1, 1, 1, 2, 3, 1, 6]
def baseStart_3567261 : Nat := 118140960795 + 3567261 * 2 ^ 59
def prefixEnd_3567261 : Nat := 4983230072969 + 3 ^ 40 * 3567261 * 2
def baseEnd_3567261 : Nat := 1831719513038472808631971

theorem tailTrace_3567261 : CollatzResearch.WordTrace tailWord_3567261 prefixEnd_3567261 1831719513038472808631971 := by
  unfold tailWord_3567261
  simp only [CollatzResearch.WordTrace]
  refine ⟨130108697529430111519861637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86739131686286741013241091 130108697529430111519861637)
  ·
    refine ⟨24395380786768145909974057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 130108697529430111519861637 24395380786768145909974057)
    ·
      refine ⟨18296535590076109432480543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24395380786768145909974057 18296535590076109432480543)
      ·
        refine ⟨27444803385114164148720815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18296535590076109432480543 27444803385114164148720815)
        ·
          refine ⟨41167205077671246223081223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27444803385114164148720815 41167205077671246223081223)
          ·
            refine ⟨61750807616506869334621835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41167205077671246223081223 61750807616506869334621835)
            ·
              refine ⟨92626211424760304001932753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61750807616506869334621835 92626211424760304001932753)
              ·
                refine ⟨69469658568570228001449565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 92626211424760304001932753 69469658568570228001449565)
                ·
                  refine ⟨26051121963213835500543587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 69469658568570228001449565 26051121963213835500543587)
                  ·
                    refine ⟨39076682944820753250815381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26051121963213835500543587 39076682944820753250815381)
                    ·
                      refine ⟨1831719513038472808631971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 39076682944820753250815381 1831719513038472808631971)
                      ·
                        rfl

theorem cell23_3567261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 2, 3, 1, 6].length) (baseStart_3567261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3567261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3567261 prefixEnd_3567261 := by exact prefixLift 3567261
  have htrace : WordTrace (prefixWord ++ tailWord_3567261) baseStart_3567261 baseEnd_3567261 := by
    simpa [prefixWord, tailWord_3567261, baseEnd_3567261] using wordTrace_append hprefix tailTrace_3567261
  have hstable : (prefixWord ++ tailWord_3567261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3567261).length < 2 ^ (prefixWord ++ tailWord_3567261).sum := by decide
  have hdescent : baseEnd_3567261 < baseStart_3567261 := by decide
  rcases family_descends (prefixWord ++ tailWord_3567261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3567262 : List Nat := [4, 3, 1, 1, 1, 2, 4, 1, 1, 5]
def baseStart_3567262 : Nat := 118140960795 + 3567262 * 2 ^ 59
def prefixEnd_3567262 : Nat := 4983230072969 + 3 ^ 40 * 3567262 * 2
def baseEnd_3567262 : Nat := 610573342173042434906489

theorem tailTrace_3567262 : CollatzResearch.WordTrace tailWord_3567262 prefixEnd_3567262 610573342173042434906489 := by
  unfold tailWord_3567262
  simp only [CollatzResearch.WordTrace]
  refine ⟨16263591750303311086331005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 86739156001617659127098693 16263591750303311086331005)
  ·
    refine ⟨6098846906363741657374127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16263591750303311086331005 6098846906363741657374127)
    ·
      refine ⟨9148270359545612486061191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6098846906363741657374127 9148270359545612486061191)
      ·
        refine ⟨13722405539318418729091787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9148270359545612486061191 13722405539318418729091787)
        ·
          refine ⟨20583608308977628093637681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13722405539318418729091787 20583608308977628093637681)
          ·
            refine ⟨15437706231733221070228261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20583608308977628093637681 15437706231733221070228261)
            ·
              refine ⟨2894569918449978950667799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15437706231733221070228261 2894569918449978950667799)
              ·
                refine ⟨4341854877674968426001699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2894569918449978950667799 4341854877674968426001699)
                ·
                  refine ⟨6512782316512452639002549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4341854877674968426001699 6512782316512452639002549)
                  ·
                    refine ⟨610573342173042434906489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6512782316512452639002549 610573342173042434906489)
                    ·
                      rfl

theorem cell23_3567262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 4, 1, 1, 5].length) (baseStart_3567262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3567262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3567262 prefixEnd_3567262 := by exact prefixLift 3567262
  have htrace : WordTrace (prefixWord ++ tailWord_3567262) baseStart_3567262 baseEnd_3567262 := by
    simpa [prefixWord, tailWord_3567262, baseEnd_3567262] using wordTrace_append hprefix tailTrace_3567262
  have hstable : (prefixWord ++ tailWord_3567262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3567262).length < 2 ^ (prefixWord ++ tailWord_3567262).sum := by decide
  have hdescent : baseEnd_3567262 < baseStart_3567262 := by decide
  rcases family_descends (prefixWord ++ tailWord_3567262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3567265 : List Nat := [1, 2, 3, 3, 2, 2, 1, 3, 1, 1, 4]
def baseStart_3567265 : Nat := 118140960795 + 3567265 * 2 ^ 59
def prefixEnd_3567265 : Nat := 4983230072969 + 3 ^ 40 * 3567265 * 2
def baseEnd_3567265 : Nat := 1831721566961090792981953

theorem tailTrace_3567265 : CollatzResearch.WordTrace tailWord_3567265 prefixEnd_3567265 1831721566961090792981953 := by
  unfold tailWord_3567265
  simp only [CollatzResearch.WordTrace]
  refine ⟨130108843421415620203007249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86739228947610413468671499 130108843421415620203007249)
  ·
    refine ⟨97581632566061715152255437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130108843421415620203007249 97581632566061715152255437)
    ·
      refine ⟨36593112212273143182095789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 97581632566061715152255437 36593112212273143182095789)
      ·
        refine ⟨13722417079602428693285921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36593112212273143182095789 13722417079602428693285921)
        ·
          refine ⟨10291812809701821519964441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13722417079602428693285921 10291812809701821519964441)
          ·
            refine ⟨7718859607276366139973331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10291812809701821519964441 7718859607276366139973331)
            ·
              refine ⟨11578289410914549209959997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7718859607276366139973331 11578289410914549209959997)
              ·
                refine ⟨4341858529092955953734999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11578289410914549209959997 4341858529092955953734999)
                ·
                  refine ⟨6512787793639433930602499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4341858529092955953734999 6512787793639433930602499)
                  ·
                    refine ⟨9769181690459150895903749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6512787793639433930602499 9769181690459150895903749)
                    ·
                      refine ⟨1831721566961090792981953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9769181690459150895903749 1831721566961090792981953)
                      ·
                        rfl

theorem cell23_3567265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 1, 3, 1, 1, 4].length) (baseStart_3567265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3567265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3567265 prefixEnd_3567265 := by exact prefixLift 3567265
  have htrace : WordTrace (prefixWord ++ tailWord_3567265) baseStart_3567265 baseEnd_3567265 := by
    simpa [prefixWord, tailWord_3567265, baseEnd_3567265] using wordTrace_append hprefix tailTrace_3567265
  have hstable : (prefixWord ++ tailWord_3567265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3567265).length < 2 ^ (prefixWord ++ tailWord_3567265).sum := by decide
  have hdescent : baseEnd_3567265 < baseStart_3567265 := by decide
  rcases family_descends (prefixWord ++ tailWord_3567265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3567285 : List Nat := [1, 3, 3, 3, 2, 1, 1, 2, 1, 1, 5]
def baseStart_3567285 : Nat := 118140960795 + 3567285 * 2 ^ 59
def prefixEnd_3567285 : Nat := 4983230072969 + 3 ^ 40 * 3567285 * 2
def baseEnd_3567285 : Nat := 1831731836574180714731861

theorem tailTrace_3567285 : CollatzResearch.WordTrace tailWord_3567285 prefixEnd_3567285 1831731836574180714731861 := by
  unfold tailWord_3567285
  simp only [CollatzResearch.WordTrace]
  refine ⟨130109572881343163618735309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86739715254228775745823539 130109572881343163618735309)
  ·
    refine ⟨48791089830503686357025741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130109572881343163618735309 48791089830503686357025741)
    ·
      refine ⟨18296658686438882383884653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48791089830503686357025741 18296658686438882383884653)
      ·
        refine ⟨6861247007414580893956745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18296658686438882383884653 6861247007414580893956745)
        ·
          refine ⟨5145935255560935670467559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6861247007414580893956745 5145935255560935670467559)
          ·
            refine ⟨7718902883341403505701339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5145935255560935670467559 7718902883341403505701339)
            ·
              refine ⟨11578354325012105258552009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7718902883341403505701339 11578354325012105258552009)
              ·
                refine ⟨8683765743759078943914007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11578354325012105258552009 8683765743759078943914007)
                ·
                  refine ⟨13025648615638618415871011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8683765743759078943914007 13025648615638618415871011)
                  ·
                    refine ⟨19538472923457927623806517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13025648615638618415871011 19538472923457927623806517)
                    ·
                      refine ⟨1831731836574180714731861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19538472923457927623806517 1831731836574180714731861)
                      ·
                        rfl

theorem cell23_3567285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 1, 2, 1, 1, 5].length) (baseStart_3567285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3567285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3567285 prefixEnd_3567285 := by exact prefixLift 3567285
  have htrace : WordTrace (prefixWord ++ tailWord_3567285) baseStart_3567285 baseEnd_3567285 := by
    simpa [prefixWord, tailWord_3567285, baseEnd_3567285] using wordTrace_append hprefix tailTrace_3567285
  have hstable : (prefixWord ++ tailWord_3567285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3567285).length < 2 ^ (prefixWord ++ tailWord_3567285).sum := by decide
  have hdescent : baseEnd_3567285 < baseStart_3567285 := by decide
  rcases family_descends (prefixWord ++ tailWord_3567285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3567292 : List Nat := [2, 2, 2, 3, 1, 3, 3, 1, 2, 4]
def baseStart_3567292 : Nat := 118140960795 + 3567292 * 2 ^ 59
def prefixEnd_3567292 : Nat := 4983230072969 + 3 ^ 40 * 3567292 * 2
def baseEnd_3567292 : Nat := 610578476979587395781443

theorem tailTrace_3567292 : CollatzResearch.WordTrace tailWord_3567292 prefixEnd_3567292 610578476979587395781443 := by
  unfold tailWord_3567292
  simp only [CollatzResearch.WordTrace]
  refine ⟨65054914096158901907120065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86739885461545202542826753 65054914096158901907120065)
  ·
    refine ⟨48791185572119176430340049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65054914096158901907120065 48791185572119176430340049)
    ·
      refine ⟨36593389179089382322755037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48791185572119176430340049 36593389179089382322755037)
      ·
        refine ⟨13722520942158518371033139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36593389179089382322755037 13722520942158518371033139)
        ·
          refine ⟨20583781413237777556549709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13722520942158518371033139 20583781413237777556549709)
          ·
            refine ⟨7718918029964166583706141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20583781413237777556549709 7718918029964166583706141)
            ·
              refine ⟨2894594261236562468889803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7718918029964166583706141 2894594261236562468889803)
              ·
                refine ⟨4341891391854843703334705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2894594261236562468889803 4341891391854843703334705)
                ·
                  refine ⟨3256418543891132777501029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4341891391854843703334705 3256418543891132777501029)
                  ·
                    refine ⟨610578476979587395781443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3256418543891132777501029 610578476979587395781443)
                    ·
                      rfl

theorem cell23_3567292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 3, 1, 2, 4].length) (baseStart_3567292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3567292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3567292 prefixEnd_3567292 := by exact prefixLift 3567292
  have htrace : WordTrace (prefixWord ++ tailWord_3567292) baseStart_3567292 baseEnd_3567292 := by
    simpa [prefixWord, tailWord_3567292, baseEnd_3567292] using wordTrace_append hprefix tailTrace_3567292
  have hstable : (prefixWord ++ tailWord_3567292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3567292).length < 2 ^ (prefixWord ++ tailWord_3567292).sum := by decide
  have hdescent : baseEnd_3567292 < baseStart_3567292 := by decide
  rcases family_descends (prefixWord ++ tailWord_3567292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3567316 : List Nat := [2, 4, 1, 3, 1, 1, 3, 3, 1, 2, 2]
def baseStart_3567316 : Nat := 118140960795 + 3567316 * 2 ^ 59
def prefixEnd_3567316 : Nat := 4983230072969 + 3 ^ 40 * 3567316 * 2
def baseEnd_3567316 : Nat := 1831747754474470093444219

theorem tailTrace_3567316 : CollatzResearch.WordTrace tailWord_3567316 prefixEnd_3567316 1831747754474470093444219 := by
  unfold tailWord_3567316
  simp only [CollatzResearch.WordTrace]
  refine ⟨65055351772115427956556901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86740469029487237275409201 65055351772115427956556901)
  ·
    refine ⟨12197878457271642741854419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 65055351772115427956556901 12197878457271642741854419)
    ·
      refine ⟨18296817685907464112781629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12197878457271642741854419 18296817685907464112781629)
      ·
        refine ⟨6861306632215299042293111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18296817685907464112781629 6861306632215299042293111)
        ·
          refine ⟨10291959948322948563439667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6861306632215299042293111 10291959948322948563439667)
          ·
            refine ⟨15437939922484422845159501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10291959948322948563439667 15437939922484422845159501)
            ·
              refine ⟨5789227470931658566934813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15437939922484422845159501 5789227470931658566934813)
              ·
                refine ⟨2170960301599371962600555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5789227470931658566934813 2170960301599371962600555)
                ·
                  refine ⟨3256440452399057943900833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2170960301599371962600555 3256440452399057943900833)
                  ·
                    refine ⟨2442330339299293457925625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3256440452399057943900833 2442330339299293457925625)
                    ·
                      refine ⟨1831747754474470093444219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2442330339299293457925625 1831747754474470093444219)
                      ·
                        rfl

theorem cell23_3567316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 3, 3, 1, 2, 2].length) (baseStart_3567316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3567316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3567316 prefixEnd_3567316 := by exact prefixLift 3567316
  have htrace : WordTrace (prefixWord ++ tailWord_3567316) baseStart_3567316 baseEnd_3567316 := by
    simpa [prefixWord, tailWord_3567316, baseEnd_3567316] using wordTrace_append hprefix tailTrace_3567316
  have hstable : (prefixWord ++ tailWord_3567316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3567316).length < 2 ^ (prefixWord ++ tailWord_3567316).sum := by decide
  have hdescent : baseEnd_3567316 < baseStart_3567316 := by decide
  rcases family_descends (prefixWord ++ tailWord_3567316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3567355 : List Nat := [1, 1, 1, 1, 1, 3, 1, 4, 6, 2, 2]
def baseStart_3567355 : Nat := 118140960795 + 3567355 * 2 ^ 59
def prefixEnd_3567355 : Nat := 4983230072969 + 3 ^ 40 * 3567355 * 2
def baseEnd_3567355 : Nat := 1831767780219995440856539

theorem tailTrace_3567355 : CollatzResearch.WordTrace tailWord_3567355 prefixEnd_3567355 1831767780219995440856539 := by
  unfold tailWord_3567355
  simp only [CollatzResearch.WordTrace]
  refine ⟨130112125991089565573783519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86741417327393043715855679 130112125991089565573783519)
  ·
    refine ⟨195168188986634348360675279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130112125991089565573783519 195168188986634348360675279)
    ·
      refine ⟨292752283479951522541012919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195168188986634348360675279 292752283479951522541012919)
      ·
        refine ⟨439128425219927283811519379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 292752283479951522541012919 439128425219927283811519379)
        ·
          refine ⟨658692637829890925717279069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 439128425219927283811519379 658692637829890925717279069)
          ·
            refine ⟨247009739186209097143979651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 658692637829890925717279069 247009739186209097143979651)
            ·
              refine ⟨370514608779313645715969477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 247009739186209097143979651 370514608779313645715969477)
              ·
                refine ⟨69471489146121308571744277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 370514608779313645715969477 69471489146121308571744277)
                ·
                  refine ⟨3256476053724436339300513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 69471489146121308571744277 3256476053724436339300513)
                  ·
                    refine ⟨2442357040293327254475385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3256476053724436339300513 2442357040293327254475385)
                    ·
                      refine ⟨1831767780219995440856539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2442357040293327254475385 1831767780219995440856539)
                      ·
                        rfl

theorem cell23_3567355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 4, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 4, 6, 2, 2].length) (baseStart_3567355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3567355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3567355 prefixEnd_3567355 := by exact prefixLift 3567355
  have htrace : WordTrace (prefixWord ++ tailWord_3567355) baseStart_3567355 baseEnd_3567355 := by
    simpa [prefixWord, tailWord_3567355, baseEnd_3567355] using wordTrace_append hprefix tailTrace_3567355
  have hstable : (prefixWord ++ tailWord_3567355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3567355).length < 2 ^ (prefixWord ++ tailWord_3567355).sum := by decide
  have hdescent : baseEnd_3567355 < baseStart_3567355 := by decide
  rcases family_descends (prefixWord ++ tailWord_3567355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3567455 : List Nat := [1, 1, 2, 3, 1, 4, 1, 3, 3, 4]
def baseStart_3567455 : Nat := 118140960795 + 3567455 * 2 ^ 59
def prefixEnd_3567455 : Nat := 4983230072969 + 3 ^ 40 * 3567455 * 2
def baseEnd_3567455 : Nat := 610606376095148349868693

theorem tailTrace_3567455 : CollatzResearch.WordTrace tailWord_3567455 prefixEnd_3567455 610606376095148349868693 := by
  unfold tailWord_3567455
  simp only [CollatzResearch.WordTrace]
  refine ⟨130115773290727282652423819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86743848860484855101615879 130115773290727282652423819)
  ·
    refine ⟨195173659936090923978635729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130115773290727282652423819 195173659936090923978635729)
    ·
      refine ⟨146380244952068192983976797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 195173659936090923978635729 146380244952068192983976797)
      ·
        refine ⟨54892591857025572368991299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 146380244952068192983976797 54892591857025572368991299)
        ·
          refine ⟨82338887785538358553486949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54892591857025572368991299 82338887785538358553486949)
          ·
            refine ⟨15438541459788442228778803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 82338887785538358553486949 15438541459788442228778803)
            ·
              refine ⟨23157812189682663343168205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15438541459788442228778803 23157812189682663343168205)
              ·
                refine ⟨8684179571130998753688077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23157812189682663343168205 8684179571130998753688077)
                ·
                  refine ⟨3256567339174124532633029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8684179571130998753688077 3256567339174124532633029)
                  ·
                    refine ⟨610606376095148349868693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3256567339174124532633029 610606376095148349868693)
                    ·
                      rfl

theorem cell23_3567455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 1, 3, 3, 4].length) (baseStart_3567455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3567455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3567455 prefixEnd_3567455 := by exact prefixLift 3567455
  have htrace : WordTrace (prefixWord ++ tailWord_3567455) baseStart_3567455 baseEnd_3567455 := by
    simpa [prefixWord, tailWord_3567455, baseEnd_3567455] using wordTrace_append hprefix tailTrace_3567455
  have hstable : (prefixWord ++ tailWord_3567455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3567455).length < 2 ^ (prefixWord ++ tailWord_3567455).sum := by decide
  have hdescent : baseEnd_3567455 < baseStart_3567455 := by decide
  rcases family_descends (prefixWord ++ tailWord_3567455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3567519 : List Nat := [1, 1, 2, 5, 3, 2, 2, 1, 6]
def baseStart_3567519 : Nat := 118140960795 + 3567519 * 2 ^ 59
def prefixEnd_3567519 : Nat := 4983230072969 + 3 ^ 40 * 3567519 * 2
def baseEnd_3567519 : Nat := 203539110116370311022865

theorem tailTrace_3567519 : CollatzResearch.WordTrace tailWord_3567519 prefixEnd_3567519 203539110116370311022865 := by
  unfold tailWord_3567519
  simp only [CollatzResearch.WordTrace]
  refine ⟨130118107562495421582753611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86745405041663614388502407 130118107562495421582753611)
  ·
    refine ⟨195177161343743132374130417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130118107562495421582753611 195177161343743132374130417)
    ·
      refine ⟨146382871007807349280597813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 195177161343743132374130417 146382871007807349280597813)
      ·
        refine ⟨13723394156981938995056045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 146382871007807349280597813 13723394156981938995056045)
        ·
          refine ⟨5146272808868227123146017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13723394156981938995056045 5146272808868227123146017)
          ·
            refine ⟨3859704606651170342359513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5146272808868227123146017 3859704606651170342359513)
            ·
              refine ⟨2894778454988377756769635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3859704606651170342359513 2894778454988377756769635)
              ·
                refine ⟨4342167682482566635154453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2894778454988377756769635 4342167682482566635154453)
                ·
                  refine ⟨203539110116370311022865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4342167682482566635154453 203539110116370311022865)
                  ·
                    rfl

theorem cell23_3567519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 2, 2, 1, 6].length) (baseStart_3567519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3567519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3567519 prefixEnd_3567519 := by exact prefixLift 3567519
  have htrace : WordTrace (prefixWord ++ tailWord_3567519) baseStart_3567519 baseEnd_3567519 := by
    simpa [prefixWord, tailWord_3567519, baseEnd_3567519] using wordTrace_append hprefix tailTrace_3567519
  have hstable : (prefixWord ++ tailWord_3567519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3567519).length < 2 ^ (prefixWord ++ tailWord_3567519).sum := by decide
  have hdescent : baseEnd_3567519 < baseStart_3567519 := by decide
  rcases family_descends (prefixWord ++ tailWord_3567519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3567535 : List Nat := [1, 1, 2, 1, 2, 2, 5, 1, 3, 1, 4]
def baseStart_3567535 : Nat := 118140960795 + 3567535 * 2 ^ 59
def prefixEnd_3567535 : Nat := 4983230072969 + 3 ^ 40 * 3567535 * 2
def baseEnd_3567535 : Nat := 1831860206737804736605711

theorem tailTrace_3567535 : CollatzResearch.WordTrace tailWord_3567535 prefixEnd_3567535 1831860206737804736605711 := by
  unfold tailWord_3567535
  simp only [CollatzResearch.WordTrace]
  refine ⟨130118691130437456315336059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86745794086958304210224039 130118691130437456315336059)
  ·
    refine ⟨195178036695656184473004089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130118691130437456315336059 195178036695656184473004089)
    ·
      refine ⟨146383527521742138354753067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 195178036695656184473004089 146383527521742138354753067)
      ·
        refine ⟨219575291282613207532129601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146383527521742138354753067 219575291282613207532129601)
        ·
          refine ⟨164681468461959905649097201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 219575291282613207532129601 164681468461959905649097201)
          ·
            refine ⟨123511101346469929236822901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 164681468461959905649097201 123511101346469929236822901)
            ·
              refine ⟨11579165751231555865952147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 123511101346469929236822901 11579165751231555865952147)
              ·
                refine ⟨17368748626847333798928221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11579165751231555865952147 17368748626847333798928221)
                ·
                  refine ⟨6513280735067750174598083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17368748626847333798928221 6513280735067750174598083)
                  ·
                    refine ⟨9769921102601625261897125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6513280735067750174598083 9769921102601625261897125)
                    ·
                      refine ⟨1831860206737804736605711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9769921102601625261897125 1831860206737804736605711)
                      ·
                        rfl

theorem cell23_3567535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 5, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 5, 1, 3, 1, 4].length) (baseStart_3567535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3567535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3567535 prefixEnd_3567535 := by exact prefixLift 3567535
  have htrace : WordTrace (prefixWord ++ tailWord_3567535) baseStart_3567535 baseEnd_3567535 := by
    simpa [prefixWord, tailWord_3567535, baseEnd_3567535] using wordTrace_append hprefix tailTrace_3567535
  have hstable : (prefixWord ++ tailWord_3567535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3567535).length < 2 ^ (prefixWord ++ tailWord_3567535).sum := by decide
  have hdescent : baseEnd_3567535 < baseStart_3567535 := by decide
  rcases family_descends (prefixWord ++ tailWord_3567535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3567545 : List Nat := [1, 2, 1, 4, 2, 1, 3, 2, 1, 6]
def baseStart_3567545 : Nat := 118140960795 + 3567545 * 2 ^ 59
def prefixEnd_3567545 : Nat := 4983230072969 + 3 ^ 40 * 3567545 * 2
def baseEnd_3567545 : Nat := 610621780514783232493555

theorem tailTrace_3567545 : CollatzResearch.WordTrace tailWord_3567545 prefixEnd_3567545 610621780514783232493555 := by
  unfold tailWord_3567545
  simp only [CollatzResearch.WordTrace]
  refine ⟨130119055860401228023200089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86746037240267485348800059 130119055860401228023200089)
  ·
    refine ⟨97589291895300921017400067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130119055860401228023200089 97589291895300921017400067)
    ·
      refine ⟨146383937842951381526100101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97589291895300921017400067 146383937842951381526100101)
      ·
        refine ⟨27446988345553384036143769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 146383937842951381526100101 27446988345553384036143769)
        ·
          refine ⟨20585241259165038027107827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27446988345553384036143769 20585241259165038027107827)
          ·
            refine ⟨30877861888747557040661741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20585241259165038027107827 30877861888747557040661741)
            ·
              refine ⟨11579198208280333890248153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30877861888747557040661741 11579198208280333890248153)
              ·
                refine ⟨8684398656210250417686115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11579198208280333890248153 8684398656210250417686115)
                ·
                  refine ⟨13026597984315375626529173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8684398656210250417686115 13026597984315375626529173)
                  ·
                    refine ⟨610621780514783232493555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13026597984315375626529173 610621780514783232493555)
                    ·
                      rfl

theorem cell23_3567545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 3, 2, 1, 6].length) (baseStart_3567545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3567545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3567545 prefixEnd_3567545 := by exact prefixLift 3567545
  have htrace : WordTrace (prefixWord ++ tailWord_3567545) baseStart_3567545 baseEnd_3567545 := by
    simpa [prefixWord, tailWord_3567545, baseEnd_3567545] using wordTrace_append hprefix tailTrace_3567545
  have hstable : (prefixWord ++ tailWord_3567545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3567545).length < 2 ^ (prefixWord ++ tailWord_3567545).sum := by decide
  have hdescent : baseEnd_3567545 < baseStart_3567545 := by decide
  rcases family_descends (prefixWord ++ tailWord_3567545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3567549 : List Nat := [1, 4, 1, 2, 3, 2, 3, 1, 1, 5]
def baseStart_3567549 : Nat := 118140960795 + 3567549 * 2 ^ 59
def prefixEnd_3567549 : Nat := 4983230072969 + 3 ^ 40 * 3567549 * 2
def baseEnd_3567549 : Nat := 610622465155655893943549

theorem tailTrace_3567549 : CollatzResearch.WordTrace tailWord_3567549 prefixEnd_3567549 610622465155655893943549 := by
  unfold tailWord_3567549
  simp only [CollatzResearch.WordTrace]
  refine ⟨130119201752386736706345701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86746134501591157804230467 130119201752386736706345701)
  ·
    refine ⟨24397350328572513132439819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 130119201752386736706345701 24397350328572513132439819)
    ·
      refine ⟨36596025492858769698659729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24397350328572513132439819 36596025492858769698659729)
      ·
        refine ⟨27447019119644077273994797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36596025492858769698659729 27447019119644077273994797)
        ·
          refine ⟨10292632169866528977748049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27447019119644077273994797 10292632169866528977748049)
          ·
            refine ⟨7719474127399896733311037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10292632169866528977748049 7719474127399896733311037)
            ·
              refine ⟨2894802797774961274991639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7719474127399896733311037 2894802797774961274991639)
              ·
                refine ⟨4342204196662441912487459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2894802797774961274991639 4342204196662441912487459)
                ·
                  refine ⟨6513306294993662868731189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4342204196662441912487459 6513306294993662868731189)
                  ·
                    refine ⟨610622465155655893943549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6513306294993662868731189 610622465155655893943549)
                    ·
                      rfl

theorem cell23_3567549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 3, 1, 1, 5].length) (baseStart_3567549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3567549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3567549 prefixEnd_3567549 := by exact prefixLift 3567549
  have htrace : WordTrace (prefixWord ++ tailWord_3567549) baseStart_3567549 baseEnd_3567549 := by
    simpa [prefixWord, tailWord_3567549, baseEnd_3567549] using wordTrace_append hprefix tailTrace_3567549
  have hstable : (prefixWord ++ tailWord_3567549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3567549).length < 2 ^ (prefixWord ++ tailWord_3567549).sum := by decide
  have hdescent : baseEnd_3567549 < baseStart_3567549 := by decide
  rcases family_descends (prefixWord ++ tailWord_3567549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3567555 : List Nat := [1, 1, 1, 3, 1, 1, 2, 1, 7, 2, 3]
def baseStart_3567555 : Nat := 118140960795 + 3567555 * 2 ^ 59
def prefixEnd_3567555 : Nat := 4983230072969 + 3 ^ 40 * 3567555 * 2
def baseEnd_3567555 : Nat := 1831870476350894658355619

theorem tailTrace_3567555 : CollatzResearch.WordTrace tailWord_3567555 prefixEnd_3567555 1831870476350894658355619 := by
  unfold tailWord_3567555
  simp only [CollatzResearch.WordTrace]
  refine ⟨130119420590364999731064119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86746280393576666487376079 130119420590364999731064119)
  ·
    refine ⟨195179130885547499596596179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130119420590364999731064119 195179130885547499596596179)
    ·
      refine ⟨292768696328321249394894269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195179130885547499596596179 292768696328321249394894269)
      ·
        refine ⟨109788261123120468523085351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 292768696328321249394894269 109788261123120468523085351)
        ·
          refine ⟨164682391684680702784628027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109788261123120468523085351 164682391684680702784628027)
          ·
            refine ⟨247023587527021054176942041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 164682391684680702784628027 247023587527021054176942041)
            ·
              refine ⟨185267690645265790632706531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 247023587527021054176942041 185267690645265790632706531)
              ·
                refine ⟨277901535967898685949059797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 185267690645265790632706531 277901535967898685949059797)
                ·
                  refine ⟨6513317249247625451931089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 277901535967898685949059797 6513317249247625451931089)
                  ·
                    refine ⟨4884987936935719088948317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6513317249247625451931089 4884987936935719088948317)
                    ·
                      refine ⟨1831870476350894658355619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4884987936935719088948317 1831870476350894658355619)
                      ·
                        rfl

theorem cell23_3567555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 1, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 1, 7, 2, 3].length) (baseStart_3567555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3567555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3567555 prefixEnd_3567555 := by exact prefixLift 3567555
  have htrace : WordTrace (prefixWord ++ tailWord_3567555) baseStart_3567555 baseEnd_3567555 := by
    simpa [prefixWord, tailWord_3567555, baseEnd_3567555] using wordTrace_append hprefix tailTrace_3567555
  have hstable : (prefixWord ++ tailWord_3567555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3567555).length < 2 ^ (prefixWord ++ tailWord_3567555).sum := by decide
  have hdescent : baseEnd_3567555 < baseStart_3567555 := by decide
  rcases family_descends (prefixWord ++ tailWord_3567555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3567562 : List Nat := [3, 1, 2, 1, 2, 1, 3, 4, 2, 4]
def baseStart_3567562 : Nat := 118140960795 + 3567562 * 2 ^ 59
def prefixEnd_3567562 : Nat := 4983230072969 + 3 ^ 40 * 3567562 * 2
def baseEnd_3567562 : Nat := 610624690238492043656029

theorem tailTrace_3567562 : CollatzResearch.WordTrace tailWord_3567562 prefixEnd_3567562 610624690238492043656029 := by
  unfold tailWord_3567562
  simp only [CollatzResearch.WordTrace]
  refine ⟨32529918975334909981642235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86746450600893093284379293 32529918975334909981642235)
  ·
    refine ⟨48794878463002364972463353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32529918975334909981642235 48794878463002364972463353)
    ·
      refine ⟨36596158847251773729347515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48794878463002364972463353 36596158847251773729347515)
      ·
        refine ⟨54894238270877660594021273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36596158847251773729347515 54894238270877660594021273)
        ·
          refine ⟨41170678703158245445515955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54894238270877660594021273 41170678703158245445515955)
          ·
            refine ⟨61756018054737368168273933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41170678703158245445515955 61756018054737368168273933)
            ·
              refine ⟨23158506770526513063102725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61756018054737368168273933 23158506770526513063102725)
              ·
                refine ⟨4342220019473721199331761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23158506770526513063102725 4342220019473721199331761)
                ·
                  refine ⟨3256665014605290899498821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4342220019473721199331761 3256665014605290899498821)
                  ·
                    refine ⟨610624690238492043656029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3256665014605290899498821 610624690238492043656029)
                    ·
                      rfl

theorem cell23_3567562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 3, 4, 2, 4].length) (baseStart_3567562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3567562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3567562 prefixEnd_3567562 := by exact prefixLift 3567562
  have htrace : WordTrace (prefixWord ++ tailWord_3567562) baseStart_3567562 baseEnd_3567562 := by
    simpa [prefixWord, tailWord_3567562, baseEnd_3567562] using wordTrace_append hprefix tailTrace_3567562
  have hstable : (prefixWord ++ tailWord_3567562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3567562).length < 2 ^ (prefixWord ++ tailWord_3567562).sum := by decide
  have hdescent : baseEnd_3567562 < baseStart_3567562 := by decide
  rcases family_descends (prefixWord ++ tailWord_3567562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3567572 : List Nat := [2, 4, 1, 2, 1, 1, 1, 1, 5, 2, 3]
def baseStart_3567572 : Nat := 118140960795 + 3567572 * 2 ^ 59
def prefixEnd_3567572 : Nat := 4983230072969 + 3 ^ 40 * 3567572 * 2
def baseEnd_3567572 : Nat := 1831879205522021091843041

theorem tailTrace_3567572 : CollatzResearch.WordTrace tailWord_3567572 prefixEnd_3567572 1831879205522021091843041 := by
  unfold tailWord_3567572
  simp only [CollatzResearch.WordTrace]
  refine ⟨65060020315651705817216485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86746693754202274422955313 65060020315651705817216485)
  ·
    refine ⟨12198753809184694840728091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 65060020315651705817216485 12198753809184694840728091)
    ·
      refine ⟨18298130713777042261092137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12198753809184694840728091 18298130713777042261092137)
      ·
        refine ⟨13723598035332781695819103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18298130713777042261092137 13723598035332781695819103)
        ·
          refine ⟨20585397052999172543728655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13723598035332781695819103 20585397052999172543728655)
          ·
            refine ⟨30878095579498758815592983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20585397052999172543728655 30878095579498758815592983)
            ·
              refine ⟨46317143369248138223389475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30878095579498758815592983 46317143369248138223389475)
              ·
                refine ⟨69475715053872207335084213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46317143369248138223389475 69475715053872207335084213)
                ·
                  refine ⟨6513348286300519437664145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 69475715053872207335084213 6513348286300519437664145)
                  ·
                    refine ⟨4885011214725389578248109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6513348286300519437664145 4885011214725389578248109)
                    ·
                      refine ⟨1831879205522021091843041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4885011214725389578248109 1831879205522021091843041)
                      ·
                        rfl

theorem cell23_3567572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 1, 5, 2, 3].length) (baseStart_3567572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3567572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3567572 prefixEnd_3567572 := by exact prefixLift 3567572
  have htrace : WordTrace (prefixWord ++ tailWord_3567572) baseStart_3567572 baseEnd_3567572 := by
    simpa [prefixWord, tailWord_3567572, baseEnd_3567572] using wordTrace_append hprefix tailTrace_3567572
  have hstable : (prefixWord ++ tailWord_3567572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3567572).length < 2 ^ (prefixWord ++ tailWord_3567572).sum := by decide
  have hdescent : baseEnd_3567572 < baseStart_3567572 := by decide
  rcases family_descends (prefixWord ++ tailWord_3567572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3567606 : List Nat := [5, 1, 1, 1, 4, 1, 1, 3, 1, 2, 3]
def baseStart_3567606 : Nat := 118140960795 + 3567606 * 2 ^ 59
def prefixEnd_3567606 : Nat := 4983230072969 + 3 ^ 40 * 3567606 * 2
def baseEnd_3567606 : Nat := 1831896663864273958817885

theorem tailTrace_3567606 : CollatzResearch.WordTrace tailWord_3567606 prefixEnd_3567606 1831896663864273958817885 := by
  unfold tailWord_3567606
  simp only [CollatzResearch.WordTrace]
  refine ⟨8132580044573764715073167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 86747520475453490294113781 8132580044573764715073167)
  ·
    refine ⟨12198870066860647072609751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8132580044573764715073167 12198870066860647072609751)
    ·
      refine ⟨18298305100290970608914627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12198870066860647072609751 18298305100290970608914627)
      ·
        refine ⟨27447457650436455913371941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18298305100290970608914627 27447457650436455913371941)
        ·
          refine ⟨5146398309456835483757239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27447457650436455913371941 5146398309456835483757239)
          ·
            refine ⟨7719597464185253225635859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5146398309456835483757239 7719597464185253225635859)
            ·
              refine ⟨11579396196277879838453789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7719597464185253225635859 11579396196277879838453789)
              ·
                refine ⟨4342273573604204939420171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11579396196277879838453789 4342273573604204939420171)
                ·
                  refine ⟨6513410360406307409130257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4342273573604204939420171 6513410360406307409130257)
                  ·
                    refine ⟨4885057770304730556847693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6513410360406307409130257 4885057770304730556847693)
                    ·
                      refine ⟨1831896663864273958817885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4885057770304730556847693 1831896663864273958817885)
                      ·
                        rfl

theorem cell23_3567606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 1, 3, 1, 2, 3].length) (baseStart_3567606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3567606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3567606 prefixEnd_3567606 := by exact prefixLift 3567606
  have htrace : WordTrace (prefixWord ++ tailWord_3567606) baseStart_3567606 baseEnd_3567606 := by
    simpa [prefixWord, tailWord_3567606, baseEnd_3567606] using wordTrace_append hprefix tailTrace_3567606
  have hstable : (prefixWord ++ tailWord_3567606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3567606).length < 2 ^ (prefixWord ++ tailWord_3567606).sum := by decide
  have hdescent : baseEnd_3567606 < baseStart_3567606 := by decide
  rcases family_descends (prefixWord ++ tailWord_3567606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3567635 : List Nat := [1, 1, 1, 2, 1, 4, 4, 1, 2, 6]
def baseStart_3567635 : Nat := 118140960795 + 3567635 * 2 ^ 59
def prefixEnd_3567635 : Nat := 4983230072969 + 3 ^ 40 * 3567635 * 2
def baseEnd_3567635 : Nat := 610637184934418115118417

theorem tailTrace_3567635 : CollatzResearch.WordTrace tailWord_3567635 prefixEnd_3567635 610637184934418115118417 := by
  unfold tailWord_3567635
  simp only [CollatzResearch.WordTrace]
  refine ⟨130122338430075173393976359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86748225620050115595984239 130122338430075173393976359)
  ·
    refine ⟨195183507645112760090964539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130122338430075173393976359 195183507645112760090964539)
    ·
      refine ⟨292775261467669140136446809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195183507645112760090964539 292775261467669140136446809)
      ·
        refine ⟨219581446100751855102335107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 292775261467669140136446809 219581446100751855102335107)
        ·
          refine ⟨329372169151127782653502661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 219581446100751855102335107 329372169151127782653502661)
          ·
            refine ⟨61757281715836459247531749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 329372169151127782653502661 61757281715836459247531749)
            ·
              refine ⟨11579490321719336108912203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 61757281715836459247531749 11579490321719336108912203)
              ·
                refine ⟨17369235482579004163368305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11579490321719336108912203 17369235482579004163368305)
                ·
                  refine ⟨13026926611934253122526229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17369235482579004163368305 13026926611934253122526229)
                  ·
                    refine ⟨610637184934418115118417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13026926611934253122526229 610637184934418115118417)
                    ·
                      rfl

theorem cell23_3567635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 4, 1, 2, 6].length) (baseStart_3567635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3567635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3567635 prefixEnd_3567635 := by exact prefixLift 3567635
  have htrace : WordTrace (prefixWord ++ tailWord_3567635) baseStart_3567635 baseEnd_3567635 := by
    simpa [prefixWord, tailWord_3567635, baseEnd_3567635] using wordTrace_append hprefix tailTrace_3567635
  have hstable : (prefixWord ++ tailWord_3567635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3567635).length < 2 ^ (prefixWord ++ tailWord_3567635).sum := by decide
  have hdescent : baseEnd_3567635 < baseStart_3567635 := by decide
  rcases family_descends (prefixWord ++ tailWord_3567635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3567662 : List Nat := [4, 1, 3, 1, 1, 2, 1, 1, 1, 3, 5]
def baseStart_3567662 : Nat := 118140960795 + 3567662 * 2 ^ 59
def prefixEnd_3567662 : Nat := 4983230072969 + 3 ^ 40 * 3567662 * 2
def baseEnd_3567662 : Nat := 1831925418780925739717627

theorem tailTrace_3567662 : CollatzResearch.WordTrace tailWord_3567662 prefixEnd_3567662 1831925418780925739717627 := by
  unfold tailWord_3567662
  simp only [CollatzResearch.WordTrace]
  refine ⟨16265415400122169625651155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 86748882133984904670139493 16265415400122169625651155)
  ·
    refine ⟨24398123100183254438476733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16265415400122169625651155 24398123100183254438476733)
    ·
      refine ⟨9149296162568720414428775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24398123100183254438476733 9149296162568720414428775)
      ·
        refine ⟨13723944243853080621643163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9149296162568720414428775 13723944243853080621643163)
        ·
          refine ⟨20585916365779620932464745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13723944243853080621643163 20585916365779620932464745)
          ·
            refine ⟨15439437274334715699348559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20585916365779620932464745 15439437274334715699348559)
            ·
              refine ⟨23159155911502073549022839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15439437274334715699348559 23159155911502073549022839)
              ·
                refine ⟨34738733867253110323534259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23159155911502073549022839 34738733867253110323534259)
                ·
                  refine ⟨52108100800879665485301389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34738733867253110323534259 52108100800879665485301389)
                  ·
                    refine ⟨19540537800329874556988021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 52108100800879665485301389 19540537800329874556988021)
                    ·
                      refine ⟨1831925418780925739717627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19540537800329874556988021 1831925418780925739717627)
                      ·
                        rfl

theorem cell23_3567662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 1, 1, 1, 3, 5].length) (baseStart_3567662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3567662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3567662 prefixEnd_3567662 := by exact prefixLift 3567662
  have htrace : WordTrace (prefixWord ++ tailWord_3567662) baseStart_3567662 baseEnd_3567662 := by
    simpa [prefixWord, tailWord_3567662, baseEnd_3567662] using wordTrace_append hprefix tailTrace_3567662
  have hstable : (prefixWord ++ tailWord_3567662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3567662).length < 2 ^ (prefixWord ++ tailWord_3567662).sum := by decide
  have hdescent : baseEnd_3567662 < baseStart_3567662 := by decide
  rcases family_descends (prefixWord ++ tailWord_3567662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3567676 : List Nat := [2, 2, 2, 2, 2, 1, 2, 4, 2, 2, 2]
def baseStart_3567676 : Nat := 118140960795 + 3567676 * 2 ^ 59
def prefixEnd_3567676 : Nat := 4983230072969 + 3 ^ 40 * 3567676 * 2
def baseEnd_3567676 : Nat := 1831932607510088684942563

theorem tailTrace_3567676 : CollatzResearch.WordTrace tailWord_3567676 prefixEnd_3567676 1831932607510088684942563 := by
  unfold tailWord_3567676
  simp only [CollatzResearch.WordTrace]
  refine ⟨65061916911463318698109441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86749222548617758264145921 65061916911463318698109441)
  ·
    refine ⟨48796437683597489023582081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65061916911463318698109441 48796437683597489023582081)
    ·
      refine ⟨36597328262698116767686561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48796437683597489023582081 36597328262698116767686561)
      ·
        refine ⟨27447996197023587575764921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36597328262698116767686561 27447996197023587575764921)
        ·
          refine ⟨20585997147767690681823691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27447996197023587575764921 20585997147767690681823691)
          ·
            refine ⟨30878995721651536022735537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20585997147767690681823691 30878995721651536022735537)
            ·
              refine ⟨23159246791238652017051653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30878995721651536022735537 23159246791238652017051653)
              ·
                refine ⟨4342358773357247253197185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23159246791238652017051653 4342358773357247253197185)
                ·
                  refine ⟨3256769080017935439897889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4342358773357247253197185 3256769080017935439897889)
                  ·
                    refine ⟨2442576810013451579923417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3256769080017935439897889 2442576810013451579923417)
                    ·
                      refine ⟨1831932607510088684942563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2442576810013451579923417 1831932607510088684942563)
                      ·
                        rfl

theorem cell23_3567676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 2, 4, 2, 2, 2].length) (baseStart_3567676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3567676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3567676 prefixEnd_3567676 := by exact prefixLift 3567676
  have htrace : WordTrace (prefixWord ++ tailWord_3567676) baseStart_3567676 baseEnd_3567676 := by
    simpa [prefixWord, tailWord_3567676, baseEnd_3567676] using wordTrace_append hprefix tailTrace_3567676
  have hstable : (prefixWord ++ tailWord_3567676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3567676).length < 2 ^ (prefixWord ++ tailWord_3567676).sum := by decide
  have hdescent : baseEnd_3567676 < baseStart_3567676 := by decide
  rcases family_descends (prefixWord ++ tailWord_3567676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3567692 : List Nat := [2, 2, 1, 3, 1, 1, 2, 3, 2, 3, 3]
def baseStart_3567692 : Nat := 118140960795 + 3567692 * 2 ^ 59
def prefixEnd_3567692 : Nat := 4983230072969 + 3 ^ 40 * 3567692 * 2
def baseEnd_3567692 : Nat := 1831940823200560622342489

theorem tailTrace_3567692 : CollatzResearch.WordTrace tailWord_3567692 prefixEnd_3567692 1831940823200560622342489 := by
  unfold tailWord_3567692
  simp only [CollatzResearch.WordTrace]
  refine ⟨65062208695434336064400665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86749611593912448085867553 65062208695434336064400665)
  ·
    refine ⟨48796656521575752048300499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65062208695434336064400665 48796656521575752048300499)
    ·
      refine ⟨73194984782363628072450749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48796656521575752048300499 73194984782363628072450749)
      ·
        refine ⟨27448119293386360527169031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73194984782363628072450749 27448119293386360527169031)
        ·
          refine ⟨41172178940079540790753547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27448119293386360527169031 41172178940079540790753547)
          ·
            refine ⟨61758268410119311186130321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41172178940079540790753547 61758268410119311186130321)
            ·
              refine ⟨46318701307589483389597741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61758268410119311186130321 46318701307589483389597741)
              ·
                refine ⟨17369512990346056271099153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46318701307589483389597741 17369512990346056271099153)
                ·
                  refine ⟨13027134742759542203324365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17369512990346056271099153 13027134742759542203324365)
                  ·
                    refine ⟨4885175528534828326246637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13027134742759542203324365 4885175528534828326246637)
                    ·
                      refine ⟨1831940823200560622342489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4885175528534828326246637 1831940823200560622342489)
                      ·
                        rfl

theorem cell23_3567692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 3, 2, 3, 3].length) (baseStart_3567692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3567692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3567692 prefixEnd_3567692 := by exact prefixLift 3567692
  have htrace : WordTrace (prefixWord ++ tailWord_3567692) baseStart_3567692 baseEnd_3567692 := by
    simpa [prefixWord, tailWord_3567692, baseEnd_3567692] using wordTrace_append hprefix tailTrace_3567692
  have hstable : (prefixWord ++ tailWord_3567692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3567692).length < 2 ^ (prefixWord ++ tailWord_3567692).sum := by decide
  have hdescent : baseEnd_3567692 < baseStart_3567692 := by decide
  rcases family_descends (prefixWord ++ tailWord_3567692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3567693 : List Nat := [1, 6, 1, 1, 1, 1, 3, 3, 2, 2, 2]
def baseStart_3567693 : Nat := 118140960795 + 3567693 * 2 ^ 59
def prefixEnd_3567693 : Nat := 4983230072969 + 3 ^ 40 * 3567693 * 2
def baseEnd_3567693 : Nat := 1831941336681215118429985

theorem tailTrace_3567693 : CollatzResearch.WordTrace tailWord_3567693 prefixEnd_3567693 1831941336681215118429985 := by
  unfold tailWord_3567693
  simp only [CollatzResearch.WordTrace]
  refine ⟨130124453863865049299587733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86749635909243366199725155 130124453863865049299587733)
  ·
    refine ⟨6099583774868674185918175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 130124453863865049299587733 6099583774868674185918175)
    ·
      refine ⟨9149375662303011278877263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6099583774868674185918175 9149375662303011278877263)
      ·
        refine ⟨13724063493454516918315895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9149375662303011278877263 13724063493454516918315895)
        ·
          refine ⟨20586095240181775377473843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13724063493454516918315895 20586095240181775377473843)
          ·
            refine ⟨30879142860272663066210765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20586095240181775377473843 30879142860272663066210765)
            ·
              refine ⟨11579678572602248649829037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30879142860272663066210765 11579678572602248649829037)
              ·
                refine ⟨4342379464725843243685889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11579678572602248649829037 4342379464725843243685889)
                ·
                  refine ⟨3256784598544382432764417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4342379464725843243685889 3256784598544382432764417)
                  ·
                    refine ⟨2442588448908286824573313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3256784598544382432764417 2442588448908286824573313)
                    ·
                      refine ⟨1831941336681215118429985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2442588448908286824573313 1831941336681215118429985)
                      ·
                        rfl

theorem cell23_3567693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 3, 3, 2, 2, 2].length) (baseStart_3567693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3567693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3567693 prefixEnd_3567693 := by exact prefixLift 3567693
  have htrace : WordTrace (prefixWord ++ tailWord_3567693) baseStart_3567693 baseEnd_3567693 := by
    simpa [prefixWord, tailWord_3567693, baseEnd_3567693] using wordTrace_append hprefix tailTrace_3567693
  have hstable : (prefixWord ++ tailWord_3567693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3567693).length < 2 ^ (prefixWord ++ tailWord_3567693).sum := by decide
  have hdescent : baseEnd_3567693 < baseStart_3567693 := by decide
  rcases family_descends (prefixWord ++ tailWord_3567693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3567705 : List Nat := [1, 2, 1, 2, 2, 1, 3, 2, 1, 1, 7]
def baseStart_3567705 : Nat := 118140960795 + 3567705 * 2 ^ 59
def prefixEnd_3567705 : Nat := 4983230072969 + 3 ^ 40 * 3567705 * 2
def baseEnd_3567705 : Nat := 1831947498449069071479929

theorem tailTrace_3567705 : CollatzResearch.WordTrace tailWord_3567705 prefixEnd_3567705 1831947498449069071479929 := by
  unfold tailWord_3567705
  simp only [CollatzResearch.WordTrace]
  refine ⟨130124891539821575349024569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86749927693214383566016379 130124891539821575349024569)
  ·
    refine ⟨97593668654866181511768427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130124891539821575349024569 97593668654866181511768427)
    ·
      refine ⟨146390502982299272267652641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97593668654866181511768427 146390502982299272267652641)
      ·
        refine ⟨109792877236724454200739481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146390502982299272267652641 109792877236724454200739481)
        ·
          refine ⟨82344657927543340650554611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109792877236724454200739481 82344657927543340650554611)
          ·
            refine ⟨123516986891315010975831917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82344657927543340650554611 123516986891315010975831917)
            ·
              refine ⟨46318870084243129115936969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 123516986891315010975831917 46318870084243129115936969)
              ·
                refine ⟨34739152563182346836952727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46318870084243129115936969 34739152563182346836952727)
                ·
                  refine ⟨52108728844773520255429091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34739152563182346836952727 52108728844773520255429091)
                  ·
                    refine ⟨78163093267160280383143637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 52108728844773520255429091 78163093267160280383143637)
                    ·
                      refine ⟨1831947498449069071479929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 78163093267160280383143637 1831947498449069071479929)
                      ·
                        rfl

theorem cell23_3567705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 2, 1, 1, 7].length) (baseStart_3567705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3567705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3567705 prefixEnd_3567705 := by exact prefixLift 3567705
  have htrace : WordTrace (prefixWord ++ tailWord_3567705) baseStart_3567705 baseEnd_3567705 := by
    simpa [prefixWord, tailWord_3567705, baseEnd_3567705] using wordTrace_append hprefix tailTrace_3567705
  have hstable : (prefixWord ++ tailWord_3567705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3567705).length < 2 ^ (prefixWord ++ tailWord_3567705).sum := by decide
  have hdescent : baseEnd_3567705 < baseStart_3567705 := by decide
  rcases family_descends (prefixWord ++ tailWord_3567705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3567710 : List Nat := [4, 4, 1, 1, 2, 1, 1, 2, 1, 4, 2]
def baseStart_3567710 : Nat := 118140960795 + 3567710 * 2 ^ 59
def prefixEnd_3567710 : Nat := 4983230072969 + 3 ^ 40 * 3567710 * 2
def baseEnd_3567710 : Nat := 1831950065852341551917407

theorem tailTrace_3567710 : CollatzResearch.WordTrace tailWord_3567710 prefixEnd_3567710 1831950065852341551917407 := by
  unfold tailWord_3567710
  simp only [CollatzResearch.WordTrace]
  refine ⟨16265634238100432650369573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 86750049269868974135304389 16265634238100432650369573)
  ·
    refine ⟨3049806419643831121944295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16265634238100432650369573 3049806419643831121944295)
    ·
      refine ⟨4574709629465746682916443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3049806419643831121944295 4574709629465746682916443)
      ·
        refine ⟨6862064444198620024374665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4574709629465746682916443 6862064444198620024374665)
        ·
          refine ⟨5146548333148965018280999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6862064444198620024374665 5146548333148965018280999)
          ·
            refine ⟨7719822499723447527421499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5146548333148965018280999 7719822499723447527421499)
            ·
              refine ⟨11579733749585171291132249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7719822499723447527421499 11579733749585171291132249)
              ·
                refine ⟨8684800312188878468349187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11579733749585171291132249 8684800312188878468349187)
                ·
                  refine ⟨13027200468283317702523781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8684800312188878468349187 13027200468283317702523781)
                  ·
                    refine ⟨2442600087803122069223209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13027200468283317702523781 2442600087803122069223209)
                    ·
                      refine ⟨1831950065852341551917407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2442600087803122069223209 1831950065852341551917407)
                      ·
                        rfl

theorem cell23_3567710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 1, 2, 1, 4, 2].length) (baseStart_3567710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3567710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3567710 prefixEnd_3567710 := by exact prefixLift 3567710
  have htrace : WordTrace (prefixWord ++ tailWord_3567710) baseStart_3567710 baseEnd_3567710 := by
    simpa [prefixWord, tailWord_3567710, baseEnd_3567710] using wordTrace_append hprefix tailTrace_3567710
  have hstable : (prefixWord ++ tailWord_3567710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3567710).length < 2 ^ (prefixWord ++ tailWord_3567710).sum := by decide
  have hdescent : baseEnd_3567710 < baseStart_3567710 := by decide
  rcases family_descends (prefixWord ++ tailWord_3567710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3567712 : List Nat := [2, 1, 1, 3, 2, 3, 1, 3, 2, 5]
def baseStart_3567712 : Nat := 118140960795 + 3567712 * 2 ^ 59
def prefixEnd_3567712 : Nat := 4983230072969 + 3 ^ 40 * 3567712 * 2
def baseEnd_3567712 : Nat := 610650364271216848030799

theorem tailTrace_3567712 : CollatzResearch.WordTrace tailWord_3567712 prefixEnd_3567712 610650364271216848030799 := by
  unfold tailWord_3567712
  simp only [CollatzResearch.WordTrace]
  refine ⟨65062573425398107772264695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86750097900530810363019593 65062573425398107772264695)
  ·
    refine ⟨97593860138097161658397043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65062573425398107772264695 97593860138097161658397043)
    ·
      refine ⟨146390790207145742487595565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97593860138097161658397043 146390790207145742487595565)
      ·
        refine ⟨54896546327679653432848337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 146390790207145742487595565 54896546327679653432848337)
        ·
          refine ⟨41172409745759740074636253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54896546327679653432848337 41172409745759740074636253)
          ·
            refine ⟨15439653654659902527988595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41172409745759740074636253 15439653654659902527988595)
            ·
              refine ⟨23159480481989853791982893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15439653654659902527988595 23159480481989853791982893)
              ·
                refine ⟨8684805180746195171993585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23159480481989853791982893 8684805180746195171993585)
                ·
                  refine ⟨6513603885559646378995189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8684805180746195171993585 6513603885559646378995189)
                  ·
                    refine ⟨610650364271216848030799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6513603885559646378995189 610650364271216848030799)
                    ·
                      rfl

theorem cell23_3567712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 1, 3, 2, 5].length) (baseStart_3567712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3567712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3567712 prefixEnd_3567712 := by exact prefixLift 3567712
  have htrace : WordTrace (prefixWord ++ tailWord_3567712) baseStart_3567712 baseEnd_3567712 := by
    simpa [prefixWord, tailWord_3567712, baseEnd_3567712] using wordTrace_append hprefix tailTrace_3567712
  have hstable : (prefixWord ++ tailWord_3567712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3567712).length < 2 ^ (prefixWord ++ tailWord_3567712).sum := by decide
  have hdescent : baseEnd_3567712 < baseStart_3567712 := by decide
  rcases family_descends (prefixWord ++ tailWord_3567712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3567749 : List Nat := [1, 3, 1, 1, 5, 1, 1, 1, 1, 6, 2]
def baseStart_3567749 : Nat := 118140960795 + 3567749 * 2 ^ 59
def prefixEnd_3567749 : Nat := 4983230072969 + 3 ^ 40 * 3567749 * 2
def baseEnd_3567749 : Nat := 1831970091597866899329727

theorem tailTrace_3567749 : CollatzResearch.WordTrace tailWord_3567749 prefixEnd_3567749 1831970091597866899329727 := by
  unfold tailWord_3567749
  simp only [CollatzResearch.WordTrace]
  refine ⟨130126496351662170863626301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86750997567774780575750867 130126496351662170863626301)
  ·
    refine ⟨48797436131873314073859863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130126496351662170863626301 48797436131873314073859863)
    ·
      refine ⟨73196154197809971110789795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48797436131873314073859863 73196154197809971110789795)
      ·
        refine ⟨109794231296714956666184693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73196154197809971110789795 109794231296714956666184693)
        ·
          refine ⟨10293209184067027187454815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 109794231296714956666184693 10293209184067027187454815)
          ·
            refine ⟨15439813776100540781182223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10293209184067027187454815 15439813776100540781182223)
            ·
              refine ⟨23159720664150811171773335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15439813776100540781182223 23159720664150811171773335)
              ·
                refine ⟨34739580996226216757660003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23159720664150811171773335 34739580996226216757660003)
                ·
                  refine ⟨52109371494339325136490005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34739580996226216757660003 52109371494339325136490005)
                  ·
                    refine ⟨2442626788797155865772969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 52109371494339325136490005 2442626788797155865772969)
                    ·
                      refine ⟨1831970091597866899329727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2442626788797155865772969 1831970091597866899329727)
                      ·
                        rfl

theorem cell23_3567749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 1, 1, 1, 6, 2].length) (baseStart_3567749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3567749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3567749 prefixEnd_3567749 := by exact prefixLift 3567749
  have htrace : WordTrace (prefixWord ++ tailWord_3567749) baseStart_3567749 baseEnd_3567749 := by
    simpa [prefixWord, tailWord_3567749, baseEnd_3567749] using wordTrace_append hprefix tailTrace_3567749
  have hstable : (prefixWord ++ tailWord_3567749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3567749).length < 2 ^ (prefixWord ++ tailWord_3567749).sum := by decide
  have hdescent : baseEnd_3567749 < baseStart_3567749 := by decide
  rcases family_descends (prefixWord ++ tailWord_3567749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3567755 : List Nat := [1, 1, 1, 1, 4, 1, 1, 1, 12]
def baseStart_3567755 : Nat := 118140960795 + 3567755 * 2 ^ 59
def prefixEnd_3567755 : Nat := 4983230072969 + 3 ^ 40 * 3567755 * 2
def baseEnd_3567755 : Nat := 203552574720199319539411

theorem tailTrace_3567755 : CollatzResearch.WordTrace tailWord_3567755 prefixEnd_3567755 203552574720199319539411 := by
  unfold tailWord_3567755
  simp only [CollatzResearch.WordTrace]
  refine ⟨130126715189640433888344719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86751143459760289258896479 130126715189640433888344719)
  ·
    refine ⟨195190072784460650832517079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130126715189640433888344719 195190072784460650832517079)
    ·
      refine ⟨292785109176690976248775619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195190072784460650832517079 292785109176690976248775619)
      ·
        refine ⟨439177663765036464373163429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 292785109176690976248775619 439177663765036464373163429)
        ·
          refine ⟨82345811955944337069968143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 439177663765036464373163429 82345811955944337069968143)
          ·
            refine ⟨123518717933916505604952215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82345811955944337069968143 123518717933916505604952215)
            ·
              refine ⟨185278076900874758407428323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 123518717933916505604952215 185278076900874758407428323)
              ·
                refine ⟨277917115351312137611142485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 185278076900874758407428323 277917115351312137611142485)
                ·
                  refine ⟨203552574720199319539411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 12 277917115351312137611142485 203552574720199319539411)
                  ·
                    rfl

theorem cell23_3567755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 1, 12].length) (baseStart_3567755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3567755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3567755 prefixEnd_3567755 := by exact prefixLift 3567755
  have htrace : WordTrace (prefixWord ++ tailWord_3567755) baseStart_3567755 baseEnd_3567755 := by
    simpa [prefixWord, tailWord_3567755, baseEnd_3567755] using wordTrace_append hprefix tailTrace_3567755
  have hstable : (prefixWord ++ tailWord_3567755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3567755).length < 2 ^ (prefixWord ++ tailWord_3567755).sum := by decide
  have hdescent : baseEnd_3567755 < baseStart_3567755 := by decide
  rcases family_descends (prefixWord ++ tailWord_3567755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3567772 : List Nat := [2, 2, 3, 2, 1, 1, 2, 2, 8]
def baseStart_3567772 : Nat := 118140960795 + 3567772 * 2 ^ 59
def prefixEnd_3567772 : Nat := 4983230072969 + 3 ^ 40 * 3567772 * 2
def baseEnd_3567772 : Nat := 203553544628102256593569

theorem tailTrace_3567772 : CollatzResearch.WordTrace tailWord_3567772 prefixEnd_3567772 203553544628102256593569 := by
  unfold tailWord_3567772
  simp only [CollatzResearch.WordTrace]
  refine ⟨65063667615289422895856785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86751556820385897194475713 65063667615289422895856785)
  ·
    refine ⟨48797750711467067171892589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65063667615289422895856785 48797750711467067171892589)
    ·
      refine ⟨18299156516800150189459721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48797750711467067171892589 18299156516800150189459721)
      ·
        refine ⟨13724367387600112642094791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18299156516800150189459721 13724367387600112642094791)
        ·
          refine ⟨20586551081400168963142187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13724367387600112642094791 20586551081400168963142187)
          ·
            refine ⟨30879826622100253444713281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20586551081400168963142187 30879826622100253444713281)
            ·
              refine ⟨23159869966575190083534961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30879826622100253444713281 23159869966575190083534961)
              ·
                refine ⟨17369902474931392562651221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23159869966575190083534961 17369902474931392562651221)
                ·
                  refine ⟨203553544628102256593569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 17369902474931392562651221 203553544628102256593569)
                  ·
                    rfl

theorem cell23_3567772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 2, 2, 8].length) (baseStart_3567772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3567772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3567772 prefixEnd_3567772 := by exact prefixLift 3567772
  have htrace : WordTrace (prefixWord ++ tailWord_3567772) baseStart_3567772 baseEnd_3567772 := by
    simpa [prefixWord, tailWord_3567772, baseEnd_3567772] using wordTrace_append hprefix tailTrace_3567772
  have hstable : (prefixWord ++ tailWord_3567772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3567772).length < 2 ^ (prefixWord ++ tailWord_3567772).sum := by decide
  have hdescent : baseEnd_3567772 < baseStart_3567772 := by decide
  rcases family_descends (prefixWord ++ tailWord_3567772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3567776 : List Nat := [2, 1, 1, 4, 2, 2, 1, 5, 1, 4]
def baseStart_3567776 : Nat := 118140960795 + 3567776 * 2 ^ 59
def prefixEnd_3567776 : Nat := 4983230072969 + 3 ^ 40 * 3567776 * 2
def baseEnd_3567776 : Nat := 610661318525179431230701

theorem tailTrace_3567776 : CollatzResearch.WordTrace tailWord_3567776 prefixEnd_3567776 610661318525179431230701 := by
  unfold tailWord_3567776
  simp only [CollatzResearch.WordTrace]
  refine ⟨65063740561282177237429591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86751654081709569649906121 65063740561282177237429591)
  ·
    refine ⟨97595610841923265856144387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65063740561282177237429591 97595610841923265856144387)
    ·
      refine ⟨146393416262884898784216581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97595610841923265856144387 146393416262884898784216581)
      ·
        refine ⟨27448765549290918522040609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 146393416262884898784216581 27448765549290918522040609)
        ·
          refine ⟨20586574161968188891530457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27448765549290918522040609 20586574161968188891530457)
          ·
            refine ⟨15439930621476141668647843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20586574161968188891530457 15439930621476141668647843)
            ·
              refine ⟨23159895932214212502971765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15439930621476141668647843 23159895932214212502971765)
              ·
                refine ⟨2171240243645082422153603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23159895932214212502971765 2171240243645082422153603)
                ·
                  refine ⟨3256860365467623633230405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2171240243645082422153603 3256860365467623633230405)
                  ·
                    refine ⟨610661318525179431230701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3256860365467623633230405 610661318525179431230701)
                    ·
                      rfl

theorem cell23_3567776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 1, 5, 1, 4].length) (baseStart_3567776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3567776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3567776 prefixEnd_3567776 := by exact prefixLift 3567776
  have htrace : WordTrace (prefixWord ++ tailWord_3567776) baseStart_3567776 baseEnd_3567776 := by
    simpa [prefixWord, tailWord_3567776, baseEnd_3567776] using wordTrace_append hprefix tailTrace_3567776
  have hstable : (prefixWord ++ tailWord_3567776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3567776).length < 2 ^ (prefixWord ++ tailWord_3567776).sum := by decide
  have hdescent : baseEnd_3567776 < baseStart_3567776 := by decide
  rcases family_descends (prefixWord ++ tailWord_3567776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3567789 : List Nat := [1, 5, 2, 1, 2, 2, 1, 1, 8]
def baseStart_3567789 : Nat := 118140960795 + 3567789 * 2 ^ 59
def prefixEnd_3567789 : Nat := 4983230072969 + 3 ^ 40 * 3567789 * 2
def baseEnd_3567789 : Nat := 203554514536005193647727

theorem tailTrace_3567789 : CollatzResearch.WordTrace tailWord_3567789 prefixEnd_3567789 203554514536005193647727 := by
  unfold tailWord_3567789
  simp only [CollatzResearch.WordTrace]
  refine ⟨130127955271517257695082421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86751970181011505130054947 130127955271517257695082421)
  ·
    refine ⟨12199495806704742908913977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 130127955271517257695082421 12199495806704742908913977)
    ·
      refine ⟨9149621855028557181685483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12199495806704742908913977 9149621855028557181685483)
      ·
        refine ⟨13724432782542835772528225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9149621855028557181685483 13724432782542835772528225)
        ·
          refine ⟨10293324586907126829396169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13724432782542835772528225 10293324586907126829396169)
          ·
            refine ⟨7719993440180345122047127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10293324586907126829396169 7719993440180345122047127)
            ·
              refine ⟨11579990160270517683070691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7719993440180345122047127 11579990160270517683070691)
              ·
                refine ⟨17369985240405776524606037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11579990160270517683070691 17369985240405776524606037)
                ·
                  refine ⟨203554514536005193647727, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 17369985240405776524606037 203554514536005193647727)
                  ·
                    rfl

theorem cell23_3567789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 1, 1, 8].length) (baseStart_3567789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3567789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3567789 prefixEnd_3567789 := by exact prefixLift 3567789
  have htrace : WordTrace (prefixWord ++ tailWord_3567789) baseStart_3567789 baseEnd_3567789 := by
    simpa [prefixWord, tailWord_3567789, baseEnd_3567789] using wordTrace_append hprefix tailTrace_3567789
  have hstable : (prefixWord ++ tailWord_3567789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3567789).length < 2 ^ (prefixWord ++ tailWord_3567789).sum := by decide
  have hdescent : baseEnd_3567789 < baseStart_3567789 := by decide
  rcases family_descends (prefixWord ++ tailWord_3567789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3567802 : List Nat := [3, 1, 1, 1, 2, 2, 2, 1, 5, 5]
def baseStart_3567802 : Nat := 118140960795 + 3567802 * 2 ^ 59
def prefixEnd_3567802 : Nat := 4983230072969 + 3 ^ 40 * 3567802 * 2
def baseEnd_3567802 : Nat := 610665768690851730655661

theorem tailTrace_3567802 : CollatzResearch.WordTrace tailWord_3567802 prefixEnd_3567802 610665768690851730655661 := by
  unfold tailWord_3567802
  simp only [CollatzResearch.WordTrace]
  refine ⟨32532107355117540228826415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86752286280313440610203773 32532107355117540228826415)
  ·
    refine ⟨48798161032676310343239623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32532107355117540228826415 48798161032676310343239623)
    ·
      refine ⟨73197241549014465514859435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48798161032676310343239623 73197241549014465514859435)
      ·
        refine ⟨109795862323521698272289153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73197241549014465514859435 109795862323521698272289153)
        ·
          refine ⟨82346896742641273704216865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109795862323521698272289153 82346896742641273704216865)
          ·
            refine ⟨61760172556980955278162649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82346896742641273704216865 61760172556980955278162649)
            ·
              refine ⟨46320129417735716458621987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61760172556980955278162649 46320129417735716458621987)
              ·
                refine ⟨69480194126603574687932981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46320129417735716458621987 69480194126603574687932981)
                ·
                  refine ⟨6513768199369085126993717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 69480194126603574687932981 6513768199369085126993717)
                  ·
                    refine ⟨610665768690851730655661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6513768199369085126993717 610665768690851730655661)
                    ·
                      rfl

theorem cell23_3567802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 1, 5, 5].length) (baseStart_3567802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3567802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3567802 prefixEnd_3567802 := by exact prefixLift 3567802
  have htrace : WordTrace (prefixWord ++ tailWord_3567802) baseStart_3567802 baseEnd_3567802 := by
    simpa [prefixWord, tailWord_3567802, baseEnd_3567802] using wordTrace_append hprefix tailTrace_3567802
  have hstable : (prefixWord ++ tailWord_3567802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3567802).length < 2 ^ (prefixWord ++ tailWord_3567802).sum := by decide
  have hdescent : baseEnd_3567802 < baseStart_3567802 := by decide
  rcases family_descends (prefixWord ++ tailWord_3567802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3567819 : List Nat := [1, 1, 1, 1, 3, 2, 6, 2, 1, 5]
def baseStart_3567819 : Nat := 118140960795 + 3567819 * 2 ^ 59
def prefixEnd_3567819 : Nat := 4983230072969 + 3 ^ 40 * 3567819 * 2
def baseEnd_3567819 : Nat := 610668678414560541818135

theorem tailTrace_3567819 : CollatzResearch.WordTrace tailWord_3567819 prefixEnd_3567819 610668678414560541818135 := by
  unfold tailWord_3567819
  simp only [CollatzResearch.WordTrace]
  refine ⟨130129049461408572818674511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86752699640939048545783007 130129049461408572818674511)
  ·
    refine ⟨195193574192112859228011767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130129049461408572818674511 195193574192112859228011767)
    ·
      refine ⟨292790361288169288842017651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195193574192112859228011767 292790361288169288842017651)
      ·
        refine ⟨439185541932253933263026477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 292790361288169288842017651 439185541932253933263026477)
        ·
          refine ⟨164694578224595224973634929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 439185541932253933263026477 164694578224595224973634929)
          ·
            refine ⟨123520933668446418730226197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 164694578224595224973634929 123520933668446418730226197)
            ·
              refine ⟨5790043765708425877979353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 123520933668446418730226197 5790043765708425877979353)
              ·
                refine ⟨4342532824281319408484515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5790043765708425877979353 4342532824281319408484515)
                ·
                  refine ⟨6513799236421979112726773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4342532824281319408484515 6513799236421979112726773)
                  ·
                    refine ⟨610668678414560541818135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6513799236421979112726773 610668678414560541818135)
                    ·
                      rfl

theorem cell23_3567819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 6, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 6, 2, 1, 5].length) (baseStart_3567819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3567819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3567819 prefixEnd_3567819 := by exact prefixLift 3567819
  have htrace : WordTrace (prefixWord ++ tailWord_3567819) baseStart_3567819 baseEnd_3567819 := by
    simpa [prefixWord, tailWord_3567819, baseEnd_3567819] using wordTrace_append hprefix tailTrace_3567819
  have hstable : (prefixWord ++ tailWord_3567819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3567819).length < 2 ^ (prefixWord ++ tailWord_3567819).sum := by decide
  have hdescent : baseEnd_3567819 < baseStart_3567819 := by decide
  rcases family_descends (prefixWord ++ tailWord_3567819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3567826 : List Nat := [3, 2, 2, 2, 1, 2, 2, 1, 1, 5, 2]
def baseStart_3567826 : Nat := 118140960795 + 3567826 * 2 ^ 59
def prefixEnd_3567826 : Nat := 4983230072969 + 3 ^ 40 * 3567826 * 2
def baseEnd_3567826 : Nat := 1832009629608263098066873

theorem tailTrace_3567826 : CollatzResearch.WordTrace tailWord_3567826 prefixEnd_3567826 1832009629608263098066873 := by
  unfold tailWord_3567826
  simp only [CollatzResearch.WordTrace]
  refine ⟨32532326193095803253544833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86752869848255475342786221 32532326193095803253544833)
  ·
    refine ⟨24399244644821852440158625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32532326193095803253544833 24399244644821852440158625)
    ·
      refine ⟨18299433483616389330118969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24399244644821852440158625 18299433483616389330118969)
      ·
        refine ⟨13724575112712291997589227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18299433483616389330118969 13724575112712291997589227)
        ·
          refine ⟨20586862669068437996383841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13724575112712291997589227 20586862669068437996383841)
          ·
            refine ⟨15440147001801328497287881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20586862669068437996383841 15440147001801328497287881)
            ·
              refine ⟨11580110251350996372965911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15440147001801328497287881 11580110251350996372965911)
              ·
                refine ⟨17370165377026494559448867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11580110251350996372965911 17370165377026494559448867)
                ·
                  refine ⟨26055248065539741839173301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17370165377026494559448867 26055248065539741839173301)
                  ·
                    refine ⟨2442679506144350797422497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 26055248065539741839173301 2442679506144350797422497)
                    ·
                      refine ⟨1832009629608263098066873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2442679506144350797422497 1832009629608263098066873)
                      ·
                        rfl

theorem cell23_3567826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 2, 1, 1, 5, 2].length) (baseStart_3567826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3567826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3567826 prefixEnd_3567826 := by exact prefixLift 3567826
  have htrace : WordTrace (prefixWord ++ tailWord_3567826) baseStart_3567826 baseEnd_3567826 := by
    simpa [prefixWord, tailWord_3567826, baseEnd_3567826] using wordTrace_append hprefix tailTrace_3567826
  have hstable : (prefixWord ++ tailWord_3567826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3567826).length < 2 ^ (prefixWord ++ tailWord_3567826).sum := by decide
  have hdescent : baseEnd_3567826 < baseStart_3567826 := by decide
  rcases family_descends (prefixWord ++ tailWord_3567826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3567833 : List Nat := [1, 2, 1, 2, 3, 1, 5, 3, 1, 1, 3]
def baseStart_3567833 : Nat := 118140960795 + 3567833 * 2 ^ 59
def prefixEnd_3567833 : Nat := 4983230072969 + 3 ^ 40 * 3567833 * 2
def baseEnd_3567833 : Nat := 1832013223972844570679341

theorem tailTrace_3567833 : CollatzResearch.WordTrace tailWord_3567833 prefixEnd_3567833 1832013223972844570679341 := by
  unfold tailWord_3567833
  simp only [CollatzResearch.WordTrace]
  refine ⟨130129560083357853209684153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86753040055571902139789435 130129560083357853209684153)
  ·
    refine ⟨97597170062518389907263115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130129560083357853209684153 97597170062518389907263115)
    ·
      refine ⟨146395755093777584860894673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97597170062518389907263115 146395755093777584860894673)
      ·
        refine ⟨109796816320333188645671005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146395755093777584860894673 109796816320333188645671005)
        ·
          refine ⟨41173806120124945742126627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 109796816320333188645671005 41173806120124945742126627)
          ·
            refine ⟨61760709180187418613189941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41173806120124945742126627 61760709180187418613189941)
            ·
              refine ⟨5790066485642570494986557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 61760709180187418613189941 5790066485642570494986557)
              ·
                refine ⟨2171274932115963935619959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5790066485642570494986557 2171274932115963935619959)
                ·
                  refine ⟨3256912398173945903429939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2171274932115963935619959 3256912398173945903429939)
                  ·
                    refine ⟨4885368597260918855144909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3256912398173945903429939 4885368597260918855144909)
                    ·
                      refine ⟨1832013223972844570679341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4885368597260918855144909 1832013223972844570679341)
                      ·
                        rfl

theorem cell23_3567833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 5, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 5, 3, 1, 1, 3].length) (baseStart_3567833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3567833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3567833 prefixEnd_3567833 := by exact prefixLift 3567833
  have htrace : WordTrace (prefixWord ++ tailWord_3567833) baseStart_3567833 baseEnd_3567833 := by
    simpa [prefixWord, tailWord_3567833, baseEnd_3567833] using wordTrace_append hprefix tailTrace_3567833
  have hstable : (prefixWord ++ tailWord_3567833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3567833).length < 2 ^ (prefixWord ++ tailWord_3567833).sum := by decide
  have hdescent : baseEnd_3567833 < baseStart_3567833 := by decide
  rcases family_descends (prefixWord ++ tailWord_3567833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3567850 : List Nat := [3, 1, 3, 1, 1, 2, 5, 2, 1, 1, 3]
def baseStart_3567850 : Nat := 118140960795 + 3567850 * 2 ^ 59
def prefixEnd_3567850 : Nat := 4983230072969 + 3 ^ 40 * 3567850 * 2
def baseEnd_3567850 : Nat := 1832021953143971004166763

theorem tailTrace_3567850 : CollatzResearch.WordTrace tailWord_3567850 prefixEnd_3567850 1832021953143971004166763 := by
  unfold tailWord_3567850
  simp only [CollatzResearch.WordTrace]
  refine ⟨32532545031074066278263251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86753453416197510075368669 32532545031074066278263251)
  ·
    refine ⟨48798817546611099417394877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32532545031074066278263251 48798817546611099417394877)
    ·
      refine ⟨18299556579979162281523079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48798817546611099417394877 18299556579979162281523079)
      ·
        refine ⟨27449334869968743422284619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18299556579979162281523079 27449334869968743422284619)
        ·
          refine ⟨41174002304953115133426929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27449334869968743422284619 41174002304953115133426929)
          ·
            refine ⟨30880501728714836350070197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41174002304953115133426929 30880501728714836350070197)
            ·
              refine ⟨2895047037067015907819081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 30880501728714836350070197 2895047037067015907819081)
              ·
                refine ⟨2171285277800261930864311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2895047037067015907819081 2171285277800261930864311)
                ·
                  refine ⟨3256927916700392896296467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2171285277800261930864311 3256927916700392896296467)
                  ·
                    refine ⟨4885391875050589344444701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3256927916700392896296467 4885391875050589344444701)
                    ·
                      refine ⟨1832021953143971004166763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4885391875050589344444701 1832021953143971004166763)
                      ·
                        rfl

theorem cell23_3567850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 5, 2, 1, 1, 3].length) (baseStart_3567850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3567850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3567850 prefixEnd_3567850 := by exact prefixLift 3567850
  have htrace : WordTrace (prefixWord ++ tailWord_3567850) baseStart_3567850 baseEnd_3567850 := by
    simpa [prefixWord, tailWord_3567850, baseEnd_3567850] using wordTrace_append hprefix tailTrace_3567850
  have hstable : (prefixWord ++ tailWord_3567850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3567850).length < 2 ^ (prefixWord ++ tailWord_3567850).sum := by decide
  have hdescent : baseEnd_3567850 < baseStart_3567850 := by decide
  rcases family_descends (prefixWord ++ tailWord_3567850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3567852 : List Nat := [2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 6]
def baseStart_3567852 : Nat := 118140960795 + 3567852 * 2 ^ 59
def prefixEnd_3567852 : Nat := 4983230072969 + 3 ^ 40 * 3567852 * 2
def baseEnd_3567852 : Nat := 1832022980105279996341753

theorem tailTrace_3567852 : CollatzResearch.WordTrace tailWord_3567852 prefixEnd_3567852 1832022980105279996341753 := by
  unfold tailWord_3567852
  simp only [CollatzResearch.WordTrace]
  refine ⟨65065126535144509727312905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86753502046859346303083873 65065126535144509727312905)
  ·
    refine ⟨48798844901358382295484679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65065126535144509727312905 48798844901358382295484679)
    ·
      refine ⟨73198267352037573443227019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48798844901358382295484679 73198267352037573443227019)
      ·
        refine ⟨109797401028056360164840529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73198267352037573443227019 109797401028056360164840529)
        ·
          refine ⟨82348050771042270123630397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109797401028056360164840529 82348050771042270123630397)
          ·
            refine ⟨30880519039140851296361399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 82348050771042270123630397 30880519039140851296361399)
            ·
              refine ⟨46320778558711276944542099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30880519039140851296361399 46320778558711276944542099)
              ·
                refine ⟨69481167838066915416813149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46320778558711276944542099 69481167838066915416813149)
                ·
                  refine ⟨26055437939275093281304931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 69481167838066915416813149 26055437939275093281304931)
                  ·
                    refine ⟨39083156908912639921957397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26055437939275093281304931 39083156908912639921957397)
                    ·
                      refine ⟨1832022980105279996341753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 39083156908912639921957397 1832022980105279996341753)
                      ·
                        rfl

theorem cell23_3567852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 6].length) (baseStart_3567852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3567852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3567852 prefixEnd_3567852 := by exact prefixLift 3567852
  have htrace : WordTrace (prefixWord ++ tailWord_3567852) baseStart_3567852 baseEnd_3567852 := by
    simpa [prefixWord, tailWord_3567852, baseEnd_3567852] using wordTrace_append hprefix tailTrace_3567852
  have hstable : (prefixWord ++ tailWord_3567852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3567852).length < 2 ^ (prefixWord ++ tailWord_3567852).sum := by decide
  have hdescent : baseEnd_3567852 < baseStart_3567852 := by decide
  rcases family_descends (prefixWord ++ tailWord_3567852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3567859 : List Nat := [1, 1, 1, 2, 2, 4, 2, 2, 3, 2, 3]
def baseStart_3567859 : Nat := 118140960795 + 3567859 * 2 ^ 59
def prefixEnd_3567859 : Nat := 4983230072969 + 3 ^ 40 * 3567859 * 2
def baseEnd_3567859 : Nat := 1832026574469861468954221

theorem tailTrace_3567859 : CollatzResearch.WordTrace tailWord_3567859 prefixEnd_3567859 1832026574469861468954221 := by
  unfold tailWord_3567859
  simp only [CollatzResearch.WordTrace]
  refine ⟨130130508381263659650130631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86753672254175773100087087 130130508381263659650130631)
  ·
    refine ⟨195195762571895489475195947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130130508381263659650130631 195195762571895489475195947)
    ·
      refine ⟨292793643857843234212793921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195195762571895489475195947 292793643857843234212793921)
      ·
        refine ⟨219595232893382425659595441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 292793643857843234212793921 219595232893382425659595441)
        ·
          refine ⟨164696424670036819244696581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 219595232893382425659595441 164696424670036819244696581)
          ·
            refine ⟨30880579625631903608380609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 164696424670036819244696581 30880579625631903608380609)
            ·
              refine ⟨23160434719223927706285457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30880579625631903608380609 23160434719223927706285457)
              ·
                refine ⟨17370326039417945779714093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23160434719223927706285457 17370326039417945779714093)
                ·
                  refine ⟨6513872264781729667392785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17370326039417945779714093 6513872264781729667392785)
                  ·
                    refine ⟨4885404198586297250544589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6513872264781729667392785 4885404198586297250544589)
                    ·
                      refine ⟨1832026574469861468954221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4885404198586297250544589 1832026574469861468954221)
                      ·
                        rfl

theorem cell23_3567859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 2, 2, 3, 2, 3].length) (baseStart_3567859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3567859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3567859 prefixEnd_3567859 := by exact prefixLift 3567859
  have htrace : WordTrace (prefixWord ++ tailWord_3567859) baseStart_3567859 baseEnd_3567859 := by
    simpa [prefixWord, tailWord_3567859, baseEnd_3567859] using wordTrace_append hprefix tailTrace_3567859
  have hstable : (prefixWord ++ tailWord_3567859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3567859).length < 2 ^ (prefixWord ++ tailWord_3567859).sum := by decide
  have hdescent : baseEnd_3567859 < baseStart_3567859 := by decide
  rcases family_descends (prefixWord ++ tailWord_3567859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3567866 : List Nat := [3, 1, 1, 1, 1, 6, 1, 3, 2, 4]
def baseStart_3567866 : Nat := 118140960795 + 3567866 * 2 ^ 59
def prefixEnd_3567866 : Nat := 4983230072969 + 3 ^ 40 * 3567866 * 2
def baseEnd_3567866 : Nat := 610676722944814313855563

theorem tailTrace_3567866 : CollatzResearch.WordTrace tailWord_3567866 prefixEnd_3567866 610676722944814313855563 := by
  unfold tailWord_3567866
  simp only [CollatzResearch.WordTrace]
  refine ⟨32532690923059574961408863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86753842461492199897090301 32532690923059574961408863)
  ·
    refine ⟨48799036384589362442113295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32532690923059574961408863 48799036384589362442113295)
    ·
      refine ⟨73198554576884043663169943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48799036384589362442113295 73198554576884043663169943)
      ·
        refine ⟨109797831865326065494754915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73198554576884043663169943 109797831865326065494754915)
        ·
          refine ⟨164696747797989098242132373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109797831865326065494754915 164696747797989098242132373)
          ·
            refine ⟨7720160053030738980099955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 164696747797989098242132373 7720160053030738980099955)
            ·
              refine ⟨11580240079546108470149933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7720160053030738980099955 11580240079546108470149933)
              ·
                refine ⟨4342590029829790676306225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11580240079546108470149933 4342590029829790676306225)
                ·
                  refine ⟨3256942522372343007229669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4342590029829790676306225 3256942522372343007229669)
                  ·
                    refine ⟨610676722944814313855563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3256942522372343007229669 610676722944814313855563)
                    ·
                      rfl

theorem cell23_3567866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 1, 3, 2, 4].length) (baseStart_3567866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3567866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3567866 prefixEnd_3567866 := by exact prefixLift 3567866
  have htrace : WordTrace (prefixWord ++ tailWord_3567866) baseStart_3567866 baseEnd_3567866 := by
    simpa [prefixWord, tailWord_3567866, baseEnd_3567866] using wordTrace_append hprefix tailTrace_3567866
  have hstable : (prefixWord ++ tailWord_3567866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3567866).length < 2 ^ (prefixWord ++ tailWord_3567866).sum := by decide
  have hdescent : baseEnd_3567866 < baseStart_3567866 := by decide
  rcases family_descends (prefixWord ++ tailWord_3567866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3567889 : List Nat := [1, 2, 2, 1, 1, 5, 1, 1, 3, 3, 3]
def baseStart_3567889 : Nat := 118140960795 + 3567889 * 2 ^ 59
def prefixEnd_3567889 : Nat := 4983230072969 + 3 ^ 40 * 3567889 * 2
def baseEnd_3567889 : Nat := 1832041978889496351579083

theorem tailTrace_3567889 : CollatzResearch.WordTrace tailWord_3567889 prefixEnd_3567889 1832041978889496351579083 := by
  unfold tailWord_3567889
  simp only [CollatzResearch.WordTrace]
  refine ⟨130131602571154974773722721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86754401714103316515815147 130131602571154974773722721)
  ·
    refine ⟨97598701928366231080292041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130131602571154974773722721 97598701928366231080292041)
    ·
      refine ⟨73199026446274673310219031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97598701928366231080292041 73199026446274673310219031)
      ·
        refine ⟨109798539669412009965328547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73199026446274673310219031 109798539669412009965328547)
        ·
          refine ⟨164697809504118014947992821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109798539669412009965328547 164697809504118014947992821)
          ·
            refine ⟨15440419641011063901374327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 164697809504118014947992821 15440419641011063901374327)
            ·
              refine ⟨23160629461516595852061491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15440419641011063901374327 23160629461516595852061491)
              ·
                refine ⟨34740944192274893778092237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23160629461516595852061491 34740944192274893778092237)
                ·
                  refine ⟨13027854072103085166784589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34740944192274893778092237 13027854072103085166784589)
                  ·
                    refine ⟨4885445277038656937544221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13027854072103085166784589 4885445277038656937544221)
                    ·
                      refine ⟨1832041978889496351579083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4885445277038656937544221 1832041978889496351579083)
                      ·
                        rfl

theorem cell23_3567889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 3, 3].length) (baseStart_3567889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3567889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3567889 prefixEnd_3567889 := by exact prefixLift 3567889
  have htrace : WordTrace (prefixWord ++ tailWord_3567889) baseStart_3567889 baseEnd_3567889 := by
    simpa [prefixWord, tailWord_3567889, baseEnd_3567889] using wordTrace_append hprefix tailTrace_3567889
  have hstable : (prefixWord ++ tailWord_3567889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3567889).length < 2 ^ (prefixWord ++ tailWord_3567889).sum := by decide
  have hdescent : baseEnd_3567889 < baseStart_3567889 := by decide
  rcases family_descends (prefixWord ++ tailWord_3567889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3567916 : List Nat := [2, 2, 1, 1, 1, 3, 3, 2, 3, 3, 2]
def baseStart_3567916 : Nat := 118140960795 + 3567916 * 2 ^ 59
def prefixEnd_3567916 : Nat := 4983230072969 + 3 ^ 40 * 3567916 * 2
def baseEnd_3567916 : Nat := 1832055842867167745941459

theorem tailTrace_3567916 : CollatzResearch.WordTrace tailWord_3567916 prefixEnd_3567916 1832055842867167745941459 := by
  unfold tailWord_3567916
  simp only [CollatzResearch.WordTrace]
  refine ⟨65066293671028579192477801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86755058228038105589970401 65066293671028579192477801)
  ·
    refine ⟨48799720253271434394358351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65066293671028579192477801 48799720253271434394358351)
    ·
      refine ⟨73199580379907151591537527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48799720253271434394358351 73199580379907151591537527)
      ·
        refine ⟨109799370569860727387306291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73199580379907151591537527 109799370569860727387306291)
        ·
          refine ⟨164699055854791091080959437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109799370569860727387306291 164699055854791091080959437)
          ·
            refine ⟨61762145945546659155359789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 164699055854791091080959437 61762145945546659155359789)
            ·
              refine ⟨23160804729579997183259921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61762145945546659155359789 23160804729579997183259921)
              ·
                refine ⟨17370603547184997887444941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23160804729579997183259921 17370603547184997887444941)
                ·
                  refine ⟨6513976330194374207791853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17370603547184997887444941 6513976330194374207791853)
                  ·
                    refine ⟨2442741123822890327921945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6513976330194374207791853 2442741123822890327921945)
                    ·
                      refine ⟨1832055842867167745941459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2442741123822890327921945 1832055842867167745941459)
                      ·
                        rfl

theorem cell23_3567916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 3, 2].length) (baseStart_3567916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3567916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3567916 prefixEnd_3567916 := by exact prefixLift 3567916
  have htrace : WordTrace (prefixWord ++ tailWord_3567916) baseStart_3567916 baseEnd_3567916 := by
    simpa [prefixWord, tailWord_3567916, baseEnd_3567916] using wordTrace_append hprefix tailTrace_3567916
  have hstable : (prefixWord ++ tailWord_3567916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3567916).length < 2 ^ (prefixWord ++ tailWord_3567916).sum := by decide
  have hdescent : baseEnd_3567916 < baseStart_3567916 := by decide
  rcases family_descends (prefixWord ++ tailWord_3567916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3567957 : List Nat := [1, 3, 2, 2, 5, 1, 1, 2, 2, 1, 3]
def baseStart_3567957 : Nat := 118140960795 + 3567957 * 2 ^ 59
def prefixEnd_3567957 : Nat := 4983230072969 + 3 ^ 40 * 3567957 * 2
def baseEnd_3567957 : Nat := 1832076895574002085528771

theorem tailTrace_3567957 : CollatzResearch.WordTrace tailWord_3567957 prefixEnd_3567957 1832076895574002085528771 := by
  unfold tailWord_3567957
  simp only [CollatzResearch.WordTrace]
  refine ⟨130134082734908622387198125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86756055156605748258132083 130134082734908622387198125)
  ·
    refine ⟨48800281025590733395199297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130134082734908622387198125 48800281025590733395199297)
    ·
      refine ⟨36600210769193050046399473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48800281025590733395199297 36600210769193050046399473)
      ·
        refine ⟨27450158076894787534799605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36600210769193050046399473 27450158076894787534799605)
        ·
          refine ⟨2573452319708886331387463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 27450158076894787534799605 2573452319708886331387463)
          ·
            refine ⟨3860178479563329497081195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2573452319708886331387463 3860178479563329497081195)
            ·
              refine ⟨5790267719344994245621793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3860178479563329497081195 5790267719344994245621793)
              ·
                refine ⟨4342700789508745684216345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5790267719344994245621793 4342700789508745684216345)
                ·
                  refine ⟨3257025592131559263162259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4342700789508745684216345 3257025592131559263162259)
                  ·
                    refine ⟨4885538388197338894743389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3257025592131559263162259 4885538388197338894743389)
                    ·
                      refine ⟨1832076895574002085528771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4885538388197338894743389 1832076895574002085528771)
                      ·
                        rfl

theorem cell23_3567957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 5, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 5, 1, 1, 2, 2, 1, 3].length) (baseStart_3567957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3567957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3567957 prefixEnd_3567957 := by exact prefixLift 3567957
  have htrace : WordTrace (prefixWord ++ tailWord_3567957) baseStart_3567957 baseEnd_3567957 := by
    simpa [prefixWord, tailWord_3567957, baseEnd_3567957] using wordTrace_append hprefix tailTrace_3567957
  have hstable : (prefixWord ++ tailWord_3567957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3567957).length < 2 ^ (prefixWord ++ tailWord_3567957).sum := by decide
  have hdescent : baseEnd_3567957 < baseStart_3567957 := by decide
  rcases family_descends (prefixWord ++ tailWord_3567957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3567959 : List Nat := [1, 1, 3, 2, 3, 1, 1, 1, 4, 2, 4]
def baseStart_3567959 : Nat := 118140960795 + 3567959 * 2 ^ 59
def prefixEnd_3567959 : Nat := 4983230072969 + 3 ^ 40 * 3567959 * 2
def baseEnd_3567959 : Nat := 1832077922535311077703761

theorem tailTrace_3567959 : CollatzResearch.WordTrace tailWord_3567959 prefixEnd_3567959 1832077922535311077703761 := by
  unfold tailWord_3567959
  simp only [CollatzResearch.WordTrace]
  refine ⟨130134155680901376728770931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86756103787267584485847287 130134155680901376728770931)
  ·
    refine ⟨195201233521352065093156397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130134155680901376728770931 195201233521352065093156397)
    ·
      refine ⟨73200462570507024409933649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 195201233521352065093156397 73200462570507024409933649)
      ·
        refine ⟨54900346927880268307450237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73200462570507024409933649 54900346927880268307450237)
        ·
          refine ⟨20587630097955100615293839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54900346927880268307450237 20587630097955100615293839)
          ·
            refine ⟨30881445146932650922940759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20587630097955100615293839 30881445146932650922940759)
            ·
              refine ⟨46322167720398976384411139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30881445146932650922940759 46322167720398976384411139)
              ·
                refine ⟨69483251580598464576616709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46322167720398976384411139 69483251580598464576616709)
                ·
                  refine ⟨13028109671362212108115633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 69483251580598464576616709 13028109671362212108115633)
                  ·
                    refine ⟨9771082253521659081086725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13028109671362212108115633 9771082253521659081086725)
                    ·
                      refine ⟨1832077922535311077703761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9771082253521659081086725 1832077922535311077703761)
                      ·
                        rfl

theorem cell23_3567959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 1, 4, 2, 4].length) (baseStart_3567959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3567959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3567959 prefixEnd_3567959 := by exact prefixLift 3567959
  have htrace : WordTrace (prefixWord ++ tailWord_3567959) baseStart_3567959 baseEnd_3567959 := by
    simpa [prefixWord, tailWord_3567959, baseEnd_3567959] using wordTrace_append hprefix tailTrace_3567959
  have hstable : (prefixWord ++ tailWord_3567959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3567959).length < 2 ^ (prefixWord ++ tailWord_3567959).sum := by decide
  have hdescent : baseEnd_3567959 < baseStart_3567959 := by decide
  rcases family_descends (prefixWord ++ tailWord_3567959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3567976 : List Nat := [2, 1, 4, 2, 2, 1, 2, 1, 2, 2, 4]
def baseStart_3567976 : Nat := 118140960795 + 3567976 * 2 ^ 59
def prefixEnd_3567976 : Nat := 4983230072969 + 3 ^ 40 * 3567976 * 2
def baseEnd_3567976 : Nat := 1832086651706437511191183

theorem tailTrace_3567976 : CollatzResearch.WordTrace tailWord_3567976 prefixEnd_3567976 1832086651706437511191183 := by
  unfold tailWord_3567976
  simp only [CollatzResearch.WordTrace]
  refine ⟨65067387860919894316069891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86756517147893192421426521 65067387860919894316069891)
  ·
    refine ⟨97601081791379841474104837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65067387860919894316069891 97601081791379841474104837)
    ·
      refine ⟨18300202835883720276394657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 97601081791379841474104837 18300202835883720276394657)
      ·
        refine ⟨13725152126912790207295993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18300202835883720276394657 13725152126912790207295993)
        ·
          refine ⟨10293864095184592655471995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13725152126912790207295993 10293864095184592655471995)
          ·
            refine ⟨15440796142776888983207993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10293864095184592655471995 15440796142776888983207993)
            ·
              refine ⟨11580597107082666737405995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15440796142776888983207993 11580597107082666737405995)
              ·
                refine ⟨17370895660624000106108993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11580597107082666737405995 17370895660624000106108993)
                ·
                  refine ⟨13028171745468000079581745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17370895660624000106108993 13028171745468000079581745)
                  ·
                    refine ⟨9771128809101000059686309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13028171745468000079581745 9771128809101000059686309)
                    ·
                      refine ⟨1832086651706437511191183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9771128809101000059686309 1832086651706437511191183)
                      ·
                        rfl

theorem cell23_3567976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 2, 1, 2, 2, 4].length) (baseStart_3567976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3567976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3567976 prefixEnd_3567976 := by exact prefixLift 3567976
  have htrace : WordTrace (prefixWord ++ tailWord_3567976) baseStart_3567976 baseEnd_3567976 := by
    simpa [prefixWord, tailWord_3567976, baseEnd_3567976] using wordTrace_append hprefix tailTrace_3567976
  have hstable : (prefixWord ++ tailWord_3567976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3567976).length < 2 ^ (prefixWord ++ tailWord_3567976).sum := by decide
  have hdescent : baseEnd_3567976 < baseStart_3567976 := by decide
  rcases family_descends (prefixWord ++ tailWord_3567976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3567980 : List Nat := [2, 2, 1, 1, 6, 2, 1, 1, 1, 4, 2]
def baseStart_3567980 : Nat := 118140960795 + 3567980 * 2 ^ 59
def prefixEnd_3567980 : Nat := 4983230072969 + 3 ^ 40 * 3567980 * 2
def baseEnd_3567980 : Nat := 1832088705629055495541165

theorem tailTrace_3567980 : CollatzResearch.WordTrace tailWord_3567980 prefixEnd_3567980 1832088705629055495541165 := by
  unfold tailWord_3567980
  simp only [CollatzResearch.WordTrace]
  refine ⟨65067460806912648657642697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86756614409216864876856929 65067460806912648657642697)
  ·
    refine ⟨48800595605184486493232023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65067460806912648657642697 48800595605184486493232023)
    ·
      refine ⟨73200893407776729739848035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48800595605184486493232023 73200893407776729739848035)
      ·
        refine ⟨109801340111665094609772053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73200893407776729739848035 109801340111665094609772053)
        ·
          refine ⟨5146937817734301309833065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 109801340111665094609772053 5146937817734301309833065)
          ·
            refine ⟨3860203363300725982374799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5146937817734301309833065 3860203363300725982374799)
            ·
              refine ⟨5790305044951088973562199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3860203363300725982374799 5790305044951088973562199)
              ·
                refine ⟨8685457567426633460343299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5790305044951088973562199 8685457567426633460343299)
                ·
                  refine ⟨13028186351139950190514949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8685457567426633460343299 13028186351139950190514949)
                  ·
                    refine ⟨2442784940838740660721553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13028186351139950190514949 2442784940838740660721553)
                    ·
                      refine ⟨1832088705629055495541165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2442784940838740660721553 1832088705629055495541165)
                      ·
                        rfl

theorem cell23_3567980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 4, 2].length) (baseStart_3567980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3567980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3567980 prefixEnd_3567980 := by exact prefixLift 3567980
  have htrace : WordTrace (prefixWord ++ tailWord_3567980) baseStart_3567980 baseEnd_3567980 := by
    simpa [prefixWord, tailWord_3567980, baseEnd_3567980] using wordTrace_append hprefix tailTrace_3567980
  have hstable : (prefixWord ++ tailWord_3567980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3567980).length < 2 ^ (prefixWord ++ tailWord_3567980).sum := by decide
  have hdescent : baseEnd_3567980 < baseStart_3567980 := by decide
  rcases family_descends (prefixWord ++ tailWord_3567980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3568020 : List Nat := [2, 4, 2, 1, 4, 1, 1, 1, 7]
def baseStart_3568020 : Nat := 118140960795 + 3568020 * 2 ^ 59
def prefixEnd_3568020 : Nat := 4983230072969 + 3 ^ 40 * 3568020 * 2
def baseEnd_3568020 : Nat := 203567693872803926560109

theorem tailTrace_3568020 : CollatzResearch.WordTrace tailWord_3568020 prefixEnd_3568020 203567693872803926560109 := by
  unfold tailWord_3568020
  simp only [CollatzResearch.WordTrace]
  refine ⟨65068190266840192073370757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86757587022453589431161009 65068190266840192073370757)
  ·
    refine ⟨12200285675032536013757017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 65068190266840192073370757 12200285675032536013757017)
    ·
      refine ⟨9150214256274402010317763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12200285675032536013757017 9150214256274402010317763)
      ·
        refine ⟨13725321384411603015476645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9150214256274402010317763 13725321384411603015476645)
        ·
          refine ⟨2573497759577175565401871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13725321384411603015476645 2573497759577175565401871)
          ·
            refine ⟨3860246639365763348102807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2573497759577175565401871 3860246639365763348102807)
            ·
              refine ⟨5790369959048645022154211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3860246639365763348102807 5790369959048645022154211)
              ·
                refine ⟨8685554938572967533231317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5790369959048645022154211 8685554938572967533231317)
                ·
                  refine ⟨203567693872803926560109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8685554938572967533231317 203567693872803926560109)
                  ·
                    rfl

theorem cell23_3568020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 4, 1, 1, 1, 7].length) (baseStart_3568020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3568020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3568020 prefixEnd_3568020 := by exact prefixLift 3568020
  have htrace : WordTrace (prefixWord ++ tailWord_3568020) baseStart_3568020 baseEnd_3568020 := by
    simpa [prefixWord, tailWord_3568020, baseEnd_3568020] using wordTrace_append hprefix tailTrace_3568020
  have hstable : (prefixWord ++ tailWord_3568020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3568020).length < 2 ^ (prefixWord ++ tailWord_3568020).sum := by decide
  have hdescent : baseEnd_3568020 < baseStart_3568020 := by decide
  rcases family_descends (prefixWord ++ tailWord_3568020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3568026 : List Nat := [3, 1, 1, 4, 1, 3, 1, 1, 1, 2, 5]
def baseStart_3568026 : Nat := 118140960795 + 3568026 * 2 ^ 59
def prefixEnd_3568026 : Nat := 4983230072969 + 3 ^ 40 * 3568026 * 2
def baseEnd_3568026 : Nat := 1832112325739162315565953

theorem tailTrace_3568026 : CollatzResearch.WordTrace tailWord_3568026 prefixEnd_3568026 1832112325739162315565953 := by
  unfold tailWord_3568026
  simp only [CollatzResearch.WordTrace]
  refine ⟨32534149842914661792864983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86757732914439098114306621 32534149842914661792864983)
  ·
    refine ⟨48801224764371992689297475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32534149842914661792864983 48801224764371992689297475)
    ·
      refine ⟨73201837146557989033946213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48801224764371992689297475 73201837146557989033946213)
      ·
        refine ⟨13725344464979622943864915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 73201837146557989033946213 13725344464979622943864915)
        ·
          refine ⟨20588016697469434415797373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13725344464979622943864915 20588016697469434415797373)
          ·
            refine ⟨7720506261551037905924015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20588016697469434415797373 7720506261551037905924015)
            ·
              refine ⟨11580759392326556858886023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7720506261551037905924015 11580759392326556858886023)
              ·
                refine ⟨17371139088489835288329035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11580759392326556858886023 17371139088489835288329035)
                ·
                  refine ⟨26056708632734752932493553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17371139088489835288329035 26056708632734752932493553)
                  ·
                    refine ⟨19542531474551064699370165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26056708632734752932493553 19542531474551064699370165)
                    ·
                      refine ⟨1832112325739162315565953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19542531474551064699370165 1832112325739162315565953)
                      ·
                        rfl

theorem cell23_3568026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 1, 1, 1, 2, 5].length) (baseStart_3568026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3568026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3568026 prefixEnd_3568026 := by exact prefixLift 3568026
  have htrace : WordTrace (prefixWord ++ tailWord_3568026) baseStart_3568026 baseEnd_3568026 := by
    simpa [prefixWord, tailWord_3568026, baseEnd_3568026] using wordTrace_append hprefix tailTrace_3568026
  have hstable : (prefixWord ++ tailWord_3568026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3568026).length < 2 ^ (prefixWord ++ tailWord_3568026).sum := by decide
  have hdescent : baseEnd_3568026 < baseStart_3568026 := by decide
  rcases family_descends (prefixWord ++ tailWord_3568026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3568079 : List Nat := [1, 1, 2, 1, 1, 4, 1, 3, 1, 2, 6]
def baseStart_3568079 : Nat := 118140960795 + 3568079 * 2 ^ 59
def prefixEnd_3568079 : Nat := 4983230072969 + 3 ^ 40 * 3568079 * 2
def baseEnd_3568079 : Nat := 1832139540213850608203209

theorem tailTrace_3568079 : CollatzResearch.WordTrace tailWord_3568079 prefixEnd_3568079 1832139540213850608203209 := by
  unfold tailWord_3568079
  simp only [CollatzResearch.WordTrace]
  refine ⟨130138532440466637223139291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86759021626977758148759527 130138532440466637223139291)
  ·
    refine ⟨195207798660699955834708937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130138532440466637223139291 195207798660699955834708937)
    ·
      refine ⟨146405848995524966876031703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 195207798660699955834708937 146405848995524966876031703)
      ·
        refine ⟨219608773493287450314047555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146405848995524966876031703 219608773493287450314047555)
        ·
          refine ⟨329413160239931175471071333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 219608773493287450314047555 329413160239931175471071333)
          ·
            refine ⟨61764967544987095400825875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 329413160239931175471071333 61764967544987095400825875)
            ·
              refine ⟨92647451317480643101238813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61764967544987095400825875 92647451317480643101238813)
              ·
                refine ⟨34742794244055241162964555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 92647451317480643101238813 34742794244055241162964555)
                ·
                  refine ⟨52114191366082861744446833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34742794244055241162964555 52114191366082861744446833)
                  ·
                    refine ⟨39085643524562146308335125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 52114191366082861744446833 39085643524562146308335125)
                    ·
                      refine ⟨1832139540213850608203209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 39085643524562146308335125 1832139540213850608203209)
                      ·
                        rfl

theorem cell23_3568079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 3, 1, 2, 6].length) (baseStart_3568079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3568079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3568079 prefixEnd_3568079 := by exact prefixLift 3568079
  have htrace : WordTrace (prefixWord ++ tailWord_3568079) baseStart_3568079 baseEnd_3568079 := by
    simpa [prefixWord, tailWord_3568079, baseEnd_3568079] using wordTrace_append hprefix tailTrace_3568079
  have hstable : (prefixWord ++ tailWord_3568079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3568079).length < 2 ^ (prefixWord ++ tailWord_3568079).sum := by decide
  have hdescent : baseEnd_3568079 < baseStart_3568079 := by decide
  rcases family_descends (prefixWord ++ tailWord_3568079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3568113 : List Nat := [1, 2, 2, 2, 3, 1, 3, 1, 1, 5, 2]
def baseStart_3568113 : Nat := 118140960795 + 3568113 * 2 ^ 59
def prefixEnd_3568113 : Nat := 4983230072969 + 3 ^ 40 * 3568113 * 2
def baseEnd_3568113 : Nat := 1832156998556103475178053

theorem tailTrace_3568113 : CollatzResearch.WordTrace tailWord_3568113 prefixEnd_3568113 1832156998556103475178053 := by
  unfold tailWord_3568113
  simp only [CollatzResearch.WordTrace]
  refine ⟨130139772522343461029876993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86759848348228974019917995 130139772522343461029876993)
  ·
    refine ⟨97604829391757595772407745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130139772522343461029876993 97604829391757595772407745)
    ·
      refine ⟨73203622043818196829305809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97604829391757595772407745 73203622043818196829305809)
      ·
        refine ⟨54902716532863647621979357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73203622043818196829305809 54902716532863647621979357)
        ·
          refine ⟨20588518699823867858242259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54902716532863647621979357 20588518699823867858242259)
          ·
            refine ⟨30882778049735801787363389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20588518699823867858242259 30882778049735801787363389)
            ·
              refine ⟨11581041768650925670261271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30882778049735801787363389 11581041768650925670261271)
              ·
                refine ⟨17371562652976388505391907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11581041768650925670261271 17371562652976388505391907)
                ·
                  refine ⟨26057343979464582758087861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17371562652976388505391907 26057343979464582758087861)
                  ·
                    refine ⟨2442875998074804633570737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 26057343979464582758087861 2442875998074804633570737)
                    ·
                      refine ⟨1832156998556103475178053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2442875998074804633570737 1832156998556103475178053)
                      ·
                        rfl

theorem cell23_3568113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 3, 1, 1, 5, 2].length) (baseStart_3568113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3568113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3568113 prefixEnd_3568113 := by exact prefixLift 3568113
  have htrace : WordTrace (prefixWord ++ tailWord_3568113) baseStart_3568113 baseEnd_3568113 := by
    simpa [prefixWord, tailWord_3568113, baseEnd_3568113] using wordTrace_append hprefix tailTrace_3568113
  have hstable : (prefixWord ++ tailWord_3568113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3568113).length < 2 ^ (prefixWord ++ tailWord_3568113).sum := by decide
  have hdescent : baseEnd_3568113 < baseStart_3568113 := by decide
  rcases family_descends (prefixWord ++ tailWord_3568113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3568119 : List Nat := [1, 1, 3, 1, 1, 1, 1, 2, 2, 10]
def baseStart_3568119 : Nat := 118140960795 + 3568119 * 2 ^ 59
def prefixEnd_3568119 : Nat := 4983230072969 + 3 ^ 40 * 3568119 * 2
def baseEnd_3568119 : Nat := 610720026480010150567675

theorem tailTrace_3568119 : CollatzResearch.WordTrace tailWord_3568119 prefixEnd_3568119 610720026480010150567675 := by
  unfold tailWord_3568119
  simp only [CollatzResearch.WordTrace]
  refine ⟨130139991360321724054595411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86759994240214482703063607 130139991360321724054595411)
  ·
    refine ⟨195209987040482586081893117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130139991360321724054595411 195209987040482586081893117)
    ·
      refine ⟨73203745140180969780709919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 195209987040482586081893117 73203745140180969780709919)
      ·
        refine ⟨109805617710271454671064879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73203745140180969780709919 109805617710271454671064879)
        ·
          refine ⟨164708426565407182006597319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109805617710271454671064879 164708426565407182006597319)
          ·
            refine ⟨247062639848110773009895979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 164708426565407182006597319 247062639848110773009895979)
            ·
              refine ⟨370593959772166159514843969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 247062639848110773009895979 370593959772166159514843969)
              ·
                refine ⟨277945469829124619636132977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 370593959772166159514843969 277945469829124619636132977)
                ·
                  refine ⟨208459102371843464727099733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 277945469829124619636132977 208459102371843464727099733)
                  ·
                    refine ⟨610720026480010150567675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 208459102371843464727099733 610720026480010150567675)
                    ·
                      rfl

theorem cell23_3568119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 2, 2, 10].length) (baseStart_3568119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3568119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3568119 prefixEnd_3568119 := by exact prefixLift 3568119
  have htrace : WordTrace (prefixWord ++ tailWord_3568119) baseStart_3568119 baseEnd_3568119 := by
    simpa [prefixWord, tailWord_3568119, baseEnd_3568119] using wordTrace_append hprefix tailTrace_3568119
  have hstable : (prefixWord ++ tailWord_3568119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3568119).length < 2 ^ (prefixWord ++ tailWord_3568119).sum := by decide
  have hdescent : baseEnd_3568119 < baseStart_3568119 := by decide
  rcases family_descends (prefixWord ++ tailWord_3568119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3568245 : List Nat := [1, 3, 4, 2, 3, 1, 2, 2, 1, 2, 2]
def baseStart_3568245 : Nat := 118140960795 + 3568245 * 2 ^ 59
def prefixEnd_3568245 : Nat := 4983230072969 + 3 ^ 40 * 3568245 * 2
def baseEnd_3568245 : Nat := 1832224778002496958727447

theorem tailTrace_3568245 : CollatzResearch.WordTrace tailWord_3568245 prefixEnd_3568245 1832224778002496958727447 := by
  unfold tailWord_3568245
  simp only [CollatzResearch.WordTrace]
  refine ⟨130144586957865247573682189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86763057971910165049121459 130144586957865247573682189)
  ·
    refine ⟨48804220109199467840130821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130144586957865247573682189 48804220109199467840130821)
    ·
      refine ⟨9150791270474900220024529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48804220109199467840130821 9150791270474900220024529)
      ·
        refine ⟨6863093452856175165018397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9150791270474900220024529 6863093452856175165018397)
        ·
          refine ⟨2573660044821065686881899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6863093452856175165018397 2573660044821065686881899)
          ·
            refine ⟨3860490067231598530322849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2573660044821065686881899 3860490067231598530322849)
            ·
              refine ⟨2895367550423698897742137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3860490067231598530322849 2895367550423698897742137)
              ·
                refine ⟨2171525662817774173306603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2895367550423698897742137 2171525662817774173306603)
                ·
                  refine ⟨3257288494226661259959905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2171525662817774173306603 3257288494226661259959905)
                  ·
                    refine ⟨2442966370669995944969929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3257288494226661259959905 2442966370669995944969929)
                    ·
                      refine ⟨1832224778002496958727447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2442966370669995944969929 1832224778002496958727447)
                      ·
                        rfl

theorem cell23_3568245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 3, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 3, 1, 2, 2, 1, 2, 2].length) (baseStart_3568245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3568245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3568245 prefixEnd_3568245 := by exact prefixLift 3568245
  have htrace : WordTrace (prefixWord ++ tailWord_3568245) baseStart_3568245 baseEnd_3568245 := by
    simpa [prefixWord, tailWord_3568245, baseEnd_3568245] using wordTrace_append hprefix tailTrace_3568245
  have hstable : (prefixWord ++ tailWord_3568245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3568245).length < 2 ^ (prefixWord ++ tailWord_3568245).sum := by decide
  have hdescent : baseEnd_3568245 < baseStart_3568245 := by decide
  rcases family_descends (prefixWord ++ tailWord_3568245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3568250 : List Nat := [3, 1, 1, 1, 1, 1, 1, 2, 8, 2, 2]
def baseStart_3568250 : Nat := 118140960795 + 3568250 * 2 ^ 59
def prefixEnd_3568250 : Nat := 4983230072969 + 3 ^ 40 * 3568250 * 2
def baseEnd_3568250 : Nat := 1832227345405769439164923

theorem tailTrace_3568250 : CollatzResearch.WordTrace tailWord_3568250 prefixEnd_3568250 1832227345405769439164923 := by
  unfold tailWord_3568250
  simp only [CollatzResearch.WordTrace]
  refine ⟨32536192330711783356903551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86763179548564755618409469 32536192330711783356903551)
  ·
    refine ⟨48804288496067675035355327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32536192330711783356903551 48804288496067675035355327)
    ·
      refine ⟨73206432744101512553032991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48804288496067675035355327 73206432744101512553032991)
      ·
        refine ⟨109809649116152268829549487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73206432744101512553032991 109809649116152268829549487)
        ·
          refine ⟨164714473674228403244324231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109809649116152268829549487 164714473674228403244324231)
          ·
            refine ⟨247071710511342604866486347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 164714473674228403244324231 247071710511342604866486347)
            ·
              refine ⟨370607565767013907299729521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 247071710511342604866486347 370607565767013907299729521)
              ·
                refine ⟨277955674325260430474797141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 370607565767013907299729521 277955674325260430474797141)
                ·
                  refine ⟨3257293058499145669626529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 277955674325260430474797141 3257293058499145669626529)
                  ·
                    refine ⟨2442969793874359252219897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3257293058499145669626529 2442969793874359252219897)
                    ·
                      refine ⟨1832227345405769439164923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2442969793874359252219897 1832227345405769439164923)
                      ·
                        rfl

theorem cell23_3568250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 2, 8, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 2, 8, 2, 2].length) (baseStart_3568250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3568250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3568250 prefixEnd_3568250 := by exact prefixLift 3568250
  have htrace : WordTrace (prefixWord ++ tailWord_3568250) baseStart_3568250 baseEnd_3568250 := by
    simpa [prefixWord, tailWord_3568250, baseEnd_3568250] using wordTrace_append hprefix tailTrace_3568250
  have hstable : (prefixWord ++ tailWord_3568250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3568250).length < 2 ^ (prefixWord ++ tailWord_3568250).sum := by decide
  have hdescent : baseEnd_3568250 < baseStart_3568250 := by decide
  rcases family_descends (prefixWord ++ tailWord_3568250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3568263 : List Nat := [1, 1, 4, 2, 1, 2, 3, 1, 2, 2, 4]
def baseStart_3568263 : Nat := 118140960795 + 3568263 * 2 ^ 59
def prefixEnd_3568263 : Nat := 4983230072969 + 3 ^ 40 * 3568263 * 2
def baseEnd_3568263 : Nat := 1832234020654277888302363

theorem tailTrace_3568263 : CollatzResearch.WordTrace tailWord_3568263 prefixEnd_3568263 1832234020654277888302363 := by
  unfold tailWord_3568263
  simp only [CollatzResearch.WordTrace]
  refine ⟨130145243471800036647837443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86763495647866691098558295 130145243471800036647837443)
  ·
    refine ⟨195217865207700054971756165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130145243471800036647837443 195217865207700054971756165)
    ·
      refine ⟨36603349726443760307204281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 195217865207700054971756165 36603349726443760307204281)
      ·
        refine ⟨27452512294832820230403211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36603349726443760307204281 27452512294832820230403211)
        ·
          refine ⟨41178768442249230345604817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27452512294832820230403211 41178768442249230345604817)
          ·
            refine ⟨30884076331686922759203613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41178768442249230345604817 30884076331686922759203613)
            ·
              refine ⟨11581528624382596034701355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30884076331686922759203613 11581528624382596034701355)
              ·
                refine ⟨17372292936573894052052033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11581528624382596034701355 17372292936573894052052033)
                ·
                  refine ⟨13029219702430420539039025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17372292936573894052052033 13029219702430420539039025)
                  ·
                    refine ⟨9771914776822815404279269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13029219702430420539039025 9771914776822815404279269)
                    ·
                      refine ⟨1832234020654277888302363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9771914776822815404279269 1832234020654277888302363)
                      ·
                        rfl

theorem cell23_3568263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 3, 1, 2, 2, 4].length) (baseStart_3568263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3568263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3568263 prefixEnd_3568263 := by exact prefixLift 3568263
  have htrace : WordTrace (prefixWord ++ tailWord_3568263) baseStart_3568263 baseEnd_3568263 := by
    simpa [prefixWord, tailWord_3568263, baseEnd_3568263] using wordTrace_append hprefix tailTrace_3568263
  have hstable : (prefixWord ++ tailWord_3568263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3568263).length < 2 ^ (prefixWord ++ tailWord_3568263).sum := by decide
  have hdescent : baseEnd_3568263 < baseStart_3568263 := by decide
  rcases family_descends (prefixWord ++ tailWord_3568263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3568301 : List Nat := [1, 5, 2, 1, 1, 4, 1, 2, 2, 2, 2]
def baseStart_3568301 : Nat := 118140960795 + 3568301 * 2 ^ 59
def prefixEnd_3568301 : Nat := 4983230072969 + 3 ^ 40 * 3568301 * 2
def baseEnd_3568301 : Nat := 1832253532919148739627189

theorem tailTrace_3568301 : CollatzResearch.WordTrace tailWord_3568301 prefixEnd_3568301 1832253532919148739627189 := by
  unfold tailWord_3568301
  simp only [CollatzResearch.WordTrace]
  refine ⟨130146629445662369137720757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86764419630441579425147171 130146629445662369137720757)
  ·
    refine ⟨12201246510530847106661321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 130146629445662369137720757 12201246510530847106661321)
    ·
      refine ⟨9150934882898135329995991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12201246510530847106661321 9150934882898135329995991)
      ·
        refine ⟨13726402324347202994993987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9150934882898135329995991 13726402324347202994993987)
        ·
          refine ⟨20589603486520804492490981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13726402324347202994993987 20589603486520804492490981)
          ·
            refine ⟨3860550653722650842342059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20589603486520804492490981 3860550653722650842342059)
            ·
              refine ⟨5790825980583976263513089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3860550653722650842342059 5790825980583976263513089)
              ·
                refine ⟨4343119485437982197634817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5790825980583976263513089 4343119485437982197634817)
                ·
                  refine ⟨3257339614078486648226113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4343119485437982197634817 3257339614078486648226113)
                  ·
                    refine ⟨2443004710558864986169585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3257339614078486648226113 2443004710558864986169585)
                    ·
                      refine ⟨1832253532919148739627189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2443004710558864986169585 1832253532919148739627189)
                      ·
                        rfl

theorem cell23_3568301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 4, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 4, 1, 2, 2, 2, 2].length) (baseStart_3568301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3568301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3568301 prefixEnd_3568301 := by exact prefixLift 3568301
  have htrace : WordTrace (prefixWord ++ tailWord_3568301) baseStart_3568301 baseEnd_3568301 := by
    simpa [prefixWord, tailWord_3568301, baseEnd_3568301] using wordTrace_append hprefix tailTrace_3568301
  have hstable : (prefixWord ++ tailWord_3568301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3568301).length < 2 ^ (prefixWord ++ tailWord_3568301).sum := by decide
  have hdescent : baseEnd_3568301 < baseStart_3568301 := by decide
  rcases family_descends (prefixWord ++ tailWord_3568301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3568341 : List Nat := [1, 3, 2, 5, 2, 1, 1, 3, 5]
def baseStart_3568341 : Nat := 118140960795 + 3568341 * 2 ^ 59
def prefixEnd_3568341 : Nat := 4983230072969 + 3 ^ 40 * 3568341 * 2
def baseEnd_3568341 : Nat := 203586008016147620347445

theorem tailTrace_3568341 : CollatzResearch.WordTrace tailWord_3568341 prefixEnd_3568341 203586008016147620347445 := by
  unfold tailWord_3568341
  simp only [CollatzResearch.WordTrace]
  refine ⟨130148088365517455969176877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86765392243678303979451251 130148088365517455969176877)
  ·
    refine ⟨48805533137069045988441329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130148088365517455969176877 48805533137069045988441329)
    ·
      refine ⟨36604149852801784491330997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48805533137069045988441329 36604149852801784491330997)
      ·
        refine ⟨3431639048700167296062281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 36604149852801784491330997 3431639048700167296062281)
        ·
          refine ⟨2573729286525125472046711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3431639048700167296062281 2573729286525125472046711)
          ·
            refine ⟨3860593929787688208070067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2573729286525125472046711 3860593929787688208070067)
            ·
              refine ⟨5790890894681532312105101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3860593929787688208070067 5790890894681532312105101)
              ·
                refine ⟨2171584085505574617039413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5790890894681532312105101 2171584085505574617039413)
                ·
                  refine ⟨203586008016147620347445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2171584085505574617039413 203586008016147620347445)
                  ·
                    rfl

theorem cell23_3568341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 2, 1, 1, 3, 5].length) (baseStart_3568341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3568341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3568341 prefixEnd_3568341 := by exact prefixLift 3568341
  have htrace : WordTrace (prefixWord ++ tailWord_3568341) baseStart_3568341 baseEnd_3568341 := by
    simpa [prefixWord, tailWord_3568341, baseEnd_3568341] using wordTrace_append hprefix tailTrace_3568341
  have hstable : (prefixWord ++ tailWord_3568341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3568341).length < 2 ^ (prefixWord ++ tailWord_3568341).sum := by decide
  have hdescent : baseEnd_3568341 < baseStart_3568341 := by decide
  rcases family_descends (prefixWord ++ tailWord_3568341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3568363 : List Nat := [1, 1, 1, 1, 2, 4, 1, 6, 6]
def baseStart_3568363 : Nat := 118140960795 + 3568363 * 2 ^ 59
def prefixEnd_3568363 : Nat := 4983230072969 + 3 ^ 40 * 3568363 * 2
def baseEnd_3568363 : Nat := 203587263191080833005767

theorem tailTrace_3568363 : CollatzResearch.WordTrace tailWord_3568363 prefixEnd_3568363 203587263191080833005767 := by
  unfold tailWord_3568363
  simp only [CollatzResearch.WordTrace]
  refine ⟨130148890771437753726477743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86765927180958502484318495 130148890771437753726477743)
  ·
    refine ⟨195223336157156630589716615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130148890771437753726477743 195223336157156630589716615)
    ·
      refine ⟨292835004235734945884574923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195223336157156630589716615 292835004235734945884574923)
      ·
        refine ⟨439252506353602418826862385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 292835004235734945884574923 439252506353602418826862385)
        ·
          refine ⟨329439379765201814120146789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 439252506353602418826862385 329439379765201814120146789)
          ·
            refine ⟨61769883705975340147527523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 329439379765201814120146789 61769883705975340147527523)
            ·
              refine ⟨92654825558963010221291285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61769883705975340147527523 92654825558963010221291285)
              ·
                refine ⟨4343194948076391104123029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 92654825558963010221291285 4343194948076391104123029)
                ·
                  refine ⟨203587263191080833005767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4343194948076391104123029 203587263191080833005767)
                  ·
                    rfl

theorem cell23_3568363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 6, 6].length) (baseStart_3568363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3568363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3568363 prefixEnd_3568363 := by exact prefixLift 3568363
  have htrace : WordTrace (prefixWord ++ tailWord_3568363) baseStart_3568363 baseEnd_3568363 := by
    simpa [prefixWord, tailWord_3568363, baseEnd_3568363] using wordTrace_append hprefix tailTrace_3568363
  have hstable : (prefixWord ++ tailWord_3568363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3568363).length < 2 ^ (prefixWord ++ tailWord_3568363).sum := by decide
  have hdescent : baseEnd_3568363 < baseStart_3568363 := by decide
  rcases family_descends (prefixWord ++ tailWord_3568363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3568367 : List Nat := [1, 1, 2, 1, 5, 4, 1, 1, 3, 4]
def baseStart_3568367 : Nat := 118140960795 + 3568367 * 2 ^ 59
def prefixEnd_3568367 : Nat := 4983230072969 + 3 ^ 40 * 3568367 * 2
def baseEnd_3568367 : Nat := 610762474214115160467295

theorem tailTrace_3568367 : CollatzResearch.WordTrace tailWord_3568367 prefixEnd_3568367 610762474214115160467295 := by
  unfold tailWord_3568367
  simp only [CollatzResearch.WordTrace]
  refine ⟨130149036663423262409623355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86766024442282174939748903 130149036663423262409623355)
  ·
    refine ⟨195223554995134893614435033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130149036663423262409623355 195223554995134893614435033)
    ·
      refine ⟨146417666246351170210826275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 195223554995134893614435033 146417666246351170210826275)
      ·
        refine ⟨219626499369526755316239413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146417666246351170210826275 219626499369526755316239413)
        ·
          refine ⟨20589984315893133310897445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 219626499369526755316239413 20589984315893133310897445)
          ·
            refine ⟨3860622059229962495793271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20589984315893133310897445 3860622059229962495793271)
            ·
              refine ⟨5790933088844943743689907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3860622059229962495793271 5790933088844943743689907)
              ·
                refine ⟨8686399633267415615534861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5790933088844943743689907 8686399633267415615534861)
                ·
                  refine ⟨3257399862475280855825573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8686399633267415615534861 3257399862475280855825573)
                  ·
                    refine ⟨610762474214115160467295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3257399862475280855825573 610762474214115160467295)
                    ·
                      rfl

theorem cell23_3568367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 4, 1, 1, 3, 4].length) (baseStart_3568367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3568367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3568367 prefixEnd_3568367 := by exact prefixLift 3568367
  have htrace : WordTrace (prefixWord ++ tailWord_3568367) baseStart_3568367 baseEnd_3568367 := by
    simpa [prefixWord, tailWord_3568367, baseEnd_3568367] using wordTrace_append hprefix tailTrace_3568367
  have hstable : (prefixWord ++ tailWord_3568367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3568367).length < 2 ^ (prefixWord ++ tailWord_3568367).sum := by decide
  have hdescent : baseEnd_3568367 < baseStart_3568367 := by decide
  rcases family_descends (prefixWord ++ tailWord_3568367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3568380 : List Nat := [2, 2, 2, 1, 3, 3, 1, 3, 6]
def baseStart_3568380 : Nat := 118140960795 + 3568380 * 2 ^ 59
def prefixEnd_3568380 : Nat := 4983230072969 + 3 ^ 40 * 3568380 * 2
def baseEnd_3568380 : Nat := 203588233098983770059925

theorem tailTrace_3568380 : CollatzResearch.WordTrace tailWord_3568380 prefixEnd_3568380 203588233098983770059925 := by
  unfold tailWord_3568380
  simp only [CollatzResearch.WordTrace]
  refine ⟨65074755406188082814923297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86766340541584110419897729 65074755406188082814923297)
  ·
    refine ⟨48806066554641062111192473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65074755406188082814923297 48806066554641062111192473)
    ·
      refine ⟨36604549915980796583394355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48806066554641062111192473 36604549915980796583394355)
      ·
        refine ⟨54906824873971194875091533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36604549915980796583394355 54906824873971194875091533)
        ·
          refine ⟨20590059327739198078159325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54906824873971194875091533 20590059327739198078159325)
          ·
            refine ⟨7721272247902199279309747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20590059327739198078159325 7721272247902199279309747)
            ·
              refine ⟨11581908371853298918964621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7721272247902199279309747 11581908371853298918964621)
              ·
                refine ⟨4343215639444987094611733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11581908371853298918964621 4343215639444987094611733)
                ·
                  refine ⟨203588233098983770059925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4343215639444987094611733 203588233098983770059925)
                  ·
                    rfl

theorem cell23_3568380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 1, 3, 6].length) (baseStart_3568380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3568380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3568380 prefixEnd_3568380 := by exact prefixLift 3568380
  have htrace : WordTrace (prefixWord ++ tailWord_3568380) baseStart_3568380 baseEnd_3568380 := by
    simpa [prefixWord, tailWord_3568380, baseEnd_3568380] using wordTrace_append hprefix tailTrace_3568380
  have hstable : (prefixWord ++ tailWord_3568380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3568380).length < 2 ^ (prefixWord ++ tailWord_3568380).sum := by decide
  have hdescent : baseEnd_3568380 < baseStart_3568380 := by decide
  rcases family_descends (prefixWord ++ tailWord_3568380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3568417 : List Nat := [1, 2, 3, 2, 1, 2, 1, 4, 2, 3, 2]
def baseStart_3568417 : Nat := 118140960795 + 3568417 * 2 ^ 59
def prefixEnd_3568417 : Nat := 4983230072969 + 3 ^ 40 * 3568417 * 2
def baseEnd_3568417 : Nat := 1832313096675070285776655

theorem tailTrace_3568417 : CollatzResearch.WordTrace tailWord_3568417 prefixEnd_3568417 1832313096675070285776655 := by
  unfold tailWord_3568417
  simp only [CollatzResearch.WordTrace]
  refine ⟨130150860313242120948943505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86767240208828080632629003 130150860313242120948943505)
  ·
    refine ⟨97613145234931590711707629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130150860313242120948943505 97613145234931590711707629)
    ·
      refine ⟨36604929463099346516890361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 97613145234931590711707629 36604929463099346516890361)
      ·
        refine ⟨27453697097324509887667771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36604929463099346516890361 27453697097324509887667771)
        ·
          refine ⟨41180545645986764831501657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27453697097324509887667771 41180545645986764831501657)
          ·
            refine ⟨30885409234490073623626243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41180545645986764831501657 30885409234490073623626243)
            ·
              refine ⟨46328113851735110435439365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30885409234490073623626243 46328113851735110435439365)
              ·
                refine ⟨8686521347200333206644881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46328113851735110435439365 8686521347200333206644881)
                ·
                  refine ⟨6514891010400249904983661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8686521347200333206644881 6514891010400249904983661)
                  ·
                    refine ⟨2443084128900093714368873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6514891010400249904983661 2443084128900093714368873)
                    ·
                      refine ⟨1832313096675070285776655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2443084128900093714368873 1832313096675070285776655)
                      ·
                        rfl

theorem cell23_3568417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 4, 2, 3, 2].length) (baseStart_3568417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3568417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3568417 prefixEnd_3568417 := by exact prefixLift 3568417
  have htrace : WordTrace (prefixWord ++ tailWord_3568417) baseStart_3568417 baseEnd_3568417 := by
    simpa [prefixWord, tailWord_3568417, baseEnd_3568417] using wordTrace_append hprefix tailTrace_3568417
  have hstable : (prefixWord ++ tailWord_3568417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3568417).length < 2 ^ (prefixWord ++ tailWord_3568417).sum := by decide
  have hdescent : baseEnd_3568417 < baseStart_3568417 := by decide
  rcases family_descends (prefixWord ++ tailWord_3568417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3568440 : List Nat := [2, 1, 2, 1, 3, 2, 4, 1, 1, 6]
def baseStart_3568440 : Nat := 118140960795 + 3568440 * 2 ^ 59
def prefixEnd_3568440 : Nat := 4983230072969 + 3 ^ 40 * 3568440 * 2
def baseEnd_3568440 : Nat := 610774968910041231929683

theorem tailTrace_3568440 : CollatzResearch.WordTrace tailWord_3568440 prefixEnd_3568440 610774968910041231929683 := by
  unfold tailWord_3568440
  simp only [CollatzResearch.WordTrace]
  refine ⟨65075849596079397938515387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86767799461439197251353849 65075849596079397938515387)
  ·
    refine ⟨97613774394119096907773081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65075849596079397938515387 97613774394119096907773081)
    ·
      refine ⟨73210330795589322680829811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97613774394119096907773081 73210330795589322680829811)
      ·
        refine ⟨109815496193383984021244717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73210330795589322680829811 109815496193383984021244717)
        ·
          refine ⟨41180811072518994007966769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 109815496193383984021244717 41180811072518994007966769)
          ·
            refine ⟨30885608304389245505975077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41180811072518994007966769 30885608304389245505975077)
            ·
              refine ⟨5791051557072983532370327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30885608304389245505975077 5791051557072983532370327)
              ·
                refine ⟨8686577335609475298555491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5791051557072983532370327 8686577335609475298555491)
                ·
                  refine ⟨13029866003414212947833237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8686577335609475298555491 13029866003414212947833237)
                  ·
                    refine ⟨610774968910041231929683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13029866003414212947833237 610774968910041231929683)
                    ·
                      rfl

theorem cell23_3568440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 4, 1, 1, 6].length) (baseStart_3568440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3568440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3568440 prefixEnd_3568440 := by exact prefixLift 3568440
  have htrace : WordTrace (prefixWord ++ tailWord_3568440) baseStart_3568440 baseEnd_3568440 := by
    simpa [prefixWord, tailWord_3568440, baseEnd_3568440] using wordTrace_append hprefix tailTrace_3568440
  have hstable : (prefixWord ++ tailWord_3568440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3568440).length < 2 ^ (prefixWord ++ tailWord_3568440).sum := by decide
  have hdescent : baseEnd_3568440 < baseStart_3568440 := by decide
  rcases family_descends (prefixWord ++ tailWord_3568440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3568474 : List Nat := [3, 1, 1, 2, 1, 6, 1, 2, 2, 4]
def baseStart_3568474 : Nat := 118140960795 + 3568474 * 2 ^ 59
def prefixEnd_3568474 : Nat := 4983230072969 + 3 ^ 40 * 3568474 * 2
def baseEnd_3568474 : Nat := 610780788357458854254631

theorem tailTrace_3568474 : CollatzResearch.WordTrace tailWord_3568474 prefixEnd_3568474 610780788357458854254631 := by
  unfold tailWord_3568474
  simp only [CollatzResearch.WordTrace]
  refine ⟨32538234818508904920942119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86768626182690413122512317 32538234818508904920942119)
  ·
    refine ⟨48807352227763357381413179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32538234818508904920942119 48807352227763357381413179)
    ·
      refine ⟨73211028341645036072119769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48807352227763357381413179 73211028341645036072119769)
      ·
        refine ⟨54908271256233777054089827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73211028341645036072119769 54908271256233777054089827)
        ·
          refine ⟨82362406884350665581134741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54908271256233777054089827 82362406884350665581134741)
          ·
            refine ⟨3860737822703937449115691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 82362406884350665581134741 3860737822703937449115691)
            ·
              refine ⟨5791106734055906173673537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3860737822703937449115691 5791106734055906173673537)
              ·
                refine ⟨4343330050541929630255153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5791106734055906173673537 4343330050541929630255153)
                ·
                  refine ⟨3257497537906447222691365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4343330050541929630255153 3257497537906447222691365)
                  ·
                    refine ⟨610780788357458854254631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3257497537906447222691365 610780788357458854254631)
                    ·
                      rfl

theorem cell23_3568474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 6, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 6, 1, 2, 2, 4].length) (baseStart_3568474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3568474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3568474 prefixEnd_3568474 := by exact prefixLift 3568474
  have htrace : WordTrace (prefixWord ++ tailWord_3568474) baseStart_3568474 baseEnd_3568474 := by
    simpa [prefixWord, tailWord_3568474, baseEnd_3568474] using wordTrace_append hprefix tailTrace_3568474
  have hstable : (prefixWord ++ tailWord_3568474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3568474).length < 2 ^ (prefixWord ++ tailWord_3568474).sum := by decide
  have hdescent : baseEnd_3568474 < baseStart_3568474 := by decide
  rcases family_descends (prefixWord ++ tailWord_3568474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3568497 : List Nat := [1, 2, 2, 2, 1, 4, 3, 1, 1, 3, 3]
def baseStart_3568497 : Nat := 118140960795 + 3568497 * 2 ^ 59
def prefixEnd_3568497 : Nat := 4983230072969 + 3 ^ 40 * 3568497 * 2
def baseEnd_3568497 : Nat := 1832354175127429972776287

theorem tailTrace_3568497 : CollatzResearch.WordTrace tailWord_3568497 prefixEnd_3568497 1832354175127429972776287 := by
  unfold tailWord_3568497
  simp only [CollatzResearch.WordTrace]
  refine ⟨130153778152952294611855745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86769185435301529741237163 130153778152952294611855745)
  ·
    refine ⟨97615333614714220958891809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130153778152952294611855745 97615333614714220958891809)
    ·
      refine ⟨73211500211035665719168857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97615333614714220958891809 73211500211035665719168857)
      ·
        refine ⟨54908625158276749289376643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73211500211035665719168857 54908625158276749289376643)
        ·
          refine ⟨82362937737415123934064965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54908625158276749289376643 82362937737415123934064965)
          ·
            refine ⟨15443050825765335737637181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 82362937737415123934064965 15443050825765335737637181)
            ·
              refine ⟨5791144059662000901613943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15443050825765335737637181 5791144059662000901613943)
              ·
                refine ⟨8686716089493001352420915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5791144059662000901613943 8686716089493001352420915)
                ·
                  refine ⟨13030074134239502028631373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8686716089493001352420915 13030074134239502028631373)
                  ·
                    refine ⟨4886277800339813260736765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13030074134239502028631373 4886277800339813260736765)
                    ·
                      refine ⟨1832354175127429972776287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4886277800339813260736765 1832354175127429972776287)
                      ·
                        rfl

theorem cell23_3568497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 3, 1, 1, 3, 3].length) (baseStart_3568497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3568497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3568497 prefixEnd_3568497 := by exact prefixLift 3568497
  have htrace : WordTrace (prefixWord ++ tailWord_3568497) baseStart_3568497 baseEnd_3568497 := by
    simpa [prefixWord, tailWord_3568497, baseEnd_3568497] using wordTrace_append hprefix tailTrace_3568497
  have hstable : (prefixWord ++ tailWord_3568497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3568497).length < 2 ^ (prefixWord ++ tailWord_3568497).sum := by decide
  have hdescent : baseEnd_3568497 < baseStart_3568497 := by decide
  rcases family_descends (prefixWord ++ tailWord_3568497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3568507 : List Nat := [1, 1, 1, 1, 1, 5, 2, 3, 3, 3, 2]
def baseStart_3568507 : Nat := 118140960795 + 3568507 * 2 ^ 59
def prefixEnd_3568507 : Nat := 4983230072969 + 3 ^ 40 * 3568507 * 2
def baseEnd_3568507 : Nat := 1832359309933974933651241

theorem tailTrace_3568507 : CollatzResearch.WordTrace tailWord_3568507 prefixEnd_3568507 1832359309933974933651241 := by
  unfold tailWord_3568507
  simp only [CollatzResearch.WordTrace]
  refine ⟨130154142882916066319719775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86769428588610710879813183 130154142882916066319719775)
  ·
    refine ⟨195231214324374099479579663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130154142882916066319719775 195231214324374099479579663)
    ·
      refine ⟨292846821486561149219369495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195231214324374099479579663 292846821486561149219369495)
      ·
        refine ⟨439270232229841723829054243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 292846821486561149219369495 439270232229841723829054243)
        ·
          refine ⟨658905348344762585743581365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 439270232229841723829054243 658905348344762585743581365)
          ·
            refine ⟨61772376407321492413460753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 658905348344762585743581365 61772376407321492413460753)
            ·
              refine ⟨46329282305491119310095565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61772376407321492413460753 46329282305491119310095565)
              ·
                refine ⟨17373480864559169741285837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46329282305491119310095565 17373480864559169741285837)
                ·
                  refine ⟨6515055324209688652982189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17373480864559169741285837 6515055324209688652982189)
                  ·
                    refine ⟨2443145746578633244868321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6515055324209688652982189 2443145746578633244868321)
                    ·
                      refine ⟨1832359309933974933651241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2443145746578633244868321 1832359309933974933651241)
                      ·
                        rfl

theorem cell23_3568507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 3, 3, 3, 2].length) (baseStart_3568507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3568507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3568507 prefixEnd_3568507 := by exact prefixLift 3568507
  have htrace : WordTrace (prefixWord ++ tailWord_3568507) baseStart_3568507 baseEnd_3568507 := by
    simpa [prefixWord, tailWord_3568507, baseEnd_3568507] using wordTrace_append hprefix tailTrace_3568507
  have hstable : (prefixWord ++ tailWord_3568507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3568507).length < 2 ^ (prefixWord ++ tailWord_3568507).sum := by decide
  have hdescent : baseEnd_3568507 < baseStart_3568507 := by decide
  rcases family_descends (prefixWord ++ tailWord_3568507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3568524 : List Nat := [2, 2, 1, 2, 1, 2, 4, 3, 1, 3, 2]
def baseStart_3568524 : Nat := 118140960795 + 3568524 * 2 ^ 59
def prefixEnd_3568524 : Nat := 4983230072969 + 3 ^ 40 * 3568524 * 2
def baseEnd_3568524 : Nat := 1832368039105101367138663

theorem tailTrace_3568524 : CollatzResearch.WordTrace tailWord_3568524 prefixEnd_3568524 1832368039105101367138663 := by
  unfold tailWord_3568524
  simp only [CollatzResearch.WordTrace]
  refine ⟨65077381461927239111544313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86769841949236318815392417 65077381461927239111544313)
  ·
    refine ⟨48808036096445429333658235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65077381461927239111544313 48808036096445429333658235)
    ·
      refine ⟨73212054144668144000487353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48808036096445429333658235 73212054144668144000487353)
      ·
        refine ⟨54909040608501108000365515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73212054144668144000487353 54909040608501108000365515)
        ·
          refine ⟨82363560912751662000548273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54909040608501108000365515 82363560912751662000548273)
          ·
            refine ⟨61772670684563746500411205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82363560912751662000548273 61772670684563746500411205)
            ·
              refine ⟨11582375753355702468827101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 61772670684563746500411205 11582375753355702468827101)
              ·
                refine ⟨4343390907508388425810163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11582375753355702468827101 4343390907508388425810163)
                ·
                  refine ⟨6515086361262582638715245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4343390907508388425810163 6515086361262582638715245)
                  ·
                    refine ⟨2443157385473468489518217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6515086361262582638715245 2443157385473468489518217)
                    ·
                      refine ⟨1832368039105101367138663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2443157385473468489518217 1832368039105101367138663)
                      ·
                        rfl

theorem cell23_3568524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 4, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 4, 3, 1, 3, 2].length) (baseStart_3568524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3568524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3568524 prefixEnd_3568524 := by exact prefixLift 3568524
  have htrace : WordTrace (prefixWord ++ tailWord_3568524) baseStart_3568524 baseEnd_3568524 := by
    simpa [prefixWord, tailWord_3568524, baseEnd_3568524] using wordTrace_append hprefix tailTrace_3568524
  have hstable : (prefixWord ++ tailWord_3568524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3568524).length < 2 ^ (prefixWord ++ tailWord_3568524).sum := by decide
  have hdescent : baseEnd_3568524 < baseStart_3568524 := by decide
  rcases family_descends (prefixWord ++ tailWord_3568524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3568637 : List Nat := [1, 4, 1, 1, 1, 2, 1, 1, 7, 4]
def baseStart_3568637 : Nat := 118140960795 + 3568637 * 2 ^ 59
def prefixEnd_3568637 : Nat := 4983230072969 + 3 ^ 40 * 3568637 * 2
def baseEnd_3568637 : Nat := 610808687473019808341881

theorem tailTrace_3568637 : CollatzResearch.WordTrace tailWord_3568637 prefixEnd_3568637 610808687473019808341881 := by
  unfold tailWord_3568637
  simp only [CollatzResearch.WordTrace]
  refine ⟨130158884372445098521952165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86772589581630065681301443 130158884372445098521952165)
  ·
    refine ⟨24404790819833455972866031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 130158884372445098521952165 24404790819833455972866031)
    ·
      refine ⟨36607186229750183959299047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24404790819833455972866031 36607186229750183959299047)
      ·
        refine ⟨54910779344625275938948571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36607186229750183959299047 54910779344625275938948571)
        ·
          refine ⟨82366169016937913908422857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54910779344625275938948571 82366169016937913908422857)
          ·
            refine ⟨61774626762703435431317143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82366169016937913908422857 61774626762703435431317143)
            ·
              refine ⟨92661940144055153146975715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61774626762703435431317143 92661940144055153146975715)
              ·
                refine ⟨138992910216082729720463573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92661940144055153146975715 138992910216082729720463573)
                ·
                  refine ⟨3257646333189438977823365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 138992910216082729720463573 3257646333189438977823365)
                  ·
                    refine ⟨610808687473019808341881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3257646333189438977823365 610808687473019808341881)
                    ·
                      rfl

theorem cell23_3568637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 1, 7, 4].length) (baseStart_3568637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3568637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3568637 prefixEnd_3568637 := by exact prefixLift 3568637
  have htrace : WordTrace (prefixWord ++ tailWord_3568637) baseStart_3568637 baseEnd_3568637 := by
    simpa [prefixWord, tailWord_3568637, baseEnd_3568637] using wordTrace_append hprefix tailTrace_3568637
  have hstable : (prefixWord ++ tailWord_3568637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3568637).length < 2 ^ (prefixWord ++ tailWord_3568637).sum := by decide
  have hdescent : baseEnd_3568637 < baseStart_3568637 := by decide
  rcases family_descends (prefixWord ++ tailWord_3568637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3568654 : List Nat := [4, 1, 1, 2, 2, 2, 1, 3, 3, 4]
def baseStart_3568654 : Nat := 118140960795 + 3568654 * 2 ^ 59
def prefixEnd_3568654 : Nat := 4983230072969 + 3 ^ 40 * 3568654 * 2
def baseEnd_3568654 : Nat := 610811597196728619504355

theorem tailTrace_3568654 : CollatzResearch.WordTrace tailWord_3568654 prefixEnd_3568654 610811597196728619504355 := by
  unfold tailWord_3568654
  simp only [CollatzResearch.WordTrace]
  refine ⟨16269938051672938803165127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 86773002942255673616880677 16269938051672938803165127)
  ·
    refine ⟨24404907077509408204747691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16269938051672938803165127 24404907077509408204747691)
    ·
      refine ⟨36607360616264112307121537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24404907077509408204747691 36607360616264112307121537)
      ·
        refine ⟨27455520462198084230341153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36607360616264112307121537 27455520462198084230341153)
        ·
          refine ⟨20591640346648563172755865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27455520462198084230341153 20591640346648563172755865)
          ·
            refine ⟨15443730259986422379566899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20591640346648563172755865 15443730259986422379566899)
            ·
              refine ⟨23165595389979633569350349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15443730259986422379566899 23165595389979633569350349)
              ·
                refine ⟨8687098271242362588506381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23165595389979633569350349 8687098271242362588506381)
                ·
                  refine ⟨3257661851715885970689893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8687098271242362588506381 3257661851715885970689893)
                  ·
                    refine ⟨610811597196728619504355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3257661851715885970689893 610811597196728619504355)
                    ·
                      rfl

theorem cell23_3568654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 1, 3, 3, 4].length) (baseStart_3568654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3568654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3568654 prefixEnd_3568654 := by exact prefixLift 3568654
  have htrace : WordTrace (prefixWord ++ tailWord_3568654) baseStart_3568654 baseEnd_3568654 := by
    simpa [prefixWord, tailWord_3568654, baseEnd_3568654] using wordTrace_append hprefix tailTrace_3568654
  have hstable : (prefixWord ++ tailWord_3568654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3568654).length < 2 ^ (prefixWord ++ tailWord_3568654).sum := by decide
  have hdescent : baseEnd_3568654 < baseStart_3568654 := by decide
  rcases family_descends (prefixWord ++ tailWord_3568654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3568677 : List Nat := [1, 3, 1, 2, 2, 2, 1, 1, 2, 5, 3]
def baseStart_3568677 : Nat := 118140960795 + 3568677 * 2 ^ 59
def prefixEnd_3568677 : Nat := 4983230072969 + 3 ^ 40 * 3568677 * 2
def baseEnd_3568677 : Nat := 1832446601645239268525459

theorem tailTrace_3568677 : CollatzResearch.WordTrace tailWord_3568677 prefixEnd_3568677 1832446601645239268525459 := by
  unfold tailWord_3568677
  simp only [CollatzResearch.WordTrace]
  refine ⟨130160343292300185353408285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86773562194866790235605523 130160343292300185353408285)
  ·
    refine ⟨48810128734612569507528107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130160343292300185353408285 48810128734612569507528107)
    ·
      refine ⟨73215193101918854261292161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48810128734612569507528107 73215193101918854261292161)
      ·
        refine ⟨54911394826439140695969121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73215193101918854261292161 54911394826439140695969121)
        ·
          refine ⟨41183546119829355521976841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54911394826439140695969121 41183546119829355521976841)
          ·
            refine ⟨30887659589872016641482631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41183546119829355521976841 30887659589872016641482631)
            ·
              refine ⟨46331489384808024962223947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30887659589872016641482631 46331489384808024962223947)
              ·
                refine ⟨69497234077212037443335921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46331489384808024962223947 69497234077212037443335921)
                ·
                  refine ⟨52122925557909028082501941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 69497234077212037443335921 52122925557909028082501941)
                  ·
                    refine ⟨4886524271053971382734557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 52122925557909028082501941 4886524271053971382734557)
                    ·
                      refine ⟨1832446601645239268525459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4886524271053971382734557 1832446601645239268525459)
                      ·
                        rfl

theorem cell23_3568677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 1, 2, 5, 3].length) (baseStart_3568677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3568677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3568677 prefixEnd_3568677 := by exact prefixLift 3568677
  have htrace : WordTrace (prefixWord ++ tailWord_3568677) baseStart_3568677 baseEnd_3568677 := by
    simpa [prefixWord, tailWord_3568677, baseEnd_3568677] using wordTrace_append hprefix tailTrace_3568677
  have hstable : (prefixWord ++ tailWord_3568677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3568677).length < 2 ^ (prefixWord ++ tailWord_3568677).sum := by decide
  have hdescent : baseEnd_3568677 < baseStart_3568677 := by decide
  rcases family_descends (prefixWord ++ tailWord_3568677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3568705 : List Nat := [1, 2, 5, 1, 3, 1, 3, 2, 1, 4]
def baseStart_3568705 : Nat := 118140960795 + 3568705 * 2 ^ 59
def prefixEnd_3568705 : Nat := 4983230072969 + 3 ^ 40 * 3568705 * 2
def baseEnd_3568705 : Nat := 610820326367855052991777

theorem tailTrace_3568705 : CollatzResearch.WordTrace tailWord_3568705 prefixEnd_3568705 610820326367855052991777 := by
  unfold tailWord_3568705
  simp only [CollatzResearch.WordTrace]
  refine ⟨130161364536198746135427569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86774243024132497423618379 130161364536198746135427569)
  ·
    refine ⟨97621023402149059601570677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130161364536198746135427569 97621023402149059601570677)
    ·
      refine ⟨9151970943951474337647251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 97621023402149059601570677 9151970943951474337647251)
      ·
        refine ⟨13727956415927211506470877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9151970943951474337647251 13727956415927211506470877)
        ·
          refine ⟨5147983655972704314926579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13727956415927211506470877 5147983655972704314926579)
          ·
            refine ⟨7721975483959056472389869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5147983655972704314926579 7721975483959056472389869)
            ·
              refine ⟨2895740806484646177146201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7721975483959056472389869 2895740806484646177146201)
              ·
                refine ⟨2171805604863484632859651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2895740806484646177146201 2171805604863484632859651)
                ·
                  refine ⟨3257708407295226949289477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2171805604863484632859651 3257708407295226949289477)
                  ·
                    refine ⟨610820326367855052991777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3257708407295226949289477 610820326367855052991777)
                    ·
                      rfl

theorem cell23_3568705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 3, 2, 1, 4].length) (baseStart_3568705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3568705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3568705 prefixEnd_3568705 := by exact prefixLift 3568705
  have htrace : WordTrace (prefixWord ++ tailWord_3568705) baseStart_3568705 baseEnd_3568705 := by
    simpa [prefixWord, tailWord_3568705, baseEnd_3568705] using wordTrace_append hprefix tailTrace_3568705
  have hstable : (prefixWord ++ tailWord_3568705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3568705).length < 2 ^ (prefixWord ++ tailWord_3568705).sum := by decide
  have hdescent : baseEnd_3568705 < baseStart_3568705 := by decide
  rcases family_descends (prefixWord ++ tailWord_3568705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3568711 : List Nat := [1, 1, 4, 1, 3, 2, 3, 1, 3, 1, 3]
def baseStart_3568711 : Nat := 118140960795 + 3568711 * 2 ^ 59
def prefixEnd_3568711 : Nat := 4983230072969 + 3 ^ 40 * 3568711 * 2
def baseEnd_3568711 : Nat := 1832464059987492135500303

theorem tailTrace_3568711 : CollatzResearch.WordTrace tailWord_3568711 prefixEnd_3568711 1832464059987492135500303 := by
  unfold tailWord_3568711
  simp only [CollatzResearch.WordTrace]
  refine ⟨130161583374177009160145987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86774388916118006106763991 130161583374177009160145987)
  ·
    refine ⟨195242375061265513740218981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130161583374177009160145987 195242375061265513740218981)
    ·
      refine ⟨36607945323987283826291059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 195242375061265513740218981 36607945323987283826291059)
      ·
        refine ⟨54911917985980925739436589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36607945323987283826291059 54911917985980925739436589)
        ·
          refine ⟨20591969244742847152288721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54911917985980925739436589 20591969244742847152288721)
          ·
            refine ⟨15443976933557135364216541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20591969244742847152288721 15443976933557135364216541)
            ·
              refine ⟨5791491350083925761581203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15443976933557135364216541 5791491350083925761581203)
              ·
                refine ⟨8687237025125888642371805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5791491350083925761581203 8687237025125888642371805)
                ·
                  refine ⟨3257713884422208240889427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8687237025125888642371805 3257713884422208240889427)
                  ·
                    refine ⟨4886570826633312361334141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3257713884422208240889427 4886570826633312361334141)
                    ·
                      refine ⟨1832464059987492135500303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4886570826633312361334141 1832464059987492135500303)
                      ·
                        rfl

theorem cell23_3568711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 3, 1, 3, 1, 3].length) (baseStart_3568711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3568711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3568711 prefixEnd_3568711 := by exact prefixLift 3568711
  have htrace : WordTrace (prefixWord ++ tailWord_3568711) baseStart_3568711 baseEnd_3568711 := by
    simpa [prefixWord, tailWord_3568711, baseEnd_3568711] using wordTrace_append hprefix tailTrace_3568711
  have hstable : (prefixWord ++ tailWord_3568711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3568711).length < 2 ^ (prefixWord ++ tailWord_3568711).sum := by decide
  have hdescent : baseEnd_3568711 < baseStart_3568711 := by decide
  rcases family_descends (prefixWord ++ tailWord_3568711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3568727 : List Nat := [1, 1, 3, 2, 2, 1, 1, 5, 1, 6]
def baseStart_3568727 : Nat := 118140960795 + 3568727 * 2 ^ 59
def prefixEnd_3568727 : Nat := 4983230072969 + 3 ^ 40 * 3568727 * 2
def baseEnd_3568727 : Nat := 610824091892654690966743

theorem tailTrace_3568727 : CollatzResearch.WordTrace tailWord_3568727 prefixEnd_3568727 610824091892654690966743 := by
  unfold tailWord_3568727
  simp only [CollatzResearch.WordTrace]
  refine ⟨130162166942119043892728435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86774777961412695928485623 130162166942119043892728435)
  ·
    refine ⟨195243250413178565839092653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130162166942119043892728435 195243250413178565839092653)
    ·
      refine ⟨73216218904941962189659745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 195243250413178565839092653 73216218904941962189659745)
      ·
        refine ⟨54912164178706471642244809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73216218904941962189659745 54912164178706471642244809)
        ·
          refine ⟨41184123134029853731683607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54912164178706471642244809 41184123134029853731683607)
          ·
            refine ⟨61776184701044780597525411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41184123134029853731683607 61776184701044780597525411)
            ·
              refine ⟨92664277051567170896288117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61776184701044780597525411 92664277051567170896288117)
              ·
                refine ⟨8687275973584422271527011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 92664277051567170896288117 8687275973584422271527011)
                ·
                  refine ⟨13030913960376633407290517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8687275973584422271527011 13030913960376633407290517)
                  ·
                    refine ⟨610824091892654690966743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13030913960376633407290517 610824091892654690966743)
                    ·
                      rfl

theorem cell23_3568727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 5, 1, 6].length) (baseStart_3568727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3568727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3568727 prefixEnd_3568727 := by exact prefixLift 3568727
  have htrace : WordTrace (prefixWord ++ tailWord_3568727) baseStart_3568727 baseEnd_3568727 := by
    simpa [prefixWord, tailWord_3568727, baseEnd_3568727] using wordTrace_append hprefix tailTrace_3568727
  have hstable : (prefixWord ++ tailWord_3568727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3568727).length < 2 ^ (prefixWord ++ tailWord_3568727).sum := by decide
  have hdescent : baseEnd_3568727 < baseStart_3568727 := by decide
  rcases family_descends (prefixWord ++ tailWord_3568727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3568737 : List Nat := [1, 2, 3, 1, 1, 2, 2, 2, 3, 1, 5]
def baseStart_3568737 : Nat := 118140960795 + 3568737 * 2 ^ 59
def prefixEnd_3568737 : Nat := 4983230072969 + 3 ^ 40 * 3568737 * 2
def baseEnd_3568737 : Nat := 1832477410484509033775183

theorem tailTrace_3568737 : CollatzResearch.WordTrace tailWord_3568737 prefixEnd_3568737 1832477410484509033775183 := by
  unfold tailWord_3568737
  simp only [CollatzResearch.WordTrace]
  refine ⟨130162531672082815600592465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86775021114721877067061643 130162531672082815600592465)
  ·
    refine ⟨97621898754062111700444349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130162531672082815600592465 97621898754062111700444349)
    ·
      refine ⟨36608212032773291887666631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 97621898754062111700444349 36608212032773291887666631)
      ·
        refine ⟨54912318049159937831499947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36608212032773291887666631 54912318049159937831499947)
        ·
          refine ⟨82368477073739906747249921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54912318049159937831499947 82368477073739906747249921)
          ·
            refine ⟨61776357805304930060437441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82368477073739906747249921 61776357805304930060437441)
            ·
              refine ⟨46332268353978697545328081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61776357805304930060437441 46332268353978697545328081)
              ·
                refine ⟨34749201265484023158996061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46332268353978697545328081 34749201265484023158996061)
                ·
                  refine ⟨13030950474556508684623523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34749201265484023158996061 13030950474556508684623523)
                  ·
                    refine ⟨19546425711834763026935285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13030950474556508684623523 19546425711834763026935285)
                    ·
                      refine ⟨1832477410484509033775183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19546425711834763026935285 1832477410484509033775183)
                      ·
                        rfl

theorem cell23_3568737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 2, 3, 1, 5].length) (baseStart_3568737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3568737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3568737 prefixEnd_3568737 := by exact prefixLift 3568737
  have htrace : WordTrace (prefixWord ++ tailWord_3568737) baseStart_3568737 baseEnd_3568737 := by
    simpa [prefixWord, tailWord_3568737, baseEnd_3568737] using wordTrace_append hprefix tailTrace_3568737
  have hstable : (prefixWord ++ tailWord_3568737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3568737).length < 2 ^ (prefixWord ++ tailWord_3568737).sum := by decide
  have hdescent : baseEnd_3568737 < baseStart_3568737 := by decide
  rcases family_descends (prefixWord ++ tailWord_3568737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3568738 : List Nat := [3, 3, 2, 2, 1, 1, 1, 3, 2, 3, 2]
def baseStart_3568738 : Nat := 118140960795 + 3568738 * 2 ^ 59
def prefixEnd_3568738 : Nat := 4983230072969 + 3 ^ 40 * 3568738 * 2
def baseEnd_3568738 : Nat := 1832477923965163529862679

theorem tailTrace_3568738 : CollatzResearch.WordTrace tailWord_3568738 prefixEnd_3568738 1832477923965163529862679 := by
  unfold tailWord_3568738
  simp only [CollatzResearch.WordTrace]
  refine ⟨32540642036269798192844717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86775045430052795180919245 32540642036269798192844717)
  ·
    refine ⟨12202740763601174322316769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32540642036269798192844717 12202740763601174322316769)
    ·
      refine ⟨9152055572700880741737577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12202740763601174322316769 9152055572700880741737577)
      ·
        refine ⟨6864041679525660556303183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9152055572700880741737577 6864041679525660556303183)
        ·
          refine ⟨10296062519288490834454775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6864041679525660556303183 10296062519288490834454775)
          ·
            refine ⟨15444093778932736251682163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10296062519288490834454775 15444093778932736251682163)
            ·
              refine ⟨23166140668399104377523245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15444093778932736251682163 23166140668399104377523245)
              ·
                refine ⟨8687302750649664141571217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23166140668399104377523245 8687302750649664141571217)
                ·
                  refine ⟨6515477062987248106178413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8687302750649664141571217 6515477062987248106178413)
                  ·
                    refine ⟨2443303898620218039816905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6515477062987248106178413 2443303898620218039816905)
                    ·
                      refine ⟨1832477923965163529862679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2443303898620218039816905 1832477923965163529862679)
                      ·
                        rfl

theorem cell23_3568738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 1, 3, 2, 3, 2].length) (baseStart_3568738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3568738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3568738 prefixEnd_3568738 := by exact prefixLift 3568738
  have htrace : WordTrace (prefixWord ++ tailWord_3568738) baseStart_3568738 baseEnd_3568738 := by
    simpa [prefixWord, tailWord_3568738, baseEnd_3568738] using wordTrace_append hprefix tailTrace_3568738
  have hstable : (prefixWord ++ tailWord_3568738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3568738).length < 2 ^ (prefixWord ++ tailWord_3568738).sum := by decide
  have hdescent : baseEnd_3568738 < baseStart_3568738 := by decide
  rcases family_descends (prefixWord ++ tailWord_3568738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3568751 : List Nat := [1, 1, 2, 1, 3, 3, 5, 1, 1, 1, 4]
def baseStart_3568751 : Nat := 118140960795 + 3568751 * 2 ^ 59
def prefixEnd_3568751 : Nat := 4983230072969 + 3 ^ 40 * 3568751 * 2
def baseEnd_3568751 : Nat := 1832484599213671979000119

theorem tailTrace_3568751 : CollatzResearch.WordTrace tailWord_3568751 prefixEnd_3568751 1832484599213671979000119 := by
  unfold tailWord_3568751
  simp only [CollatzResearch.WordTrace]
  refine ⟨130163042294032095991602107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86775361529354730661068071 130163042294032095991602107)
  ·
    refine ⟨195244563441048143987403161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130163042294032095991602107 195244563441048143987403161)
    ·
      refine ⟨146433422580786107990552371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 195244563441048143987403161 146433422580786107990552371)
      ·
        refine ⟨219650133871179161985828557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146433422580786107990552371 219650133871179161985828557)
        ·
          refine ⟨82368800201692185744685709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 219650133871179161985828557 82368800201692185744685709)
          ·
            refine ⟨30888300075634569654257141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 82368800201692185744685709 30888300075634569654257141)
            ·
              refine ⟨2895778132090740905086607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 30888300075634569654257141 2895778132090740905086607)
              ·
                refine ⟨4343667198136111357629911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2895778132090740905086607 4343667198136111357629911)
                ·
                  refine ⟨6515500797204167036444867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4343667198136111357629911 6515500797204167036444867)
                  ·
                    refine ⟨9773251195806250554667301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6515500797204167036444867 9773251195806250554667301)
                    ·
                      refine ⟨1832484599213671979000119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9773251195806250554667301 1832484599213671979000119)
                      ·
                        rfl

theorem cell23_3568751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 5, 1, 1, 1, 4].length) (baseStart_3568751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3568751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3568751 prefixEnd_3568751 := by exact prefixLift 3568751
  have htrace : WordTrace (prefixWord ++ tailWord_3568751) baseStart_3568751 baseEnd_3568751 := by
    simpa [prefixWord, tailWord_3568751, baseEnd_3568751] using wordTrace_append hprefix tailTrace_3568751
  have hstable : (prefixWord ++ tailWord_3568751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3568751).length < 2 ^ (prefixWord ++ tailWord_3568751).sum := by decide
  have hdescent : baseEnd_3568751 < baseStart_3568751 := by decide
  rcases family_descends (prefixWord ++ tailWord_3568751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3568801 : List Nat := [1, 2, 3, 3, 1, 1, 2, 2, 4, 1, 3]
def baseStart_3568801 : Nat := 118140960795 + 3568801 * 2 ^ 59
def prefixEnd_3568801 : Nat := 4983230072969 + 3 ^ 40 * 3568801 * 2
def baseEnd_3568801 : Nat := 1832510273246396783374889

theorem tailTrace_3568801 : CollatzResearch.WordTrace tailWord_3568801 prefixEnd_3568801 1832510273246396783374889 := by
  unfold tailWord_3568801
  simp only [CollatzResearch.WordTrace]
  refine ⟨130164865943850954530922257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86776577295900636353948171 130164865943850954530922257)
  ·
    refine ⟨97623649457888215898191693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130164865943850954530922257 97623649457888215898191693)
    ·
      refine ⟨36608868546708080961821885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 97623649457888215898191693 36608868546708080961821885)
      ·
        refine ⟨13728325705015530360683207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36608868546708080961821885 13728325705015530360683207)
        ·
          refine ⟨20592488557523295541024811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13728325705015530360683207 20592488557523295541024811)
          ·
            refine ⟨30888732836284943311537217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20592488557523295541024811 30888732836284943311537217)
            ·
              refine ⟨23166549627213707483652913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30888732836284943311537217 23166549627213707483652913)
              ·
                refine ⟨17374912220410280612739685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23166549627213707483652913 17374912220410280612739685)
                ·
                  refine ⟨3257796041326927614888691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17374912220410280612739685 3257796041326927614888691)
                  ·
                    refine ⟨4886694061990391422333037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3257796041326927614888691 4886694061990391422333037)
                    ·
                      refine ⟨1832510273246396783374889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4886694061990391422333037 1832510273246396783374889)
                      ·
                        rfl

theorem cell23_3568801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 2, 2, 4, 1, 3].length) (baseStart_3568801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3568801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3568801 prefixEnd_3568801 := by exact prefixLift 3568801
  have htrace : WordTrace (prefixWord ++ tailWord_3568801) baseStart_3568801 baseEnd_3568801 := by
    simpa [prefixWord, tailWord_3568801, baseEnd_3568801] using wordTrace_append hprefix tailTrace_3568801
  have hstable : (prefixWord ++ tailWord_3568801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3568801).length < 2 ^ (prefixWord ++ tailWord_3568801).sum := by decide
  have hdescent : baseEnd_3568801 < baseStart_3568801 := by decide
  rcases family_descends (prefixWord ++ tailWord_3568801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3568802 : List Nat := [3, 3, 1, 3, 3, 1, 2, 1, 1, 1, 4]
def baseStart_3568802 : Nat := 118140960795 + 3568802 * 2 ^ 59
def prefixEnd_3568802 : Nat := 4983230072969 + 3 ^ 40 * 3568802 * 2
def baseEnd_3568802 : Nat := 1832510786727051279462385

theorem tailTrace_3568802 : CollatzResearch.WordTrace tailWord_3568802 prefixEnd_3568802 1832510786727051279462385 := by
  unfold tailWord_3568802
  simp only [CollatzResearch.WordTrace]
  refine ⟨32541225604211832925427165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86776601611231554467805773 32541225604211832925427165)
  ·
    refine ⟨12202959601579437347035187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32541225604211832925427165 12202959601579437347035187)
    ·
      refine ⟨18304439402369156020552781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12202959601579437347035187 18304439402369156020552781)
      ·
        refine ⟨6864164775888433507707293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18304439402369156020552781 6864164775888433507707293)
        ·
          refine ⟨2574061790958162565390235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6864164775888433507707293 2574061790958162565390235)
          ·
            refine ⟨3861092686437243848085353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2574061790958162565390235 3861092686437243848085353)
            ·
              refine ⟨2895819514827932886064015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3861092686437243848085353 2895819514827932886064015)
              ·
                refine ⟨4343729272241899329096023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2895819514827932886064015 4343729272241899329096023)
                ·
                  refine ⟨6515593908362848993644035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4343729272241899329096023 6515593908362848993644035)
                  ·
                    refine ⟨9773390862544273490466053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6515593908362848993644035 9773390862544273490466053)
                    ·
                      refine ⟨1832510786727051279462385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9773390862544273490466053 1832510786727051279462385)
                      ·
                        rfl

theorem cell23_3568802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 3, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 3, 1, 2, 1, 1, 1, 4].length) (baseStart_3568802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3568802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3568802 prefixEnd_3568802 := by exact prefixLift 3568802
  have htrace : WordTrace (prefixWord ++ tailWord_3568802) baseStart_3568802 baseEnd_3568802 := by
    simpa [prefixWord, tailWord_3568802, baseEnd_3568802] using wordTrace_append hprefix tailTrace_3568802
  have hstable : (prefixWord ++ tailWord_3568802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3568802).length < 2 ^ (prefixWord ++ tailWord_3568802).sum := by decide
  have hdescent : baseEnd_3568802 < baseStart_3568802 := by decide
  rcases family_descends (prefixWord ++ tailWord_3568802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3568818 : List Nat := [3, 2, 1, 1, 1, 4, 3, 2, 2, 1, 3]
def baseStart_3568818 : Nat := 118140960795 + 3568818 * 2 ^ 59
def prefixEnd_3568818 : Nat := 4983230072969 + 3 ^ 40 * 3568818 * 2
def baseEnd_3568818 : Nat := 1832519002417523216862311

theorem tailTrace_3568818 : CollatzResearch.WordTrace tailWord_3568818 prefixEnd_3568818 1832519002417523216862311 := by
  unfold tailWord_3568818
  simp only [CollatzResearch.WordTrace]
  refine ⟨32541371496197341608572777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86776990656526244289527405 32541371496197341608572777)
  ·
    refine ⟨24406028622148006206429583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32541371496197341608572777 24406028622148006206429583)
    ·
      refine ⟨36609042933222009309644375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24406028622148006206429583 36609042933222009309644375)
      ·
        refine ⟨54913564399833013964466563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36609042933222009309644375 54913564399833013964466563)
        ·
          refine ⟨82370346599749520946699845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54913564399833013964466563 82370346599749520946699845)
          ·
            refine ⟨15444439987453035177506221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 82370346599749520946699845 15444439987453035177506221)
            ·
              refine ⟨5791664995294888191564833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15444439987453035177506221 5791664995294888191564833)
              ·
                refine ⟨4343748746471166143673625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5791664995294888191564833 4343748746471166143673625)
                ·
                  refine ⟨3257811559853374607755219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4343748746471166143673625 3257811559853374607755219)
                  ·
                    refine ⟨4886717339780061911632829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3257811559853374607755219 4886717339780061911632829)
                    ·
                      refine ⟨1832519002417523216862311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4886717339780061911632829 1832519002417523216862311)
                      ·
                        rfl

theorem cell23_3568818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 3, 2, 2, 1, 3].length) (baseStart_3568818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3568818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3568818 prefixEnd_3568818 := by exact prefixLift 3568818
  have htrace : WordTrace (prefixWord ++ tailWord_3568818) baseStart_3568818 baseEnd_3568818 := by
    simpa [prefixWord, tailWord_3568818, baseEnd_3568818] using wordTrace_append hprefix tailTrace_3568818
  have hstable : (prefixWord ++ tailWord_3568818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3568818).length < 2 ^ (prefixWord ++ tailWord_3568818).sum := by decide
  have hdescent : baseEnd_3568818 < baseStart_3568818 := by decide
  rcases family_descends (prefixWord ++ tailWord_3568818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3568827 : List Nat := [1, 1, 1, 1, 1, 2, 4, 1, 3, 3, 5]
def baseStart_3568827 : Nat := 118140960795 + 3568827 * 2 ^ 59
def prefixEnd_3568827 : Nat := 4983230072969 + 3 ^ 40 * 3568827 * 2
def baseEnd_3568827 : Nat := 1832523623743413681649769

theorem tailTrace_3568827 : CollatzResearch.WordTrace tailWord_3568827 prefixEnd_3568827 1832523623743413681649769 := by
  unfold tailWord_3568827
  simp only [CollatzResearch.WordTrace]
  refine ⟨130165814241756760971368735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86777209494504507314245823 130165814241756760971368735)
  ·
    refine ⟨195248721362635141457053103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130165814241756760971368735 195248721362635141457053103)
    ·
      refine ⟨292873082043952712185579655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195248721362635141457053103 292873082043952712185579655)
      ·
        refine ⟨439309623065929068278369483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 292873082043952712185579655 439309623065929068278369483)
        ·
          refine ⟨658964434598893602417554225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 439309623065929068278369483 658964434598893602417554225)
          ·
            refine ⟨494223325949170201813165669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 658964434598893602417554225 494223325949170201813165669)
            ·
              refine ⟨92666873615469412839968563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 494223325949170201813165669 92666873615469412839968563)
              ·
                refine ⟨139000310423204119259952845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92666873615469412839968563 139000310423204119259952845)
                ·
                  refine ⟨52125116408701544722482317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 139000310423204119259952845 52125116408701544722482317)
                  ·
                    refine ⟨19546918653263079270930869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 52125116408701544722482317 19546918653263079270930869)
                    ·
                      refine ⟨1832523623743413681649769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19546918653263079270930869 1832523623743413681649769)
                      ·
                        rfl

theorem cell23_3568827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 1, 3, 3, 5].length) (baseStart_3568827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3568827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3568827 prefixEnd_3568827 := by exact prefixLift 3568827
  have htrace : WordTrace (prefixWord ++ tailWord_3568827) baseStart_3568827 baseEnd_3568827 := by
    simpa [prefixWord, tailWord_3568827, baseEnd_3568827] using wordTrace_append hprefix tailTrace_3568827
  have hstable : (prefixWord ++ tailWord_3568827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3568827).length < 2 ^ (prefixWord ++ tailWord_3568827).sum := by decide
  have hdescent : baseEnd_3568827 < baseStart_3568827 := by decide
  rcases family_descends (prefixWord ++ tailWord_3568827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3568847 : List Nat := [1, 1, 2, 1, 1, 3, 2, 3, 9]
def baseStart_3568847 : Nat := 118140960795 + 3568847 * 2 ^ 59
def prefixEnd_3568847 : Nat := 4983230072969 + 3 ^ 40 * 3568847 * 2
def baseEnd_3568847 : Nat := 203614877039611511488853

theorem tailTrace_3568847 : CollatzResearch.WordTrace tailWord_3568847 prefixEnd_3568847 203614877039611511488853 := by
  unfold tailWord_3568847
  simp only [CollatzResearch.WordTrace]
  refine ⟨130166543701684304387096795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86777695801122869591397863 130166543701684304387096795)
  ·
    refine ⟨195249815552526456580645193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130166543701684304387096795 195249815552526456580645193)
    ·
      refine ⟨146437361664394842435483895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 195249815552526456580645193 146437361664394842435483895)
      ·
        refine ⟨219656042496592263653225843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146437361664394842435483895 219656042496592263653225843)
        ·
          refine ⟨329484063744888395479838765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 219656042496592263653225843 329484063744888395479838765)
          ·
            refine ⟨123556523904333148304939537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 329484063744888395479838765 123556523904333148304939537)
            ·
              refine ⟨92667392928249861228704653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 123556523904333148304939537 92667392928249861228704653)
              ·
                refine ⟨34750272348093697960764245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 92667392928249861228704653 34750272348093697960764245)
                ·
                  refine ⟨203614877039611511488853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 34750272348093697960764245 203614877039611511488853)
                  ·
                    rfl

theorem cell23_3568847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 3, 9].length) (baseStart_3568847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3568847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3568847 prefixEnd_3568847 := by exact prefixLift 3568847
  have htrace : WordTrace (prefixWord ++ tailWord_3568847) baseStart_3568847 baseEnd_3568847 := by
    simpa [prefixWord, tailWord_3568847, baseEnd_3568847] using wordTrace_append hprefix tailTrace_3568847
  have hstable : (prefixWord ++ tailWord_3568847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3568847).length < 2 ^ (prefixWord ++ tailWord_3568847).sum := by decide
  have hdescent : baseEnd_3568847 < baseStart_3568847 := by decide
  rcases family_descends (prefixWord ++ tailWord_3568847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3568931 : List Nat := [1, 1, 1, 4, 2, 3, 2, 2, 2, 1, 4]
def baseStart_3568931 : Nat := 118140960795 + 3568931 * 2 ^ 59
def prefixEnd_3568931 : Nat := 4983230072969 + 3 ^ 40 * 3568931 * 2
def baseEnd_3568931 : Nat := 1832577025731481274749291

theorem tailTrace_3568931 : CollatzResearch.WordTrace tailWord_3568931 prefixEnd_3568931 1832577025731481274749291 := by
  unfold tailWord_3568931
  simp only [CollatzResearch.WordTrace]
  refine ⟨130169607433379986733154647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86779738288919991155436431 130169607433379986733154647)
  ·
    refine ⟨195254411150069980099731971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130169607433379986733154647 195254411150069980099731971)
    ·
      refine ⟨292881616725104970149597957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195254411150069980099731971 292881616725104970149597957)
      ·
        refine ⟨54915303135957181903049617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 292881616725104970149597957 54915303135957181903049617)
        ·
          refine ⟨41186477351967886427287213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54915303135957181903049617 41186477351967886427287213)
          ·
            refine ⟨15444929006987957410232705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41186477351967886427287213 15444929006987957410232705)
            ·
              refine ⟨11583696755240968057674529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15444929006987957410232705 11583696755240968057674529)
              ·
                refine ⟨8687772566430726043255897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11583696755240968057674529 8687772566430726043255897)
                ·
                  refine ⟨6515829424823044532441923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8687772566430726043255897 6515829424823044532441923)
                  ·
                    refine ⟨9773744137234566798662885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6515829424823044532441923 9773744137234566798662885)
                    ·
                      refine ⟨1832577025731481274749291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9773744137234566798662885 1832577025731481274749291)
                      ·
                        rfl

theorem cell23_3568931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 2, 2, 2, 1, 4].length) (baseStart_3568931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3568931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3568931 prefixEnd_3568931 := by exact prefixLift 3568931
  have htrace : WordTrace (prefixWord ++ tailWord_3568931) baseStart_3568931 baseEnd_3568931 := by
    simpa [prefixWord, tailWord_3568931, baseEnd_3568931] using wordTrace_append hprefix tailTrace_3568931
  have hstable : (prefixWord ++ tailWord_3568931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3568931).length < 2 ^ (prefixWord ++ tailWord_3568931).sum := by decide
  have hdescent : baseEnd_3568931 < baseStart_3568931 := by decide
  rcases family_descends (prefixWord ++ tailWord_3568931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3568958 : List Nat := [4, 2, 1, 2, 1, 1, 3, 2, 3, 4]
def baseStart_3568958 : Nat := 118140960795 + 3568958 * 2 ^ 59
def prefixEnd_3568958 : Nat := 4983230072969 + 3 ^ 40 * 3568958 * 2
def baseEnd_3568958 : Nat := 610863629903050889703889

theorem tailTrace_3568958 : CollatzResearch.WordTrace tailWord_3568958 prefixEnd_3568958 610863629903050889703889 := by
  unfold tailWord_3568958
  simp only [CollatzResearch.WordTrace]
  refine ⟨16271324025535271293048441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 86780394802854780229591685 16271324025535271293048441)
  ·
    refine ⟨12203493019151453469786331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16271324025535271293048441 12203493019151453469786331)
    ·
      refine ⟨18305239528727180204679497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12203493019151453469786331 18305239528727180204679497)
      ·
        refine ⟨13728929646545385153509623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18305239528727180204679497 13728929646545385153509623)
        ·
          refine ⟨20593394469818077730264435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13728929646545385153509623 20593394469818077730264435)
          ·
            refine ⟨30890091704727116595396653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20593394469818077730264435 30890091704727116595396653)
            ·
              refine ⟨11583784389272668723273745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30890091704727116595396653 11583784389272668723273745)
              ·
                refine ⟨8687838291954501542455309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11583784389272668723273745 8687838291954501542455309)
                ·
                  refine ⟨3257939359482938078420741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8687838291954501542455309 3257939359482938078420741)
                  ·
                    refine ⟨610863629903050889703889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3257939359482938078420741 610863629903050889703889)
                    ·
                      rfl

theorem cell23_3568958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 3, 2, 3, 4].length) (baseStart_3568958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3568958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3568958 prefixEnd_3568958 := by exact prefixLift 3568958
  have htrace : WordTrace (prefixWord ++ tailWord_3568958) baseStart_3568958 baseEnd_3568958 := by
    simpa [prefixWord, tailWord_3568958, baseEnd_3568958] using wordTrace_append hprefix tailTrace_3568958
  have hstable : (prefixWord ++ tailWord_3568958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3568958).length < 2 ^ (prefixWord ++ tailWord_3568958).sum := by decide
  have hdescent : baseEnd_3568958 < baseStart_3568958 := by decide
  rcases family_descends (prefixWord ++ tailWord_3568958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3569032 : List Nat := [2, 1, 3, 3, 1, 2, 3, 3, 1, 1, 3]
def baseStart_3569032 : Nat := 118140960795 + 3569032 * 2 ^ 59
def prefixEnd_3569032 : Nat := 4983230072969 + 3 ^ 40 * 3569032 * 2
def baseEnd_3569032 : Nat := 1832628887277585379586327

theorem tailTrace_3569032 : CollatzResearch.WordTrace tailWord_3569032 prefixEnd_3569032 1832628887277585379586327 := by
  unfold tailWord_3569032
  simp only [CollatzResearch.WordTrace]
  refine ⟨65086645603007040491290675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86782194137342720655054233 65086645603007040491290675)
  ·
    refine ⟨97629968404510560736936013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65086645603007040491290675 97629968404510560736936013)
    ·
      refine ⟨36611238151691460276351005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 97629968404510560736936013 36611238151691460276351005)
      ·
        refine ⟨13729214306884297603631627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36611238151691460276351005 13729214306884297603631627)
        ·
          refine ⟨20593821460326446405447441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13729214306884297603631627 20593821460326446405447441)
          ·
            refine ⟨15445366095244834804085581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20593821460326446405447441 15445366095244834804085581)
            ·
              refine ⟨5792012285716813051532093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15445366095244834804085581 5792012285716813051532093)
              ·
                refine ⟨2172004607143804894324535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5792012285716813051532093 2172004607143804894324535)
                ·
                  refine ⟨3258006910715707341486803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2172004607143804894324535 3258006910715707341486803)
                  ·
                    refine ⟨4887010366073561012230205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3258006910715707341486803 4887010366073561012230205)
                    ·
                      refine ⟨1832628887277585379586327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4887010366073561012230205 1832628887277585379586327)
                      ·
                        rfl

theorem cell23_3569032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 3, 3, 1, 1, 3].length) (baseStart_3569032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3569032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3569032 prefixEnd_3569032 := by exact prefixLift 3569032
  have htrace : WordTrace (prefixWord ++ tailWord_3569032) baseStart_3569032 baseEnd_3569032 := by
    simpa [prefixWord, tailWord_3569032, baseEnd_3569032] using wordTrace_append hprefix tailTrace_3569032
  have hstable : (prefixWord ++ tailWord_3569032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3569032).length < 2 ^ (prefixWord ++ tailWord_3569032).sum := by decide
  have hdescent : baseEnd_3569032 < baseStart_3569032 := by decide
  rcases family_descends (prefixWord ++ tailWord_3569032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3569058 : List Nat := [3, 3, 1, 2, 1, 2, 2, 2, 1, 1, 5]
def baseStart_3569058 : Nat := 118140960795 + 3569058 * 2 ^ 59
def prefixEnd_3569058 : Nat := 4983230072969 + 3 ^ 40 * 3569058 * 2
def baseEnd_3569058 : Nat := 1832642237774602277861207

theorem tailTrace_3569058 : CollatzResearch.WordTrace tailWord_3569058 prefixEnd_3569058 1832642237774602277861207 := by
  unfold tailWord_3569058
  simp only [CollatzResearch.WordTrace]
  refine ⟨32543559875979971855756957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86782826335946591615351885 32543559875979971855756957)
  ·
    refine ⟨12203834953492489445908859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32543559875979971855756957 12203834953492489445908859)
    ·
      refine ⟨18305752430238734168863289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12203834953492489445908859 18305752430238734168863289)
      ·
        refine ⟨13729314322679050626647467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18305752430238734168863289 13729314322679050626647467)
        ·
          refine ⟨20593971484018575939971201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13729314322679050626647467 20593971484018575939971201)
          ·
            refine ⟨15445478613013931954978401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20593971484018575939971201 15445478613013931954978401)
            ·
              refine ⟨11584108959760448966233801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15445478613013931954978401 11584108959760448966233801)
              ·
                refine ⟨8688081719820336724675351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11584108959760448966233801 8688081719820336724675351)
                ·
                  refine ⟨13032122579730505087013027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8688081719820336724675351 13032122579730505087013027)
                  ·
                    refine ⟨19548183869595757630519541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13032122579730505087013027 19548183869595757630519541)
                    ·
                      refine ⟨1832642237774602277861207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19548183869595757630519541 1832642237774602277861207)
                      ·
                        rfl

theorem cell23_3569058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 2, 2, 1, 1, 5].length) (baseStart_3569058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3569058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3569058 prefixEnd_3569058 := by exact prefixLift 3569058
  have htrace : WordTrace (prefixWord ++ tailWord_3569058) baseStart_3569058 baseEnd_3569058 := by
    simpa [prefixWord, tailWord_3569058, baseEnd_3569058] using wordTrace_append hprefix tailTrace_3569058
  have hstable : (prefixWord ++ tailWord_3569058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3569058).length < 2 ^ (prefixWord ++ tailWord_3569058).sum := by decide
  have hdescent : baseEnd_3569058 < baseStart_3569058 := by decide
  rcases family_descends (prefixWord ++ tailWord_3569058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3569071 : List Nat := [1, 1, 2, 1, 2, 2, 1, 2, 5, 3, 3]
def baseStart_3569071 : Nat := 118140960795 + 3569071 * 2 ^ 59
def prefixEnd_3569071 : Nat := 4983230072969 + 3 ^ 40 * 3569071 * 2
def baseEnd_3569071 : Nat := 1832648913023110726998647

theorem tailTrace_3569071 : CollatzResearch.WordTrace tailWord_3569071 prefixEnd_3569071 1832648913023110726998647 := by
  unfold tailWord_3569071
  simp only [CollatzResearch.WordTrace]
  refine ⟨130174713652872790643251067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86783142435248527095500711 130174713652872790643251067)
  ·
    refine ⟨195262070479309185964876601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130174713652872790643251067 195262070479309185964876601)
    ·
      refine ⟨146446552859481889473657451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 195262070479309185964876601 146446552859481889473657451)
      ·
        refine ⟨219669829289222834210486177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146446552859481889473657451 219669829289222834210486177)
        ·
          refine ⟨164752371966917125657864633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 219669829289222834210486177 164752371966917125657864633)
          ·
            refine ⟨123564278975187844243398475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 164752371966917125657864633 123564278975187844243398475)
            ·
              refine ⟨185346418462781766365097713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 123564278975187844243398475 185346418462781766365097713)
              ·
                refine ⟨139009813847086324773823285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 185346418462781766365097713 139009813847086324773823285)
                ·
                  refine ⟨13032170048164342947545933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 139009813847086324773823285 13032170048164342947545933)
                  ·
                    refine ⟨4887063768061628605329725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13032170048164342947545933 4887063768061628605329725)
                    ·
                      refine ⟨1832648913023110726998647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4887063768061628605329725 1832648913023110726998647)
                      ·
                        rfl

theorem cell23_3569071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 2, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 2, 5, 3, 3].length) (baseStart_3569071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3569071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3569071 prefixEnd_3569071 := by exact prefixLift 3569071
  have htrace : WordTrace (prefixWord ++ tailWord_3569071) baseStart_3569071 baseEnd_3569071 := by
    simpa [prefixWord, tailWord_3569071, baseEnd_3569071] using wordTrace_append hprefix tailTrace_3569071
  have hstable : (prefixWord ++ tailWord_3569071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3569071).length < 2 ^ (prefixWord ++ tailWord_3569071).sum := by decide
  have hdescent : baseEnd_3569071 < baseStart_3569071 := by decide
  rcases family_descends (prefixWord ++ tailWord_3569071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3569088 : List Nat := [2, 1, 1, 2, 3, 1, 2, 1, 6, 1, 3]
def baseStart_3569088 : Nat := 118140960795 + 3569088 * 2 ^ 59
def prefixEnd_3569088 : Nat := 4983230072969 + 3 ^ 40 * 3569088 * 2
def baseEnd_3569088 : Nat := 1832657642194237160486069

theorem tailTrace_3569088 : CollatzResearch.WordTrace tailWord_3569088 prefixEnd_3569088 1832657642194237160486069 := by
  unfold tailWord_3569088
  simp only [CollatzResearch.WordTrace]
  refine ⟨65087666846905601273309959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86783555795874135031079945 65087666846905601273309959)
  ·
    refine ⟨97631500270358401909964939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65087666846905601273309959 97631500270358401909964939)
    ·
      refine ⟨146447250405537602864947409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97631500270358401909964939 146447250405537602864947409)
      ·
        refine ⟨109835437804153202148710557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146447250405537602864947409 109835437804153202148710557)
        ·
          refine ⟨41188289176557450805766459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 109835437804153202148710557 41188289176557450805766459)
          ·
            refine ⟨61782433764836176208649689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41188289176557450805766459 61782433764836176208649689)
            ·
              refine ⟨46336825323627132156487267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61782433764836176208649689 46336825323627132156487267)
              ·
                refine ⟨69505237985440698234730901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46336825323627132156487267 69505237985440698234730901)
                ·
                  refine ⟨3258058030567532729753011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 69505237985440698234730901 3258058030567532729753011)
                  ·
                    refine ⟨4887087045851299094629517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3258058030567532729753011 4887087045851299094629517)
                    ·
                      refine ⟨1832657642194237160486069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4887087045851299094629517 1832657642194237160486069)
                      ·
                        rfl

theorem cell23_3569088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 1, 6, 1, 3].length) (baseStart_3569088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3569088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3569088 prefixEnd_3569088 := by exact prefixLift 3569088
  have htrace : WordTrace (prefixWord ++ tailWord_3569088) baseStart_3569088 baseEnd_3569088 := by
    simpa [prefixWord, tailWord_3569088, baseEnd_3569088] using wordTrace_append hprefix tailTrace_3569088
  have hstable : (prefixWord ++ tailWord_3569088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3569088).length < 2 ^ (prefixWord ++ tailWord_3569088).sum := by decide
  have hdescent : baseEnd_3569088 < baseStart_3569088 := by decide
  rcases family_descends (prefixWord ++ tailWord_3569088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3569121 : List Nat := [1, 2, 3, 1, 2, 3, 1, 1, 1, 8]
def baseStart_3569121 : Nat := 118140960795 + 3569121 * 2 ^ 59
def prefixEnd_3569121 : Nat := 4983230072969 + 3 ^ 40 * 3569121 * 2
def baseEnd_3569121 : Nat := 610891529018611843791139

theorem tailTrace_3569121 : CollatzResearch.WordTrace tailWord_3569121 prefixEnd_3569121 610891529018611843791139 := by
  unfold tailWord_3569121
  simp only [CollatzResearch.WordTrace]
  refine ⟨130176537302691649182571217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86784358201794432788380811 130176537302691649182571217)
  ·
    refine ⟨97632402977018736886928413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130176537302691649182571217 97632402977018736886928413)
    ·
      refine ⟨36612151116382026332598155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 97632402977018736886928413 36612151116382026332598155)
      ·
        refine ⟨54918226674573039498897233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36612151116382026332598155 54918226674573039498897233)
        ·
          refine ⟨41188670005929779624172925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54918226674573039498897233 41188670005929779624172925)
          ·
            refine ⟨15445751252223667359064847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41188670005929779624172925 15445751252223667359064847)
            ·
              refine ⟨23168626878335501038597271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15445751252223667359064847 23168626878335501038597271)
              ·
                refine ⟨34752940317503251557895907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23168626878335501038597271 34752940317503251557895907)
                ·
                  refine ⟨52129410476254877336843861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34752940317503251557895907 52129410476254877336843861)
                  ·
                    refine ⟨610891529018611843791139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 52129410476254877336843861 610891529018611843791139)
                    ·
                      rfl

theorem cell23_3569121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 1, 1, 1, 8].length) (baseStart_3569121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3569121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3569121 prefixEnd_3569121 := by exact prefixLift 3569121
  have htrace : WordTrace (prefixWord ++ tailWord_3569121) baseStart_3569121 baseEnd_3569121 := by
    simpa [prefixWord, tailWord_3569121, baseEnd_3569121] using wordTrace_append hprefix tailTrace_3569121
  have hstable : (prefixWord ++ tailWord_3569121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3569121).length < 2 ^ (prefixWord ++ tailWord_3569121).sum := by decide
  have hdescent : baseEnd_3569121 < baseStart_3569121 := by decide
  rcases family_descends (prefixWord ++ tailWord_3569121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3569131 : List Nat := [1, 1, 1, 1, 2, 3, 2, 4, 2, 1, 5]
def baseStart_3569131 : Nat := 118140960795 + 3569131 * 2 ^ 59
def prefixEnd_3569131 : Nat := 4983230072969 + 3 ^ 40 * 3569131 * 2
def baseEnd_3569131 : Nat := 1832679721862380492248371

theorem tailTrace_3569131 : CollatzResearch.WordTrace tailWord_3569131 prefixEnd_3569131 1832679721862380492248371 := by
  unfold tailWord_3569131
  simp only [CollatzResearch.WordTrace]
  refine ⟨130176902032655420890435247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86784601355103613926956831 130176902032655420890435247)
  ·
    refine ⟨195265353048983131335652871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130176902032655420890435247 195265353048983131335652871)
    ·
      refine ⟨292898029573474697003479307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195265353048983131335652871 292898029573474697003479307)
      ·
        refine ⟨439347044360212045505218961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 292898029573474697003479307 439347044360212045505218961)
        ·
          refine ⟨329510283270159034128914221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 439347044360212045505218961 329510283270159034128914221)
          ·
            refine ⟨123566356226309637798342833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 329510283270159034128914221 123566356226309637798342833)
            ·
              refine ⟨92674767169732228348757125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 123566356226309637798342833 92674767169732228348757125)
              ·
                refine ⟨17376518844324792815391961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 92674767169732228348757125 17376518844324792815391961)
                ·
                  refine ⟨13032389133243594611543971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17376518844324792815391961 13032389133243594611543971)
                  ·
                    refine ⟨19548583699865391917315957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13032389133243594611543971 19548583699865391917315957)
                    ·
                      refine ⟨1832679721862380492248371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19548583699865391917315957 1832679721862380492248371)
                      ·
                        rfl

theorem cell23_3569131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 4, 2, 1, 5].length) (baseStart_3569131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3569131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3569131 prefixEnd_3569131 := by exact prefixLift 3569131
  have htrace : WordTrace (prefixWord ++ tailWord_3569131) baseStart_3569131 baseEnd_3569131 := by
    simpa [prefixWord, tailWord_3569131, baseEnd_3569131] using wordTrace_append hprefix tailTrace_3569131
  have hstable : (prefixWord ++ tailWord_3569131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3569131).length < 2 ^ (prefixWord ++ tailWord_3569131).sum := by decide
  have hdescent : baseEnd_3569131 < baseStart_3569131 := by decide
  rcases family_descends (prefixWord ++ tailWord_3569131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3569145 : List Nat := [1, 2, 1, 3, 1, 2, 1, 4, 4, 2, 2]
def baseStart_3569145 : Nat := 118140960795 + 3569145 * 2 ^ 59
def prefixEnd_3569145 : Nat := 4983230072969 + 3 ^ 40 * 3569145 * 2
def baseEnd_3569145 : Nat := 1832686910591543437473307

theorem tailTrace_3569145 : CollatzResearch.WordTrace tailWord_3569145 prefixEnd_3569145 1832686910591543437473307 := by
  unfold tailWord_3569145
  simp only [CollatzResearch.WordTrace]
  refine ⟨130177412654604701281444889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86784941769736467520963259 130177412654604701281444889)
  ·
    refine ⟨97633059490953525961083667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130177412654604701281444889 97633059490953525961083667)
    ·
      refine ⟨146449589236430288941625501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97633059490953525961083667 146449589236430288941625501)
      ·
        refine ⟨54918595963661358353109563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 146449589236430288941625501 54918595963661358353109563)
        ·
          refine ⟨82377893945492037529664345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54918595963661358353109563 82377893945492037529664345)
          ·
            refine ⟨61783420459119028147248259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82377893945492037529664345 61783420459119028147248259)
            ·
              refine ⟨92675130688678542220872389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61783420459119028147248259 92675130688678542220872389)
              ·
                refine ⟨17376587004127226666413573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 92675130688678542220872389 17376587004127226666413573)
                ·
                  refine ⟨3258110063273854999952545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17376587004127226666413573 3258110063273854999952545)
                  ·
                    refine ⟨2443582547455391249964409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3258110063273854999952545 2443582547455391249964409)
                    ·
                      refine ⟨1832686910591543437473307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2443582547455391249964409 1832686910591543437473307)
                      ·
                        rfl

theorem cell23_3569145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 4, 4, 2, 2].length) (baseStart_3569145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3569145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3569145 prefixEnd_3569145 := by exact prefixLift 3569145
  have htrace : WordTrace (prefixWord ++ tailWord_3569145) baseStart_3569145 baseEnd_3569145 := by
    simpa [prefixWord, tailWord_3569145, baseEnd_3569145] using wordTrace_append hprefix tailTrace_3569145
  have hstable : (prefixWord ++ tailWord_3569145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3569145).length < 2 ^ (prefixWord ++ tailWord_3569145).sum := by decide
  have hdescent : baseEnd_3569145 < baseStart_3569145 := by decide
  rcases family_descends (prefixWord ++ tailWord_3569145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3569149 : List Nat := [1, 4, 1, 1, 1, 6, 2, 1, 1, 3, 2]
def baseStart_3569149 : Nat := 118140960795 + 3569149 * 2 ^ 59
def prefixEnd_3569149 : Nat := 4983230072969 + 3 ^ 40 * 3569149 * 2
def baseEnd_3569149 : Nat := 1832688964514161421823289

theorem tailTrace_3569149 : CollatzResearch.WordTrace tailWord_3569149 prefixEnd_3569149 1832688964514161421823289 := by
  unfold tailWord_3569149
  simp only [CollatzResearch.WordTrace]
  refine ⟨130177558546590209964590501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86785039031060139976393667 130177558546590209964590501)
  ·
    refine ⟨24408292227485664368360719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 130177558546590209964590501 24408292227485664368360719)
    ·
      refine ⟨36612438341228496552541079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24408292227485664368360719 36612438341228496552541079)
      ·
        refine ⟨54918657511842744828811619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36612438341228496552541079 54918657511842744828811619)
        ·
          refine ⟨82377986267764117243217429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54918657511842744828811619 82377986267764117243217429)
          ·
            refine ⟨3861468106301442995775817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 82377986267764117243217429 3861468106301442995775817)
            ·
              refine ⟨2896101079726082246831863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3861468106301442995775817 2896101079726082246831863)
              ·
                refine ⟨4344151619589123370247795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2896101079726082246831863 4344151619589123370247795)
                ·
                  refine ⟨6516227429383685055371693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4344151619589123370247795 6516227429383685055371693)
                  ·
                    refine ⟨2443585286018881895764385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6516227429383685055371693 2443585286018881895764385)
                    ·
                      refine ⟨1832688964514161421823289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2443585286018881895764385 1832688964514161421823289)
                      ·
                        rfl

theorem cell23_3569149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 6, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 6, 2, 1, 1, 3, 2].length) (baseStart_3569149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3569149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3569149 prefixEnd_3569149 := by exact prefixLift 3569149
  have htrace : WordTrace (prefixWord ++ tailWord_3569149) baseStart_3569149 baseEnd_3569149 := by
    simpa [prefixWord, tailWord_3569149, baseEnd_3569149] using wordTrace_append hprefix tailTrace_3569149
  have hstable : (prefixWord ++ tailWord_3569149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3569149).length < 2 ^ (prefixWord ++ tailWord_3569149).sum := by decide
  have hdescent : baseEnd_3569149 < baseStart_3569149 := by decide
  rcases family_descends (prefixWord ++ tailWord_3569149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3569156 : List Nat := [2, 3, 2, 3, 3, 1, 1, 2, 2, 1, 3]
def baseStart_3569156 : Nat := 118140960795 + 3569156 * 2 ^ 59
def prefixEnd_3569156 : Nat := 4983230072969 + 3 ^ 40 * 3569156 * 2
def baseEnd_3569156 : Nat := 1832692558878742894435757

theorem tailTrace_3569156 : CollatzResearch.WordTrace tailWord_3569156 prefixEnd_3569156 1832692558878742894435757 := by
  unfold tailWord_3569156
  simp only [CollatzResearch.WordTrace]
  refine ⟨65088906928782425080047661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86785209238376566773396881 65088906928782425080047661)
  ·
    refine ⟨24408340098293409405017873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65088906928782425080047661 24408340098293409405017873)
    ·
      refine ⟨18306255073720057053763405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24408340098293409405017873 18306255073720057053763405)
      ·
        refine ⟨6864845652645021395161277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18306255073720057053763405 6864845652645021395161277)
        ·
          refine ⟨2574317119741883023185479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6864845652645021395161277 2574317119741883023185479)
          ·
            refine ⟨3861475679612824534778219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2574317119741883023185479 3861475679612824534778219)
            ·
              refine ⟨5792213519419236802167329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3861475679612824534778219 5792213519419236802167329)
              ·
                refine ⟨4344160139564427601625497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5792213519419236802167329 4344160139564427601625497)
                ·
                  refine ⟨3258120104673320701219123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4344160139564427601625497 3258120104673320701219123)
                  ·
                    refine ⟨4887180157009981051828685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3258120104673320701219123 4887180157009981051828685)
                    ·
                      refine ⟨1832692558878742894435757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4887180157009981051828685 1832692558878742894435757)
                      ·
                        rfl

theorem cell23_3569156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 3, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 3, 1, 1, 2, 2, 1, 3].length) (baseStart_3569156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3569156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3569156 prefixEnd_3569156 := by exact prefixLift 3569156
  have htrace : WordTrace (prefixWord ++ tailWord_3569156) baseStart_3569156 baseEnd_3569156 := by
    simpa [prefixWord, tailWord_3569156, baseEnd_3569156] using wordTrace_append hprefix tailTrace_3569156
  have hstable : (prefixWord ++ tailWord_3569156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3569156).length < 2 ^ (prefixWord ++ tailWord_3569156).sum := by decide
  have hdescent : baseEnd_3569156 < baseStart_3569156 := by decide
  rcases family_descends (prefixWord ++ tailWord_3569156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3569162 : List Nat := [3, 1, 2, 2, 2, 3, 1, 1, 4, 2, 2]
def baseStart_3569162 : Nat := 118140960795 + 3569162 * 2 ^ 59
def prefixEnd_3569162 : Nat := 4983230072969 + 3 ^ 40 * 3569162 * 2
def baseEnd_3569162 : Nat := 1832695639762669870960729

theorem tailTrace_3569162 : CollatzResearch.WordTrace tailWord_3569162 prefixEnd_3569162 1832695639762669870960729 := by
  unfold tailWord_3569162
  simp only [CollatzResearch.WordTrace]
  refine ⟨32544508173885778296203435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86785355130362075456542493 32544508173885778296203435)
  ·
    refine ⟨48816762260828667444305153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32544508173885778296203435 48816762260828667444305153)
    ·
      refine ⟨36612571695621500583228865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48816762260828667444305153 36612571695621500583228865)
      ·
        refine ⟨27459428771716125437421649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36612571695621500583228865 27459428771716125437421649)
        ·
          refine ⟨20594571578787094078066237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27459428771716125437421649 20594571578787094078066237)
          ·
            refine ⟨7722964342045160279274839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20594571578787094078066237 7722964342045160279274839)
            ·
              refine ⟨11584446513067740418912259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7722964342045160279274839 11584446513067740418912259)
              ·
                refine ⟨17376669769601610628368389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11584446513067740418912259 17376669769601610628368389)
                ·
                  refine ⟨3258125581800301992819073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17376669769601610628368389 3258125581800301992819073)
                  ·
                    refine ⟨2443594186350226494614305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3258125581800301992819073 2443594186350226494614305)
                    ·
                      refine ⟨1832695639762669870960729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2443594186350226494614305 1832695639762669870960729)
                      ·
                        rfl

theorem cell23_3569162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 1, 1, 4, 2, 2].length) (baseStart_3569162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3569162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3569162 prefixEnd_3569162 := by exact prefixLift 3569162
  have htrace : WordTrace (prefixWord ++ tailWord_3569162) baseStart_3569162 baseEnd_3569162 := by
    simpa [prefixWord, tailWord_3569162, baseEnd_3569162] using wordTrace_append hprefix tailTrace_3569162
  have hstable : (prefixWord ++ tailWord_3569162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3569162).length < 2 ^ (prefixWord ++ tailWord_3569162).sum := by decide
  have hdescent : baseEnd_3569162 < baseStart_3569162 := by decide
  rcases family_descends (prefixWord ++ tailWord_3569162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3569255 : List Nat := [1, 1, 5, 1, 1, 1, 3, 3, 2, 2, 3]
def baseStart_3569255 : Nat := 118140960795 + 3569255 * 2 ^ 59
def prefixEnd_3569255 : Nat := 4983230072969 + 3 ^ 40 * 3569255 * 2
def baseEnd_3569255 : Nat := 1832743393463538007097801

theorem tailTrace_3569255 : CollatzResearch.WordTrace tailWord_3569255 prefixEnd_3569255 1832743393463538007097801 := by
  unfold tailWord_3569255
  simp only [CollatzResearch.WordTrace]
  refine ⟨130181424684206190067949219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86787616456137460045299479 130181424684206190067949219)
  ·
    refine ⟨195272137026309285101923829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130181424684206190067949219 195272137026309285101923829)
    ·
      refine ⟨18306762846216495478305359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 195272137026309285101923829 18306762846216495478305359)
      ·
        refine ⟨27460144269324743217458039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18306762846216495478305359 27460144269324743217458039)
        ·
          refine ⟨41190216403987114826187059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27460144269324743217458039 41190216403987114826187059)
          ·
            refine ⟨61785324605980672239280589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41190216403987114826187059 61785324605980672239280589)
            ·
              refine ⟨23169496727242752089730221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61785324605980672239280589 23169496727242752089730221)
              ·
                refine ⟨8688561272716032033648833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23169496727242752089730221 8688561272716032033648833)
                ·
                  refine ⟨6516420954537024025236625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8688561272716032033648833 6516420954537024025236625)
                  ·
                    refine ⟨4887315715902768018927469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6516420954537024025236625 4887315715902768018927469)
                    ·
                      refine ⟨1832743393463538007097801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4887315715902768018927469 1832743393463538007097801)
                      ·
                        rfl

theorem cell23_3569255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 3, 3, 2, 2, 3].length) (baseStart_3569255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3569255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3569255 prefixEnd_3569255 := by exact prefixLift 3569255
  have htrace : WordTrace (prefixWord ++ tailWord_3569255) baseStart_3569255 baseEnd_3569255 := by
    simpa [prefixWord, tailWord_3569255, baseEnd_3569255] using wordTrace_append hprefix tailTrace_3569255
  have hstable : (prefixWord ++ tailWord_3569255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3569255).length < 2 ^ (prefixWord ++ tailWord_3569255).sum := by decide
  have hdescent : baseEnd_3569255 < baseStart_3569255 := by decide
  rcases family_descends (prefixWord ++ tailWord_3569255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3569312 : List Nat := [2, 1, 1, 4, 3, 2, 1, 1, 1, 5, 2]
def baseStart_3569312 : Nat := 118140960795 + 3569312 * 2 ^ 59
def prefixEnd_3569312 : Nat := 4983230072969 + 3 ^ 40 * 3569312 * 2
def baseEnd_3569312 : Nat := 1832772661860844284085039

theorem tailTrace_3569312 : CollatzResearch.WordTrace tailWord_3569312 prefixEnd_3569312 1832772661860844284085039 := by
  unfold tailWord_3569312
  simp only [CollatzResearch.WordTrace]
  refine ⟨65091751822499844401387095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86789002429999792535182793 65091751822499844401387095)
  ·
    refine ⟨97637627733749766602080643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65091751822499844401387095 97637627733749766602080643)
    ·
      refine ⟨146456441600624649903120965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97637627733749766602080643 146456441600624649903120965)
      ·
        refine ⟨27460582800117121856835181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 146456441600624649903120965 27460582800117121856835181)
        ·
          refine ⟨10297718550043920696313193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27460582800117121856835181 10297718550043920696313193)
          ·
            refine ⟨7723288912532940522234895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10297718550043920696313193 7723288912532940522234895)
            ·
              refine ⟨11584933368799410783352343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7723288912532940522234895 11584933368799410783352343)
              ·
                refine ⟨17377400053199116175028515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11584933368799410783352343 17377400053199116175028515)
                ·
                  refine ⟨26066100079798674262542773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17377400053199116175028515 26066100079798674262542773)
                  ·
                    refine ⟨2443696882481125712113385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 26066100079798674262542773 2443696882481125712113385)
                    ·
                      refine ⟨1832772661860844284085039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2443696882481125712113385 1832772661860844284085039)
                      ·
                        rfl

theorem cell23_3569312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 1, 1, 1, 5, 2].length) (baseStart_3569312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3569312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3569312 prefixEnd_3569312 := by exact prefixLift 3569312
  have htrace : WordTrace (prefixWord ++ tailWord_3569312) baseStart_3569312 baseEnd_3569312 := by
    simpa [prefixWord, tailWord_3569312, baseEnd_3569312] using wordTrace_append hprefix tailTrace_3569312
  have hstable : (prefixWord ++ tailWord_3569312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3569312).length < 2 ^ (prefixWord ++ tailWord_3569312).sum := by decide
  have hdescent : baseEnd_3569312 < baseStart_3569312 := by decide
  rcases family_descends (prefixWord ++ tailWord_3569312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3569326 : List Nat := [4, 1, 4, 1, 3, 1, 1, 2, 6]
def baseStart_3569326 : Nat := 118140960795 + 3569326 * 2 ^ 59
def prefixEnd_3569326 : Nat := 4983230072969 + 3 ^ 40 * 3569326 * 2
def baseEnd_3569326 : Nat := 203642205621111914367775

theorem tailTrace_3569326 : CollatzResearch.WordTrace tailWord_3569326 prefixEnd_3569326 203642205621111914367775 := by
  unfold tailWord_3569326
  simp only [CollatzResearch.WordTrace]
  refine ⟨16273001783368621149222979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 86789342844632646129189221 16273001783368621149222979)
  ·
    refine ⟨24409502675052931723834469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16273001783368621149222979 24409502675052931723834469)
    ·
      refine ⟨4576781751572424698218963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24409502675052931723834469 4576781751572424698218963)
      ·
        refine ⟨6865172627358637047328445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4576781751572424698218963 6865172627358637047328445)
        ·
          refine ⟨2574439735259488892748167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6865172627358637047328445 2574439735259488892748167)
          ·
            refine ⟨3861659602889233339122251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2574439735259488892748167 3861659602889233339122251)
            ·
              refine ⟨5792489404333850008683377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3861659602889233339122251 5792489404333850008683377)
              ·
                refine ⟨4344367053250387506512533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5792489404333850008683377 4344367053250387506512533)
                ·
                  refine ⟨203642205621111914367775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4344367053250387506512533 203642205621111914367775)
                  ·
                    rfl

theorem cell23_3569326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 3, 1, 1, 2, 6].length) (baseStart_3569326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3569326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3569326 prefixEnd_3569326 := by exact prefixLift 3569326
  have htrace : WordTrace (prefixWord ++ tailWord_3569326) baseStart_3569326 baseEnd_3569326 := by
    simpa [prefixWord, tailWord_3569326, baseEnd_3569326] using wordTrace_append hprefix tailTrace_3569326
  have hstable : (prefixWord ++ tailWord_3569326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3569326).length < 2 ^ (prefixWord ++ tailWord_3569326).sum := by decide
  have hdescent : baseEnd_3569326 < baseStart_3569326 := by decide
  rcases family_descends (prefixWord ++ tailWord_3569326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3569375 : List Nat := [1, 1, 2, 3, 2, 2, 2, 1, 3, 3, 3]
def baseStart_3569375 : Nat := 118140960795 + 3569375 * 2 ^ 59
def prefixEnd_3569375 : Nat := 4983230072969 + 3 ^ 40 * 3569375 * 2
def baseEnd_3569375 : Nat := 1832805011142077537597249

theorem tailTrace_3569375 : CollatzResearch.WordTrace tailWord_3569375 prefixEnd_3569375 1832805011142077537597249 := by
  unfold tailWord_3569375
  simp only [CollatzResearch.WordTrace]
  refine ⟨130185801443771450562317579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86790534295847633708211719 130185801443771450562317579)
  ·
    refine ⟨195278702165657175843476369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130185801443771450562317579 195278702165657175843476369)
    ·
      refine ⟨146459026624242881882607277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 195278702165657175843476369 146459026624242881882607277)
      ·
        refine ⟨54922134984091080705977729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 146459026624242881882607277 54922134984091080705977729)
        ·
          refine ⟨41191601238068310529483297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54922134984091080705977729 41191601238068310529483297)
          ·
            refine ⟨30893700928551232897112473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41191601238068310529483297 30893700928551232897112473)
            ·
              refine ⟨23170275696413424672834355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30893700928551232897112473 23170275696413424672834355)
              ·
                refine ⟨34755413544620137009251533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23170275696413424672834355 34755413544620137009251533)
                ·
                  refine ⟨13033280079232551378469325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34755413544620137009251533 13033280079232551378469325)
                  ·
                    refine ⟨4887480029712206766925997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13033280079232551378469325 4887480029712206766925997)
                    ·
                      refine ⟨1832805011142077537597249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4887480029712206766925997 1832805011142077537597249)
                      ·
                        rfl

theorem cell23_3569375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 2, 1, 3, 3, 3].length) (baseStart_3569375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3569375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3569375 prefixEnd_3569375 := by exact prefixLift 3569375
  have htrace : WordTrace (prefixWord ++ tailWord_3569375) baseStart_3569375 baseEnd_3569375 := by
    simpa [prefixWord, tailWord_3569375, baseEnd_3569375] using wordTrace_append hprefix tailTrace_3569375
  have hstable : (prefixWord ++ tailWord_3569375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3569375).length < 2 ^ (prefixWord ++ tailWord_3569375).sum := by decide
  have hdescent : baseEnd_3569375 < baseStart_3569375 := by decide
  rcases family_descends (prefixWord ++ tailWord_3569375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3569376 : List Nat := [2, 1, 1, 3, 1, 2, 5, 3, 1, 2, 2]
def baseStart_3569376 : Nat := 118140960795 + 3569376 * 2 ^ 59
def prefixEnd_3569376 : Nat := 4983230072969 + 3 ^ 40 * 3569376 * 2
def baseEnd_3569376 : Nat := 1832805524622732033684745

theorem tailTrace_3569376 : CollatzResearch.WordTrace tailWord_3569376 prefixEnd_3569376 1832805524622732033684745 := by
  unfold tailWord_3569376
  simp only [CollatzResearch.WordTrace]
  refine ⟨65092918958383913866551991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86790558611178551822069321 65092918958383913866551991)
  ·
    refine ⟨97639378437575870799827987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65092918958383913866551991 97639378437575870799827987)
    ·
      refine ⟨146459067656363806199741981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97639378437575870799827987 146459067656363806199741981)
      ·
        refine ⟨54922150371136427324903243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 146459067656363806199741981 54922150371136427324903243)
        ·
          refine ⟨82383225556704640987354865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54922150371136427324903243 82383225556704640987354865)
          ·
            refine ⟨61787419167528480740516149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82383225556704640987354865 61787419167528480740516149)
            ·
              refine ⟨5792570546955795069423389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 61787419167528480740516149 5792570546955795069423389)
              ·
                refine ⟨2172213955108423151033771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5792570546955795069423389 2172213955108423151033771)
                ·
                  refine ⟨3258320932662634726550657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2172213955108423151033771 3258320932662634726550657)
                  ·
                    refine ⟨2443740699496976044912993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3258320932662634726550657 2443740699496976044912993)
                    ·
                      refine ⟨1832805524622732033684745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2443740699496976044912993 1832805524622732033684745)
                      ·
                        rfl

theorem cell23_3569376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 5, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 5, 3, 1, 2, 2].length) (baseStart_3569376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3569376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3569376 prefixEnd_3569376 := by exact prefixLift 3569376
  have htrace : WordTrace (prefixWord ++ tailWord_3569376) baseStart_3569376 baseEnd_3569376 := by
    simpa [prefixWord, tailWord_3569376, baseEnd_3569376] using wordTrace_append hprefix tailTrace_3569376
  have hstable : (prefixWord ++ tailWord_3569376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3569376).length < 2 ^ (prefixWord ++ tailWord_3569376).sum := by decide
  have hdescent : baseEnd_3569376 < baseStart_3569376 := by decide
  rcases family_descends (prefixWord ++ tailWord_3569376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3569393 : List Nat := [1, 2, 2, 2, 2, 4, 3, 2, 1, 2, 2]
def baseStart_3569393 : Nat := 118140960795 + 3569393 * 2 ^ 59
def prefixEnd_3569393 : Nat := 4983230072969 + 3 ^ 40 * 3569393 * 2
def baseEnd_3569393 : Nat := 1832814253793858467172167

theorem tailTrace_3569393 : CollatzResearch.WordTrace tailWord_3569393 prefixEnd_3569393 1832814253793858467172167 := by
  unfold tailWord_3569393
  simp only [CollatzResearch.WordTrace]
  refine ⟨130186457957706239636472833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86790971971804159757648555 130186457957706239636472833)
  ·
    refine ⟨97639843468279679727354625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130186457957706239636472833 97639843468279679727354625)
    ·
      refine ⟨73229882601209759795515969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97639843468279679727354625 73229882601209759795515969)
      ·
        refine ⟨54922411950907319846636977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73229882601209759795515969 54922411950907319846636977)
        ·
          refine ⟨41191808963180489884977733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54922411950907319846636977 41191808963180489884977733)
          ·
            refine ⟨7723464180596341853433325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41191808963180489884977733 7723464180596341853433325)
            ·
              refine ⟨2896299067723628195037497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7723464180596341853433325 2896299067723628195037497)
              ·
                refine ⟨2172224300792721146278123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2896299067723628195037497 2172224300792721146278123)
                ·
                  refine ⟨3258336451189081719417185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2172224300792721146278123 3258336451189081719417185)
                  ·
                    refine ⟨2443752338391811289562889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3258336451189081719417185 2443752338391811289562889)
                    ·
                      refine ⟨1832814253793858467172167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2443752338391811289562889 1832814253793858467172167)
                      ·
                        rfl

theorem cell23_3569393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 3, 2, 1, 2, 2].length) (baseStart_3569393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3569393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3569393 prefixEnd_3569393 := by exact prefixLift 3569393
  have htrace : WordTrace (prefixWord ++ tailWord_3569393) baseStart_3569393 baseEnd_3569393 := by
    simpa [prefixWord, tailWord_3569393, baseEnd_3569393] using wordTrace_append hprefix tailTrace_3569393
  have hstable : (prefixWord ++ tailWord_3569393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3569393).length < 2 ^ (prefixWord ++ tailWord_3569393).sum := by decide
  have hdescent : baseEnd_3569393 < baseStart_3569393 := by decide
  rcases family_descends (prefixWord ++ tailWord_3569393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3569402 : List Nat := [3, 1, 1, 1, 1, 3, 1, 4, 3, 3, 2]
def baseStart_3569402 : Nat := 118140960795 + 3569402 * 2 ^ 59
def prefixEnd_3569402 : Nat := 4983230072969 + 3 ^ 40 * 3569402 * 2
def baseEnd_3569402 : Nat := 1832818875119748931959625

theorem tailTrace_3569402 : CollatzResearch.WordTrace tailWord_3569402 prefixEnd_3569402 1832818875119748931959625 := by
  unfold tailWord_3569402
  simp only [CollatzResearch.WordTrace]
  refine ⟨32546696553668408543387615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86791190809782422782366973 32546696553668408543387615)
  ·
    refine ⟨48820044830502612815081423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32546696553668408543387615 48820044830502612815081423)
    ·
      refine ⟨73230067245753919222622135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48820044830502612815081423 73230067245753919222622135)
      ·
        refine ⟨109845100868630878833933203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73230067245753919222622135 109845100868630878833933203)
        ·
          refine ⟨164767651302946318250899805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109845100868630878833933203 164767651302946318250899805)
          ·
            refine ⟨61787869238604869344087427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 164767651302946318250899805 61787869238604869344087427)
            ·
              refine ⟨92681803857907304016131141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61787869238604869344087427 92681803857907304016131141)
              ·
                refine ⟨17377838223357619503024589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 92681803857907304016131141 17377838223357619503024589)
                ·
                  refine ⟨6516689333759107313634221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17377838223357619503024589 6516689333759107313634221)
                  ·
                    refine ⟨2443758500159665242612833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6516689333759107313634221 2443758500159665242612833)
                    ·
                      refine ⟨1832818875119748931959625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2443758500159665242612833 1832818875119748931959625)
                      ·
                        rfl

theorem cell23_3569402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 4, 3, 3, 2].length) (baseStart_3569402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3569402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3569402 prefixEnd_3569402 := by exact prefixLift 3569402
  have htrace : WordTrace (prefixWord ++ tailWord_3569402) baseStart_3569402 baseEnd_3569402 := by
    simpa [prefixWord, tailWord_3569402, baseEnd_3569402] using wordTrace_append hprefix tailTrace_3569402
  have hstable : (prefixWord ++ tailWord_3569402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3569402).length < 2 ^ (prefixWord ++ tailWord_3569402).sum := by decide
  have hdescent : baseEnd_3569402 < baseStart_3569402 := by decide
  rcases family_descends (prefixWord ++ tailWord_3569402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3569419 : List Nat := [1, 1, 1, 1, 5, 1, 5, 2, 1, 3, 2]
def baseStart_3569419 : Nat := 118140960795 + 3569419 * 2 ^ 59
def prefixEnd_3569419 : Nat := 4983230072969 + 3 ^ 40 * 3569419 * 2
def baseEnd_3569419 : Nat := 1832827604290875365447047

theorem tailTrace_3569419 : CollatzResearch.WordTrace tailWord_3569419 prefixEnd_3569419 1832827604290875365447047 := by
  unfold tailWord_3569419
  simp only [CollatzResearch.WordTrace]
  refine ⟨130187406255612046076919311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86791604170408030717946207 130187406255612046076919311)
  ·
    refine ⟨195281109383418069115378967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130187406255612046076919311 195281109383418069115378967)
    ·
      refine ⟨292921664075127103673068451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195281109383418069115378967 292921664075127103673068451)
      ·
        refine ⟨439382496112690655509602677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 292921664075127103673068451 439382496112690655509602677)
        ·
          refine ⟨41192109010564748954025251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 439382496112690655509602677 41192109010564748954025251)
          ·
            refine ⟨61788163515847123431037877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41192109010564748954025251 61788163515847123431037877)
            ·
              refine ⟨5792640329610667821659801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 61788163515847123431037877 5792640329610667821659801)
              ·
                refine ⟨4344480247208000866244851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5792640329610667821659801 4344480247208000866244851)
                ·
                  refine ⟨6516720370812001299367277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4344480247208000866244851 6516720370812001299367277)
                  ·
                    refine ⟨2443770139054500487262729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6516720370812001299367277 2443770139054500487262729)
                    ·
                      refine ⟨1832827604290875365447047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2443770139054500487262729 1832827604290875365447047)
                      ·
                        rfl

theorem cell23_3569419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 5, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 5, 2, 1, 3, 2].length) (baseStart_3569419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3569419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3569419 prefixEnd_3569419 := by exact prefixLift 3569419
  have htrace : WordTrace (prefixWord ++ tailWord_3569419) baseStart_3569419 baseEnd_3569419 := by
    simpa [prefixWord, tailWord_3569419, baseEnd_3569419] using wordTrace_append hprefix tailTrace_3569419
  have hstable : (prefixWord ++ tailWord_3569419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3569419).length < 2 ^ (prefixWord ++ tailWord_3569419).sum := by decide
  have hdescent : baseEnd_3569419 < baseStart_3569419 := by decide
  rcases family_descends (prefixWord ++ tailWord_3569419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3569432 : List Nat := [2, 1, 2, 3, 1, 1, 3, 1, 3, 4, 2]
def baseStart_3569432 : Nat := 118140960795 + 3569432 * 2 ^ 59
def prefixEnd_3569432 : Nat := 4983230072969 + 3 ^ 40 * 3569432 * 2
def baseEnd_3569432 : Nat := 1832834279539383814584487

theorem tailTrace_3569432 : CollatzResearch.WordTrace tailWord_3569432 prefixEnd_3569432 1832834279539383814584487 := by
  unfold tailWord_3569432
  simp only [CollatzResearch.WordTrace]
  refine ⟨65093940202282474648571275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86791920269709966198095033 65093940202282474648571275)
  ·
    refine ⟨97640910303423711972856913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65093940202282474648571275 97640910303423711972856913)
    ·
      refine ⟨73230682727567783979642685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97640910303423711972856913 73230682727567783979642685)
      ·
        refine ⟨27461506022837918992366007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73230682727567783979642685 27461506022837918992366007)
        ·
          refine ⟨41192259034256878488549011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27461506022837918992366007 41192259034256878488549011)
          ·
            refine ⟨61788388551385317732823517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41192259034256878488549011 61788388551385317732823517)
            ·
              refine ⟨23170645706769494149808819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61788388551385317732823517 23170645706769494149808819)
              ·
                refine ⟨34755968560154241224713229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23170645706769494149808819 34755968560154241224713229)
                ·
                  refine ⟨13033488210057840459267461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34755968560154241224713229 13033488210057840459267461)
                  ·
                    refine ⟨2443779039385845086112649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13033488210057840459267461 2443779039385845086112649)
                    ·
                      refine ⟨1832834279539383814584487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2443779039385845086112649 1832834279539383814584487)
                      ·
                        rfl

theorem cell23_3569432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 3, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 3, 1, 3, 4, 2].length) (baseStart_3569432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3569432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3569432 prefixEnd_3569432 := by exact prefixLift 3569432
  have htrace : WordTrace (prefixWord ++ tailWord_3569432) baseStart_3569432 baseEnd_3569432 := by
    simpa [prefixWord, tailWord_3569432, baseEnd_3569432] using wordTrace_append hprefix tailTrace_3569432
  have hstable : (prefixWord ++ tailWord_3569432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3569432).length < 2 ^ (prefixWord ++ tailWord_3569432).sum := by decide
  have hdescent : baseEnd_3569432 < baseStart_3569432 := by decide
  rcases family_descends (prefixWord ++ tailWord_3569432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3569436 : List Nat := [2, 2, 3, 1, 1, 2, 5, 1, 1, 3, 2]
def baseStart_3569436 : Nat := 118140960795 + 3569436 * 2 ^ 59
def prefixEnd_3569436 : Nat := 4983230072969 + 3 ^ 40 * 3569436 * 2
def baseEnd_3569436 : Nat := 1832836333462001798934469

theorem tailTrace_3569436 : CollatzResearch.WordTrace tailWord_3569436 prefixEnd_3569436 1832836333462001798934469 := by
  unfold tailWord_3569436
  simp only [CollatzResearch.WordTrace]
  refine ⟨65094013148275228990144081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86792017531033638653525441 65094013148275228990144081)
  ·
    refine ⟨48820509861206421742608061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65094013148275228990144081 48820509861206421742608061)
    ·
      refine ⟨18307691197952408153478023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48820509861206421742608061 18307691197952408153478023)
      ·
        refine ⟨27461536796928612230217035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18307691197952408153478023 27461536796928612230217035)
        ·
          refine ⟨41192305195392918345325553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27461536796928612230217035 41192305195392918345325553)
          ·
            refine ⟨30894228896544688758994165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41192305195392918345325553 30894228896544688758994165)
            ·
              refine ⟨2896333959051064571155703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 30894228896544688758994165 2896333959051064571155703)
              ·
                refine ⟨4344500938576596856733555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2896333959051064571155703 4344500938576596856733555)
                ·
                  refine ⟨6516751407864895285100333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4344500938576596856733555 6516751407864895285100333)
                  ·
                    refine ⟨2443781777949335731912625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6516751407864895285100333 2443781777949335731912625)
                    ·
                      refine ⟨1832836333462001798934469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2443781777949335731912625 1832836333462001798934469)
                      ·
                        rfl

theorem cell23_3569436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 5, 1, 1, 3, 2].length) (baseStart_3569436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3569436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3569436 prefixEnd_3569436 := by exact prefixLift 3569436
  have htrace : WordTrace (prefixWord ++ tailWord_3569436) baseStart_3569436 baseEnd_3569436 := by
    simpa [prefixWord, tailWord_3569436, baseEnd_3569436] using wordTrace_append hprefix tailTrace_3569436
  have hstable : (prefixWord ++ tailWord_3569436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3569436).length < 2 ^ (prefixWord ++ tailWord_3569436).sum := by decide
  have hdescent : baseEnd_3569436 < baseStart_3569436 := by decide
  rcases family_descends (prefixWord ++ tailWord_3569436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3569466 : List Nat := [3, 1, 1, 1, 5, 1, 2, 3, 2, 2, 2]
def baseStart_3569466 : Nat := 118140960795 + 3569466 * 2 ^ 59
def prefixEnd_3569466 : Nat := 4983230072969 + 3 ^ 40 * 3569466 * 2
def baseEnd_3569466 : Nat := 1832851737881636681559331

theorem tailTrace_3569466 : CollatzResearch.WordTrace tailWord_3569466 prefixEnd_3569466 1832851737881636681559331 := by
  unfold tailWord_3569466
  simp only [CollatzResearch.WordTrace]
  refine ⟨32547280121610443275970063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86792746990961182069253501 32547280121610443275970063)
  ·
    refine ⟨48820920182415664913955095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32547280121610443275970063 48820920182415664913955095)
    ·
      refine ⟨73231380273623497370932643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48820920182415664913955095 73231380273623497370932643)
      ·
        refine ⟨109847070410435246056398965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73231380273623497370932643 109847070410435246056398965)
        ·
          refine ⟨10298162850978304317787403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 109847070410435246056398965 10298162850978304317787403)
          ·
            refine ⟨15447244276467456476681105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10298162850978304317787403 15447244276467456476681105)
            ·
              refine ⟨11585433207350592357510829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15447244276467456476681105 11585433207350592357510829)
              ·
                refine ⟨4344537452756472134066561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11585433207350592357510829 4344537452756472134066561)
                ·
                  refine ⟨3258403089567354100549921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4344537452756472134066561 3258403089567354100549921)
                  ·
                    refine ⟨2443802317175515575412441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3258403089567354100549921 2443802317175515575412441)
                    ·
                      refine ⟨1832851737881636681559331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2443802317175515575412441 1832851737881636681559331)
                      ·
                        rfl

theorem cell23_3569466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 2, 3, 2, 2, 2].length) (baseStart_3569466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3569466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3569466 prefixEnd_3569466 := by exact prefixLift 3569466
  have htrace : WordTrace (prefixWord ++ tailWord_3569466) baseStart_3569466 baseEnd_3569466 := by
    simpa [prefixWord, tailWord_3569466, baseEnd_3569466] using wordTrace_append hprefix tailTrace_3569466
  have hstable : (prefixWord ++ tailWord_3569466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3569466).length < 2 ^ (prefixWord ++ tailWord_3569466).sum := by decide
  have hdescent : baseEnd_3569466 < baseStart_3569466 := by decide
  rcases family_descends (prefixWord ++ tailWord_3569466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3569489 : List Nat := [1, 2, 2, 1, 5, 2, 2, 3, 5]
def baseStart_3569489 : Nat := 118140960795 + 3569489 * 2 ^ 59
def prefixEnd_3569489 : Nat := 4983230072969 + 3 ^ 40 * 3569489 * 2
def baseEnd_3569489 : Nat := 203651505326298899063525

theorem tailTrace_3569489 : CollatzResearch.WordTrace tailWord_3569489 prefixEnd_3569489 203651505326298899063525 := by
  unfold tailWord_3569489
  simp only [CollatzResearch.WordTrace]
  refine ⟨130189959365358448031967521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86793306243572298687978347 130189959365358448031967521)
  ·
    refine ⟨97642469524018836023975641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130189959365358448031967521 97642469524018836023975641)
    ·
      refine ⟨73231852143014127017981731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97642469524018836023975641 73231852143014127017981731)
      ·
        refine ⟨109847778214521190526972597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73231852143014127017981731 109847778214521190526972597)
        ·
          refine ⟨10298229207611361611903681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 109847778214521190526972597 10298229207611361611903681)
          ·
            refine ⟨7723671905708521208927761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10298229207611361611903681 7723671905708521208927761)
            ·
              refine ⟨5792753929281390906695821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7723671905708521208927761 5792753929281390906695821)
              ·
                refine ⟨2172282723480521590010933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5792753929281390906695821 2172282723480521590010933)
                ·
                  refine ⟨203651505326298899063525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2172282723480521590010933 203651505326298899063525)
                  ·
                    rfl

theorem cell23_3569489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 2, 3, 5].length) (baseStart_3569489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3569489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3569489 prefixEnd_3569489 := by exact prefixLift 3569489
  have htrace : WordTrace (prefixWord ++ tailWord_3569489) baseStart_3569489 baseEnd_3569489 := by
    simpa [prefixWord, tailWord_3569489, baseEnd_3569489] using wordTrace_append hprefix tailTrace_3569489
  have hstable : (prefixWord ++ tailWord_3569489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3569489).length < 2 ^ (prefixWord ++ tailWord_3569489).sum := by decide
  have hdescent : baseEnd_3569489 < baseStart_3569489 := by decide
  rcases family_descends (prefixWord ++ tailWord_3569489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3569500 : List Nat := [2, 2, 4, 2, 2, 2, 1, 2, 2, 2, 2]
def baseStart_3569500 : Nat := 118140960795 + 3569500 * 2 ^ 59
def prefixEnd_3569500 : Nat := 4983230072969 + 3 ^ 40 * 3569500 * 2
def baseEnd_3569500 : Nat := 1832869196223889548534175

theorem tailTrace_3569500 : CollatzResearch.WordTrace tailWord_3569500 prefixEnd_3569500 1832869196223889548534175 := by
  unfold tailWord_3569500
  simp only [CollatzResearch.WordTrace]
  refine ⟨65095180284159298455308977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86793573712212397940411969 65095180284159298455308977)
  ·
    refine ⟨48821385213119473841481733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65095180284159298455308977 48821385213119473841481733)
    ·
      refine ⟨9154009727459901345277825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48821385213119473841481733 9154009727459901345277825)
      ·
        refine ⟨6865507295594926008958369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9154009727459901345277825 6865507295594926008958369)
        ·
          refine ⟨5149130471696194506718777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6865507295594926008958369 5149130471696194506718777)
          ·
            refine ⟨3861847853772145880039083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5149130471696194506718777 3861847853772145880039083)
            ·
              refine ⟨5792771780658218820058625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3861847853772145880039083 5792771780658218820058625)
              ·
                refine ⟨4344578835493664115043969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5792771780658218820058625 4344578835493664115043969)
                ·
                  refine ⟨3258434126620248086282977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4344578835493664115043969 3258434126620248086282977)
                  ·
                    refine ⟨2443825594965186064712233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3258434126620248086282977 2443825594965186064712233)
                    ·
                      refine ⟨1832869196223889548534175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2443825594965186064712233 1832869196223889548534175)
                      ·
                        rfl

theorem cell23_3569500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 2, 1, 2, 2, 2, 2].length) (baseStart_3569500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3569500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3569500 prefixEnd_3569500 := by exact prefixLift 3569500
  have htrace : WordTrace (prefixWord ++ tailWord_3569500) baseStart_3569500 baseEnd_3569500 := by
    simpa [prefixWord, tailWord_3569500, baseEnd_3569500] using wordTrace_append hprefix tailTrace_3569500
  have hstable : (prefixWord ++ tailWord_3569500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3569500).length < 2 ^ (prefixWord ++ tailWord_3569500).sum := by decide
  have hdescent : baseEnd_3569500 < baseStart_3569500 := by decide
  rcases family_descends (prefixWord ++ tailWord_3569500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3569535 : List Nat := [1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 4]
def baseStart_3569535 : Nat := 118140960795 + 3569535 * 2 ^ 59
def prefixEnd_3569535 : Nat := 4983230072969 + 3 ^ 40 * 3569535 * 2
def baseEnd_3569535 : Nat := 1832887168046796911596513

theorem tailTrace_3569535 : CollatzResearch.WordTrace tailWord_3569535 prefixEnd_3569535 1832887168046796911596513 := by
  unfold tailWord_3569535
  simp only [CollatzResearch.WordTrace]
  refine ⟨130191637123191797888142059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86794424748794531925428039 130191637123191797888142059)
  ·
    refine ⟨195287455684787696832213089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130191637123191797888142059 195287455684787696832213089)
    ·
      refine ⟨146465591763590772624159817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 195287455684787696832213089 146465591763590772624159817)
      ·
        refine ⟨109849193822693079468119863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146465591763590772624159817 109849193822693079468119863)
        ·
          refine ⟨164773790734039619202179795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109849193822693079468119863 164773790734039619202179795)
          ·
            refine ⟨247160686101059428803269693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 164773790734039619202179795 247160686101059428803269693)
            ·
              refine ⟨92685257287897285801226135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 247160686101059428803269693 92685257287897285801226135)
              ·
                refine ⟨139027885931845928701839203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92685257287897285801226135 139027885931845928701839203)
                ·
                  refine ⟨208541828897768893052758805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 139027885931845928701839203 208541828897768893052758805)
                  ·
                    refine ⟨9775398229582916861848069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 208541828897768893052758805 9775398229582916861848069)
                    ·
                      refine ⟨1832887168046796911596513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9775398229582916861848069 1832887168046796911596513)
                      ·
                        rfl

theorem cell23_3569535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 4].length) (baseStart_3569535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3569535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3569535 prefixEnd_3569535 := by exact prefixLift 3569535
  have htrace : WordTrace (prefixWord ++ tailWord_3569535) baseStart_3569535 baseEnd_3569535 := by
    simpa [prefixWord, tailWord_3569535, baseEnd_3569535] using wordTrace_append hprefix tailTrace_3569535
  have hstable : (prefixWord ++ tailWord_3569535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3569535).length < 2 ^ (prefixWord ++ tailWord_3569535).sum := by decide
  have hdescent : baseEnd_3569535 < baseStart_3569535 := by decide
  rcases family_descends (prefixWord ++ tailWord_3569535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3569545 : List Nat := [1, 2, 1, 1, 5, 1, 1, 1, 10]
def baseStart_3569545 : Nat := 118140960795 + 3569545 * 2 ^ 59
def prefixEnd_3569545 : Nat := 4983230072969 + 3 ^ 40 * 3569545 * 2
def baseEnd_3569545 : Nat := 203654700317037985830163

theorem tailTrace_3569545 : CollatzResearch.WordTrace tailWord_3569545 prefixEnd_3569545 203654700317037985830163 := by
  unfold tailWord_3569545
  simp only [CollatzResearch.WordTrace]
  refine ⟨130192001853155569596006089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86794667902103713064004059 130192001853155569596006089)
  ·
    refine ⟨97644001389866677197004567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130192001853155569596006089 97644001389866677197004567)
    ·
      refine ⟨146466002084800015795506851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97644001389866677197004567 146466002084800015795506851)
      ·
        refine ⟨219699003127200023693260277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146466002084800015795506851 219699003127200023693260277)
        ·
          refine ⟨20596781543175002221243151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 219699003127200023693260277 20596781543175002221243151)
          ·
            refine ⟨30895172314762503331864727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20596781543175002221243151 30895172314762503331864727)
            ·
              refine ⟨46342758472143754997797091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30895172314762503331864727 46342758472143754997797091)
              ·
                refine ⟨69514137708215632496695637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46342758472143754997797091 69514137708215632496695637)
                ·
                  refine ⟨203654700317037985830163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 69514137708215632496695637 203654700317037985830163)
                  ·
                    rfl

theorem cell23_3569545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 1, 10].length) (baseStart_3569545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3569545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3569545 prefixEnd_3569545 := by exact prefixLift 3569545
  have htrace : WordTrace (prefixWord ++ tailWord_3569545) baseStart_3569545 baseEnd_3569545 := by
    simpa [prefixWord, tailWord_3569545, baseEnd_3569545] using wordTrace_append hprefix tailTrace_3569545
  have hstable : (prefixWord ++ tailWord_3569545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3569545).length < 2 ^ (prefixWord ++ tailWord_3569545).sum := by decide
  have hdescent : baseEnd_3569545 < baseStart_3569545 := by decide
  rcases family_descends (prefixWord ++ tailWord_3569545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3569559 : List Nat := [1, 1, 3, 3, 1, 4, 1, 2, 2, 2, 3]
def baseStart_3569559 : Nat := 118140960795 + 3569559 * 2 ^ 59
def prefixEnd_3569559 : Nat := 4983230072969 + 3 ^ 40 * 3569559 * 2
def baseEnd_3569559 : Nat := 1832899491582504817696403

theorem tailTrace_3569559 : CollatzResearch.WordTrace tailWord_3569559 prefixEnd_3569559 1832899491582504817696403 := by
  unfold tailWord_3569559
  simp only [CollatzResearch.WordTrace]
  refine ⟨130192512475104849987015731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86795008316736566658010487 130192512475104849987015731)
  ·
    refine ⟨195288768712657274980523597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130192512475104849987015731 195288768712657274980523597)
    ·
      refine ⟨73233288267246478117696349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 195288768712657274980523597 73233288267246478117696349)
      ·
        refine ⟨27462483100217429294136131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73233288267246478117696349 27462483100217429294136131)
        ·
          refine ⟨41193724650326143941204197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27462483100217429294136131 41193724650326143941204197)
          ·
            refine ⟨7723823371936151988975787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41193724650326143941204197 7723823371936151988975787)
            ·
              refine ⟨11585735057904227983463681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7723823371936151988975787 11585735057904227983463681)
              ·
                refine ⟨8689301293428170987597761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11585735057904227983463681 8689301293428170987597761)
                ·
                  refine ⟨6516975970071128240698321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8689301293428170987597761 6516975970071128240698321)
                  ·
                    refine ⟨4887731977553346180523741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6516975970071128240698321 4887731977553346180523741)
                    ·
                      refine ⟨1832899491582504817696403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4887731977553346180523741 1832899491582504817696403)
                      ·
                        rfl

theorem cell23_3569559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 1, 2, 2, 2, 3].length) (baseStart_3569559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3569559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3569559 prefixEnd_3569559 := by exact prefixLift 3569559
  have htrace : WordTrace (prefixWord ++ tailWord_3569559) baseStart_3569559 baseEnd_3569559 := by
    simpa [prefixWord, tailWord_3569559, baseEnd_3569559] using wordTrace_append hprefix tailTrace_3569559
  have hstable : (prefixWord ++ tailWord_3569559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3569559).length < 2 ^ (prefixWord ++ tailWord_3569559).sum := by decide
  have hdescent : baseEnd_3569559 < baseStart_3569559 := by decide
  rcases family_descends (prefixWord ++ tailWord_3569559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3569562 : List Nat := [3, 1, 1, 4, 2, 1, 2, 1, 8]
def baseStart_3569562 : Nat := 118140960795 + 3569562 * 2 ^ 59
def prefixEnd_3569562 : Nat := 4983230072969 + 3 ^ 40 * 3569562 * 2
def baseEnd_3569562 : Nat := 203655670224940922884321

theorem tailTrace_3569562 : CollatzResearch.WordTrace tailWord_3569562 prefixEnd_3569562 203655670224940922884321 := by
  unfold tailWord_3569562
  simp only [CollatzResearch.WordTrace]
  refine ⟨32548155473523495374843735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86795081262729320999583293 32548155473523495374843735)
  ·
    refine ⟨48822233210285243062265603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32548155473523495374843735 48822233210285243062265603)
    ·
      refine ⟨73233349815427864593398405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48822233210285243062265603 73233349815427864593398405)
      ·
        refine ⟨13731253090392724611262201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 73233349815427864593398405 13731253090392724611262201)
        ·
          refine ⟨10298439817794543458446651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13731253090392724611262201 10298439817794543458446651)
          ·
            refine ⟨15447659726691815187669977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10298439817794543458446651 15447659726691815187669977)
            ·
              refine ⟨11585744795018861390752483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15447659726691815187669977 11585744795018861390752483)
              ·
                refine ⟨17378617192528292086128725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11585744795018861390752483 17378617192528292086128725)
                ·
                  refine ⟨203655670224940922884321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 17378617192528292086128725 203655670224940922884321)
                  ·
                    rfl

theorem cell23_3569562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 2, 1, 8].length) (baseStart_3569562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3569562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3569562 prefixEnd_3569562 := by exact prefixLift 3569562
  have htrace : WordTrace (prefixWord ++ tailWord_3569562) baseStart_3569562 baseEnd_3569562 := by
    simpa [prefixWord, tailWord_3569562, baseEnd_3569562] using wordTrace_append hprefix tailTrace_3569562
  have hstable : (prefixWord ++ tailWord_3569562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3569562).length < 2 ^ (prefixWord ++ tailWord_3569562).sum := by decide
  have hdescent : baseEnd_3569562 < baseStart_3569562 := by decide
  rcases family_descends (prefixWord ++ tailWord_3569562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3569592 : List Nat := [2, 1, 2, 1, 2, 3, 3, 1, 3, 5]
def baseStart_3569592 : Nat := 118140960795 + 3569592 * 2 ^ 59
def prefixEnd_3569592 : Nat := 4983230072969 + 3 ^ 40 * 3569592 * 2
def baseEnd_3569592 : Nat := 610972145481367729527917

theorem tailTrace_3569592 : CollatzResearch.WordTrace tailWord_3569592 prefixEnd_3569592 610972145481367729527917 := by
  unfold tailWord_3569592
  simp only [CollatzResearch.WordTrace]
  refine ⟨65096858041992648311483515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86795810722656864415311353 65096858041992648311483515)
  ·
    refine ⟨97645287062988972467225273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65096858041992648311483515 97645287062988972467225273)
    ·
      refine ⟨73233965297241729350418955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97645287062988972467225273 73233965297241729350418955)
      ·
        refine ⟨109850947945862594025628433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73233965297241729350418955 109850947945862594025628433)
        ·
          refine ⟨82388210959396945519221325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109850947945862594025628433 82388210959396945519221325)
          ·
            refine ⟨30895579109773854569707997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 82388210959396945519221325 30895579109773854569707997)
            ·
              refine ⟨11585842166165195463640499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30895579109773854569707997 11585842166165195463640499)
              ·
                refine ⟨17378763249247793195460749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11585842166165195463640499 17378763249247793195460749)
                ·
                  refine ⟨6517036218467922448297781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17378763249247793195460749 6517036218467922448297781)
                  ·
                    refine ⟨610972145481367729527917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6517036218467922448297781 610972145481367729527917)
                    ·
                      rfl

theorem cell23_3569592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 3, 1, 3, 5].length) (baseStart_3569592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3569592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3569592 prefixEnd_3569592 := by exact prefixLift 3569592
  have htrace : WordTrace (prefixWord ++ tailWord_3569592) baseStart_3569592 baseEnd_3569592 := by
    simpa [prefixWord, tailWord_3569592, baseEnd_3569592] using wordTrace_append hprefix tailTrace_3569592
  have hstable : (prefixWord ++ tailWord_3569592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3569592).length < 2 ^ (prefixWord ++ tailWord_3569592).sum := by decide
  have hdescent : baseEnd_3569592 < baseStart_3569592 := by decide
  rcases family_descends (prefixWord ++ tailWord_3569592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3569632 : List Nat := [2, 1, 1, 3, 1, 1, 1, 6, 1, 1, 5]
def baseStart_3569632 : Nat := 118140960795 + 3569632 * 2 ^ 59
def prefixEnd_3569632 : Nat := 4983230072969 + 3 ^ 40 * 3569632 * 2
def baseEnd_3569632 : Nat := 1832936975670283032083567

theorem tailTrace_3569632 : CollatzResearch.WordTrace tailWord_3569632 prefixEnd_3569632 1832936975670283032083567 := by
  unfold tailWord_3569632
  simp only [CollatzResearch.WordTrace]
  refine ⟨65097587501920191727211575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86796783335893588969615433 65097587501920191727211575)
  ·
    refine ⟨97646381252880287590817363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65097587501920191727211575 97646381252880287590817363)
    ·
      refine ⟨146469571879320431386226045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97646381252880287590817363 146469571879320431386226045)
      ·
        refine ⟨54926089454745161769834767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 146469571879320431386226045 54926089454745161769834767)
        ·
          refine ⟨82389134182117742654752151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54926089454745161769834767 82389134182117742654752151)
          ·
            refine ⟨123583701273176613982128227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82389134182117742654752151 123583701273176613982128227)
            ·
              refine ⟨185375551909764920973192341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 123583701273176613982128227 185375551909764920973192341)
              ·
                refine ⟨8689478995770230670618391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 185375551909764920973192341 8689478995770230670618391)
                ·
                  refine ⟨13034218493655346005927587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8689478995770230670618391 13034218493655346005927587)
                  ·
                    refine ⟨19551327740483019008891381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13034218493655346005927587 19551327740483019008891381)
                    ·
                      refine ⟨1832936975670283032083567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19551327740483019008891381 1832936975670283032083567)
                      ·
                        rfl

theorem cell23_3569632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 6, 1, 1, 5].length) (baseStart_3569632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3569632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3569632 prefixEnd_3569632 := by exact prefixLift 3569632
  have htrace : WordTrace (prefixWord ++ tailWord_3569632) baseStart_3569632 baseEnd_3569632 := by
    simpa [prefixWord, tailWord_3569632, baseEnd_3569632] using wordTrace_append hprefix tailTrace_3569632
  have hstable : (prefixWord ++ tailWord_3569632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3569632).length < 2 ^ (prefixWord ++ tailWord_3569632).sum := by decide
  have hdescent : baseEnd_3569632 < baseStart_3569632 := by decide
  rcases family_descends (prefixWord ++ tailWord_3569632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3569703 : List Nat := [1, 1, 7, 1, 2, 2, 2, 7]
def baseStart_3569703 : Nat := 118140960795 + 3569703 * 2 ^ 59
def prefixEnd_3569703 : Nat := 4983230072969 + 3 ^ 40 * 3569703 * 2
def baseEnd_3569703 : Nat := 67887904918398231640583

theorem tailTrace_3569703 : CollatzResearch.WordTrace tailWord_3569703 prefixEnd_3569703 67887904918398231640583 := by
  unfold tailWord_3569703
  simp only [CollatzResearch.WordTrace]
  refine ⟨130197764586583162580257763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86798509724388775053505175 130197764586583162580257763)
  ·
    refine ⟨195296646879874743870386645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130197764586583162580257763 195296646879874743870386645)
    ·
      refine ⟨4577265161247064309462187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 195296646879874743870386645 4577265161247064309462187)
      ·
        refine ⟨6865897741870596464193281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4577265161247064309462187 6865897741870596464193281)
        ·
          refine ⟨5149423306402947348144961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6865897741870596464193281 5149423306402947348144961)
          ·
            refine ⟨3862067479802210511108721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5149423306402947348144961 3862067479802210511108721)
            ·
              refine ⟨2896550609851657883331541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3862067479802210511108721 2896550609851657883331541)
              ·
                refine ⟨67887904918398231640583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2896550609851657883331541 67887904918398231640583)
                ·
                  rfl

theorem cell23_3569703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 2, 2, 7].length) (baseStart_3569703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3569703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3569703 prefixEnd_3569703 := by exact prefixLift 3569703
  have htrace : WordTrace (prefixWord ++ tailWord_3569703) baseStart_3569703 baseEnd_3569703 := by
    simpa [prefixWord, tailWord_3569703, baseEnd_3569703] using wordTrace_append hprefix tailTrace_3569703
  have hstable : (prefixWord ++ tailWord_3569703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3569703).length < 2 ^ (prefixWord ++ tailWord_3569703).sum := by decide
  have hdescent : baseEnd_3569703 < baseStart_3569703 := by decide
  rcases family_descends (prefixWord ++ tailWord_3569703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3569753 : List Nat := [1, 2, 1, 2, 2, 1, 5, 3, 2, 2, 2]
def baseStart_3569753 : Nat := 118140960795 + 3569753 * 2 ^ 59
def prefixEnd_3569753 : Nat := 4983230072969 + 3 ^ 40 * 3569753 * 2
def baseEnd_3569753 : Nat := 1832999106829477058670511

theorem tailTrace_3569753 : CollatzResearch.WordTrace tailWord_3569753 prefixEnd_3569753 1832999106829477058670511 := by
  unfold tailWord_3569753
  simp only [CollatzResearch.WordTrace]
  refine ⟨130199588236402021119577913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86799725490934680746385275 130199588236402021119577913)
  ·
    refine ⟨97649691177301515839683435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130199588236402021119577913 97649691177301515839683435)
    ·
      refine ⟨146474536765952273759525153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97649691177301515839683435 146474536765952273759525153)
      ·
        refine ⟨109855902574464205319643865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146474536765952273759525153 109855902574464205319643865)
        ·
          refine ⟨82391926930848153989732899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109855902574464205319643865 82391926930848153989732899)
          ·
            refine ⟨123587890396272230984599349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82391926930848153989732899 123587890396272230984599349)
            ·
              refine ⟨11586364724650521654806189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 123587890396272230984599349 11586364724650521654806189)
              ·
                refine ⟨4344886771743945620552321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11586364724650521654806189 4344886771743945620552321)
                ·
                  refine ⟨3258665078807959215414241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4344886771743945620552321 3258665078807959215414241)
                  ·
                    refine ⟨2443998809105969411560681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3258665078807959215414241 2443998809105969411560681)
                    ·
                      refine ⟨1832999106829477058670511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2443998809105969411560681 1832999106829477058670511)
                      ·
                        rfl

theorem cell23_3569753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 5, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 5, 3, 2, 2, 2].length) (baseStart_3569753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3569753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3569753 prefixEnd_3569753 := by exact prefixLift 3569753
  have htrace : WordTrace (prefixWord ++ tailWord_3569753) baseStart_3569753 baseEnd_3569753 := by
    simpa [prefixWord, tailWord_3569753, baseEnd_3569753] using wordTrace_append hprefix tailTrace_3569753
  have hstable : (prefixWord ++ tailWord_3569753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3569753).length < 2 ^ (prefixWord ++ tailWord_3569753).sum := by decide
  have hdescent : baseEnd_3569753 < baseStart_3569753 := by decide
  rcases family_descends (prefixWord ++ tailWord_3569753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3569757 : List Nat := [1, 4, 4, 1, 1, 3, 1, 2, 1, 3, 2]
def baseStart_3569757 : Nat := 118140960795 + 3569757 * 2 ^ 59
def prefixEnd_3569757 : Nat := 4983230072969 + 3 ^ 40 * 3569757 * 2
def baseEnd_3569757 : Nat := 1833001160752095043020493

theorem tailTrace_3569757 : CollatzResearch.WordTrace tailWord_3569757 prefixEnd_3569757 1833001160752095043020493 := by
  unfold tailWord_3569757
  simp only [CollatzResearch.WordTrace]
  refine ⟨130199734128387529802723525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86799822752258353201815683 130199734128387529802723525)
  ·
    refine ⟨24412450149072661838010661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 130199734128387529802723525 24412450149072661838010661)
    ·
      refine ⟨4577334402951124094626999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24412450149072661838010661 4577334402951124094626999)
      ·
        refine ⟨6866001604426686141940499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4577334402951124094626999 6866001604426686141940499)
        ·
          refine ⟨10299002406640029212910749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6866001604426686141940499 10299002406640029212910749)
          ·
            refine ⟨3862125902490010954841531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10299002406640029212910749 3862125902490010954841531)
            ·
              refine ⟨5793188853735016432262297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3862125902490010954841531 5793188853735016432262297)
              ·
                refine ⟨4344891640301262324196723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5793188853735016432262297 4344891640301262324196723)
                ·
                  refine ⟨6517337460451893486295085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4344891640301262324196723 6517337460451893486295085)
                  ·
                    refine ⟨2444001547669460057360657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6517337460451893486295085 2444001547669460057360657)
                    ·
                      refine ⟨1833001160752095043020493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2444001547669460057360657 1833001160752095043020493)
                      ·
                        rfl

theorem cell23_3569757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 3, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 3, 1, 2, 1, 3, 2].length) (baseStart_3569757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3569757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3569757 prefixEnd_3569757 := by exact prefixLift 3569757
  have htrace : WordTrace (prefixWord ++ tailWord_3569757) baseStart_3569757 baseEnd_3569757 := by
    simpa [prefixWord, tailWord_3569757, baseEnd_3569757] using wordTrace_append hprefix tailTrace_3569757
  have hstable : (prefixWord ++ tailWord_3569757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3569757).length < 2 ^ (prefixWord ++ tailWord_3569757).sum := by decide
  have hdescent : baseEnd_3569757 < baseStart_3569757 := by decide
  rcases family_descends (prefixWord ++ tailWord_3569757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3569793 : List Nat := [1, 2, 4, 2, 3, 1, 1, 4, 5]
def baseStart_3569793 : Nat := 118140960795 + 3569793 * 2 ^ 59
def prefixEnd_3569793 : Nat := 4983230072969 + 3 ^ 40 * 3569793 * 2
def baseEnd_3569793 : Nat := 203668849561739655796703

theorem tailTrace_3569793 : CollatzResearch.WordTrace tailWord_3569793 prefixEnd_3569793 203668849561739655796703 := by
  unfold tailWord_3569793
  simp only [CollatzResearch.WordTrace]
  refine ⟨130201047156257107951034033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86800698104171405300689355 130201047156257107951034033)
  ·
    refine ⟨97650785367192830963275525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130201047156257107951034033 97650785367192830963275525)
    ·
      refine ⟨18309522256348655805614161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 97650785367192830963275525 18309522256348655805614161)
      ·
        refine ⟨13732141692261491854210621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18309522256348655805614161 13732141692261491854210621)
        ·
          refine ⟨5149553134598059445328983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13732141692261491854210621 5149553134598059445328983)
          ·
            refine ⟨7724329701897089167993475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5149553134598059445328983 7724329701897089167993475)
            ·
              refine ⟨11586494552845633751990213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7724329701897089167993475 11586494552845633751990213)
              ·
                refine ⟨2172467728658556328498165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11586494552845633751990213 2172467728658556328498165)
                ·
                  refine ⟨203668849561739655796703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2172467728658556328498165 203668849561739655796703)
                  ·
                    rfl

theorem cell23_3569793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 1, 4, 5].length) (baseStart_3569793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3569793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3569793 prefixEnd_3569793 := by exact prefixLift 3569793
  have htrace : WordTrace (prefixWord ++ tailWord_3569793) baseStart_3569793 baseEnd_3569793 := by
    simpa [prefixWord, tailWord_3569793, baseEnd_3569793] using wordTrace_append hprefix tailTrace_3569793
  have hstable : (prefixWord ++ tailWord_3569793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3569793).length < 2 ^ (prefixWord ++ tailWord_3569793).sum := by decide
  have hdescent : baseEnd_3569793 < baseStart_3569793 := by decide
  rcases family_descends (prefixWord ++ tailWord_3569793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3569796 : List Nat := [2, 3, 2, 1, 2, 1, 1, 1, 1, 7, 2]
def baseStart_3569796 : Nat := 118140960795 + 3569796 * 2 ^ 59
def prefixEnd_3569796 : Nat := 4983230072969 + 3 ^ 40 * 3569796 * 2
def baseEnd_3569796 : Nat := 1833021186497620390432813

theorem tailTrace_3569796 : CollatzResearch.WordTrace tailWord_3569796 prefixEnd_3569796 1833021186497620390432813 := by
  unfold tailWord_3569796
  simp only [CollatzResearch.WordTrace]
  refine ⟨65100578287623119731696621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86800771050164159642262161 65100578287623119731696621)
  ·
    refine ⟨24412716857858669899386233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65100578287623119731696621 24412716857858669899386233)
    ·
      refine ⟨18309537643394002424539675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24412716857858669899386233 18309537643394002424539675)
      ·
        refine ⟨27464306465091003636809513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18309537643394002424539675 27464306465091003636809513)
        ·
          refine ⟨20598229848818252727607135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27464306465091003636809513 20598229848818252727607135)
          ·
            refine ⟨30897344773227379091410703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20598229848818252727607135 30897344773227379091410703)
            ·
              refine ⟨46346017159841068637116055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30897344773227379091410703 46346017159841068637116055)
              ·
                refine ⟨69519025739761602955674083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46346017159841068637116055 69519025739761602955674083)
                ·
                  refine ⟨104278538609642404433511125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 69519025739761602955674083 104278538609642404433511125)
                  ·
                    refine ⟨2444028248663493853910417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 104278538609642404433511125 2444028248663493853910417)
                    ·
                      refine ⟨1833021186497620390432813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2444028248663493853910417 1833021186497620390432813)
                      ·
                        rfl

theorem cell23_3569796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 1, 1, 7, 2].length) (baseStart_3569796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3569796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3569796 prefixEnd_3569796 := by exact prefixLift 3569796
  have htrace : WordTrace (prefixWord ++ tailWord_3569796) baseStart_3569796 baseEnd_3569796 := by
    simpa [prefixWord, tailWord_3569796, baseEnd_3569796] using wordTrace_append hprefix tailTrace_3569796
  have hstable : (prefixWord ++ tailWord_3569796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3569796).length < 2 ^ (prefixWord ++ tailWord_3569796).sum := by decide
  have hdescent : baseEnd_3569796 < baseStart_3569796 := by decide
  rcases family_descends (prefixWord ++ tailWord_3569796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3569799 : List Nat := [1, 1, 4, 2, 1, 1, 4, 1, 1, 2, 5]
def baseStart_3569799 : Nat := 118140960795 + 3569799 * 2 ^ 59
def prefixEnd_3569799 : Nat := 4983230072969 + 3 ^ 40 * 3569799 * 2
def baseEnd_3569799 : Nat := 1833022726939583878695299

theorem tailTrace_3569799 : CollatzResearch.WordTrace tailWord_3569799 prefixEnd_3569799 1833022726939583878695299 := by
  unfold tailWord_3569799
  simp only [CollatzResearch.WordTrace]
  refine ⟨130201265994235370975752451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86800843996156913983834967 130201265994235370975752451)
  ·
    refine ⟨195301898991353056463628677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130201265994235370975752451 195301898991353056463628677)
    ·
      refine ⟨36619106060878698086930377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 195301898991353056463628677 36619106060878698086930377)
      ·
        refine ⟨27464329545659023565197783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36619106060878698086930377 27464329545659023565197783)
        ·
          refine ⟨41196494318488535347796675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27464329545659023565197783 41196494318488535347796675)
          ·
            refine ⟨61794741477732803021695013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41196494318488535347796675 61794741477732803021695013)
            ·
              refine ⟨11586514027074900566567815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 61794741477732803021695013 11586514027074900566567815)
              ·
                refine ⟨17379771040612350849851723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11586514027074900566567815 17379771040612350849851723)
                ·
                  refine ⟨26069656560918526274777585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17379771040612350849851723 26069656560918526274777585)
                  ·
                    refine ⟨19552242420688894706083189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26069656560918526274777585 19552242420688894706083189)
                    ·
                      refine ⟨1833022726939583878695299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19552242420688894706083189 1833022726939583878695299)
                      ·
                        rfl

theorem cell23_3569799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 4, 1, 1, 2, 5].length) (baseStart_3569799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3569799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3569799 prefixEnd_3569799 := by exact prefixLift 3569799
  have htrace : WordTrace (prefixWord ++ tailWord_3569799) baseStart_3569799 baseEnd_3569799 := by
    simpa [prefixWord, tailWord_3569799, baseEnd_3569799] using wordTrace_append hprefix tailTrace_3569799
  have hstable : (prefixWord ++ tailWord_3569799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3569799).length < 2 ^ (prefixWord ++ tailWord_3569799).sum := by decide
  have hdescent : baseEnd_3569799 < baseStart_3569799 := by decide
  rcases family_descends (prefixWord ++ tailWord_3569799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3569823 : List Nat := [1, 1, 2, 6, 1, 3, 1, 1, 2, 5]
def baseStart_3569823 : Nat := 118140960795 + 3569823 * 2 ^ 59
def prefixEnd_3569823 : Nat := 4983230072969 + 3 ^ 40 * 3569823 * 2
def baseEnd_3569823 : Nat := 611011683491763928265063

theorem tailTrace_3569823 : CollatzResearch.WordTrace tailWord_3569823 prefixEnd_3569823 611011683491763928265063 := by
  unfold tailWord_3569823
  simp only [CollatzResearch.WordTrace]
  refine ⟨130202141346148423074626123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86801427564098948716417415 130202141346148423074626123)
  ·
    refine ⟨195303212019222634611939185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130202141346148423074626123 195303212019222634611939185)
    ·
      refine ⟨146477409014416975958954389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 195303212019222634611939185 146477409014416975958954389)
      ·
        refine ⟨6866128547550795748075987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 146477409014416975958954389 6866128547550795748075987)
        ·
          refine ⟨10299192821326193622113981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6866128547550795748075987 10299192821326193622113981)
          ·
            refine ⟨3862197307997322608292743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10299192821326193622113981 3862197307997322608292743)
            ·
              refine ⟨5793295961995983912439115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3862197307997322608292743 5793295961995983912439115)
              ·
                refine ⟨8689943942993975868658673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5793295961995983912439115 8689943942993975868658673)
                ·
                  refine ⟨6517457957245481901494005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8689943942993975868658673 6517457957245481901494005)
                  ·
                    refine ⟨611011683491763928265063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6517457957245481901494005 611011683491763928265063)
                    ·
                      rfl

theorem cell23_3569823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 3, 1, 1, 2, 5].length) (baseStart_3569823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3569823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3569823 prefixEnd_3569823 := by exact prefixLift 3569823
  have htrace : WordTrace (prefixWord ++ tailWord_3569823) baseStart_3569823 baseEnd_3569823 := by
    simpa [prefixWord, tailWord_3569823, baseEnd_3569823] using wordTrace_append hprefix tailTrace_3569823
  have hstable : (prefixWord ++ tailWord_3569823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3569823).length < 2 ^ (prefixWord ++ tailWord_3569823).sum := by decide
  have hdescent : baseEnd_3569823 < baseStart_3569823 := by decide
  rcases family_descends (prefixWord ++ tailWord_3569823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3569849 : List Nat := [1, 2, 1, 4, 1, 2, 3, 1, 8]
def baseStart_3569849 : Nat := 118140960795 + 3569849 * 2 ^ 59
def prefixEnd_3569849 : Nat := 4983230072969 + 3 ^ 40 * 3569849 * 2
def baseEnd_3569849 : Nat := 203672044552478742563341

theorem tailTrace_3569849 : CollatzResearch.WordTrace tailWord_3569849 prefixEnd_3569849 203672044552478742563341 := by
  unfold tailWord_3569849
  simp only [CollatzResearch.WordTrace]
  refine ⟨130203089644054229515072601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86802059762702819676715067 130203089644054229515072601)
  ·
    refine ⟨97652317233040672136304451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130203089644054229515072601 97652317233040672136304451)
    ·
      refine ⟨146478475849561008204456677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97652317233040672136304451 146478475849561008204456677)
      ·
        refine ⟨27464714221792689038335627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 146478475849561008204456677 27464714221792689038335627)
        ·
          refine ⟨41197071332689033557503441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27464714221792689038335627 41197071332689033557503441)
          ·
            refine ⟨30897803499516775168127581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41197071332689033557503441 30897803499516775168127581)
            ·
              refine ⟨11586676312318790688047843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30897803499516775168127581 11586676312318790688047843)
              ·
                refine ⟨17380014468478186032071765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11586676312318790688047843 17380014468478186032071765)
                ·
                  refine ⟨203672044552478742563341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 17380014468478186032071765 203672044552478742563341)
                  ·
                    rfl

theorem cell23_3569849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 3, 1, 8].length) (baseStart_3569849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3569849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3569849 prefixEnd_3569849 := by exact prefixLift 3569849
  have htrace : WordTrace (prefixWord ++ tailWord_3569849) baseStart_3569849 baseEnd_3569849 := by
    simpa [prefixWord, tailWord_3569849, baseEnd_3569849] using wordTrace_append hprefix tailTrace_3569849
  have hstable : (prefixWord ++ tailWord_3569849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3569849).length < 2 ^ (prefixWord ++ tailWord_3569849).sum := by decide
  have hdescent : baseEnd_3569849 < baseStart_3569849 := by decide
  rcases family_descends (prefixWord ++ tailWord_3569849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3569903 : List Nat := [1, 1, 2, 1, 6, 1, 1, 1, 4, 3, 2]
def baseStart_3569903 : Nat := 118140960795 + 3569903 * 2 ^ 59
def prefixEnd_3569903 : Nat := 4983230072969 + 3 ^ 40 * 3569903 * 2
def baseEnd_3569903 : Nat := 1833076128927651471794821

theorem tailTrace_3569903 : CollatzResearch.WordTrace tailWord_3569903 prefixEnd_3569903 1833076128927651471794821 := by
  unfold tailWord_3569903
  simp only [CollatzResearch.WordTrace]
  refine ⟨130205059185858596737538363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86803372790572397825025575 130205059185858596737538363)
  ·
    refine ⟨195307588778787895106307545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130205059185858596737538363 195307588778787895106307545)
    ·
      refine ⟨146480691584090921329730659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 195307588778787895106307545 146480691584090921329730659)
      ·
        refine ⟨219721037376136381994595989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146480691584090921329730659 219721037376136381994595989)
        ·
          refine ⟨10299423627006392905996687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 219721037376136381994595989 10299423627006392905996687)
          ·
            refine ⟨15449135440509589358995031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10299423627006392905996687 15449135440509589358995031)
            ·
              refine ⟨23173703160764384038492547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15449135440509589358995031 23173703160764384038492547)
              ·
                refine ⟨34760554741146576057738821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23173703160764384038492547 34760554741146576057738821)
                ·
                  refine ⟨6517604013964983010826029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34760554741146576057738821 6517604013964983010826029)
                  ·
                    refine ⟨2444101505236868629059761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6517604013964983010826029 2444101505236868629059761)
                    ·
                      refine ⟨1833076128927651471794821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2444101505236868629059761 1833076128927651471794821)
                      ·
                        rfl

theorem cell23_3569903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 1, 1, 4, 3, 2].length) (baseStart_3569903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3569903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3569903 prefixEnd_3569903 := by exact prefixLift 3569903
  have htrace : WordTrace (prefixWord ++ tailWord_3569903) baseStart_3569903 baseEnd_3569903 := by
    simpa [prefixWord, tailWord_3569903, baseEnd_3569903] using wordTrace_append hprefix tailTrace_3569903
  have hstable : (prefixWord ++ tailWord_3569903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3569903).length < 2 ^ (prefixWord ++ tailWord_3569903).sum := by decide
  have hdescent : baseEnd_3569903 < baseStart_3569903 := by decide
  rcases family_descends (prefixWord ++ tailWord_3569903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3569910 : List Nat := [5, 1, 1, 1, 1, 1, 5, 1, 3, 1, 3]
def baseStart_3569910 : Nat := 118140960795 + 3569910 * 2 ^ 59
def prefixEnd_3569910 : Nat := 4983230072969 + 3 ^ 40 * 3569910 * 2
def baseEnd_3569910 : Nat := 1833079723292232944407289

theorem tailTrace_3569910 : CollatzResearch.WordTrace tailWord_3569910 prefixEnd_3569910 1833079723292232944407289 := by
  unfold tailWord_3569910
  simp only [CollatzResearch.WordTrace]
  refine ⟨8137832156052077308315199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 86803542997888824622028789 8137832156052077308315199)
  ·
    refine ⟨12206748234078115962472799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8137832156052077308315199 12206748234078115962472799)
    ·
      refine ⟨18310122351117173943709199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12206748234078115962472799 18310122351117173943709199)
      ·
        refine ⟨27465183526675760915563799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18310122351117173943709199 27465183526675760915563799)
        ·
          refine ⟨41197775290013641373345699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27465183526675760915563799 41197775290013641373345699)
          ·
            refine ⟨61796662935020462060018549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41197775290013641373345699 61796662935020462060018549)
            ·
              refine ⟨5793437150158168318126739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 61796662935020462060018549 5793437150158168318126739)
              ·
                refine ⟨8690155725237252477190109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5793437150158168318126739 8690155725237252477190109)
                ·
                  refine ⟨3258808396963969678946291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8690155725237252477190109 3258808396963969678946291)
                  ·
                    refine ⟨4888212595445954518419437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3258808396963969678946291 4888212595445954518419437)
                    ·
                      refine ⟨1833079723292232944407289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4888212595445954518419437 1833079723292232944407289)
                      ·
                        rfl

theorem cell23_3569910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 5, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 5, 1, 3, 1, 3].length) (baseStart_3569910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3569910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3569910 prefixEnd_3569910 := by exact prefixLift 3569910
  have htrace : WordTrace (prefixWord ++ tailWord_3569910) baseStart_3569910 baseEnd_3569910 := by
    simpa [prefixWord, tailWord_3569910, baseEnd_3569910] using wordTrace_append hprefix tailTrace_3569910
  have hstable : (prefixWord ++ tailWord_3569910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3569910).length < 2 ^ (prefixWord ++ tailWord_3569910).sum := by decide
  have hdescent : baseEnd_3569910 < baseStart_3569910 := by decide
  rcases family_descends (prefixWord ++ tailWord_3569910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3569953 : List Nat := [1, 2, 3, 2, 1, 1, 2, 5, 1, 2, 3]
def baseStart_3569953 : Nat := 118140960795 + 3569953 * 2 ^ 59
def prefixEnd_3569953 : Nat := 4983230072969 + 3 ^ 40 * 3569953 * 2
def baseEnd_3569953 : Nat := 1833101802960376276169591

theorem tailTrace_3569953 : CollatzResearch.WordTrace tailWord_3569953 prefixEnd_3569953 1833101802960376276169591 := by
  unfold tailWord_3569953
  simp only [CollatzResearch.WordTrace]
  refine ⟨130206882835677455276858513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86804588557118303517905675 130206882835677455276858513)
  ·
    refine ⟨97655162126758091457643885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130206882835677455276858513 97655162126758091457643885)
    ·
      refine ⟨36620685797534284296616457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 97655162126758091457643885 36620685797534284296616457)
      ·
        refine ⟨27465514348150713222462343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36620685797534284296616457 27465514348150713222462343)
        ·
          refine ⟨41198271522226069833693515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27465514348150713222462343 41198271522226069833693515)
          ·
            refine ⟨61797407283339104750540273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41198271522226069833693515 61797407283339104750540273)
            ·
              refine ⟨46348055462504328562905205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61797407283339104750540273 46348055462504328562905205)
              ·
                refine ⟨4345130199609780802772363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 46348055462504328562905205 4345130199609780802772363)
                ·
                  refine ⟨6517695299414671204158545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4345130199609780802772363 6517695299414671204158545)
                  ·
                    refine ⟨4888271474561003403118909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6517695299414671204158545 4888271474561003403118909)
                    ·
                      refine ⟨1833101802960376276169591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4888271474561003403118909 1833101802960376276169591)
                      ·
                        rfl

theorem cell23_3569953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 5, 1, 2, 3].length) (baseStart_3569953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3569953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3569953 prefixEnd_3569953 := by exact prefixLift 3569953
  have htrace : WordTrace (prefixWord ++ tailWord_3569953) baseStart_3569953 baseEnd_3569953 := by
    simpa [prefixWord, tailWord_3569953, baseEnd_3569953] using wordTrace_append hprefix tailTrace_3569953
  have hstable : (prefixWord ++ tailWord_3569953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3569953).length < 2 ^ (prefixWord ++ tailWord_3569953).sum := by decide
  have hdescent : baseEnd_3569953 < baseStart_3569953 := by decide
  rcases family_descends (prefixWord ++ tailWord_3569953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3569983 : List Nat := [1, 1, 2, 2, 4, 1, 4, 1, 1, 3, 3]
def baseStart_3569983 : Nat := 118140960795 + 3569983 * 2 ^ 59
def prefixEnd_3569983 : Nat := 4983230072969 + 3 ^ 40 * 3569983 * 2
def baseEnd_3569983 : Nat := 1833117207380011158794453

theorem tailTrace_3569983 : CollatzResearch.WordTrace tailWord_3569983 prefixEnd_3569983 1833117207380011158794453 := by
  unfold tailWord_3569983
  simp only [CollatzResearch.WordTrace]
  refine ⟨130207977025568770400450603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86805318017045846933633735 130207977025568770400450603)
  ·
    refine ⟨195311965538353155600675905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130207977025568770400450603 195311965538353155600675905)
    ·
      refine ⟨146483974153764866700506929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 195311965538353155600675905 146483974153764866700506929)
      ·
        refine ⟨109862980615323650025380197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146483974153764866700506929 109862980615323650025380197)
        ·
          refine ⟨20599308865373184379758787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 109862980615323650025380197 20599308865373184379758787)
          ·
            refine ⟨30898963298059776569638181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20599308865373184379758787 30898963298059776569638181)
            ·
              refine ⟨5793555618386208106807159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30898963298059776569638181 5793555618386208106807159)
              ·
                refine ⟨8690333427579312160210739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5793555618386208106807159 8690333427579312160210739)
                ·
                  refine ⟨13035500141368968240316109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8690333427579312160210739 13035500141368968240316109)
                  ·
                    refine ⟨4888312553013363090118541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13035500141368968240316109 4888312553013363090118541)
                    ·
                      refine ⟨1833117207380011158794453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4888312553013363090118541 1833117207380011158794453)
                      ·
                        rfl

theorem cell23_3569983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 4, 1, 1, 3, 3].length) (baseStart_3569983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3569983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3569983 prefixEnd_3569983 := by exact prefixLift 3569983
  have htrace : WordTrace (prefixWord ++ tailWord_3569983) baseStart_3569983 baseEnd_3569983 := by
    simpa [prefixWord, tailWord_3569983, baseEnd_3569983] using wordTrace_append hprefix tailTrace_3569983
  have hstable : (prefixWord ++ tailWord_3569983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3569983).length < 2 ^ (prefixWord ++ tailWord_3569983).sum := by decide
  have hdescent : baseEnd_3569983 < baseStart_3569983 := by decide
  rcases family_descends (prefixWord ++ tailWord_3569983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3569996 : List Nat := [2, 2, 1, 3, 2, 1, 2, 1, 2, 2, 5]
def baseStart_3569996 : Nat := 118140960795 + 3569996 * 2 ^ 59
def prefixEnd_3569996 : Nat := 4983230072969 + 3 ^ 40 * 3569996 * 2
def baseEnd_3569996 : Nat := 1833123882628519607931893

theorem tailTrace_3569996 : CollatzResearch.WordTrace tailWord_3569996 prefixEnd_3569996 1833123882628519607931893 := by
  unfold tailWord_3569996
  simp only [CollatzResearch.WordTrace]
  refine ⟨65104225587260836810336921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86805634116347782413782561 65104225587260836810336921)
  ·
    refine ⟨48828169190445627607752691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65104225587260836810336921 48828169190445627607752691)
    ·
      refine ⟨73242253785668441411629037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48828169190445627607752691 73242253785668441411629037)
      ·
        refine ⟨27465845169625665529360889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73242253785668441411629037 27465845169625665529360889)
        ·
          refine ⟨20599383877219249147020667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27465845169625665529360889 20599383877219249147020667)
          ·
            refine ⟨30899075815828873720531001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20599383877219249147020667 30899075815828873720531001)
            ·
              refine ⟨23174306861871655290398251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30899075815828873720531001 23174306861871655290398251)
              ·
                refine ⟨34761460292807482935597377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23174306861871655290398251 34761460292807482935597377)
                ·
                  refine ⟨26071095219605612201698033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34761460292807482935597377 26071095219605612201698033)
                  ·
                    refine ⟨19553321414704209151273525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26071095219605612201698033 19553321414704209151273525)
                    ·
                      refine ⟨1833123882628519607931893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19553321414704209151273525 1833123882628519607931893)
                      ·
                        rfl

theorem cell23_3569996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 2, 1, 2, 2, 5].length) (baseStart_3569996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3569996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3569996 prefixEnd_3569996 := by exact prefixLift 3569996
  have htrace : WordTrace (prefixWord ++ tailWord_3569996) baseStart_3569996 baseEnd_3569996 := by
    simpa [prefixWord, tailWord_3569996, baseEnd_3569996] using wordTrace_append hprefix tailTrace_3569996
  have hstable : (prefixWord ++ tailWord_3569996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3569996).length < 2 ^ (prefixWord ++ tailWord_3569996).sum := by decide
  have hdescent : baseEnd_3569996 < baseStart_3569996 := by decide
  rcases family_descends (prefixWord ++ tailWord_3569996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3570106 : List Nat := [3, 1, 1, 1, 2, 1, 1, 3, 2, 8]
def baseStart_3570106 : Nat := 118140960795 + 3570106 * 2 ^ 59
def prefixEnd_3570106 : Nat := 4983230072969 + 3 ^ 40 * 3570106 * 2
def baseEnd_3570106 : Nat := 611060121833504725852129

theorem tailTrace_3570106 : CollatzResearch.WordTrace tailWord_3570106 prefixEnd_3570106 611060121833504725852129 := by
  unfold tailWord_3570106
  simp only [CollatzResearch.WordTrace]
  refine ⟨32553115801030790601794543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86808308802748774938118781 32553115801030790601794543)
  ·
    refine ⟨48829673701546185902691815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32553115801030790601794543 48829673701546185902691815)
    ·
      refine ⟨73244510552319278854037723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48829673701546185902691815 73244510552319278854037723)
      ·
        refine ⟨109866765828478918281056585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73244510552319278854037723 109866765828478918281056585)
        ·
          refine ⟨82400074371359188710792439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109866765828478918281056585 82400074371359188710792439)
          ·
            refine ⟨123600111557038783066188659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82400074371359188710792439 123600111557038783066188659)
            ·
              refine ⟨185400167335558174599282989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 123600111557038783066188659 185400167335558174599282989)
              ·
                refine ⟨69525062750834315474731121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 185400167335558174599282989 69525062750834315474731121)
                ·
                  refine ⟨52143797063125736606048341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 69525062750834315474731121 52143797063125736606048341)
                  ·
                    refine ⟨611060121833504725852129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 52143797063125736606048341 611060121833504725852129)
                    ·
                      rfl

theorem cell23_3570106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 3, 2, 8].length) (baseStart_3570106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3570106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3570106 prefixEnd_3570106 := by exact prefixLift 3570106
  have htrace : WordTrace (prefixWord ++ tailWord_3570106) baseStart_3570106 baseEnd_3570106 := by
    simpa [prefixWord, tailWord_3570106, baseEnd_3570106] using wordTrace_append hprefix tailTrace_3570106
  have hstable : (prefixWord ++ tailWord_3570106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3570106).length < 2 ^ (prefixWord ++ tailWord_3570106).sum := by decide
  have hdescent : baseEnd_3570106 < baseStart_3570106 := by decide
  rcases family_descends (prefixWord ++ tailWord_3570106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3570147 : List Nat := [1, 1, 1, 6, 3, 1, 1, 1, 2, 4, 2]
def baseStart_3570147 : Nat := 118140960795 + 3570147 * 2 ^ 59
def prefixEnd_3570147 : Nat := 4983230072969 + 3 ^ 40 * 3570147 * 2
def baseEnd_3570147 : Nat := 1833201418207348517143699

theorem tailTrace_3570147 : CollatzResearch.WordTrace tailWord_3570147 prefixEnd_3570147 1833201418207348517143699 := by
  unfold tailWord_3570147
  simp only [CollatzResearch.WordTrace]
  refine ⟨130213958596974626409420695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86809305731316417606280463 130213958596974626409420695)
  ·
    refine ⟨195320937895461939614131043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130213958596974626409420695 195320937895461939614131043)
    ·
      refine ⟨292981406843192909421196565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195320937895461939614131043 292981406843192909421196565)
      ·
        refine ⟨13733503445774667629118589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 292981406843192909421196565 13733503445774667629118589)
        ·
          refine ⟨5150063792165500360919471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13733503445774667629118589 5150063792165500360919471)
          ·
            refine ⟨7725095688248250541379207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5150063792165500360919471 7725095688248250541379207)
            ·
              refine ⟨11587643532372375812068811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7725095688248250541379207 11587643532372375812068811)
              ·
                refine ⟨17381465298558563718103217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11587643532372375812068811 17381465298558563718103217)
                ·
                  refine ⟨13036098973918922788577413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17381465298558563718103217 13036098973918922788577413)
                  ·
                    refine ⟨2444268557609798022858265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13036098973918922788577413 2444268557609798022858265)
                    ·
                      refine ⟨1833201418207348517143699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2444268557609798022858265 1833201418207348517143699)
                      ·
                        rfl

theorem cell23_3570147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 1, 1, 2, 4, 2].length) (baseStart_3570147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3570147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3570147 prefixEnd_3570147 := by exact prefixLift 3570147
  have htrace : WordTrace (prefixWord ++ tailWord_3570147) baseStart_3570147 baseEnd_3570147 := by
    simpa [prefixWord, tailWord_3570147, baseEnd_3570147] using wordTrace_append hprefix tailTrace_3570147
  have hstable : (prefixWord ++ tailWord_3570147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3570147).length < 2 ^ (prefixWord ++ tailWord_3570147).sum := by decide
  have hdescent : baseEnd_3570147 < baseStart_3570147 := by decide
  rcases family_descends (prefixWord ++ tailWord_3570147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3570157 : List Nat := [1, 5, 1, 3, 1, 2, 1, 2, 3, 4]
def baseStart_3570157 : Nat := 118140960795 + 3570157 * 2 ^ 59
def prefixEnd_3570157 : Nat := 4983230072969 + 3 ^ 40 * 3570157 * 2
def baseEnd_3570157 : Nat := 611068851004631159339551

theorem tailTrace_3570157 : CollatzResearch.WordTrace tailWord_3570157 prefixEnd_3570157 611068851004631159339551 := by
  unfold tailWord_3570157
  simp only [CollatzResearch.WordTrace]
  refine ⟨130214323326938398117284725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86809548884625598744856483 130214323326938398117284725)
  ·
    refine ⟨12207592811900474823495443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 130214323326938398117284725 12207592811900474823495443)
    ·
      refine ⟨18311389217850712235243165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12207592811900474823495443 18311389217850712235243165)
      ·
        refine ⟨6866770956694017088216187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18311389217850712235243165 6866770956694017088216187)
        ·
          refine ⟨10300156435041025632324281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6866770956694017088216187 10300156435041025632324281)
          ·
            refine ⟨7725117326280769224243211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10300156435041025632324281 7725117326280769224243211)
            ·
              refine ⟨11587675989421153836364817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7725117326280769224243211 11587675989421153836364817)
              ·
                refine ⟨8690756992065865377273613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11587675989421153836364817 8690756992065865377273613)
                ·
                  refine ⟨3259033872024699516477605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8690756992065865377273613 3259033872024699516477605)
                  ·
                    refine ⟨611068851004631159339551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3259033872024699516477605 611068851004631159339551)
                    ·
                      rfl

theorem cell23_3570157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 1, 2, 3, 4].length) (baseStart_3570157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3570157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3570157 prefixEnd_3570157 := by exact prefixLift 3570157
  have htrace : WordTrace (prefixWord ++ tailWord_3570157) baseStart_3570157 baseEnd_3570157 := by
    simpa [prefixWord, tailWord_3570157, baseEnd_3570157] using wordTrace_append hprefix tailTrace_3570157
  have hstable : (prefixWord ++ tailWord_3570157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3570157).length < 2 ^ (prefixWord ++ tailWord_3570157).sum := by decide
  have hdescent : baseEnd_3570157 < baseStart_3570157 := by decide
  rcases family_descends (prefixWord ++ tailWord_3570157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3570197 : List Nat := [1, 3, 2, 1, 3, 1, 4, 1, 3, 1, 3]
def baseStart_3570197 : Nat := 118140960795 + 3570197 * 2 ^ 59
def prefixEnd_3570197 : Nat := 4983230072969 + 3 ^ 40 * 3570197 * 2
def baseEnd_3570197 : Nat := 1833227092240073321518469

theorem tailTrace_3570197 : CollatzResearch.WordTrace tailWord_3570197 prefixEnd_3570197 1833227092240073321518469 := by
  unfold tailWord_3570197
  simp only [CollatzResearch.WordTrace]
  refine ⟨130215782246793484948740845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86810521497862323299160563 130215782246793484948740845)
  ·
    refine ⟨48830918342547556855777817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130215782246793484948740845 48830918342547556855777817)
    ·
      refine ⟨36623188756910667641833363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48830918342547556855777817 36623188756910667641833363)
      ·
        refine ⟨54934783135366001462750045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36623188756910667641833363 54934783135366001462750045)
        ·
          refine ⟨20600543675762250548531267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54934783135366001462750045 20600543675762250548531267)
          ·
            refine ⟨30900815513643375822796901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20600543675762250548531267 30900815513643375822796901)
            ·
              refine ⟨5793902908808132966774419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30900815513643375822796901 5793902908808132966774419)
              ·
                refine ⟨8690854363212199450161629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5793902908808132966774419 8690854363212199450161629)
                ·
                  refine ⟨3259070386204574793810611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8690854363212199450161629 3259070386204574793810611)
                  ·
                    refine ⟨4888605579306862190715917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3259070386204574793810611 4888605579306862190715917)
                    ·
                      refine ⟨1833227092240073321518469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4888605579306862190715917 1833227092240073321518469)
                      ·
                        rfl

theorem cell23_3570197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 4, 1, 3, 1, 3].length) (baseStart_3570197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3570197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3570197 prefixEnd_3570197 := by exact prefixLift 3570197
  have htrace : WordTrace (prefixWord ++ tailWord_3570197) baseStart_3570197 baseEnd_3570197 := by
    simpa [prefixWord, tailWord_3570197, baseEnd_3570197] using wordTrace_append hprefix tailTrace_3570197
  have hstable : (prefixWord ++ tailWord_3570197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3570197).length < 2 ^ (prefixWord ++ tailWord_3570197).sum := by decide
  have hdescent : baseEnd_3570197 < baseStart_3570197 := by decide
  rcases family_descends (prefixWord ++ tailWord_3570197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3570223 : List Nat := [1, 1, 2, 1, 2, 1, 1, 1, 4, 6, 3]
def baseStart_3570223 : Nat := 118140960795 + 3570223 * 2 ^ 59
def prefixEnd_3570223 : Nat := 4983230072969 + 3 ^ 40 * 3570223 * 2
def baseEnd_3570223 : Nat := 1833240442737090219793349

theorem tailTrace_3570223 : CollatzResearch.WordTrace tailWord_3570223 prefixEnd_3570223 1833240442737090219793349 := by
  unfold tailWord_3570223
  simp only [CollatzResearch.WordTrace]
  refine ⟨130216730544699291389187323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86811153696466194259458215 130216730544699291389187323)
  ·
    refine ⟨195325095817048937083780985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130216730544699291389187323 195325095817048937083780985)
    ·
      refine ⟨146493821862786702812835739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 195325095817048937083780985 146493821862786702812835739)
      ·
        refine ⟨219740732794180054219253609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146493821862786702812835739 219740732794180054219253609)
        ·
          refine ⟨164805549595635040664440207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 219740732794180054219253609 164805549595635040664440207)
          ·
            refine ⟨247208324393452560996660311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 164805549595635040664440207 247208324393452560996660311)
            ·
              refine ⟨370812486590178841494990467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 247208324393452560996660311 370812486590178841494990467)
              ·
                refine ⟨556218729885268262242485701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 370812486590178841494990467 556218729885268262242485701)
                ·
                  refine ⟨104291011853487799170466069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 556218729885268262242485701 104291011853487799170466069)
                  ·
                    refine ⟨4888641180632240586115597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 104291011853487799170466069 4888641180632240586115597)
                    ·
                      refine ⟨1833240442737090219793349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4888641180632240586115597 1833240442737090219793349)
                      ·
                        rfl

theorem cell23_3570223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 1, 4, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 1, 4, 6, 3].length) (baseStart_3570223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3570223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3570223 prefixEnd_3570223 := by exact prefixLift 3570223
  have htrace : WordTrace (prefixWord ++ tailWord_3570223) baseStart_3570223 baseEnd_3570223 := by
    simpa [prefixWord, tailWord_3570223, baseEnd_3570223] using wordTrace_append hprefix tailTrace_3570223
  have hstable : (prefixWord ++ tailWord_3570223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3570223).length < 2 ^ (prefixWord ++ tailWord_3570223).sum := by decide
  have hdescent : baseEnd_3570223 < baseStart_3570223 := by decide
  rcases family_descends (prefixWord ++ tailWord_3570223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3570237 : List Nat := [1, 4, 1, 3, 2, 1, 2, 3, 1, 1, 4]
def baseStart_3570237 : Nat := 118140960795 + 3570237 * 2 ^ 59
def prefixEnd_3570237 : Nat := 4983230072969 + 3 ^ 40 * 3570237 * 2
def baseEnd_3570237 : Nat := 1833247631466253165018285

theorem tailTrace_3570237 : CollatzResearch.WordTrace tailWord_3570237 prefixEnd_3570237 1833247631466253165018285 := by
  unfold tailWord_3570237
  simp only [CollatzResearch.WordTrace]
  refine ⟨130217241166648571780196965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86811494111099047853464643 130217241166648571780196965)
  ·
    refine ⟨24415732718746607208786931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 130217241166648571780196965 24415732718746607208786931)
    ·
      refine ⟨36623599078119910813180397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24415732718746607208786931 36623599078119910813180397)
      ·
        refine ⟨13733849654294966554942649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36623599078119910813180397 13733849654294966554942649)
        ·
          refine ⟨10300387240721224916206987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13733849654294966554942649 10300387240721224916206987)
          ·
            refine ⟨15450580861081837374310481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10300387240721224916206987 15450580861081837374310481)
            ·
              refine ⟨11587935645811378030732861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15450580861081837374310481 11587935645811378030732861)
              ·
                refine ⟨4345475867179266761524823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11587935645811378030732861 4345475867179266761524823)
                ·
                  refine ⟨6518213800768900142287235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4345475867179266761524823 6518213800768900142287235)
                  ·
                    refine ⟨9777320701153350213430853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6518213800768900142287235 9777320701153350213430853)
                    ·
                      refine ⟨1833247631466253165018285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9777320701153350213430853 1833247631466253165018285)
                      ·
                        rfl

theorem cell23_3570237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 2, 3, 1, 1, 4].length) (baseStart_3570237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3570237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3570237 prefixEnd_3570237 := by exact prefixLift 3570237
  have htrace : WordTrace (prefixWord ++ tailWord_3570237) baseStart_3570237 baseEnd_3570237 := by
    simpa [prefixWord, tailWord_3570237, baseEnd_3570237] using wordTrace_append hprefix tailTrace_3570237
  have hstable : (prefixWord ++ tailWord_3570237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3570237).length < 2 ^ (prefixWord ++ tailWord_3570237).sum := by decide
  have hdescent : baseEnd_3570237 < baseStart_3570237 := by decide
  rcases family_descends (prefixWord ++ tailWord_3570237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3570254 : List Nat := [4, 1, 1, 1, 1, 2, 5, 1, 3, 2, 2]
def baseStart_3570254 : Nat := 118140960795 + 3570254 * 2 ^ 59
def prefixEnd_3570254 : Nat := 4983230072969 + 3 ^ 40 * 3570254 * 2
def baseEnd_3570254 : Nat := 1833256360637379598505707

theorem tailTrace_3570254 : CollatzResearch.WordTrace tailWord_3570254 prefixEnd_3570254 1833256360637379598505707 := by
  unfold tailWord_3570254
  simp only [CollatzResearch.WordTrace]
  refine ⟨16277232650948372960445727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 86811907471724655789043877 16277232650948372960445727)
  ·
    refine ⟨24415848976422559440668591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16277232650948372960445727 24415848976422559440668591)
    ·
      refine ⟨36623773464633839161002887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24415848976422559440668591 36623773464633839161002887)
      ·
        refine ⟨54935660196950758741504331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36623773464633839161002887 54935660196950758741504331)
        ·
          refine ⟨82403490295426138112256497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54935660196950758741504331 82403490295426138112256497)
          ·
            refine ⟨61802617721569603584192373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82403490295426138112256497 61802617721569603584192373)
            ·
              refine ⟨5793995411397150336018035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 61802617721569603584192373 5793995411397150336018035)
              ·
                refine ⟨8690993117095725504027053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5793995411397150336018035 8690993117095725504027053)
                ·
                  refine ⟨3259122418910897064010145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8690993117095725504027053 3259122418910897064010145)
                  ·
                    refine ⟨2444341814183172798007609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3259122418910897064010145 2444341814183172798007609)
                    ·
                      refine ⟨1833256360637379598505707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2444341814183172798007609 1833256360637379598505707)
                      ·
                        rfl

theorem cell23_3570254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 5, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 5, 1, 3, 2, 2].length) (baseStart_3570254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3570254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3570254 prefixEnd_3570254 := by exact prefixLift 3570254
  have htrace : WordTrace (prefixWord ++ tailWord_3570254) baseStart_3570254 baseEnd_3570254 := by
    simpa [prefixWord, tailWord_3570254, baseEnd_3570254] using wordTrace_append hprefix tailTrace_3570254
  have hstable : (prefixWord ++ tailWord_3570254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3570254).length < 2 ^ (prefixWord ++ tailWord_3570254).sum := by decide
  have hdescent : baseEnd_3570254 < baseStart_3570254 := by decide
  rcases family_descends (prefixWord ++ tailWord_3570254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3570260 : List Nat := [2, 4, 1, 1, 1, 4, 2, 8]
def baseStart_3570260 : Nat := 118140960795 + 3570260 * 2 ^ 59
def prefixEnd_3570260 : Nat := 4983230072969 + 3 ^ 40 * 3570260 * 2
def baseEnd_3570260 : Nat := 67898497834122465741877

theorem tailTrace_3570260 : CollatzResearch.WordTrace tailWord_3570260 prefixEnd_3570260 67898497834122465741877 := by
  unfold tailWord_3570260
  simp only [CollatzResearch.WordTrace]
  refine ⟨65109040022782623354142117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86812053363710164472189489 65109040022782623354142117)
  ·
    refine ⟨12207945004271741878901647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 65109040022782623354142117 12207945004271741878901647)
    ·
      refine ⟨18311917506407612818352471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12207945004271741878901647 18311917506407612818352471)
      ·
        refine ⟨27467876259611419227528707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18311917506407612818352471 27467876259611419227528707)
        ·
          refine ⟨41201814389417128841293061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27467876259611419227528707 41201814389417128841293061)
          ·
            refine ⟨7725340198015711657742449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41201814389417128841293061 7725340198015711657742449)
            ·
              refine ⟨5794005148511783743306837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7725340198015711657742449 5794005148511783743306837)
              ·
                refine ⟨67898497834122465741877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5794005148511783743306837 67898497834122465741877)
                ·
                  rfl

theorem cell23_3570260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 2, 8].length) (baseStart_3570260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3570260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3570260 prefixEnd_3570260 := by exact prefixLift 3570260
  have htrace : WordTrace (prefixWord ++ tailWord_3570260) baseStart_3570260 baseEnd_3570260 := by
    simpa [prefixWord, tailWord_3570260, baseEnd_3570260] using wordTrace_append hprefix tailTrace_3570260
  have hstable : (prefixWord ++ tailWord_3570260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3570260).length < 2 ^ (prefixWord ++ tailWord_3570260).sum := by decide
  have hdescent : baseEnd_3570260 < baseStart_3570260 := by decide
  rcases family_descends (prefixWord ++ tailWord_3570260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3570263 : List Nat := [1, 1, 3, 2, 2, 2, 1, 1, 2, 2, 6]
def baseStart_3570263 : Nat := 118140960795 + 3570263 * 2 ^ 59
def prefixEnd_3570263 : Nat := 4983230072969 + 3 ^ 40 * 3570263 * 2
def baseEnd_3570263 : Nat := 1833260981963270063293165

theorem tailTrace_3570263 : CollatzResearch.WordTrace tailWord_3570263 prefixEnd_3570263 1833260981963270063293165 := by
  unfold tailWord_3570263
  simp only [CollatzResearch.WordTrace]
  refine ⟨130218189464554378220643443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86812126309702918813762295 130218189464554378220643443)
  ·
    refine ⟨195327284196831567330965165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130218189464554378220643443 195327284196831567330965165)
    ·
      refine ⟨73247731573811837749111937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 195327284196831567330965165 73247731573811837749111937)
      ·
        refine ⟨54935798680358878311833953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73247731573811837749111937 54935798680358878311833953)
        ·
          refine ⟨41201849010269158733875465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54935798680358878311833953 41201849010269158733875465)
          ·
            refine ⟨30901386757701869050406599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41201849010269158733875465 30901386757701869050406599)
            ·
              refine ⟨46352080136552803575609899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30901386757701869050406599 46352080136552803575609899)
              ·
                refine ⟨69528120204829205363414849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46352080136552803575609899 69528120204829205363414849)
                ·
                  refine ⟨52146090153621904022561137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 69528120204829205363414849 52146090153621904022561137)
                  ·
                    refine ⟨39109567615216428016920853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 52146090153621904022561137 39109567615216428016920853)
                    ·
                      refine ⟨1833260981963270063293165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 39109567615216428016920853 1833260981963270063293165)
                      ·
                        rfl

theorem cell23_3570263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 1, 2, 2, 6].length) (baseStart_3570263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3570263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3570263 prefixEnd_3570263 := by exact prefixLift 3570263
  have htrace : WordTrace (prefixWord ++ tailWord_3570263) baseStart_3570263 baseEnd_3570263 := by
    simpa [prefixWord, tailWord_3570263, baseEnd_3570263] using wordTrace_append hprefix tailTrace_3570263
  have hstable : (prefixWord ++ tailWord_3570263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3570263).length < 2 ^ (prefixWord ++ tailWord_3570263).sum := by decide
  have hdescent : baseEnd_3570263 < baseStart_3570263 := by decide
  rcases family_descends (prefixWord ++ tailWord_3570263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3570283 : List Nat := [1, 1, 1, 1, 2, 2, 1, 5, 2, 2, 5]
def baseStart_3570283 : Nat := 118140960795 + 3570283 * 2 ^ 59
def prefixEnd_3570283 : Nat := 4983230072969 + 3 ^ 40 * 3570283 * 2
def baseEnd_3570283 : Nat := 1833271251576359985043073

theorem tailTrace_3570283 : CollatzResearch.WordTrace tailWord_3570283 prefixEnd_3570283 1833271251576359985043073 := by
  unfold tailWord_3570283
  simp only [CollatzResearch.WordTrace]
  refine ⟨130218918924481921636371503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86812612616321281090914335 130218918924481921636371503)
  ·
    refine ⟨195328378386722882454557255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130218918924481921636371503 195328378386722882454557255)
    ·
      refine ⟨292992567580084323681835883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195328378386722882454557255 292992567580084323681835883)
      ·
        refine ⟨439488851370126485522753825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 292992567580084323681835883 439488851370126485522753825)
        ·
          refine ⟨329616638527594864142065369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 439488851370126485522753825 329616638527594864142065369)
          ·
            refine ⟨247212478895696148106549027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 329616638527594864142065369 247212478895696148106549027)
            ·
              refine ⟨370818718343544222159823541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 247212478895696148106549027 370818718343544222159823541)
              ·
                refine ⟨34764254844707270827483457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 370818718343544222159823541 34764254844707270827483457)
                ·
                  refine ⟨26073191133530453120612593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34764254844707270827483457 26073191133530453120612593)
                  ·
                    refine ⟨19554893350147839840459445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26073191133530453120612593 19554893350147839840459445)
                    ·
                      refine ⟨1833271251576359985043073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19554893350147839840459445 1833271251576359985043073)
                      ·
                        rfl

theorem cell23_3570283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 5, 2, 2, 5].length) (baseStart_3570283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3570283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3570283 prefixEnd_3570283 := by exact prefixLift 3570283
  have htrace : WordTrace (prefixWord ++ tailWord_3570283) baseStart_3570283 baseEnd_3570283 := by
    simpa [prefixWord, tailWord_3570283, baseEnd_3570283] using wordTrace_append hprefix tailTrace_3570283
  have hstable : (prefixWord ++ tailWord_3570283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3570283).length < 2 ^ (prefixWord ++ tailWord_3570283).sum := by decide
  have hdescent : baseEnd_3570283 < baseStart_3570283 := by decide
  rcases family_descends (prefixWord ++ tailWord_3570283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3570304 : List Nat := [2, 1, 1, 2, 1, 6, 2, 2, 2, 1, 3]
def baseStart_3570304 : Nat := 118140960795 + 3570304 * 2 ^ 59
def prefixEnd_3570304 : Nat := 4983230072969 + 3 ^ 40 * 3570304 * 2
def baseEnd_3570304 : Nat := 1833282034670104402880477

theorem tailTrace_3570304 : CollatzResearch.WordTrace tailWord_3570304 prefixEnd_3570304 1833282034670104402880477 := by
  unfold tailWord_3570304
  simp only [CollatzResearch.WordTrace]
  refine ⟨65109842428702921111442983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86813123238270561481923977 65109842428702921111442983)
  ·
    refine ⟨97664763643054381667164475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65109842428702921111442983 97664763643054381667164475)
    ·
      refine ⟨146497145464581572500746713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97664763643054381667164475 146497145464581572500746713)
      ·
        refine ⟨109872859098436179375560035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146497145464581572500746713 109872859098436179375560035)
        ·
          refine ⟨164809288647654269063340053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109872859098436179375560035 164809288647654269063340053)
          ·
            refine ⟨7725435405358793862344065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 164809288647654269063340053 7725435405358793862344065)
            ·
              refine ⟨5794076554019095396758049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7725435405358793862344065 5794076554019095396758049)
              ·
                refine ⟨4345557415514321547568537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5794076554019095396758049 4345557415514321547568537)
                ·
                  refine ⟨3259168061635741160676403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4345557415514321547568537 3259168061635741160676403)
                  ·
                    refine ⟨4888752092453611741014605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3259168061635741160676403 4888752092453611741014605)
                    ·
                      refine ⟨1833282034670104402880477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4888752092453611741014605 1833282034670104402880477)
                      ·
                        rfl

theorem cell23_3570304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 2, 2, 2, 1, 3].length) (baseStart_3570304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3570304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3570304 prefixEnd_3570304 := by exact prefixLift 3570304
  have htrace : WordTrace (prefixWord ++ tailWord_3570304) baseStart_3570304 baseEnd_3570304 := by
    simpa [prefixWord, tailWord_3570304, baseEnd_3570304] using wordTrace_append hprefix tailTrace_3570304
  have hstable : (prefixWord ++ tailWord_3570304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3570304).length < 2 ^ (prefixWord ++ tailWord_3570304).sum := by decide
  have hdescent : baseEnd_3570304 < baseStart_3570304 := by decide
  rcases family_descends (prefixWord ++ tailWord_3570304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3570323 : List Nat := [1, 1, 1, 2, 1, 2, 2, 2, 2, 3, 6]
def baseStart_3570323 : Nat := 118140960795 + 3570323 * 2 ^ 59
def prefixEnd_3570323 : Nat := 4983230072969 + 3 ^ 40 * 3570323 * 2
def baseEnd_3570323 : Nat := 1833291790802539828542889

theorem tailTrace_3570323 : CollatzResearch.WordTrace tailWord_3570323 prefixEnd_3570323 1833291790802539828542889 := by
  unfold tailWord_3570323
  simp only [CollatzResearch.WordTrace]
  refine ⟨130220377844337008467827623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86813585229558005645218415 130220377844337008467827623)
  ·
    refine ⟨195330566766505512701741435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130220377844337008467827623 195330566766505512701741435)
    ·
      refine ⟨292995850149758269052612153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195330566766505512701741435 292995850149758269052612153)
      ·
        refine ⟨219746887612318701789459115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 292995850149758269052612153 219746887612318701789459115)
        ·
          refine ⟨329620331418478052684188673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 219746887612318701789459115 329620331418478052684188673)
          ·
            refine ⟨247215248563858539513141505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 329620331418478052684188673 247215248563858539513141505)
            ·
              refine ⟨185411436422893904634856129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 247215248563858539513141505 185411436422893904634856129)
              ·
                refine ⟨139058577317170428476142097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 185411436422893904634856129 139058577317170428476142097)
                ·
                  refine ⟨104293932987877821357106573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 139058577317170428476142097 104293932987877821357106573)
                  ·
                    refine ⟨39110224870454183008914965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 104293932987877821357106573 39110224870454183008914965)
                    ·
                      refine ⟨1833291790802539828542889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 39110224870454183008914965 1833291790802539828542889)
                      ·
                        rfl

theorem cell23_3570323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 2, 2, 3, 6].length) (baseStart_3570323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3570323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3570323 prefixEnd_3570323 := by exact prefixLift 3570323
  have htrace : WordTrace (prefixWord ++ tailWord_3570323) baseStart_3570323 baseEnd_3570323 := by
    simpa [prefixWord, tailWord_3570323, baseEnd_3570323] using wordTrace_append hprefix tailTrace_3570323
  have hstable : (prefixWord ++ tailWord_3570323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3570323).length < 2 ^ (prefixWord ++ tailWord_3570323).sum := by decide
  have hdescent : baseEnd_3570323 < baseStart_3570323 := by decide
  rcases family_descends (prefixWord ++ tailWord_3570323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3570340 : List Nat := [2, 3, 1, 2, 2, 1, 1, 2, 1, 4, 4]
def baseStart_3570340 : Nat := 118140960795 + 3570340 * 2 ^ 59
def prefixEnd_3570340 : Nat := 4983230072969 + 3 ^ 40 * 3570340 * 2
def baseEnd_3570340 : Nat := 1833300519973666262030311

theorem tailTrace_3570340 : CollatzResearch.WordTrace tailWord_3570340 prefixEnd_3570340 1833300519973666262030311 := by
  unfold tailWord_3570340
  simp only [CollatzResearch.WordTrace]
  refine ⟨65110498942637710185598237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86813998590183613580797649 65110498942637710185598237)
  ·
    refine ⟨24416437103489141319599339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65110498942637710185598237 24416437103489141319599339)
    ·
      refine ⟨36624655655233711979399009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24416437103489141319599339 36624655655233711979399009)
      ·
        refine ⟨27468491741425283984549257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36624655655233711979399009 27468491741425283984549257)
        ·
          refine ⟨20601368806068962988411943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27468491741425283984549257 20601368806068962988411943)
          ·
            refine ⟨30902053209103444482617915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20601368806068962988411943 30902053209103444482617915)
            ·
              refine ⟨46353079813655166723926873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30902053209103444482617915 46353079813655166723926873)
              ·
                refine ⟨34764809860241375042945155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46353079813655166723926873 34764809860241375042945155)
                ·
                  refine ⟨52147214790362062564417733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34764809860241375042945155 52147214790362062564417733)
                  ·
                    refine ⟨9777602773192886730828325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 52147214790362062564417733 9777602773192886730828325)
                    ·
                      refine ⟨1833300519973666262030311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9777602773192886730828325 1833300519973666262030311)
                      ·
                        rfl

theorem cell23_3570340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 2, 1, 4, 4].length) (baseStart_3570340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3570340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3570340 prefixEnd_3570340 := by exact prefixLift 3570340
  have htrace : WordTrace (prefixWord ++ tailWord_3570340) baseStart_3570340 baseEnd_3570340 := by
    simpa [prefixWord, tailWord_3570340, baseEnd_3570340] using wordTrace_append hprefix tailTrace_3570340
  have hstable : (prefixWord ++ tailWord_3570340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3570340).length < 2 ^ (prefixWord ++ tailWord_3570340).sum := by decide
  have hdescent : baseEnd_3570340 < baseStart_3570340 := by decide
  rcases family_descends (prefixWord ++ tailWord_3570340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3570357 : List Nat := [1, 3, 3, 3, 1, 1, 1, 2, 2, 2, 4]
def baseStart_3570357 : Nat := 118140960795 + 3570357 * 2 ^ 59
def prefixEnd_3570357 : Nat := 4983230072969 + 3 ^ 40 * 3570357 * 2
def baseEnd_3570357 : Nat := 1833309249144792695517733

theorem tailTrace_3570357 : CollatzResearch.WordTrace tailWord_3570357 prefixEnd_3570357 1833309249144792695517733 := by
  unfold tailWord_3570357
  simp only [CollatzResearch.WordTrace]
  refine ⟨130221617926213832274565325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86814411950809221516376883 130221617926213832274565325)
  ·
    refine ⟨48833106722330187102961997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130221617926213832274565325 48833106722330187102961997)
    ·
      refine ⟨18312415020873820163610749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48833106722330187102961997 18312415020873820163610749)
      ·
        refine ⟨6867155632827682561354031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18312415020873820163610749 6867155632827682561354031)
        ·
          refine ⟨10300733449241523842031047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6867155632827682561354031 10300733449241523842031047)
          ·
            refine ⟨15451100173862285763046571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10300733449241523842031047 15451100173862285763046571)
            ·
              refine ⟨23176650260793428644569857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15451100173862285763046571 23176650260793428644569857)
              ·
                refine ⟨17382487695595071483427393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23176650260793428644569857 17382487695595071483427393)
                ·
                  refine ⟨13036865771696303612570545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17382487695595071483427393 13036865771696303612570545)
                  ·
                    refine ⟨9777649328772227709427909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13036865771696303612570545 9777649328772227709427909)
                    ·
                      refine ⟨1833309249144792695517733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9777649328772227709427909 1833309249144792695517733)
                      ·
                        rfl

theorem cell23_3570357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 1, 2, 2, 2, 4].length) (baseStart_3570357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3570357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3570357 prefixEnd_3570357 := by exact prefixLift 3570357
  have htrace : WordTrace (prefixWord ++ tailWord_3570357) baseStart_3570357 baseEnd_3570357 := by
    simpa [prefixWord, tailWord_3570357, baseEnd_3570357] using wordTrace_append hprefix tailTrace_3570357
  have hstable : (prefixWord ++ tailWord_3570357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3570357).length < 2 ^ (prefixWord ++ tailWord_3570357).sum := by decide
  have hdescent : baseEnd_3570357 < baseStart_3570357 := by decide
  rcases family_descends (prefixWord ++ tailWord_3570357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3570367 : List Nat := [1, 1, 2, 2, 2, 4, 2, 4, 5]
def baseStart_3570367 : Nat := 118140960795 + 3570367 * 2 ^ 59
def prefixEnd_3570367 : Nat := 4983230072969 + 3 ^ 40 * 3570367 * 2
def baseEnd_3570367 : Nat := 203701598216815295154743

theorem tailTrace_3570367 : CollatzResearch.WordTrace tailWord_3570367 prefixEnd_3570367 203701598216815295154743 := by
  unfold tailWord_3570367
  simp only [CollatzResearch.WordTrace]
  refine ⟨130221982656177603982429355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86814655104118402654952903 130221982656177603982429355)
  ·
    refine ⟨195332973984266405973644033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130221982656177603982429355 195332973984266405973644033)
    ·
      refine ⟨146499730488199804480233025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 195332973984266405973644033 146499730488199804480233025)
      ·
        refine ⟨109874797866149853360174769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146499730488199804480233025 109874797866149853360174769)
        ·
          refine ⟨82406098399612390020131077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109874797866149853360174769 82406098399612390020131077)
          ·
            refine ⟨15451143449927323128774577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 82406098399612390020131077 15451143449927323128774577)
            ·
              refine ⟨11588357587445492346580933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15451143449927323128774577 11588357587445492346580933)
              ·
                refine ⟨2172817047646029814983925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11588357587445492346580933 2172817047646029814983925)
                ·
                  refine ⟨203701598216815295154743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2172817047646029814983925 203701598216815295154743)
                  ·
                    rfl

theorem cell23_3570367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 2, 4, 5].length) (baseStart_3570367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3570367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3570367 prefixEnd_3570367 := by exact prefixLift 3570367
  have htrace : WordTrace (prefixWord ++ tailWord_3570367) baseStart_3570367 baseEnd_3570367 := by
    simpa [prefixWord, tailWord_3570367, baseEnd_3570367] using wordTrace_append hprefix tailTrace_3570367
  have hstable : (prefixWord ++ tailWord_3570367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3570367).length < 2 ^ (prefixWord ++ tailWord_3570367).sum := by decide
  have hdescent : baseEnd_3570367 < baseStart_3570367 := by decide
  rcases family_descends (prefixWord ++ tailWord_3570367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3570378 : List Nat := [3, 1, 2, 1, 4, 2, 3, 1, 2, 2, 2]
def baseStart_3570378 : Nat := 118140960795 + 3570378 * 2 ^ 59
def prefixEnd_3570378 : Nat := 4983230072969 + 3 ^ 40 * 3570378 * 2
def baseEnd_3570378 : Nat := 1833320032238537113355137

theorem tailTrace_3570378 : CollatzResearch.WordTrace tailWord_3570378 prefixEnd_3570378 1833320032238537113355137 := by
  unfold tailWord_3570378
  simp only [CollatzResearch.WordTrace]
  refine ⟨32555595964784438215269947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86814922572758501907386525 32555595964784438215269947)
  ·
    refine ⟨48833393947176657322904921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32555595964784438215269947 48833393947176657322904921)
    ·
      refine ⟨36625045460382492992178691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48833393947176657322904921 36625045460382492992178691)
      ·
        refine ⟨54937568190573739488268037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36625045460382492992178691 54937568190573739488268037)
        ·
          refine ⟨10300794035732576154050257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 54937568190573739488268037 10300794035732576154050257)
          ·
            refine ⟨7725595526799432115537693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10300794035732576154050257 7725595526799432115537693)
            ·
              refine ⟨2897098322549787043326635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7725595526799432115537693 2897098322549787043326635)
              ·
                refine ⟨4345647483824680564989953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2897098322549787043326635 4345647483824680564989953)
                ·
                  refine ⟨3259235612868510423742465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4345647483824680564989953 3259235612868510423742465)
                  ·
                    refine ⟨2444426709651382817806849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3259235612868510423742465 2444426709651382817806849)
                    ·
                      refine ⟨1833320032238537113355137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2444426709651382817806849 1833320032238537113355137)
                      ·
                        rfl

theorem cell23_3570378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 3, 1, 2, 2, 2].length) (baseStart_3570378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3570378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3570378 prefixEnd_3570378 := by exact prefixLift 3570378
  have htrace : WordTrace (prefixWord ++ tailWord_3570378) baseStart_3570378 baseEnd_3570378 := by
    simpa [prefixWord, tailWord_3570378, baseEnd_3570378] using wordTrace_append hprefix tailTrace_3570378
  have hstable : (prefixWord ++ tailWord_3570378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3570378).length < 2 ^ (prefixWord ++ tailWord_3570378).sum := by decide
  have hdescent : baseEnd_3570378 < baseStart_3570378 := by decide
  rcases family_descends (prefixWord ++ tailWord_3570378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3570417 : List Nat := [1, 2, 2, 2, 2, 2, 3, 2, 2, 1, 4]
def baseStart_3570417 : Nat := 118140960795 + 3570417 * 2 ^ 59
def prefixEnd_3570417 : Nat := 4983230072969 + 3 ^ 40 * 3570417 * 2
def baseEnd_3570417 : Nat := 1833340057984062460767457

theorem tailTrace_3570417 : CollatzResearch.WordTrace tailWord_3570417 prefixEnd_3570417 1833340057984062460767457 := by
  unfold tailWord_3570417
  simp only [CollatzResearch.WordTrace]
  refine ⟨130223806305996462521749505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86815870870664308347833003 130223806305996462521749505)
  ·
    refine ⟨97667854729497346891312129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130223806305996462521749505 97667854729497346891312129)
    ·
      refine ⟨73250891047123010168484097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97667854729497346891312129 73250891047123010168484097)
      ·
        refine ⟨54938168285342257626363073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73250891047123010168484097 54938168285342257626363073)
        ·
          refine ⟨41203626214006693219772305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54938168285342257626363073 41203626214006693219772305)
          ·
            refine ⟨30902719660505019914829229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41203626214006693219772305 30902719660505019914829229)
            ·
              refine ⟨11588519872689382468060961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30902719660505019914829229 11588519872689382468060961)
              ·
                refine ⟨8691389904517036851045721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11588519872689382468060961 8691389904517036851045721)
                ·
                  refine ⟨6518542428387777638284291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8691389904517036851045721 6518542428387777638284291)
                  ·
                    refine ⟨9777813642581666457426437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6518542428387777638284291 9777813642581666457426437)
                    ·
                      refine ⟨1833340057984062460767457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9777813642581666457426437 1833340057984062460767457)
                      ·
                        rfl

theorem cell23_3570417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 3, 2, 2, 1, 4].length) (baseStart_3570417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3570417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3570417 prefixEnd_3570417 := by exact prefixLift 3570417
  have htrace : WordTrace (prefixWord ++ tailWord_3570417) baseStart_3570417 baseEnd_3570417 := by
    simpa [prefixWord, tailWord_3570417, baseEnd_3570417] using wordTrace_append hprefix tailTrace_3570417
  have hstable : (prefixWord ++ tailWord_3570417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3570417).length < 2 ^ (prefixWord ++ tailWord_3570417).sum := by decide
  have hdescent : baseEnd_3570417 < baseStart_3570417 := by decide
  rcases family_descends (prefixWord ++ tailWord_3570417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3570478 : List Nat := [4, 1, 3, 2, 1, 2, 1, 4, 1, 4]
def baseStart_3570478 : Nat := 118140960795 + 3570478 * 2 ^ 59
def prefixEnd_3570478 : Nat := 4983230072969 + 3 ^ 40 * 3570478 * 2
def baseEnd_3570478 : Nat := 611123793434662240701559

theorem tailTrace_3570478 : CollatzResearch.WordTrace tailWord_3570478 prefixEnd_3570478 611123793434662240701559 := by
  unfold tailWord_3570478
  simp only [CollatzResearch.WordTrace]
  refine ⟨16278253894846933742465011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 86817354105850313293146725 16278253894846933742465011)
  ·
    refine ⟨24417380842270400613697517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16278253894846933742465011 24417380842270400613697517)
    ·
      refine ⟨9156517815851400230136569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24417380842270400613697517 9156517815851400230136569)
      ·
        refine ⟨6867388361888550172602427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9156517815851400230136569 6867388361888550172602427)
        ·
          refine ⟨10301082542832825258903641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6867388361888550172602427 10301082542832825258903641)
          ·
            refine ⟨7725811907124618944177731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10301082542832825258903641 7725811907124618944177731)
            ·
              refine ⟨11588717860686928416266597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7725811907124618944177731 11588717860686928416266597)
              ·
                refine ⟨2172884598878799078049987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11588717860686928416266597 2172884598878799078049987)
                ·
                  refine ⟨3259326898318198617074981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2172884598878799078049987 3259326898318198617074981)
                  ·
                    refine ⟨611123793434662240701559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3259326898318198617074981 611123793434662240701559)
                    ·
                      rfl

theorem cell23_3570478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 1, 4, 1, 4].length) (baseStart_3570478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3570478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3570478 prefixEnd_3570478 := by exact prefixLift 3570478
  have htrace : WordTrace (prefixWord ++ tailWord_3570478) baseStart_3570478 baseEnd_3570478 := by
    simpa [prefixWord, tailWord_3570478, baseEnd_3570478] using wordTrace_append hprefix tailTrace_3570478
  have hstable : (prefixWord ++ tailWord_3570478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3570478).length < 2 ^ (prefixWord ++ tailWord_3570478).sum := by decide
  have hdescent : baseEnd_3570478 < baseStart_3570478 := by decide
  rcases family_descends (prefixWord ++ tailWord_3570478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3570480 : List Nat := [2, 1, 1, 1, 2, 2, 1, 2, 2, 4, 5]
def baseStart_3570480 : Nat := 118140960795 + 3570480 * 2 ^ 59
def prefixEnd_3570480 : Nat := 4983230072969 + 3 ^ 40 * 3570480 * 2
def baseEnd_3570480 : Nat := 1833372407265295714279667

theorem tailTrace_3570480 : CollatzResearch.WordTrace tailWord_3570480 prefixEnd_3570480 1833372407265295714279667 := by
  unfold tailWord_3570480
  simp only [CollatzResearch.WordTrace]
  refine ⟨65113052052384112140646447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86817402736512149520861929 65113052052384112140646447)
  ·
    refine ⟨97669578078576168210969671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65113052052384112140646447 97669578078576168210969671)
    ·
      refine ⟨146504367117864252316454507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97669578078576168210969671 146504367117864252316454507)
      ·
        refine ⟨219756550676796378474681761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146504367117864252316454507 219756550676796378474681761)
        ·
          refine ⟨164817413007597283856011321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 219756550676796378474681761 164817413007597283856011321)
          ·
            refine ⟨123613059755697962892008491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 164817413007597283856011321 123613059755697962892008491)
            ·
              refine ⟨185419589633546944338012737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 123613059755697962892008491 185419589633546944338012737)
              ·
                refine ⟨139064692225160208253509553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 185419589633546944338012737 139064692225160208253509553)
                ·
                  refine ⟨104298519168870156190132165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 139064692225160208253509553 104298519168870156190132165)
                  ·
                    refine ⟨19555972344163154285649781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 104298519168870156190132165 19555972344163154285649781)
                    ·
                      refine ⟨1833372407265295714279667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19555972344163154285649781 1833372407265295714279667)
                      ·
                        rfl

theorem cell23_3570480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 2, 2, 4, 5].length) (baseStart_3570480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3570480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3570480 prefixEnd_3570480 := by exact prefixLift 3570480
  have htrace : WordTrace (prefixWord ++ tailWord_3570480) baseStart_3570480 baseEnd_3570480 := by
    simpa [prefixWord, tailWord_3570480, baseEnd_3570480] using wordTrace_append hprefix tailTrace_3570480
  have hstable : (prefixWord ++ tailWord_3570480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3570480).length < 2 ^ (prefixWord ++ tailWord_3570480).sum := by decide
  have hdescent : baseEnd_3570480 < baseStart_3570480 := by decide
  rcases family_descends (prefixWord ++ tailWord_3570480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3570517 : List Nat := [1, 3, 2, 2, 2, 1, 1, 4, 1, 6]
def baseStart_3570517 : Nat := 118140960795 + 3570517 * 2 ^ 59
def prefixEnd_3570517 : Nat := 4983230072969 + 3 ^ 40 * 3570517 * 2
def baseEnd_3570517 : Nat := 611130468683170689838999

theorem tailTrace_3570517 : CollatzResearch.WordTrace tailWord_3570517 prefixEnd_3570517 611130468683170689838999 := by
  unfold tailWord_3570517
  simp only [CollatzResearch.WordTrace]
  refine ⟨130227453605634179600389805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86818302403756119733593203 130227453605634179600389805)
  ·
    refine ⟨48835295102112817350146177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130227453605634179600389805 48835295102112817350146177)
    ·
      refine ⟨36626471326584613012609633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48835295102112817350146177 36626471326584613012609633)
      ·
        refine ⟨27469853494938459759457225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36626471326584613012609633 27469853494938459759457225)
        ·
          refine ⟨20602390121203844819592919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27469853494938459759457225 20602390121203844819592919)
          ·
            refine ⟨30903585181805767229389379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20602390121203844819592919 30903585181805767229389379)
            ·
              refine ⟨46355377772708650844084069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30903585181805767229389379 46355377772708650844084069)
              ·
                refine ⟨8691633332382872033265763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46355377772708650844084069 8691633332382872033265763)
                ·
                  refine ⟨13037449998574308049898645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8691633332382872033265763 13037449998574308049898645)
                  ·
                    refine ⟨611130468683170689838999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13037449998574308049898645 611130468683170689838999)
                    ·
                      rfl

theorem cell23_3570517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 4, 1, 6].length) (baseStart_3570517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3570517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3570517 prefixEnd_3570517 := by exact prefixLift 3570517
  have htrace : WordTrace (prefixWord ++ tailWord_3570517) baseStart_3570517 baseEnd_3570517 := by
    simpa [prefixWord, tailWord_3570517, baseEnd_3570517] using wordTrace_append hprefix tailTrace_3570517
  have hstable : (prefixWord ++ tailWord_3570517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3570517).length < 2 ^ (prefixWord ++ tailWord_3570517).sum := by decide
  have hdescent : baseEnd_3570517 < baseStart_3570517 := by decide
  rcases family_descends (prefixWord ++ tailWord_3570517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3570521 : List Nat := [1, 2, 1, 2, 2, 6, 2, 1, 1, 5]
def baseStart_3570521 : Nat := 118140960795 + 3570521 * 2 ^ 59
def prefixEnd_3570521 : Nat := 4983230072969 + 3 ^ 40 * 3570521 * 2
def baseEnd_3570521 : Nat := 611131153324043351288993

theorem tailTrace_3570521 : CollatzResearch.WordTrace tailWord_3570521 prefixEnd_3570521 611131153324043351288993 := by
  unfold tailWord_3570521
  simp only [CollatzResearch.WordTrace]
  refine ⟨130227599497619688283535417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86818399665079792189023611 130227599497619688283535417)
  ·
    refine ⟨97670699623214766212651563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130227599497619688283535417 97670699623214766212651563)
    ·
      refine ⟨146506049434822149318977345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97670699623214766212651563 146506049434822149318977345)
      ·
        refine ⟨109879537076116611989233009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146506049434822149318977345 109879537076116611989233009)
        ·
          refine ⟨82409652807087458991924757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109879537076116611989233009 82409652807087458991924757)
          ·
            refine ⟨3862952475332224640246473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 82409652807087458991924757 3862952475332224640246473)
            ·
              refine ⟨2897214356499168480184855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3862952475332224640246473 2897214356499168480184855)
              ·
                refine ⟨4345821534748752720277283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2897214356499168480184855 4345821534748752720277283)
                ·
                  refine ⟨6518732302123129080415925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4345821534748752720277283 6518732302123129080415925)
                  ·
                    refine ⟨611131153324043351288993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6518732302123129080415925 611131153324043351288993)
                    ·
                      rfl

theorem cell23_3570521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 6, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 6, 2, 1, 1, 5].length) (baseStart_3570521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3570521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3570521 prefixEnd_3570521 := by exact prefixLift 3570521
  have htrace : WordTrace (prefixWord ++ tailWord_3570521) baseStart_3570521 baseEnd_3570521 := by
    simpa [prefixWord, tailWord_3570521, baseEnd_3570521] using wordTrace_append hprefix tailTrace_3570521
  have hstable : (prefixWord ++ tailWord_3570521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3570521).length < 2 ^ (prefixWord ++ tailWord_3570521).sum := by decide
  have hdescent : baseEnd_3570521 < baseStart_3570521 := by decide
  rcases family_descends (prefixWord ++ tailWord_3570521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3570527 : List Nat := [1, 1, 2, 3, 1, 3, 2, 3, 1, 1, 5]
def baseStart_3570527 : Nat := 118140960795 + 3570527 * 2 ^ 59
def prefixEnd_3570527 : Nat := 4983230072969 + 3 ^ 40 * 3570527 * 2
def baseEnd_3570527 : Nat := 1833396540856057030391951

theorem tailTrace_3570527 : CollatzResearch.WordTrace tailWord_3570527 prefixEnd_3570527 1833396540856057030391951 := by
  unfold tailWord_3570527
  simp only [CollatzResearch.WordTrace]
  refine ⟨130227818335597951308253835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86818545557065300872169223 130227818335597951308253835)
  ·
    refine ⟨195341727503396926962380753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130227818335597951308253835 195341727503396926962380753)
    ·
      refine ⟨146506295627547695221785565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 195341727503396926962380753 146506295627547695221785565)
      ·
        refine ⟨54939860860330385708169587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 146506295627547695221785565 54939860860330385708169587)
        ·
          refine ⟨82409791290495578562254381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54939860860330385708169587 82409791290495578562254381)
          ·
            refine ⟨30903671733935841960845393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 82409791290495578562254381 30903671733935841960845393)
            ·
              refine ⟨23177753800451881470634045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30903671733935841960845393 23177753800451881470634045)
              ·
                refine ⟨8691657675169455551487767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23177753800451881470634045 8691657675169455551487767)
                ·
                  refine ⟨13037486512754183327231651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8691657675169455551487767 13037486512754183327231651)
                  ·
                    refine ⟨19556229769131274990847477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13037486512754183327231651 19556229769131274990847477)
                    ·
                      refine ⟨1833396540856057030391951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19556229769131274990847477 1833396540856057030391951)
                      ·
                        rfl

theorem cell23_3570527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 2, 3, 1, 1, 5].length) (baseStart_3570527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3570527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3570527 prefixEnd_3570527 := by exact prefixLift 3570527
  have htrace : WordTrace (prefixWord ++ tailWord_3570527) baseStart_3570527 baseEnd_3570527 := by
    simpa [prefixWord, tailWord_3570527, baseEnd_3570527] using wordTrace_append hprefix tailTrace_3570527
  have hstable : (prefixWord ++ tailWord_3570527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3570527).length < 2 ^ (prefixWord ++ tailWord_3570527).sum := by decide
  have hdescent : baseEnd_3570527 < baseStart_3570527 := by decide
  rcases family_descends (prefixWord ++ tailWord_3570527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3570591 : List Nat := [1, 1, 2, 5, 2, 1, 2, 1, 4, 1, 3]
def baseStart_3570591 : Nat := 118140960795 + 3570591 * 2 ^ 59
def prefixEnd_3570591 : Nat := 4983230072969 + 3 ^ 40 * 3570591 * 2
def baseEnd_3570591 : Nat := 1833429403617944779991657

theorem tailTrace_3570591 : CollatzResearch.WordTrace tailWord_3570591 prefixEnd_3570591 1833429403617944779991657 := by
  unfold tailWord_3570591
  simp only [CollatzResearch.WordTrace]
  refine ⟨130230152607366090238583627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86820101738244060159055751 130230152607366090238583627)
  ·
    refine ⟨195345228911049135357875441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130230152607366090238583627 195345228911049135357875441)
    ·
      refine ⟨146508921683286851518406581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 195345228911049135357875441 146508921683286851518406581)
      ·
        refine ⟨13735211407808142329850617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 146508921683286851518406581 13735211407808142329850617)
        ·
          refine ⟨10301408555856106747387963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13735211407808142329850617 10301408555856106747387963)
          ·
            refine ⟨15452112833784160121081945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10301408555856106747387963 15452112833784160121081945)
            ·
              refine ⟨11589084625338120090811459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15452112833784160121081945 11589084625338120090811459)
              ·
                refine ⟨17383626938007180136217189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11589084625338120090811459 17383626938007180136217189)
                ·
                  refine ⟨3259430050876346275540723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17383626938007180136217189 3259430050876346275540723)
                  ·
                    refine ⟨4889145076314519413311085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3259430050876346275540723 4889145076314519413311085)
                    ·
                      refine ⟨1833429403617944779991657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4889145076314519413311085 1833429403617944779991657)
                      ·
                        rfl

theorem cell23_3570591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 2, 1, 4, 1, 3].length) (baseStart_3570591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3570591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3570591 prefixEnd_3570591 := by exact prefixLift 3570591
  have htrace : WordTrace (prefixWord ++ tailWord_3570591) baseStart_3570591 baseEnd_3570591 := by
    simpa [prefixWord, tailWord_3570591, baseEnd_3570591] using wordTrace_append hprefix tailTrace_3570591
  have hstable : (prefixWord ++ tailWord_3570591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3570591).length < 2 ^ (prefixWord ++ tailWord_3570591).sum := by decide
  have hdescent : baseEnd_3570591 < baseStart_3570591 := by decide
  rcases family_descends (prefixWord ++ tailWord_3570591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3570627 : List Nat := [1, 1, 1, 3, 1, 1, 2, 4, 1, 4, 4]
def baseStart_3570627 : Nat := 118140960795 + 3570627 * 2 ^ 59
def prefixEnd_3570627 : Nat := 4983230072969 + 3 ^ 40 * 3570627 * 2
def baseEnd_3570627 : Nat := 1833447888921506639141491

theorem tailTrace_3570627 : CollatzResearch.WordTrace tailWord_3570627 prefixEnd_3570627 1833447888921506639141491 := by
  unfold tailWord_3570627
  simp only [CollatzResearch.WordTrace]
  refine ⟨130231465635235668386894135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86820977090157112257929423 130231465635235668386894135)
  ·
    refine ⟨195347198452853502580341203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130231465635235668386894135 195347198452853502580341203)
    ·
      refine ⟨293020797679280253870511805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195347198452853502580341203 293020797679280253870511805)
      ·
        refine ⟨109882799129730095201441927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 293020797679280253870511805 109882799129730095201441927)
        ·
          refine ⟨164824198694595142802162891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109882799129730095201441927 164824198694595142802162891)
          ·
            refine ⟨247236298041892714203244337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 164824198694595142802162891 247236298041892714203244337)
            ·
              refine ⟨185427223531419535652433253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 247236298041892714203244337 185427223531419535652433253)
              ·
                refine ⟨34767604412141162934831235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 185427223531419535652433253 34767604412141162934831235)
                ·
                  refine ⟨52151406618211744402246853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34767604412141162934831235 52151406618211744402246853)
                  ·
                    refine ⟨9778388740914702075421285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 52151406618211744402246853 9778388740914702075421285)
                    ·
                      refine ⟨1833447888921506639141491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9778388740914702075421285 1833447888921506639141491)
                      ·
                        rfl

theorem cell23_3570627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 1, 4, 4].length) (baseStart_3570627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3570627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3570627 prefixEnd_3570627 := by exact prefixLift 3570627
  have htrace : WordTrace (prefixWord ++ tailWord_3570627) baseStart_3570627 baseEnd_3570627 := by
    simpa [prefixWord, tailWord_3570627, baseEnd_3570627] using wordTrace_append hprefix tailTrace_3570627
  have hstable : (prefixWord ++ tailWord_3570627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3570627).length < 2 ^ (prefixWord ++ tailWord_3570627).sum := by decide
  have hdescent : baseEnd_3570627 < baseStart_3570627 := by decide
  rcases family_descends (prefixWord ++ tailWord_3570627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3570631 : List Nat := [1, 1, 4, 1, 1, 2, 2, 1, 6, 2, 2]
def baseStart_3570631 : Nat := 118140960795 + 3570631 * 2 ^ 59
def prefixEnd_3570631 : Nat := 4983230072969 + 3 ^ 40 * 3570631 * 2
def baseEnd_3570631 : Nat := 1833449942844124623491473

theorem tailTrace_3570631 : CollatzResearch.WordTrace tailWord_3570631 prefixEnd_3570631 1833449942844124623491473 := by
  unfold tailWord_3570631
  simp only [CollatzResearch.WordTrace]
  refine ⟨130231611527221177070039747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86821074351480784713359831 130231611527221177070039747)
  ·
    refine ⟨195347417290831765605059621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130231611527221177070039747 195347417290831765605059621)
    ·
      refine ⟨36627640742030956050948679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 195347417290831765605059621 36627640742030956050948679)
      ·
        refine ⟨54941461113046434076423019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36627640742030956050948679 54941461113046434076423019)
        ·
          refine ⟨82412191669569651114634529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54941461113046434076423019 82412191669569651114634529)
          ·
            refine ⟨61809143752177238335975897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82412191669569651114634529 61809143752177238335975897)
            ·
              refine ⟨46356857814132928751981923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61809143752177238335975897 46356857814132928751981923)
              ·
                refine ⟨69535286721199393127972885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46356857814132928751981923 69535286721199393127972885)
                ·
                  refine ⟨3259466565056221552873729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 69535286721199393127972885 3259466565056221552873729)
                  ·
                    refine ⟨2444599923792166164655297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3259466565056221552873729 2444599923792166164655297)
                    ·
                      refine ⟨1833449942844124623491473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2444599923792166164655297 1833449942844124623491473)
                      ·
                        rfl

theorem cell23_3570631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 1, 6, 2, 2].length) (baseStart_3570631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3570631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3570631 prefixEnd_3570631 := by exact prefixLift 3570631
  have htrace : WordTrace (prefixWord ++ tailWord_3570631) baseStart_3570631 baseEnd_3570631 := by
    simpa [prefixWord, tailWord_3570631, baseEnd_3570631] using wordTrace_append hprefix tailTrace_3570631
  have hstable : (prefixWord ++ tailWord_3570631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3570631).length < 2 ^ (prefixWord ++ tailWord_3570631).sum := by decide
  have hdescent : baseEnd_3570631 < baseStart_3570631 := by decide
  rcases family_descends (prefixWord ++ tailWord_3570631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3570648 : List Nat := [2, 1, 2, 2, 2, 3, 1, 4, 2, 2, 2]
def baseStart_3570648 : Nat := 118140960795 + 3570648 * 2 ^ 59
def prefixEnd_3570648 : Nat := 4983230072969 + 3 ^ 40 * 3570648 * 2
def baseEnd_3570648 : Nat := 1833458672015251056978895

theorem tailTrace_3570648 : CollatzResearch.WordTrace tailWord_3570648 prefixEnd_3570648 1833458672015251056978895 := by
  unfold tailWord_3570648
  simp only [CollatzResearch.WordTrace]
  refine ⟨65116115784079794486704299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86821487712106392648939065 65116115784079794486704299)
  ·
    refine ⟨97674173676119691730056449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65116115784079794486704299 97674173676119691730056449)
    ·
      refine ⟨73255630257089768797542337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97674173676119691730056449 73255630257089768797542337)
      ·
        refine ⟨54941722692817326598156753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73255630257089768797542337 54941722692817326598156753)
        ·
          refine ⟨41206292019612994948617565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54941722692817326598156753 41206292019612994948617565)
          ·
            refine ⟨15452359507354873105731587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41206292019612994948617565 15452359507354873105731587)
            ·
              refine ⟨23178539261032309658597381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15452359507354873105731587 23178539261032309658597381)
              ·
                refine ⟨4345976111443558060987009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23178539261032309658597381 4345976111443558060987009)
                ·
                  refine ⟨3259482083582668545740257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4345976111443558060987009 3259482083582668545740257)
                  ·
                    refine ⟨2444611562687001409305193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3259482083582668545740257 2444611562687001409305193)
                    ·
                      refine ⟨1833458672015251056978895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2444611562687001409305193 1833458672015251056978895)
                      ·
                        rfl

theorem cell23_3570648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 1, 4, 2, 2, 2].length) (baseStart_3570648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3570648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3570648 prefixEnd_3570648 := by exact prefixLift 3570648
  have htrace : WordTrace (prefixWord ++ tailWord_3570648) baseStart_3570648 baseEnd_3570648 := by
    simpa [prefixWord, tailWord_3570648, baseEnd_3570648] using wordTrace_append hprefix tailTrace_3570648
  have hstable : (prefixWord ++ tailWord_3570648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3570648).length < 2 ^ (prefixWord ++ tailWord_3570648).sum := by decide
  have hdescent : baseEnd_3570648 < baseStart_3570648 := by decide
  rcases family_descends (prefixWord ++ tailWord_3570648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3570657 : List Nat := [1, 2, 3, 1, 2, 1, 1, 1, 2, 1, 8]
def baseStart_3570657 : Nat := 118140960795 + 3570657 * 2 ^ 59
def prefixEnd_3570657 : Nat := 4983230072969 + 3 ^ 40 * 3570657 * 2
def baseEnd_3570657 : Nat := 1833463293341141521766353

theorem tailTrace_3570657 : CollatzResearch.WordTrace tailWord_3570657 prefixEnd_3570657 1833463293341141521766353 := by
  unfold tailWord_3570657
  simp only [CollatzResearch.WordTrace]
  refine ⟨130232559825126983510486225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86821706550084655673657483 130232559825126983510486225)
  ·
    refine ⟨97674419868845237632864669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130232559825126983510486225 97674419868845237632864669)
    ·
      refine ⟨36627907450816964112324251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 97674419868845237632864669 36627907450816964112324251)
      ·
        refine ⟨54941861176225446168486377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36627907450816964112324251 54941861176225446168486377)
        ·
          refine ⟨41206395882169084626364783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54941861176225446168486377 41206395882169084626364783)
          ·
            refine ⟨61809593823253626939547175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41206395882169084626364783 61809593823253626939547175)
            ·
              refine ⟨92714390734880440409320763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61809593823253626939547175 92714390734880440409320763)
              ·
                refine ⟨139071586102320660613981145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92714390734880440409320763 139071586102320660613981145)
                ·
                  refine ⟨104303689576740495460485859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 139071586102320660613981145 104303689576740495460485859)
                  ·
                    refine ⟨156455534365110743190728789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 104303689576740495460485859 156455534365110743190728789)
                    ·
                      refine ⟨1833463293341141521766353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 156455534365110743190728789 1833463293341141521766353)
                      ·
                        rfl

theorem cell23_3570657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 1, 2, 1, 8].length) (baseStart_3570657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3570657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3570657 prefixEnd_3570657 := by exact prefixLift 3570657
  have htrace : WordTrace (prefixWord ++ tailWord_3570657) baseStart_3570657 baseEnd_3570657 := by
    simpa [prefixWord, tailWord_3570657, baseEnd_3570657] using wordTrace_append hprefix tailTrace_3570657
  have hstable : (prefixWord ++ tailWord_3570657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3570657).length < 2 ^ (prefixWord ++ tailWord_3570657).sum := by decide
  have hdescent : baseEnd_3570657 < baseStart_3570657 := by decide
  rcases family_descends (prefixWord ++ tailWord_3570657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3570664 : List Nat := [2, 1, 4, 1, 1, 1, 3, 1, 1, 5, 3]
def baseStart_3570664 : Nat := 118140960795 + 3570664 * 2 ^ 59
def prefixEnd_3570664 : Nat := 4983230072969 + 3 ^ 40 * 3570664 * 2
def baseEnd_3570664 : Nat := 1833466887705722994378821

theorem tailTrace_3570664 : CollatzResearch.WordTrace tailWord_3570664 prefixEnd_3570664 1833466887705722994378821 := by
  unfold tailWord_3570664
  simp only [CollatzResearch.WordTrace]
  refine ⟨65116407568050811852995523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86821876757401082470660697 65116407568050811852995523)
  ·
    refine ⟨97674611352076217779493285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65116407568050811852995523 97674611352076217779493285)
    ·
      refine ⟨18313989628514290833654991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 97674611352076217779493285 18313989628514290833654991)
      ·
        refine ⟨27470984442771436250482487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18313989628514290833654991 27470984442771436250482487)
        ·
          refine ⟨41206476664157154375723731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27470984442771436250482487 41206476664157154375723731)
          ·
            refine ⟨61809714996235731563585597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41206476664157154375723731 61809714996235731563585597)
            ·
              refine ⟨23178643123588399336344599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61809714996235731563585597 23178643123588399336344599)
              ·
                refine ⟨34767964685382599004516899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23178643123588399336344599 34767964685382599004516899)
                ·
                  refine ⟨52151947028073898506775349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34767964685382599004516899 52151947028073898506775349)
                  ·
                    refine ⟨4889245033881927985010189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 52151947028073898506775349 4889245033881927985010189)
                    ·
                      refine ⟨1833466887705722994378821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4889245033881927985010189 1833466887705722994378821)
                      ·
                        rfl

theorem cell23_3570664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 3, 1, 1, 5, 3].length) (baseStart_3570664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3570664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3570664 prefixEnd_3570664 := by exact prefixLift 3570664
  have htrace : WordTrace (prefixWord ++ tailWord_3570664) baseStart_3570664 baseEnd_3570664 := by
    simpa [prefixWord, tailWord_3570664, baseEnd_3570664] using wordTrace_append hprefix tailTrace_3570664
  have hstable : (prefixWord ++ tailWord_3570664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3570664).length < 2 ^ (prefixWord ++ tailWord_3570664).sum := by decide
  have hdescent : baseEnd_3570664 < baseStart_3570664 := by decide
  rcases family_descends (prefixWord ++ tailWord_3570664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3570684 : List Nat := [2, 2, 2, 1, 2, 4, 1, 1, 1, 7]
def baseStart_3570684 : Nat := 118140960795 + 3570684 * 2 ^ 59
def prefixEnd_3570684 : Nat := 4983230072969 + 3 ^ 40 * 3570684 * 2
def baseEnd_3570684 : Nat := 611159052439604305376243

theorem tailTrace_3570684 : CollatzResearch.WordTrace tailWord_3570684 prefixEnd_3570684 611159052439604305376243 := by
  unfold tailWord_3570684
  simp only [CollatzResearch.WordTrace]
  refine ⟨65116772298014583560859553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86822363064019444747812737 65116772298014583560859553)
  ·
    refine ⟨48837579223510937670644665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65116772298014583560859553 48837579223510937670644665)
    ·
      refine ⟨36628184417633203252983499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48837579223510937670644665 36628184417633203252983499)
      ·
        refine ⟨54942276626449804879475249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36628184417633203252983499 54942276626449804879475249)
        ·
          refine ⟨41206707469837353659606437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54942276626449804879475249 41206707469837353659606437)
          ·
            refine ⟨7726257650594503811176207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41206707469837353659606437 7726257650594503811176207)
            ·
              refine ⟨11589386475891755716764311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7726257650594503811176207 11589386475891755716764311)
              ·
                refine ⟨17384079713837633575146467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11589386475891755716764311 17384079713837633575146467)
                ·
                  refine ⟨26076119570756450362719701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17384079713837633575146467 26076119570756450362719701)
                  ·
                    refine ⟨611159052439604305376243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 26076119570756450362719701 611159052439604305376243)
                    ·
                      rfl

theorem cell23_3570684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 1, 1, 1, 7].length) (baseStart_3570684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3570684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3570684 prefixEnd_3570684 := by exact prefixLift 3570684
  have htrace : WordTrace (prefixWord ++ tailWord_3570684) baseStart_3570684 baseEnd_3570684 := by
    simpa [prefixWord, tailWord_3570684, baseEnd_3570684] using wordTrace_append hprefix tailTrace_3570684
  have hstable : (prefixWord ++ tailWord_3570684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3570684).length < 2 ^ (prefixWord ++ tailWord_3570684).sum := by decide
  have hdescent : baseEnd_3570684 < baseStart_3570684 := by decide
  rcases family_descends (prefixWord ++ tailWord_3570684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3570697 : List Nat := [1, 2, 1, 1, 3, 1, 1, 2, 1, 10]
def baseStart_3570697 : Nat := 118140960795 + 3570697 * 2 ^ 59
def prefixEnd_3570697 : Nat := 4983230072969 + 3 ^ 40 * 3570697 * 2
def baseEnd_3570697 : Nat := 611161277522440455088723

theorem tailTrace_3570697 : CollatzResearch.WordTrace tailWord_3570697 prefixEnd_3570697 611161277522440455088723 := by
  unfold tailWord_3570697
  simp only [CollatzResearch.WordTrace]
  refine ⟨130234018744982070341942345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86822679163321380227961563 130234018744982070341942345)
  ·
    refine ⟨97675514058736552756456759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130234018744982070341942345 97675514058736552756456759)
    ·
      refine ⟨146513271088104829134685139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97675514058736552756456759 146513271088104829134685139)
      ·
        refine ⟨219769906632157243702027709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146513271088104829134685139 219769906632157243702027709)
        ·
          refine ⟨82413714987058966388260391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 219769906632157243702027709 82413714987058966388260391)
          ·
            refine ⟨123620572480588449582390587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82413714987058966388260391 123620572480588449582390587)
            ·
              refine ⟨185430858720882674373585881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 123620572480588449582390587 185430858720882674373585881)
              ·
                refine ⟨139073144040662005780189411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 185430858720882674373585881 139073144040662005780189411)
                ·
                  refine ⟨208609716060993008670284117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 139073144040662005780189411 208609716060993008670284117)
                  ·
                    refine ⟨611161277522440455088723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 208609716060993008670284117 611161277522440455088723)
                    ·
                      rfl

theorem cell23_3570697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 2, 1, 10].length) (baseStart_3570697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3570697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3570697 prefixEnd_3570697 := by exact prefixLift 3570697
  have htrace : WordTrace (prefixWord ++ tailWord_3570697) baseStart_3570697 baseEnd_3570697 := by
    simpa [prefixWord, tailWord_3570697, baseEnd_3570697] using wordTrace_append hprefix tailTrace_3570697
  have hstable : (prefixWord ++ tailWord_3570697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3570697).length < 2 ^ (prefixWord ++ tailWord_3570697).sum := by decide
  have hdescent : baseEnd_3570697 < baseStart_3570697 := by decide
  rcases family_descends (prefixWord ++ tailWord_3570697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3570741 : List Nat := [1, 3, 3, 1, 1, 1, 1, 5, 2, 2, 3]
def baseStart_3570741 : Nat := 118140960795 + 3570741 * 2 ^ 59
def prefixEnd_3570741 : Nat := 4983230072969 + 3 ^ 40 * 3570741 * 2
def baseEnd_3570741 : Nat := 1833506425716119193115967

theorem tailTrace_3570741 : CollatzResearch.WordTrace tailWord_3570741 prefixEnd_3570741 1833506425716119193115967 := by
  unfold tailWord_3570741
  simp only [CollatzResearch.WordTrace]
  refine ⟨130235623556822665856544077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86823749037881777237696051 130235623556822665856544077)
  ·
    refine ⟨48838358833808499696204029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130235623556822665856544077 48838358833808499696204029)
    ·
      refine ⟨18314384562678187386076511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48838358833808499696204029 18314384562678187386076511)
      ·
        refine ⟨27471576844017281079114767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18314384562678187386076511 27471576844017281079114767)
        ·
          refine ⟨41207365266025921618672151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27471576844017281079114767 41207365266025921618672151)
          ·
            refine ⟨61811047899038882428008227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41207365266025921618672151 61811047899038882428008227)
            ·
              refine ⟨92716571848558323642012341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61811047899038882428008227 92716571848558323642012341)
              ·
                refine ⟨8692178610802342841438657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 92716571848558323642012341 8692178610802342841438657)
                ·
                  refine ⟨6519133958101757131078993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8692178610802342841438657 6519133958101757131078993)
                  ·
                    refine ⟨4889350468576317848309245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6519133958101757131078993 4889350468576317848309245)
                    ·
                      refine ⟨1833506425716119193115967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4889350468576317848309245 1833506425716119193115967)
                      ·
                        rfl

theorem cell23_3570741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 5, 2, 2, 3].length) (baseStart_3570741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3570741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3570741 prefixEnd_3570741 := by exact prefixLift 3570741
  have htrace : WordTrace (prefixWord ++ tailWord_3570741) baseStart_3570741 baseEnd_3570741 := by
    simpa [prefixWord, tailWord_3570741, baseEnd_3570741] using wordTrace_append hprefix tailTrace_3570741
  have hstable : (prefixWord ++ tailWord_3570741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3570741).length < 2 ^ (prefixWord ++ tailWord_3570741).sum := by decide
  have hdescent : baseEnd_3570741 < baseStart_3570741 := by decide
  rcases family_descends (prefixWord ++ tailWord_3570741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3570744 : List Nat := [2, 1, 2, 1, 5, 1, 1, 2, 8]
def baseStart_3570744 : Nat := 118140960795 + 3570744 * 2 ^ 59
def prefixEnd_3570744 : Nat := 4983230072969 + 3 ^ 40 * 3570744 * 2
def baseEnd_3570744 : Nat := 203723107350898075708717

theorem tailTrace_3570744 : CollatzResearch.WordTrace tailWord_3570744 prefixEnd_3570744 203723107350898075708717 := by
  unfold tailWord_3570744
  simp only [CollatzResearch.WordTrace]
  refine ⟨65117866487905898684451643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86823821983874531579268857 65117866487905898684451643)
  ·
    refine ⟨97676799731858848026677465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65117866487905898684451643 97676799731858848026677465)
    ·
      refine ⟨73257599798894136020008099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97676799731858848026677465 73257599798894136020008099)
      ·
        refine ⟨109886399698341204030012149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73257599798894136020008099 109886399698341204030012149)
        ·
          refine ⟨10301849971719487877813639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 109886399698341204030012149 10301849971719487877813639)
          ·
            refine ⟨15452774957579231816720459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10301849971719487877813639 15452774957579231816720459)
            ·
              refine ⟨23179162436368847725080689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15452774957579231816720459 23179162436368847725080689)
              ·
                refine ⟨17384371827276635793810517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23179162436368847725080689 17384371827276635793810517)
                ·
                  refine ⟨203723107350898075708717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 17384371827276635793810517 203723107350898075708717)
                  ·
                    rfl

theorem cell23_3570744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 1, 2, 8].length) (baseStart_3570744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3570744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3570744 prefixEnd_3570744 := by exact prefixLift 3570744
  have htrace : WordTrace (prefixWord ++ tailWord_3570744) baseStart_3570744 baseEnd_3570744 := by
    simpa [prefixWord, tailWord_3570744, baseEnd_3570744] using wordTrace_append hprefix tailTrace_3570744
  have hstable : (prefixWord ++ tailWord_3570744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3570744).length < 2 ^ (prefixWord ++ tailWord_3570744).sum := by decide
  have hdescent : baseEnd_3570744 < baseStart_3570744 := by decide
  rcases family_descends (prefixWord ++ tailWord_3570744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3570765 : List Nat := [1, 6, 1, 1, 1, 4, 1, 1, 3, 4]
def baseStart_3570765 : Nat := 118140960795 + 3570765 * 2 ^ 59
def prefixEnd_3570765 : Nat := 4983230072969 + 3 ^ 40 * 3570765 * 2
def baseEnd_3570765 : Nat := 611172916417275699738619

theorem tailTrace_3570765 : CollatzResearch.WordTrace tailWord_3570765 prefixEnd_3570765 611172916417275699738619 := by
  unfold tailWord_3570765
  simp only [CollatzResearch.WordTrace]
  refine ⟨130236498908735717955417749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86824332605823811970278499 130236498908735717955417749)
  ·
    refine ⟨6104835886346986779160207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 130236498908735717955417749 6104835886346986779160207)
    ·
      refine ⟨9157253829520480168740311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6104835886346986779160207 9157253829520480168740311)
      ·
        refine ⟨13735880744280720253110467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9157253829520480168740311 13735880744280720253110467)
        ·
          refine ⟨20603821116421080379665701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13735880744280720253110467 20603821116421080379665701)
          ·
            refine ⟨3863216459328952571187319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20603821116421080379665701 3863216459328952571187319)
            ·
              refine ⟨5794824688993428856780979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3863216459328952571187319 5794824688993428856780979)
              ·
                refine ⟨8692237033490143285171469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5794824688993428856780979 8692237033490143285171469)
                ·
                  refine ⟨3259588887558803731939301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8692237033490143285171469 3259588887558803731939301)
                  ·
                    refine ⟨611172916417275699738619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3259588887558803731939301 611172916417275699738619)
                    ·
                      rfl

theorem cell23_3570765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 4, 1, 1, 3, 4].length) (baseStart_3570765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3570765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3570765 prefixEnd_3570765 := by exact prefixLift 3570765
  have htrace : WordTrace (prefixWord ++ tailWord_3570765) baseStart_3570765 baseEnd_3570765 := by
    simpa [prefixWord, tailWord_3570765, baseEnd_3570765] using wordTrace_append hprefix tailTrace_3570765
  have hstable : (prefixWord ++ tailWord_3570765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3570765).length < 2 ^ (prefixWord ++ tailWord_3570765).sum := by decide
  have hdescent : baseEnd_3570765 < baseStart_3570765 := by decide
  rcases family_descends (prefixWord ++ tailWord_3570765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3570791 : List Nat := [1, 1, 5, 1, 1, 4, 1, 1, 3, 5]
def baseStart_3570791 : Nat := 118140960795 + 3570791 * 2 ^ 59
def prefixEnd_3570791 : Nat := 4983230072969 + 3 ^ 40 * 3570791 * 2
def baseEnd_3570791 : Nat := 611177366582947999163579

theorem tailTrace_3570791 : CollatzResearch.WordTrace tailWord_3570791 prefixEnd_3570791 611177366582947999163579 := by
  unfold tailWord_3570791
  simp only [CollatzResearch.WordTrace]
  refine ⟨130237447206641524395864227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86824964804427682930576151 130237447206641524395864227)
  ·
    refine ⟨195356170809962286593796341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130237447206641524395864227 195356170809962286593796341)
    ·
      refine ⟨18314641013433964368168407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 195356170809962286593796341 18314641013433964368168407)
      ·
        refine ⟨27471961520150946552252611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18314641013433964368168407 27471961520150946552252611)
        ·
          refine ⟨41207942280226419828378917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27471961520150946552252611 41207942280226419828378917)
          ·
            refine ⟨7726489177542453717821047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41207942280226419828378917 7726489177542453717821047)
            ·
              refine ⟨11589733766313680576731571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7726489177542453717821047 11589733766313680576731571)
              ·
                refine ⟨17384600649470520865097357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11589733766313680576731571 17384600649470520865097357)
                ·
                  refine ⟨6519225243551445324411509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17384600649470520865097357 6519225243551445324411509)
                  ·
                    refine ⟨611177366582947999163579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6519225243551445324411509 611177366582947999163579)
                    ·
                      rfl

theorem cell23_3570791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 1, 1, 3, 5].length) (baseStart_3570791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3570791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3570791 prefixEnd_3570791 := by exact prefixLift 3570791
  have htrace : WordTrace (prefixWord ++ tailWord_3570791) baseStart_3570791 baseEnd_3570791 := by
    simpa [prefixWord, tailWord_3570791, baseEnd_3570791] using wordTrace_append hprefix tailTrace_3570791
  have hstable : (prefixWord ++ tailWord_3570791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3570791).length < 2 ^ (prefixWord ++ tailWord_3570791).sum := by decide
  have hdescent : baseEnd_3570791 < baseStart_3570791 := by decide
  rcases family_descends (prefixWord ++ tailWord_3570791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3570811 : List Nat := [1, 1, 1, 1, 1, 4, 1, 7, 1, 1, 4]
def baseStart_3570811 : Nat := 118140960795 + 3570811 * 2 ^ 59
def prefixEnd_3570811 : Nat := 4983230072969 + 3 ^ 40 * 3570811 * 2
def baseEnd_3570811 : Nat := 1833542369361933919240645

theorem tailTrace_3570811 : CollatzResearch.WordTrace tailWord_3570811 prefixEnd_3570811 1833542369361933919240645 := by
  unfold tailWord_3570811
  simp only [CollatzResearch.WordTrace]
  refine ⟨130238176666569067811592287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86825451111046045207728191 130238176666569067811592287)
  ·
    refine ⟨195357264999853601717388431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130238176666569067811592287 195357264999853601717388431)
    ·
      refine ⟨293035897499780402576082647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195357264999853601717388431 293035897499780402576082647)
      ·
        refine ⟨439553846249670603864123971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 293035897499780402576082647 439553846249670603864123971)
        ·
          refine ⟨659330769374505905796185957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 439553846249670603864123971 659330769374505905796185957)
          ·
            refine ⟨123624519257719857336784867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 659330769374505905796185957 123624519257719857336784867)
            ·
              refine ⟨185436778886579786005177301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 123624519257719857336784867 185436778886579786005177301)
              ·
                refine ⟨4346174505154213734496343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 185436778886579786005177301 4346174505154213734496343)
                ·
                  refine ⟨6519261757731320601744515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4346174505154213734496343 6519261757731320601744515)
                  ·
                    refine ⟨9778892636596980902616773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6519261757731320601744515 9778892636596980902616773)
                    ·
                      refine ⟨1833542369361933919240645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9778892636596980902616773 1833542369361933919240645)
                      ·
                        rfl

theorem cell23_3570811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 7, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 7, 1, 1, 4].length) (baseStart_3570811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3570811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3570811 prefixEnd_3570811 := by exact prefixLift 3570811
  have htrace : WordTrace (prefixWord ++ tailWord_3570811) baseStart_3570811 baseEnd_3570811 := by
    simpa [prefixWord, tailWord_3570811, baseEnd_3570811] using wordTrace_append hprefix tailTrace_3570811
  have hstable : (prefixWord ++ tailWord_3570811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3570811).length < 2 ^ (prefixWord ++ tailWord_3570811).sum := by decide
  have hdescent : baseEnd_3570811 < baseStart_3570811 := by decide
  rcases family_descends (prefixWord ++ tailWord_3570811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3570828 : List Nat := [2, 2, 1, 2, 1, 1, 1, 2, 7, 2, 2]
def baseStart_3570828 : Nat := 118140960795 + 3570828 * 2 ^ 59
def prefixEnd_3570828 : Nat := 4983230072969 + 3 ^ 40 * 3570828 * 2
def baseEnd_3570828 : Nat := 1833551098533060352728067

theorem tailTrace_3570828 : CollatzResearch.WordTrace tailWord_3570828 prefixEnd_3570828 1833551098533060352728067 := by
  unfold tailWord_3570828
  simp only [CollatzResearch.WordTrace]
  refine ⟨65119398353753739857480569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86825864471671653143307425 65119398353753739857480569)
  ·
    refine ⟨48839548765315304893110427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65119398353753739857480569 48839548765315304893110427)
    ·
      refine ⟨73259323147972957339665641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48839548765315304893110427 73259323147972957339665641)
      ·
        refine ⟨54944492360979718004749231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73259323147972957339665641 54944492360979718004749231)
        ·
          refine ⟨82416738541469577007123847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54944492360979718004749231 82416738541469577007123847)
          ·
            refine ⟨123625107812204365510685771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82416738541469577007123847 123625107812204365510685771)
            ·
              refine ⟨185437661718306548266028657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 123625107812204365510685771 185437661718306548266028657)
              ·
                refine ⟨139078246288729911199521493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 185437661718306548266028657 139078246288729911199521493)
                ·
                  refine ⟨3259646397392107293738785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 139078246288729911199521493 3259646397392107293738785)
                  ·
                    refine ⟨2444734798044080470304089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3259646397392107293738785 2444734798044080470304089)
                    ·
                      refine ⟨1833551098533060352728067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2444734798044080470304089 1833551098533060352728067)
                      ·
                        rfl

theorem cell23_3570828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 7, 2, 2].length) (baseStart_3570828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3570828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3570828 prefixEnd_3570828 := by exact prefixLift 3570828
  have htrace : WordTrace (prefixWord ++ tailWord_3570828) baseStart_3570828 baseEnd_3570828 := by
    simpa [prefixWord, tailWord_3570828, baseEnd_3570828] using wordTrace_append hprefix tailTrace_3570828
  have hstable : (prefixWord ++ tailWord_3570828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3570828).length < 2 ^ (prefixWord ++ tailWord_3570828).sum := by decide
  have hdescent : baseEnd_3570828 < baseStart_3570828 := by decide
  rcases family_descends (prefixWord ++ tailWord_3570828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3570845 : List Nat := [1, 4, 2, 1, 1, 2, 3, 2, 3, 2, 2]
def baseStart_3570845 : Nat := 118140960795 + 3570845 * 2 ^ 59
def prefixEnd_3570845 : Nat := 4983230072969 + 3 ^ 40 * 3570845 * 2
def baseEnd_3570845 : Nat := 1833559827704186786215489

theorem tailTrace_3570845 : CollatzResearch.WordTrace tailWord_3570845 prefixEnd_3570845 1833559827704186786215489 := by
  unfold tailWord_3570845
  simp only [CollatzResearch.WordTrace]
  refine ⟨130239416748445891618329989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86826277832297261078886659 130239416748445891618329989)
  ·
    refine ⟨24419890640333604678436873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 130239416748445891618329989 24419890640333604678436873)
    ·
      refine ⟨18314917980250203508827655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24419890640333604678436873 18314917980250203508827655)
      ·
        refine ⟨27472376970375305263241483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18314917980250203508827655 27472376970375305263241483)
        ·
          refine ⟨41208565455562957894862225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27472376970375305263241483 41208565455562957894862225)
          ·
            refine ⟨30906424091672218421146669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41208565455562957894862225 30906424091672218421146669)
            ·
              refine ⟨11589909034377081907930001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30906424091672218421146669 11589909034377081907930001)
              ·
                refine ⟨8692431775782811430947501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11589909034377081907930001 8692431775782811430947501)
                ·
                  refine ⟨3259661915918554286605313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8692431775782811430947501 3259661915918554286605313)
                  ·
                    refine ⟨2444746436938915714953985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3259661915918554286605313 2444746436938915714953985)
                    ·
                      refine ⟨1833559827704186786215489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2444746436938915714953985 1833559827704186786215489)
                      ·
                        rfl

theorem cell23_3570845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 3, 2, 3, 2, 2].length) (baseStart_3570845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3570845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3570845 prefixEnd_3570845 := by exact prefixLift 3570845
  have htrace : WordTrace (prefixWord ++ tailWord_3570845) baseStart_3570845 baseEnd_3570845 := by
    simpa [prefixWord, tailWord_3570845, baseEnd_3570845] using wordTrace_append hprefix tailTrace_3570845
  have hstable : (prefixWord ++ tailWord_3570845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3570845).length < 2 ^ (prefixWord ++ tailWord_3570845).sum := by decide
  have hdescent : baseEnd_3570845 < baseStart_3570845 := by decide
  rcases family_descends (prefixWord ++ tailWord_3570845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3570848 : List Nat := [2, 1, 1, 4, 2, 1, 2, 4, 1, 2, 3]
def baseStart_3570848 : Nat := 118140960795 + 3570848 * 2 ^ 59
def prefixEnd_3570848 : Nat := 4983230072969 + 3 ^ 40 * 3570848 * 2
def baseEnd_3570848 : Nat := 1833561368146150274477975

theorem tailTrace_3570848 : CollatzResearch.WordTrace tailWord_3570848 prefixEnd_3570848 1833561368146150274477975 := by
  unfold tailWord_3570848
  simp only [CollatzResearch.WordTrace]
  refine ⟨65119763083717511565344599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86826350778290015420459465 65119763083717511565344599)
  ·
    refine ⟨97679644625576267348016899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65119763083717511565344599 97679644625576267348016899)
    ·
      refine ⟨146519466938364401022025349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97679644625576267348016899 146519466938364401022025349)
      ·
        refine ⟨27472400050943325191629753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 146519466938364401022025349 27472400050943325191629753)
        ·
          refine ⟨20604300038207493893722315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27472400050943325191629753 20604300038207493893722315)
          ·
            refine ⟨30906450057311240840583473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20604300038207493893722315 30906450057311240840583473)
            ·
              refine ⟨23179837542983430630437605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30906450057311240840583473 23179837542983430630437605)
              ·
                refine ⟨4346219539309393243207051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23179837542983430630437605 4346219539309393243207051)
                ·
                  refine ⟨6519329308964089864810577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4346219539309393243207051 6519329308964089864810577)
                  ·
                    refine ⟨4889496981723067398607933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6519329308964089864810577 4889496981723067398607933)
                    ·
                      refine ⟨1833561368146150274477975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4889496981723067398607933 1833561368146150274477975)
                      ·
                        rfl

theorem cell23_3570848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 2, 4, 1, 2, 3].length) (baseStart_3570848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3570848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3570848 prefixEnd_3570848 := by exact prefixLift 3570848
  have htrace : WordTrace (prefixWord ++ tailWord_3570848) baseStart_3570848 baseEnd_3570848 := by
    simpa [prefixWord, tailWord_3570848, baseEnd_3570848] using wordTrace_append hprefix tailTrace_3570848
  have hstable : (prefixWord ++ tailWord_3570848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3570848).length < 2 ^ (prefixWord ++ tailWord_3570848).sum := by decide
  have hdescent : baseEnd_3570848 < baseStart_3570848 := by decide
  rcases family_descends (prefixWord ++ tailWord_3570848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3570864 : List Nat := [2, 1, 1, 1, 2, 1, 2, 2, 4, 7]
def baseStart_3570864 : Nat := 118140960795 + 3570864 * 2 ^ 59
def prefixEnd_3570864 : Nat := 4983230072969 + 3 ^ 40 * 3570864 * 2
def baseEnd_3570864 : Nat := 611189861278874070625967

theorem tailTrace_3570864 : CollatzResearch.WordTrace tailWord_3570864 prefixEnd_3570864 611189861278874070625967 := by
  unfold tailWord_3570864
  simp only [CollatzResearch.WordTrace]
  refine ⟨65120054867688528931635823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86826739823584705242181097 65120054867688528931635823)
  ·
    refine ⟨97680082301532793397453735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65120054867688528931635823 97680082301532793397453735)
    ·
      refine ⟨146520123452299190096180603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97680082301532793397453735 146520123452299190096180603)
      ·
        refine ⟨219780185178448785144270905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146520123452299190096180603 219780185178448785144270905)
        ·
          refine ⟨164835138883836588858203179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 219780185178448785144270905 164835138883836588858203179)
          ·
            refine ⟨247252708325754883287304769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 164835138883836588858203179 247252708325754883287304769)
            ·
              refine ⟨185439531244316162465478577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 247252708325754883287304769 185439531244316162465478577)
              ·
                refine ⟨139079648433237121849108933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 185439531244316162465478577 139079648433237121849108933)
                ·
                  refine ⟨26077434081231960346707925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 139079648433237121849108933 26077434081231960346707925)
                  ·
                    refine ⟨611189861278874070625967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 26077434081231960346707925 611189861278874070625967)
                    ·
                      rfl

theorem cell23_3570864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 2, 4, 7].length) (baseStart_3570864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3570864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3570864 prefixEnd_3570864 := by exact prefixLift 3570864
  have htrace : WordTrace (prefixWord ++ tailWord_3570864) baseStart_3570864 baseEnd_3570864 := by
    simpa [prefixWord, tailWord_3570864, baseEnd_3570864] using wordTrace_append hprefix tailTrace_3570864
  have hstable : (prefixWord ++ tailWord_3570864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3570864).length < 2 ^ (prefixWord ++ tailWord_3570864).sum := by decide
  have hdescent : baseEnd_3570864 < baseStart_3570864 := by decide
  rcases family_descends (prefixWord ++ tailWord_3570864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3570865 : List Nat := [1, 2, 2, 5, 1, 2, 1, 3, 1, 2, 3]
def baseStart_3570865 : Nat := 118140960795 + 3570865 * 2 ^ 59
def prefixEnd_3570865 : Nat := 4983230072969 + 3 ^ 40 * 3570865 * 2
def baseEnd_3570865 : Nat := 1833570097317276707965397

theorem tailTrace_3570865 : CollatzResearch.WordTrace tailWord_3570865 prefixEnd_3570865 1833570097317276707965397 := by
  unfold tailWord_3570865
  simp only [CollatzResearch.WordTrace]
  refine ⟨130240146208373435034058049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86826764138915623356038699 130240146208373435034058049)
  ·
    refine ⟨97680109656280076275543537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130240146208373435034058049 97680109656280076275543537)
    ·
      refine ⟨73260082242210057206657653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97680109656280076275543537 73260082242210057206657653)
      ·
        refine ⟨6868132710207192863124155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 73260082242210057206657653 6868132710207192863124155)
        ·
          refine ⟨10302199065310789294686233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6868132710207192863124155 10302199065310789294686233)
          ·
            refine ⟨7726649298983091971014675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10302199065310789294686233 7726649298983091971014675)
            ·
              refine ⟨11589973948474637956522013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7726649298983091971014675 11589973948474637956522013)
              ·
                refine ⟨4346240230677989233695755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11589973948474637956522013 4346240230677989233695755)
                ·
                  refine ⟨6519360346016983850543633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4346240230677989233695755 6519360346016983850543633)
                  ·
                    refine ⟨4889520259512737887907725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6519360346016983850543633 4889520259512737887907725)
                    ·
                      refine ⟨1833570097317276707965397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4889520259512737887907725 1833570097317276707965397)
                      ·
                        rfl

theorem cell23_3570865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 1, 3, 1, 2, 3].length) (baseStart_3570865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3570865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3570865 prefixEnd_3570865 := by exact prefixLift 3570865
  have htrace : WordTrace (prefixWord ++ tailWord_3570865) baseStart_3570865 baseEnd_3570865 := by
    simpa [prefixWord, tailWord_3570865, baseEnd_3570865] using wordTrace_append hprefix tailTrace_3570865
  have hstable : (prefixWord ++ tailWord_3570865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3570865).length < 2 ^ (prefixWord ++ tailWord_3570865).sum := by decide
  have hdescent : baseEnd_3570865 < baseStart_3570865 := by decide
  rcases family_descends (prefixWord ++ tailWord_3570865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3570882 : List Nat := [3, 5, 1, 1, 2, 1, 1, 2, 1, 1, 5]
def baseStart_3570882 : Nat := 118140960795 + 3570882 * 2 ^ 59
def prefixEnd_3570882 : Nat := 4983230072969 + 3 ^ 40 * 3570882 * 2
def baseEnd_3570882 : Nat := 1833578826488403141452819

theorem tailTrace_3570882 : CollatzResearch.WordTrace tailWord_3570882 prefixEnd_3570882 1833578826488403141452819 := by
  unfold tailWord_3570882
  simp only [CollatzResearch.WordTrace]
  refine ⟨32560191562327961734356725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86827177499541231291617933 32560191562327961734356725)
  ·
    refine ⟨3052517958968246412595943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 32560191562327961734356725 3052517958968246412595943)
    ·
      refine ⟨4578776938452369618893915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3052517958968246412595943 4578776938452369618893915)
      ·
        refine ⟨6868165407678554428340873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4578776938452369618893915 6868165407678554428340873)
        ·
          refine ⟨5151124055758915821255655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6868165407678554428340873 5151124055758915821255655)
          ·
            refine ⟨7726686083638373731883483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5151124055758915821255655 7726686083638373731883483)
            ·
              refine ⟨11590029125457560597825225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7726686083638373731883483 11590029125457560597825225)
              ·
                refine ⟨8692521844093170448368919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11590029125457560597825225 8692521844093170448368919)
                ·
                  refine ⟨13038782766139755672553379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8692521844093170448368919 13038782766139755672553379)
                  ·
                    refine ⟨19558174149209633508830069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13038782766139755672553379 19558174149209633508830069)
                    ·
                      refine ⟨1833578826488403141452819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19558174149209633508830069 1833578826488403141452819)
                      ·
                        rfl

theorem cell23_3570882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 1, 2, 1, 1, 5].length) (baseStart_3570882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3570882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3570882 prefixEnd_3570882 := by exact prefixLift 3570882
  have htrace : WordTrace (prefixWord ++ tailWord_3570882) baseStart_3570882 baseEnd_3570882 := by
    simpa [prefixWord, tailWord_3570882, baseEnd_3570882] using wordTrace_append hprefix tailTrace_3570882
  have hstable : (prefixWord ++ tailWord_3570882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3570882).length < 2 ^ (prefixWord ++ tailWord_3570882).sum := by decide
  have hdescent : baseEnd_3570882 < baseStart_3570882 := by decide
  rcases family_descends (prefixWord ++ tailWord_3570882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3570888 : List Nat := [2, 1, 3, 1, 2, 1, 2, 1, 5, 3, 2]
def baseStart_3570888 : Nat := 118140960795 + 3570888 * 2 ^ 59
def prefixEnd_3570888 : Nat := 4983230072969 + 3 ^ 40 * 3570888 * 2
def baseEnd_3570888 : Nat := 1833581907372330117977791

theorem tailTrace_3570888 : CollatzResearch.WordTrace tailWord_3570888 prefixEnd_3570888 1833581907372330117977791 := by
  unfold tailWord_3570888
  simp only [CollatzResearch.WordTrace]
  refine ⟨65120492543645054981072659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86827323391526739974763545 65120492543645054981072659)
  ·
    refine ⟨97680738815467582471608989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65120492543645054981072659 97680738815467582471608989)
    ·
      refine ⟨36630277055800343426853371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 97680738815467582471608989 36630277055800343426853371)
      ·
        refine ⟨54945415583700515140280057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36630277055800343426853371 54945415583700515140280057)
        ·
          refine ⟨41209061687775386355210043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54945415583700515140280057 41209061687775386355210043)
          ·
            refine ⟨61813592531663079532815065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41209061687775386355210043 61813592531663079532815065)
            ·
              refine ⟨46360194398747309649611299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61813592531663079532815065 46360194398747309649611299)
              ·
                refine ⟨69540291598120964474416949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46360194398747309649611299 69540291598120964474416949)
                ·
                  refine ⟨6519402337323840419476589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 69540291598120964474416949 6519402337323840419476589)
                  ·
                    refine ⟨2444775876496440157303721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6519402337323840419476589 2444775876496440157303721)
                    ·
                      refine ⟨1833581907372330117977791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2444775876496440157303721 1833581907372330117977791)
                      ·
                        rfl

theorem cell23_3570888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 1, 5, 3, 2].length) (baseStart_3570888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3570888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3570888 prefixEnd_3570888 := by exact prefixLift 3570888
  have htrace : WordTrace (prefixWord ++ tailWord_3570888) baseStart_3570888 baseEnd_3570888 := by
    simpa [prefixWord, tailWord_3570888, baseEnd_3570888] using wordTrace_append hprefix tailTrace_3570888
  have hstable : (prefixWord ++ tailWord_3570888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3570888).length < 2 ^ (prefixWord ++ tailWord_3570888).sum := by decide
  have hdescent : baseEnd_3570888 < baseStart_3570888 := by decide
  rcases family_descends (prefixWord ++ tailWord_3570888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3570902 : List Nat := [5, 2, 1, 2, 2, 2, 2, 7]
def baseStart_3570902 : Nat := 118140960795 + 3570902 * 2 ^ 59
def prefixEnd_3570902 : Nat := 4983230072969 + 3 ^ 40 * 3570902 * 2
def baseEnd_3570902 : Nat := 67910707263018261600101

theorem tailTrace_3570902 : CollatzResearch.WordTrace tailWord_3570902 prefixEnd_3570902 67910707263018261600101 := by
  unfold tailWord_3570902
  simp only [CollatzResearch.WordTrace]
  refine ⟨8140093481827461897072185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 86827663806159593568769973 8140093481827461897072185)
  ·
    refine ⟨6105070111370596422804139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8140093481827461897072185 6105070111370596422804139)
    ·
      refine ⟨9157605167055894634206209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6105070111370596422804139 9157605167055894634206209)
      ·
        refine ⟨6868203875291920975654657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9157605167055894634206209 6868203875291920975654657)
        ·
          refine ⟨5151152906468940731740993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6868203875291920975654657 5151152906468940731740993)
          ·
            refine ⟨3863364679851705548805745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5151152906468940731740993 3863364679851705548805745)
            ·
              refine ⟨2897523509888779161604309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3863364679851705548805745 2897523509888779161604309)
              ·
                refine ⟨67910707263018261600101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2897523509888779161604309 67910707263018261600101)
                ·
                  rfl

theorem cell23_3570902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 2, 2, 7].length) (baseStart_3570902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3570902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3570902 prefixEnd_3570902 := by exact prefixLift 3570902
  have htrace : WordTrace (prefixWord ++ tailWord_3570902) baseStart_3570902 baseEnd_3570902 := by
    simpa [prefixWord, tailWord_3570902, baseEnd_3570902] using wordTrace_append hprefix tailTrace_3570902
  have hstable : (prefixWord ++ tailWord_3570902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3570902).length < 2 ^ (prefixWord ++ tailWord_3570902).sum := by decide
  have hdescent : baseEnd_3570902 < baseStart_3570902 := by decide
  rcases family_descends (prefixWord ++ tailWord_3570902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3570946 : List Nat := [3, 4, 1, 1, 3, 2, 2, 1, 2, 1, 3]
def baseStart_3570946 : Nat := 118140960795 + 3570946 * 2 ^ 59
def prefixEnd_3570946 : Nat := 4983230072969 + 3 ^ 40 * 3570946 * 2
def baseEnd_3570946 : Nat := 1833611689250290891052525

theorem tailTrace_3570946 : CollatzResearch.WordTrace tailWord_3570946 prefixEnd_3570946 1833611689250290891052525 := by
  unfold tailWord_3570946
  simp only [CollatzResearch.WordTrace]
  refine ⟨32560775130269996466939173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86828733680719990578504461 32560775130269996466939173)
  ·
    refine ⟨6105145336925624337551095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32560775130269996466939173 6105145336925624337551095)
    ·
      refine ⟨9157718005388436506326643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6105145336925624337551095 9157718005388436506326643)
      ·
        refine ⟨13736577008082654759489965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9157718005388436506326643 13736577008082654759489965)
        ·
          refine ⟨5151216378030995534808737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13736577008082654759489965 5151216378030995534808737)
          ·
            refine ⟨3863412283523246651106553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5151216378030995534808737 3863412283523246651106553)
            ·
              refine ⟨2897559212642434988329915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3863412283523246651106553 2897559212642434988329915)
              ·
                refine ⟨4346338818963652482494873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2897559212642434988329915 4346338818963652482494873)
                ·
                  refine ⟨3259754114222739361871155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4346338818963652482494873 3259754114222739361871155)
                  ·
                    refine ⟨4889631171334109042806733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3259754114222739361871155 4889631171334109042806733)
                    ·
                      refine ⟨1833611689250290891052525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4889631171334109042806733 1833611689250290891052525)
                      ·
                        rfl

theorem cell23_3570946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 2, 2, 1, 2, 1, 3].length) (baseStart_3570946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3570946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3570946 prefixEnd_3570946 := by exact prefixLift 3570946
  have htrace : WordTrace (prefixWord ++ tailWord_3570946) baseStart_3570946 baseEnd_3570946 := by
    simpa [prefixWord, tailWord_3570946, baseEnd_3570946] using wordTrace_append hprefix tailTrace_3570946
  have hstable : (prefixWord ++ tailWord_3570946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3570946).length < 2 ^ (prefixWord ++ tailWord_3570946).sum := by decide
  have hdescent : baseEnd_3570946 < baseStart_3570946 := by decide
  rcases family_descends (prefixWord ++ tailWord_3570946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3570991 : List Nat := [1, 1, 2, 1, 2, 1, 3, 2, 3, 3, 4]
def baseStart_3570991 : Nat := 118140960795 + 3570991 * 2 ^ 59
def prefixEnd_3570991 : Nat := 4983230072969 + 3 ^ 40 * 3570991 * 2
def baseEnd_3570991 : Nat := 1833634795879743214989817

theorem tailTrace_3570991 : CollatzResearch.WordTrace tailWord_3570991 prefixEnd_3570991 1833634795879743214989817 := by
  unfold tailWord_3570991
  simp only [CollatzResearch.WordTrace]
  refine ⟨130244741805916958553144827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86829827870611305702096551 130244741805916958553144827)
  ·
    refine ⟨195367112708875437829717241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130244741805916958553144827 195367112708875437829717241)
    ·
      refine ⟨146525334531656578372287931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 195367112708875437829717241 146525334531656578372287931)
      ·
        refine ⟨219788001797484867558431897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146525334531656578372287931 219788001797484867558431897)
        ·
          refine ⟨164841001348113650668823923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 219788001797484867558431897 164841001348113650668823923)
          ·
            refine ⟨247261502022170476003235885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 164841001348113650668823923 247261502022170476003235885)
            ·
              refine ⟨92723063258313928501213457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 247261502022170476003235885 92723063258313928501213457)
              ·
                refine ⟨69542297443735446375910093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 92723063258313928501213457 69542297443735446375910093)
                ·
                  refine ⟨26078361541400792390966285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 69542297443735446375910093 26078361541400792390966285)
                  ·
                    refine ⟨9779385578025297146612357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26078361541400792390966285 9779385578025297146612357)
                    ·
                      refine ⟨1833634795879743214989817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9779385578025297146612357 1833634795879743214989817)
                      ·
                        rfl

theorem cell23_3570991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 2, 3, 3, 4].length) (baseStart_3570991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3570991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3570991 prefixEnd_3570991 := by exact prefixLift 3570991
  have htrace : WordTrace (prefixWord ++ tailWord_3570991) baseStart_3570991 baseEnd_3570991 := by
    simpa [prefixWord, tailWord_3570991, baseEnd_3570991] using wordTrace_append hprefix tailTrace_3570991
  have hstable : (prefixWord ++ tailWord_3570991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3570991).length < 2 ^ (prefixWord ++ tailWord_3570991).sum := by decide
  have hdescent : baseEnd_3570991 < baseStart_3570991 := by decide
  rcases family_descends (prefixWord ++ tailWord_3570991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3571052 : List Nat := [2, 2, 1, 1, 5, 1, 2, 4, 1, 4]
def baseStart_3571052 : Nat := 118140960795 + 3571052 * 2 ^ 59
def prefixEnd_3571052 : Nat := 4983230072969 + 3 ^ 40 * 3571052 * 2
def baseEnd_3571052 : Nat := 611222039399889158775679

theorem tailTrace_3571052 : CollatzResearch.WordTrace tailWord_3571052 prefixEnd_3571052 611222039399889158775679 := by
  unfold tailWord_3571052
  simp only [CollatzResearch.WordTrace]
  refine ⟨65123483329347982985557705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86831311105797310647410273 65123483329347982985557705)
  ·
    refine ⟨48842612497010987239168279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65123483329347982985557705 48842612497010987239168279)
    ·
      refine ⟨73263918745516480858752419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48842612497010987239168279 73263918745516480858752419)
      ·
        refine ⟨109895878118274721288128629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73263918745516480858752419 109895878118274721288128629)
        ·
          refine ⟨10302738573588255120762059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 109895878118274721288128629 10302738573588255120762059)
          ·
            refine ⟨15454107860382382681143089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10302738573588255120762059 15454107860382382681143089)
            ·
              refine ⟨11590580895286787010857317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15454107860382382681143089 11590580895286787010857317)
              ·
                refine ⟨2173233917866272564535747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11590580895286787010857317 2173233917866272564535747)
                ·
                  refine ⟨3259850876799408846803621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2173233917866272564535747 3259850876799408846803621)
                  ·
                    refine ⟨611222039399889158775679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3259850876799408846803621 611222039399889158775679)
                    ·
                      rfl

theorem cell23_3571052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 2, 4, 1, 4].length) (baseStart_3571052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3571052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3571052 prefixEnd_3571052 := by exact prefixLift 3571052
  have htrace : WordTrace (prefixWord ++ tailWord_3571052) baseStart_3571052 baseEnd_3571052 := by
    simpa [prefixWord, tailWord_3571052, baseEnd_3571052] using wordTrace_append hprefix tailTrace_3571052
  have hstable : (prefixWord ++ tailWord_3571052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3571052).length < 2 ^ (prefixWord ++ tailWord_3571052).sum := by decide
  have hdescent : baseEnd_3571052 < baseStart_3571052 := by decide
  rcases family_descends (prefixWord ++ tailWord_3571052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3571086 : List Nat := [4, 1, 1, 4, 2, 2, 1, 3, 1, 4]
def baseStart_3571086 : Nat := 118140960795 + 3571086 * 2 ^ 59
def prefixEnd_3571086 : Nat := 4983230072969 + 3 ^ 40 * 3571086 * 2
def baseEnd_3571086 : Nat := 611227858847306781100627

theorem tailTrace_3571086 : CollatzResearch.WordTrace tailWord_3571086 prefixEnd_3571086 611227858847306781100627 := by
  unfold tailWord_3571086
  simp only [CollatzResearch.WordTrace]
  refine ⟨16281025842571598722231639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 86832137827048526518568741 16281025842571598722231639)
  ·
    refine ⟨24421538763857398083347459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16281025842571598722231639 24421538763857398083347459)
    ·
      refine ⟨36632308145786097125021189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24421538763857398083347459 36632308145786097125021189)
      ·
        refine ⟨6868557777334893210941473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36632308145786097125021189 6868557777334893210941473)
        ·
          refine ⟨5151418333001169908206105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6868557777334893210941473 5151418333001169908206105)
          ·
            refine ⟨3863563749750877431154579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5151418333001169908206105 3863563749750877431154579)
            ·
              refine ⟨5795345624626316146731869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3863563749750877431154579 5795345624626316146731869)
              ·
                refine ⟨2173254609234868555024451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5795345624626316146731869 2173254609234868555024451)
                ·
                  refine ⟨3259881913852302832536677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2173254609234868555024451 3259881913852302832536677)
                  ·
                    refine ⟨611227858847306781100627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3259881913852302832536677 611227858847306781100627)
                    ·
                      rfl

theorem cell23_3571086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 2, 1, 3, 1, 4].length) (baseStart_3571086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3571086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3571086 prefixEnd_3571086 := by exact prefixLift 3571086
  have htrace : WordTrace (prefixWord ++ tailWord_3571086) baseStart_3571086 baseEnd_3571086 := by
    simpa [prefixWord, tailWord_3571086, baseEnd_3571086] using wordTrace_append hprefix tailTrace_3571086
  have hstable : (prefixWord ++ tailWord_3571086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3571086).length < 2 ^ (prefixWord ++ tailWord_3571086).sum := by decide
  have hdescent : baseEnd_3571086 < baseStart_3571086 := by decide
  rcases family_descends (prefixWord ++ tailWord_3571086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3571128 : List Nat := [2, 1, 2, 1, 2, 2, 4, 1, 1, 1, 6]
def baseStart_3571128 : Nat := 118140960795 + 3571128 * 2 ^ 59
def prefixEnd_3571128 : Nat := 4983230072969 + 3 ^ 40 * 3571128 * 2
def baseEnd_3571128 : Nat := 1833705142729409178976687

theorem tailTrace_3571128 : CollatzResearch.WordTrace tailWord_3571128 prefixEnd_3571128 1833705142729409178976687 := by
  unfold tailWord_3571128
  simp only [CollatzResearch.WordTrace]
  refine ⟨65124869303210315475441019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86833159070947087300588025 65124869303210315475441019)
  ·
    refine ⟨97687303954815473213161529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65124869303210315475441019 97687303954815473213161529)
    ·
      refine ⟨73265477966111604909871147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97687303954815473213161529 73265477966111604909871147)
      ·
        refine ⟨109898216949167407364806721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73265477966111604909871147 109898216949167407364806721)
        ·
          refine ⟨82423662711875555523605041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109898216949167407364806721 82423662711875555523605041)
          ·
            refine ⟨61817747033906666642703781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82423662711875555523605041 61817747033906666642703781)
            ·
              refine ⟨11590827568857499995506959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 61817747033906666642703781 11590827568857499995506959)
              ·
                refine ⟨17386241353286249993260439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11590827568857499995506959 17386241353286249993260439)
                ·
                  refine ⟨26079362029929374989890659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17386241353286249993260439 26079362029929374989890659)
                  ·
                    refine ⟨39119043044894062484835989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26079362029929374989890659 39119043044894062484835989)
                    ·
                      refine ⟨1833705142729409178976687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 39119043044894062484835989 1833705142729409178976687)
                      ·
                        rfl

theorem cell23_3571128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 4, 1, 1, 1, 6].length) (baseStart_3571128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3571128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3571128 prefixEnd_3571128 := by exact prefixLift 3571128
  have htrace : WordTrace (prefixWord ++ tailWord_3571128) baseStart_3571128 baseEnd_3571128 := by
    simpa [prefixWord, tailWord_3571128, baseEnd_3571128] using wordTrace_append hprefix tailTrace_3571128
  have hstable : (prefixWord ++ tailWord_3571128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3571128).length < 2 ^ (prefixWord ++ tailWord_3571128).sum := by decide
  have hdescent : baseEnd_3571128 < baseStart_3571128 := by decide
  rcases family_descends (prefixWord ++ tailWord_3571128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3571129 : List Nat := [1, 2, 1, 4, 5, 1, 1, 2, 1, 5]
def baseStart_3571129 : Nat := 118140960795 + 3571129 * 2 ^ 59
def prefixEnd_3571129 : Nat := 4983230072969 + 3 ^ 40 * 3571129 * 2
def baseEnd_3571129 : Nat := 611235218736687891688061

theorem tailTrace_3571129 : CollatzResearch.WordTrace tailWord_3571129 prefixEnd_3571129 611235218736687891688061 := by
  unfold tailWord_3571129
  simp only [CollatzResearch.WordTrace]
  refine ⟨130249775079417008121668441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86833183386278005414445627 130249775079417008121668441)
  ·
    refine ⟨97687331309562756091251331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130249775079417008121668441 97687331309562756091251331)
    ·
      refine ⟨146530996964344134136876997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97687331309562756091251331 146530996964344134136876997)
      ·
        refine ⟨27474561930814525150664437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 146530996964344134136876997 27474561930814525150664437)
        ·
          refine ⟨2575740181013861732874791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 27474561930814525150664437 2575740181013861732874791)
          ·
            refine ⟨3863610271520792599312187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2575740181013861732874791 3863610271520792599312187)
            ·
              refine ⟨5795415407281188898968281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3863610271520792599312187 5795415407281188898968281)
              ·
                refine ⟨4346561555460891674226211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5795415407281188898968281 4346561555460891674226211)
                ·
                  refine ⟨6519842333191337511339317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4346561555460891674226211 6519842333191337511339317)
                  ·
                    refine ⟨611235218736687891688061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6519842333191337511339317 611235218736687891688061)
                    ·
                      rfl

theorem cell23_3571129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 5, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 5, 1, 1, 2, 1, 5].length) (baseStart_3571129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3571129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3571129 prefixEnd_3571129 := by exact prefixLift 3571129
  have htrace : WordTrace (prefixWord ++ tailWord_3571129) baseStart_3571129 baseEnd_3571129 := by
    simpa [prefixWord, tailWord_3571129, baseEnd_3571129] using wordTrace_append hprefix tailTrace_3571129
  have hstable : (prefixWord ++ tailWord_3571129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3571129).length < 2 ^ (prefixWord ++ tailWord_3571129).sum := by decide
  have hdescent : baseEnd_3571129 < baseStart_3571129 := by decide
  rcases family_descends (prefixWord ++ tailWord_3571129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3571132 : List Nat := [2, 2, 2, 4, 2, 1, 1, 1, 3, 1, 4]
def baseStart_3571132 : Nat := 118140960795 + 3571132 * 2 ^ 59
def prefixEnd_3571132 : Nat := 4983230072969 + 3 ^ 40 * 3571132 * 2
def baseEnd_3571132 : Nat := 1833707196652027163326669

theorem tailTrace_3571132 : CollatzResearch.WordTrace tailWord_3571132 prefixEnd_3571132 1833707196652027163326669 := by
  unfold tailWord_3571132
  simp only [CollatzResearch.WordTrace]
  refine ⟨65124942249203069817013825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86833256332270759756018433 65124942249203069817013825)
  ·
    refine ⟨48843706686902302362760369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65124942249203069817013825 48843706686902302362760369)
    ·
      refine ⟨36632780015176726772070277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48843706686902302362760369 36632780015176726772070277)
      ·
        refine ⟨6868646252845636269763177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36632780015176726772070277 6868646252845636269763177)
        ·
          refine ⟨5151484689634227202322383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6868646252845636269763177 5151484689634227202322383)
          ·
            refine ⟨7727227034451340803483575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5151484689634227202322383 7727227034451340803483575)
            ·
              refine ⟨11590840551677011205225363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7727227034451340803483575 11590840551677011205225363)
              ·
                refine ⟨17386260827515516807838045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11590840551677011205225363 17386260827515516807838045)
                ·
                  refine ⟨6519847810318318802939267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17386260827515516807838045 6519847810318318802939267)
                  ·
                    refine ⟨9779771715477478204408901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6519847810318318802939267 9779771715477478204408901)
                    ·
                      refine ⟨1833707196652027163326669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9779771715477478204408901 1833707196652027163326669)
                      ·
                        rfl

theorem cell23_3571132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 1, 1, 3, 1, 4].length) (baseStart_3571132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3571132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3571132 prefixEnd_3571132 := by exact prefixLift 3571132
  have htrace : WordTrace (prefixWord ++ tailWord_3571132) baseStart_3571132 baseEnd_3571132 := by
    simpa [prefixWord, tailWord_3571132, baseEnd_3571132] using wordTrace_append hprefix tailTrace_3571132
  have hstable : (prefixWord ++ tailWord_3571132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3571132).length < 2 ^ (prefixWord ++ tailWord_3571132).sum := by decide
  have hdescent : baseEnd_3571132 < baseStart_3571132 := by decide
  rcases family_descends (prefixWord ++ tailWord_3571132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3571182 : List Nat := [4, 1, 2, 1, 2, 1, 4, 1, 1, 3, 3]
def baseStart_3571182 : Nat := 118140960795 + 3571182 * 2 ^ 59
def prefixEnd_3571182 : Nat := 4983230072969 + 3 ^ 40 * 3571182 * 2
def baseEnd_3571182 : Nat := 1833732870684751967701439

theorem tailTrace_3571182 : CollatzResearch.WordTrace tailWord_3571182 prefixEnd_3571182 1833732870684751967701439 := by
  unfold tailWord_3571182
  simp only [CollatzResearch.WordTrace]
  refine ⟨16281463518528124771668475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 86834472098816665448898533 16281463518528124771668475)
  ·
    refine ⟨24422195277792187157502713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16281463518528124771668475 24422195277792187157502713)
    ·
      refine ⟨18316646458344140368127035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24422195277792187157502713 18316646458344140368127035)
      ·
        refine ⟨27474969687516210552190553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18316646458344140368127035 27474969687516210552190553)
        ·
          refine ⟨20606227265637157914142915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27474969687516210552190553 20606227265637157914142915)
          ·
            refine ⟨30909340898455736871214373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20606227265637157914142915 30909340898455736871214373)
            ·
              refine ⟨5795501418460450663352695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30909340898455736871214373 5795501418460450663352695)
              ·
                refine ⟨8693252127690675995029043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5795501418460450663352695 8693252127690675995029043)
                ·
                  refine ⟨13039878191536013992543565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8693252127690675995029043 13039878191536013992543565)
                  ·
                    refine ⟨4889954321826005247203837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13039878191536013992543565 4889954321826005247203837)
                    ·
                      refine ⟨1833732870684751967701439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4889954321826005247203837 1833732870684751967701439)
                      ·
                        rfl

theorem cell23_3571182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 4, 1, 1, 3, 3].length) (baseStart_3571182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3571182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3571182 prefixEnd_3571182 := by exact prefixLift 3571182
  have htrace : WordTrace (prefixWord ++ tailWord_3571182) baseStart_3571182 baseEnd_3571182 := by
    simpa [prefixWord, tailWord_3571182, baseEnd_3571182] using wordTrace_append hprefix tailTrace_3571182
  have hstable : (prefixWord ++ tailWord_3571182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3571182).length < 2 ^ (prefixWord ++ tailWord_3571182).sum := by decide
  have hdescent : baseEnd_3571182 < baseStart_3571182 := by decide
  rcases family_descends (prefixWord ++ tailWord_3571182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3571192 : List Nat := [2, 1, 2, 1, 1, 5, 2, 1, 3, 3, 2]
def baseStart_3571192 : Nat := 118140960795 + 3571192 * 2 ^ 59
def prefixEnd_3571192 : Nat := 4983230072969 + 3 ^ 40 * 3571192 * 2
def baseEnd_3571192 : Nat := 1833738005491296928576393

theorem tailTrace_3571192 : CollatzResearch.WordTrace tailWord_3571192 prefixEnd_3571192 1833738005491296928576393 := by
  unfold tailWord_3571192
  simp only [CollatzResearch.WordTrace]
  refine ⟨65126036439094384940605915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86834715252125846587474553 65126036439094384940605915)
  ·
    refine ⟨97689054658641577410908873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65126036439094384940605915 97689054658641577410908873)
    ·
      refine ⟨73266790993981183058181655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97689054658641577410908873 73266790993981183058181655)
      ·
        refine ⟨109900186490971774587272483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73266790993981183058181655 109900186490971774587272483)
        ·
          refine ⟨164850279736457661880908725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109900186490971774587272483 164850279736457661880908725)
          ·
            refine ⟨15454713725292905801335193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 164850279736457661880908725 15454713725292905801335193)
            ·
              refine ⟨11591035293969679351001395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15454713725292905801335193 11591035293969679351001395)
              ·
                refine ⟨17386552940954519026502093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11591035293969679351001395 17386552940954519026502093)
                ·
                  refine ⟨6519957352857944634938285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17386552940954519026502093 6519957352857944634938285)
                  ·
                    refine ⟨2444984007321729238101857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6519957352857944634938285 2444984007321729238101857)
                    ·
                      refine ⟨1833738005491296928576393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2444984007321729238101857 1833738005491296928576393)
                      ·
                        rfl

theorem cell23_3571192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 2, 1, 3, 3, 2].length) (baseStart_3571192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3571192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3571192 prefixEnd_3571192 := by exact prefixLift 3571192
  have htrace : WordTrace (prefixWord ++ tailWord_3571192) baseStart_3571192 baseEnd_3571192 := by
    simpa [prefixWord, tailWord_3571192, baseEnd_3571192] using wordTrace_append hprefix tailTrace_3571192
  have hstable : (prefixWord ++ tailWord_3571192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3571192).length < 2 ^ (prefixWord ++ tailWord_3571192).sum := by decide
  have hdescent : baseEnd_3571192 < baseStart_3571192 := by decide
  rcases family_descends (prefixWord ++ tailWord_3571192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3571230 : List Nat := [4, 3, 3, 1, 2, 1, 1, 1, 1, 2, 4]
def baseStart_3571230 : Nat := 118140960795 + 3571230 * 2 ^ 59
def prefixEnd_3571230 : Nat := 4983230072969 + 3 ^ 40 * 3571230 * 2
def baseEnd_3571230 : Nat := 1833757517756167779901219

theorem tailTrace_3571230 : CollatzResearch.WordTrace tailWord_3571230 prefixEnd_3571230 1833757517756167779901219 := by
  unfold tailWord_3571230
  simp only [CollatzResearch.WordTrace]
  refine ⟨16281682356506387796386893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 86835639234700734914063429 16281682356506387796386893)
  ·
    refine ⟨6105630883689895423645085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16281682356506387796386893 6105630883689895423645085)
    ·
      refine ⟨2289611581383710783866907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6105630883689895423645085 2289611581383710783866907)
      ·
        refine ⟨3434417372075566175800361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2289611581383710783866907 3434417372075566175800361)
        ·
          refine ⟨2575813029056674631850271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3434417372075566175800361 2575813029056674631850271)
          ·
            refine ⟨3863719543585011947775407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2575813029056674631850271 3863719543585011947775407)
            ·
              refine ⟨5795579315377517921663111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3863719543585011947775407 5795579315377517921663111)
              ·
                refine ⟨8693368973066276882494667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5795579315377517921663111 8693368973066276882494667)
                ·
                  refine ⟨13040053459599415323742001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8693368973066276882494667 13040053459599415323742001)
                  ·
                    refine ⟨9780040094699561492806501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13040053459599415323742001 9780040094699561492806501)
                    ·
                      refine ⟨1833757517756167779901219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9780040094699561492806501 1833757517756167779901219)
                      ·
                        rfl

theorem cell23_3571230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 2, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 2, 1, 1, 1, 1, 2, 4].length) (baseStart_3571230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3571230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3571230 prefixEnd_3571230 := by exact prefixLift 3571230
  have htrace : WordTrace (prefixWord ++ tailWord_3571230) baseStart_3571230 baseEnd_3571230 := by
    simpa [prefixWord, tailWord_3571230, baseEnd_3571230] using wordTrace_append hprefix tailTrace_3571230
  have hstable : (prefixWord ++ tailWord_3571230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3571230).length < 2 ^ (prefixWord ++ tailWord_3571230).sum := by decide
  have hdescent : baseEnd_3571230 < baseStart_3571230 := by decide
  rcases family_descends (prefixWord ++ tailWord_3571230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3571309 : List Nat := [1, 5, 1, 1, 4, 1, 2, 1, 2, 5]
def baseStart_3571309 : Nat := 118140960795 + 3571309 * 2 ^ 59
def prefixEnd_3571309 : Nat := 4983230072969 + 3 ^ 40 * 3571309 * 2
def baseEnd_3571309 : Nat := 611266027575957656937785

theorem tailTrace_3571309 : CollatzResearch.WordTrace tailWord_3571309 prefixEnd_3571309 611266027575957656937785 := by
  unfold tailWord_3571309
  simp only [CollatzResearch.WordTrace]
  refine ⟨130256340218764898863220981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86837560145843265908813987 130256340218764898863220981)
  ·
    refine ⟨12211531895509209268426967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 130256340218764898863220981 12211531895509209268426967)
    ·
      refine ⟨18317297843263813902640451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12211531895509209268426967 18317297843263813902640451)
      ·
        refine ⟨27475946764895720853960677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18317297843263813902640451 27475946764895720853960677)
        ·
          refine ⟨5151740018417947660117627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27475946764895720853960677 5151740018417947660117627)
          ·
            refine ⟨7727610027626921490176441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5151740018417947660117627 7727610027626921490176441)
            ·
              refine ⟨5795707520720191117632331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7727610027626921490176441 5795707520720191117632331)
              ·
                refine ⟨8693561281080286676448497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5795707520720191117632331 8693561281080286676448497)
                ·
                  refine ⟨6520170960810215007336373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8693561281080286676448497 6520170960810215007336373)
                  ·
                    refine ⟨611266027575957656937785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6520170960810215007336373 611266027575957656937785)
                    ·
                      rfl

theorem cell23_3571309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 2, 1, 2, 5].length) (baseStart_3571309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3571309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3571309 prefixEnd_3571309 := by exact prefixLift 3571309
  have htrace : WordTrace (prefixWord ++ tailWord_3571309) baseStart_3571309 baseEnd_3571309 := by
    simpa [prefixWord, tailWord_3571309, baseEnd_3571309] using wordTrace_append hprefix tailTrace_3571309
  have hstable : (prefixWord ++ tailWord_3571309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3571309).length < 2 ^ (prefixWord ++ tailWord_3571309).sum := by decide
  have hdescent : baseEnd_3571309 < baseStart_3571309 := by decide
  rcases family_descends (prefixWord ++ tailWord_3571309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3571312 : List Nat := [2, 1, 1, 1, 6, 1, 1, 3, 2, 1, 4]
def baseStart_3571312 : Nat := 118140960795 + 3571312 * 2 ^ 59
def prefixEnd_3571312 : Nat := 4983230072969 + 3 ^ 40 * 3571312 * 2
def baseEnd_3571312 : Nat := 1833799623169836459075841

theorem tailTrace_3571312 : CollatzResearch.WordTrace tailWord_3571312 prefixEnd_3571312 1833799623169836459075841 := by
  unfold tailWord_3571312
  simp only [CollatzResearch.WordTrace]
  refine ⟨65128224818877015187790095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86837633091836020250386793 65128224818877015187790095)
  ·
    refine ⟨97692337228315522781685143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65128224818877015187790095 97692337228315522781685143)
    ·
      refine ⟨146538505842473284172527715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97692337228315522781685143 146538505842473284172527715)
      ·
        refine ⟨219807758763709926258791573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146538505842473284172527715 219807758763709926258791573)
        ·
          refine ⟨10303488692048902793380855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 219807758763709926258791573 10303488692048902793380855)
          ·
            refine ⟨15455233038073354190071283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10303488692048902793380855 15455233038073354190071283)
            ·
              refine ⟨23182849557110031285106925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15455233038073354190071283 23182849557110031285106925)
              ·
                refine ⟨8693568583916261731915097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23182849557110031285106925 8693568583916261731915097)
                ·
                  refine ⟨6520176437937196298936323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8693568583916261731915097 6520176437937196298936323)
                  ·
                    refine ⟨9780264656905794448404485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6520176437937196298936323 9780264656905794448404485)
                    ·
                      refine ⟨1833799623169836459075841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9780264656905794448404485 1833799623169836459075841)
                      ·
                        rfl

theorem cell23_3571312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 1, 3, 2, 1, 4].length) (baseStart_3571312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3571312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3571312 prefixEnd_3571312 := by exact prefixLift 3571312
  have htrace : WordTrace (prefixWord ++ tailWord_3571312) baseStart_3571312 baseEnd_3571312 := by
    simpa [prefixWord, tailWord_3571312, baseEnd_3571312] using wordTrace_append hprefix tailTrace_3571312
  have hstable : (prefixWord ++ tailWord_3571312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3571312).length < 2 ^ (prefixWord ++ tailWord_3571312).sum := by decide
  have hdescent : baseEnd_3571312 < baseStart_3571312 := by decide
  rcases family_descends (prefixWord ++ tailWord_3571312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3571315 : List Nat := [1, 1, 1, 2, 2, 1, 1, 2, 5, 4, 3]
def baseStart_3571315 : Nat := 118140960795 + 3571315 * 2 ^ 59
def prefixEnd_3571315 : Nat := 4983230072969 + 3 ^ 40 * 3571315 * 2
def baseEnd_3571315 : Nat := 1833801163611799947338327

theorem tailTrace_3571315 : CollatzResearch.WordTrace tailWord_3571315 prefixEnd_3571315 1833801163611799947338327 := by
  unfold tailWord_3571315
  simp only [CollatzResearch.WordTrace]
  refine ⟨130256559056743161887939399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86837706037828774591959599 130256559056743161887939399)
  ·
    refine ⟨195384838585114742831909099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130256559056743161887939399 195384838585114742831909099)
    ·
      refine ⟨293077257877672114247863649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195384838585114742831909099 293077257877672114247863649)
      ·
        refine ⟨219807943408254085685897737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 293077257877672114247863649 219807943408254085685897737)
        ·
          refine ⟨164855957556190564264423303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 219807943408254085685897737 164855957556190564264423303)
          ·
            refine ⟨247283936334285846396634955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 164855957556190564264423303 247283936334285846396634955)
            ·
              refine ⟨370925904501428769594952433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 247283936334285846396634955 370925904501428769594952433)
              ·
                refine ⟨278194428376071577196214325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 370925904501428769594952433 278194428376071577196214325)
                ·
                  refine ⟨26080727660256710362145093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 278194428376071577196214325 26080727660256710362145093)
                  ·
                    refine ⟨4890136436298133192902205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26080727660256710362145093 4890136436298133192902205)
                    ·
                      refine ⟨1833801163611799947338327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4890136436298133192902205 1833801163611799947338327)
                      ·
                        rfl

theorem cell23_3571315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 2, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 2, 5, 4, 3].length) (baseStart_3571315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3571315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3571315 prefixEnd_3571315 := by exact prefixLift 3571315
  have htrace : WordTrace (prefixWord ++ tailWord_3571315) baseStart_3571315 baseEnd_3571315 := by
    simpa [prefixWord, tailWord_3571315, baseEnd_3571315] using wordTrace_append hprefix tailTrace_3571315
  have hstable : (prefixWord ++ tailWord_3571315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3571315).length < 2 ^ (prefixWord ++ tailWord_3571315).sum := by decide
  have hdescent : baseEnd_3571315 < baseStart_3571315 := by decide
  rcases family_descends (prefixWord ++ tailWord_3571315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3571339 : List Nat := [1, 1, 1, 1, 4, 1, 5, 4, 1, 4]
def baseStart_3571339 : Nat := 118140960795 + 3571339 * 2 ^ 59
def prefixEnd_3571339 : Nat := 4983230072969 + 3 ^ 40 * 3571339 * 2
def baseEnd_3571339 : Nat := 611271162382502617812739

theorem tailTrace_3571339 : CollatzResearch.WordTrace tailWord_3571339 prefixEnd_3571339 611271162382502617812739 := by
  unfold tailWord_3571339
  simp only [CollatzResearch.WordTrace]
  refine ⟨130257434408656213986813071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86838289605770809324542047 130257434408656213986813071)
  ·
    refine ⟨195386151612984320980219607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130257434408656213986813071 195386151612984320980219607)
    ·
      refine ⟨293079227419476481470329411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195386151612984320980219607 293079227419476481470329411)
      ·
        refine ⟨439618841129214722205494117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 293079227419476481470329411 439618841129214722205494117)
        ·
          refine ⟨82428532711727760413530147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 439618841129214722205494117 82428532711727760413530147)
          ·
            refine ⟨123642799067591640620295221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82428532711727760413530147 123642799067591640620295221)
            ·
              refine ⟨11591512412586716308152677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 123642799067591640620295221 11591512412586716308152677)
              ·
                refine ⟨2173408577360009307778627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11591512412586716308152677 2173408577360009307778627)
                ·
                  refine ⟨3260112866040013961667941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2173408577360009307778627 3260112866040013961667941)
                  ·
                    refine ⟨611271162382502617812739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3260112866040013961667941 611271162382502617812739)
                    ·
                      rfl

theorem cell23_3571339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 5, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 5, 4, 1, 4].length) (baseStart_3571339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3571339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3571339 prefixEnd_3571339 := by exact prefixLift 3571339
  have htrace : WordTrace (prefixWord ++ tailWord_3571339) baseStart_3571339 baseEnd_3571339 := by
    simpa [prefixWord, tailWord_3571339, baseEnd_3571339] using wordTrace_append hprefix tailTrace_3571339
  have hstable : (prefixWord ++ tailWord_3571339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3571339).length < 2 ^ (prefixWord ++ tailWord_3571339).sum := by decide
  have hdescent : baseEnd_3571339 < baseStart_3571339 := by decide
  rcases family_descends (prefixWord ++ tailWord_3571339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3571346 : List Nat := [3, 2, 3, 1, 3, 1, 1, 1, 2, 4, 2]
def baseStart_3571346 : Nat := 118140960795 + 3571346 * 2 ^ 59
def prefixEnd_3571346 : Nat := 4983230072969 + 3 ^ 40 * 3571346 * 2
def baseEnd_3571346 : Nat := 1833817081512089326050685

theorem tailTrace_3571346 : CollatzResearch.WordTrace tailWord_3571346 prefixEnd_3571346 1833817081512089326050685 := by
  unfold tailWord_3571346
  simp only [CollatzResearch.WordTrace]
  refine ⟨32564422429907713545579473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86838459813087236121545261 32564422429907713545579473)
  ·
    refine ⟨24423316822430785159184605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32564422429907713545579473 24423316822430785159184605)
    ·
      refine ⟨9158743808411544434694227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24423316822430785159184605 9158743808411544434694227)
      ·
        refine ⟨13738115712617316652041341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9158743808411544434694227 13738115712617316652041341)
        ·
          refine ⟨5151793392231493744515503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13738115712617316652041341 5151793392231493744515503)
          ·
            refine ⟨7727690088347240616773255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5151793392231493744515503 7727690088347240616773255)
            ·
              refine ⟨11591535132520860925159883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7727690088347240616773255 11591535132520860925159883)
              ·
                refine ⟨17387302698781291387739825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11591535132520860925159883 17387302698781291387739825)
                ·
                  refine ⟨13040477024085968540804869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17387302698781291387739825 13040477024085968540804869)
                  ·
                    refine ⟨2445089442016119101400913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13040477024085968540804869 2445089442016119101400913)
                    ·
                      refine ⟨1833817081512089326050685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2445089442016119101400913 1833817081512089326050685)
                      ·
                        rfl

theorem cell23_3571346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 1, 1, 2, 4, 2].length) (baseStart_3571346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3571346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3571346 prefixEnd_3571346 := by exact prefixLift 3571346
  have htrace : WordTrace (prefixWord ++ tailWord_3571346) baseStart_3571346 baseEnd_3571346 := by
    simpa [prefixWord, tailWord_3571346, baseEnd_3571346] using wordTrace_append hprefix tailTrace_3571346
  have hstable : (prefixWord ++ tailWord_3571346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3571346).length < 2 ^ (prefixWord ++ tailWord_3571346).sum := by decide
  have hdescent : baseEnd_3571346 < baseStart_3571346 := by decide
  rcases family_descends (prefixWord ++ tailWord_3571346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3571352 : List Nat := [2, 1, 2, 4, 1, 2, 2, 3, 6]
def baseStart_3571352 : Nat := 118140960795 + 3571352 * 2 ^ 59
def prefixEnd_3571352 : Nat := 4983230072969 + 3 ^ 40 * 3571352 * 2
def baseEnd_3571352 : Nat := 203757795821779589175073

theorem tailTrace_3571352 : CollatzResearch.WordTrace tailWord_3571352 prefixEnd_3571352 203757795821779589175073 := by
  unfold tailWord_3571352
  simp only [CollatzResearch.WordTrace]
  refine ⟨65128954278804558603518155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86838605705072744804690873 65128954278804558603518155)
  ·
    refine ⟨97693431418206837905277233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65128954278804558603518155 97693431418206837905277233)
    ·
      refine ⟨73270073563655128428957925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97693431418206837905277233 73270073563655128428957925)
      ·
        refine ⟨13738138793185336580429611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 73270073563655128428957925 13738138793185336580429611)
        ·
          refine ⟨20607208189778004870644417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13738138793185336580429611 20607208189778004870644417)
          ·
            refine ⟨15455406142333503652983313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20607208189778004870644417 15455406142333503652983313)
            ·
              refine ⟨11591554606750127739737485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15455406142333503652983313 11591554606750127739737485)
              ·
                refine ⟨4346832977531297902401557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11591554606750127739737485 4346832977531297902401557)
                ·
                  refine ⟨203757795821779589175073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4346832977531297902401557 203757795821779589175073)
                  ·
                    rfl

theorem cell23_3571352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 2, 3, 6].length) (baseStart_3571352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3571352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3571352 prefixEnd_3571352 := by exact prefixLift 3571352
  have htrace : WordTrace (prefixWord ++ tailWord_3571352) baseStart_3571352 baseEnd_3571352 := by
    simpa [prefixWord, tailWord_3571352, baseEnd_3571352] using wordTrace_append hprefix tailTrace_3571352
  have hstable : (prefixWord ++ tailWord_3571352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3571352).length < 2 ^ (prefixWord ++ tailWord_3571352).sum := by decide
  have hdescent : baseEnd_3571352 < baseStart_3571352 := by decide
  rcases family_descends (prefixWord ++ tailWord_3571352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3571389 : List Nat := [1, 4, 1, 2, 1, 2, 2, 1, 4, 3, 2]
def baseStart_3571389 : Nat := 118140960795 + 3571389 * 2 ^ 59
def prefixEnd_3571389 : Nat := 4983230072969 + 3 ^ 40 * 3571389 * 2
def baseEnd_3571389 : Nat := 1833839161180232657812987

theorem tailTrace_3571389 : CollatzResearch.WordTrace tailWord_3571389 prefixEnd_3571389 1833839161180232657812987 := by
  unfold tailWord_3571389
  simp only [CollatzResearch.WordTrace]
  refine ⟨130259258058475072526133221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86839505372316715017422147 130259258058475072526133221)
  ·
    refine ⟨24423610885964076098649979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 130259258058475072526133221 24423610885964076098649979)
    ·
      refine ⟨36635416328946114147974969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24423610885964076098649979 36635416328946114147974969)
      ·
        refine ⟨27476562246709585610981227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36635416328946114147974969 27476562246709585610981227)
        ·
          refine ⟨41214843370064378416471841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27476562246709585610981227 41214843370064378416471841)
          ·
            refine ⟨30911132527548283812353881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41214843370064378416471841 30911132527548283812353881)
            ·
              refine ⟨23183349395661212859265411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30911132527548283812353881 23183349395661212859265411)
              ·
                refine ⟨34775024093491819288898117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23183349395661212859265411 34775024093491819288898117)
                ·
                  refine ⟨6520317017529716116668397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34775024093491819288898117 6520317017529716116668397)
                  ·
                    refine ⟨2445118881573643543750649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6520317017529716116668397 2445118881573643543750649)
                    ·
                      refine ⟨1833839161180232657812987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2445118881573643543750649 1833839161180232657812987)
                      ·
                        rfl

theorem cell23_3571389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 2, 1, 4, 3, 2].length) (baseStart_3571389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3571389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3571389 prefixEnd_3571389 := by exact prefixLift 3571389
  have htrace : WordTrace (prefixWord ++ tailWord_3571389) baseStart_3571389 baseEnd_3571389 := by
    simpa [prefixWord, tailWord_3571389, baseEnd_3571389] using wordTrace_append hprefix tailTrace_3571389
  have hstable : (prefixWord ++ tailWord_3571389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3571389).length < 2 ^ (prefixWord ++ tailWord_3571389).sum := by decide
  have hdescent : baseEnd_3571389 < baseStart_3571389 := by decide
  rcases family_descends (prefixWord ++ tailWord_3571389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3571396 : List Nat := [2, 3, 3, 1, 1, 1, 4, 1, 3, 1, 3]
def baseStart_3571396 : Nat := 118140960795 + 3571396 * 2 ^ 59
def prefixEnd_3571396 : Nat := 4983230072969 + 3 ^ 40 * 3571396 * 2
def baseEnd_3571396 : Nat := 1833842755544814130425455

theorem tailTrace_3571396 : CollatzResearch.WordTrace tailWord_3571396 prefixEnd_3571396 1833842755544814130425455 := by
  unfold tailWord_3571396
  simp only [CollatzResearch.WordTrace]
  refine ⟨65129756684724856360819021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86839675579633141814425361 65129756684724856360819021)
  ·
    refine ⟨24423658756771821135307133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65129756684724856360819021 24423658756771821135307133)
    ·
      refine ⟨9158872033789432925740175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24423658756771821135307133 9158872033789432925740175)
      ·
        refine ⟨13738308050684149388610263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9158872033789432925740175 13738308050684149388610263)
        ·
          refine ⟨20607462076026224082915395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13738308050684149388610263 20607462076026224082915395)
          ·
            refine ⟨30911193114039336124373093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20607462076026224082915395 30911193114039336124373093)
            ·
              refine ⟨5795848708882375523319955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30911193114039336124373093 5795848708882375523319955)
              ·
                refine ⟨8693773063323563284979933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5795848708882375523319955 8693773063323563284979933)
                ·
                  refine ⟨3260164898746336231867475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8693773063323563284979933 3260164898746336231867475)
                  ·
                    refine ⟨4890247348119504347801213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3260164898746336231867475 4890247348119504347801213)
                    ·
                      refine ⟨1833842755544814130425455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4890247348119504347801213 1833842755544814130425455)
                      ·
                        rfl

theorem cell23_3571396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 4, 1, 3, 1, 3].length) (baseStart_3571396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3571396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3571396 prefixEnd_3571396 := by exact prefixLift 3571396
  have htrace : WordTrace (prefixWord ++ tailWord_3571396) baseStart_3571396 baseEnd_3571396 := by
    simpa [prefixWord, tailWord_3571396, baseEnd_3571396] using wordTrace_append hprefix tailTrace_3571396
  have hstable : (prefixWord ++ tailWord_3571396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3571396).length < 2 ^ (prefixWord ++ tailWord_3571396).sum := by decide
  have hdescent : baseEnd_3571396 < baseStart_3571396 := by decide
  rcases family_descends (prefixWord ++ tailWord_3571396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3571439 : List Nat := [1, 1, 2, 1, 5, 1, 1, 5, 1, 2, 3]
def baseStart_3571439 : Nat := 118140960795 + 3571439 * 2 ^ 59
def prefixEnd_3571439 : Nat := 4983230072969 + 3 ^ 40 * 3571439 * 2
def baseEnd_3571439 : Nat := 1833864835212957462187757

theorem tailTrace_3571439 : CollatzResearch.WordTrace tailWord_3571439 prefixEnd_3571439 1833864835212957462187757 := by
  unfold tailWord_3571439
  simp only [CollatzResearch.WordTrace]
  refine ⟨130261081708293931065453371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86840721138862620710302247 130261081708293931065453371)
  ·
    refine ⟨195391622562440896598180057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130261081708293931065453371 195391622562440896598180057)
    ·
      refine ⟨146543716921830672448635043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 195391622562440896598180057 146543716921830672448635043)
      ·
        refine ⟨219815575382746008672952565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146543716921830672448635043 219815575382746008672952565)
        ·
          refine ⟨20607710192132438313089303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 219815575382746008672952565 20607710192132438313089303)
          ·
            refine ⟨30911565288198657469633955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20607710192132438313089303 30911565288198657469633955)
            ·
              refine ⟨46367347932297986204450933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30911565288198657469633955 46367347932297986204450933)
              ·
                refine ⟨4346938868652936206667275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 46367347932297986204450933 4346938868652936206667275)
                ·
                  refine ⟨6520408302979404310000913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4346938868652936206667275 6520408302979404310000913)
                  ·
                    refine ⟨4890306227234553232500685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6520408302979404310000913 4890306227234553232500685)
                    ·
                      refine ⟨1833864835212957462187757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4890306227234553232500685 1833864835212957462187757)
                      ·
                        rfl

theorem cell23_3571439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 5, 1, 2, 3].length) (baseStart_3571439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3571439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3571439 prefixEnd_3571439 := by exact prefixLift 3571439
  have htrace : WordTrace (prefixWord ++ tailWord_3571439) baseStart_3571439 baseEnd_3571439 := by
    simpa [prefixWord, tailWord_3571439, baseEnd_3571439] using wordTrace_append hprefix tailTrace_3571439
  have hstable : (prefixWord ++ tailWord_3571439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3571439).length < 2 ^ (prefixWord ++ tailWord_3571439).sum := by decide
  have hdescent : baseEnd_3571439 < baseStart_3571439 := by decide
  rcases family_descends (prefixWord ++ tailWord_3571439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3571519 : List Nat := [1, 1, 2, 2, 6, 1, 1, 1, 2, 6]
def baseStart_3571519 : Nat := 118140960795 + 3571519 * 2 ^ 59
def prefixEnd_3571519 : Nat := 4983230072969 + 3 ^ 40 * 3571519 * 2
def baseEnd_3571519 : Nat := 611301971221772383062463

theorem tailTrace_3571519 : CollatzResearch.WordTrace tailWord_3571519 prefixEnd_3571519 611301971221772383062463 := by
  unfold tailWord_3571519
  simp only [CollatzResearch.WordTrace]
  refine ⟨130263999548004104728365611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86842666365336069818910407 130263999548004104728365611)
  ·
    refine ⟨195395999322006157092548417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130263999548004104728365611 195395999322006157092548417)
    ·
      refine ⟨146546999491504617819411313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 195395999322006157092548417 146546999491504617819411313)
      ·
        refine ⟨109910249618628463364558485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146546999491504617819411313 109910249618628463364558485)
        ·
          refine ⟨5152042950873209220213679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 109910249618628463364558485 5152042950873209220213679)
          ·
            refine ⟨7728064426309813830320519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5152042950873209220213679 7728064426309813830320519)
            ·
              refine ⟨11592096639464720745480779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7728064426309813830320519 11592096639464720745480779)
              ·
                refine ⟨17388144959197081118221169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11592096639464720745480779 17388144959197081118221169)
                ·
                  refine ⟨13041108719397810838665877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17388144959197081118221169 13041108719397810838665877)
                  ·
                    refine ⟨611301971221772383062463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13041108719397810838665877 611301971221772383062463)
                    ·
                      rfl

theorem cell23_3571519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 1, 1, 2, 6].length) (baseStart_3571519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3571519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3571519 prefixEnd_3571519 := by exact prefixLift 3571519
  have htrace : WordTrace (prefixWord ++ tailWord_3571519) baseStart_3571519 baseEnd_3571519 := by
    simpa [prefixWord, tailWord_3571519, baseEnd_3571519] using wordTrace_append hprefix tailTrace_3571519
  have hstable : (prefixWord ++ tailWord_3571519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3571519).length < 2 ^ (prefixWord ++ tailWord_3571519).sum := by decide
  have hdescent : baseEnd_3571519 < baseStart_3571519 := by decide
  rcases family_descends (prefixWord ++ tailWord_3571519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3571559 : List Nat := [1, 1, 5, 1, 2, 1, 1, 1, 4, 3, 3]
def baseStart_3571559 : Nat := 118140960795 + 3571559 * 2 ^ 59
def prefixEnd_3571559 : Nat := 4983230072969 + 3 ^ 40 * 3571559 * 2
def baseEnd_3571559 : Nat := 1833926452891496992687205

theorem tailTrace_3571559 : CollatzResearch.WordTrace tailWord_3571559 prefixEnd_3571559 1833926452891496992687205 := by
  unfold tailWord_3571559
  simp only [CollatzResearch.WordTrace]
  refine ⟨130265458467859191559821731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86843638978572794373214487 130265458467859191559821731)
  ·
    refine ⟨195398187701788787339732597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130265458467859191559821731 195398187701788787339732597)
    ·
      refine ⟨18318580097042698813099931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 195398187701788787339732597 18318580097042698813099931)
      ·
        refine ⟨27477870145564048219649897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18318580097042698813099931 27477870145564048219649897)
        ·
          refine ⟨20608402609173036164737423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27477870145564048219649897 20608402609173036164737423)
          ·
            refine ⟨30912603913759554247106135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20608402609173036164737423 30912603913759554247106135)
            ·
              refine ⟨46368905870639331370659203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30912603913759554247106135 46368905870639331370659203)
              ·
                refine ⟨69553358805958997055988805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46368905870639331370659203 69553358805958997055988805)
                ·
                  refine ⟨13041254776117311947997901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 69553358805958997055988805 13041254776117311947997901)
                  ·
                    refine ⟨4890470541043991980499213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13041254776117311947997901 4890470541043991980499213)
                    ·
                      refine ⟨1833926452891496992687205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4890470541043991980499213 1833926452891496992687205)
                      ·
                        rfl

theorem cell23_3571559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 1, 4, 3, 3].length) (baseStart_3571559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3571559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3571559 prefixEnd_3571559 := by exact prefixLift 3571559
  have htrace : WordTrace (prefixWord ++ tailWord_3571559) baseStart_3571559 baseEnd_3571559 := by
    simpa [prefixWord, tailWord_3571559, baseEnd_3571559] using wordTrace_append hprefix tailTrace_3571559
  have hstable : (prefixWord ++ tailWord_3571559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3571559).length < 2 ^ (prefixWord ++ tailWord_3571559).sum := by decide
  have hdescent : baseEnd_3571559 < baseStart_3571559 := by decide
  rcases family_descends (prefixWord ++ tailWord_3571559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3571566 : List Nat := [4, 1, 2, 3, 1, 2, 2, 1, 7]
def baseStart_3571566 : Nat := 118140960795 + 3571566 * 2 ^ 59
def prefixEnd_3571566 : Nat := 4983230072969 + 3 ^ 40 * 3571566 * 2
def baseEnd_3571566 : Nat := 203770005250675385033297

theorem tailTrace_3571566 : CollatzResearch.WordTrace tailWord_3571566 prefixEnd_3571566 203770005250675385033297 := by
  unfold tailWord_3571566
  simp only [CollatzResearch.WordTrace]
  refine ⟨16283214222354228969415819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 86843809185889221170217701 16283214222354228969415819)
  ·
    refine ⟨24424821333531343454123729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16283214222354228969415819 24424821333531343454123729)
    ·
      refine ⟨18318616000148507590592797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24424821333531343454123729 18318616000148507590592797)
      ·
        refine ⟨6869481000055690346472299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18318616000148507590592797 6869481000055690346472299)
        ·
          refine ⟨10304221500083535519708449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6869481000055690346472299 10304221500083535519708449)
          ·
            refine ⟨7728166125062651639781337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10304221500083535519708449 7728166125062651639781337)
            ·
              refine ⟨5796124593796988729836003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7728166125062651639781337 5796124593796988729836003)
              ·
                refine ⟨8694186890695483094754005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5796124593796988729836003 8694186890695483094754005)
                ·
                  refine ⟨203770005250675385033297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8694186890695483094754005 203770005250675385033297)
                  ·
                    rfl

theorem cell23_3571566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 2, 1, 7].length) (baseStart_3571566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3571566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3571566 prefixEnd_3571566 := by exact prefixLift 3571566
  have htrace : WordTrace (prefixWord ++ tailWord_3571566) baseStart_3571566 baseEnd_3571566 := by
    simpa [prefixWord, tailWord_3571566, baseEnd_3571566] using wordTrace_append hprefix tailTrace_3571566
  have hstable : (prefixWord ++ tailWord_3571566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3571566).length < 2 ^ (prefixWord ++ tailWord_3571566).sum := by decide
  have hdescent : baseEnd_3571566 < baseStart_3571566 := by decide
  rcases family_descends (prefixWord ++ tailWord_3571566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3571609 : List Nat := [1, 2, 1, 2, 1, 3, 2, 2, 5, 4]
def baseStart_3571609 : Nat := 118140960795 + 3571609 * 2 ^ 59
def prefixEnd_3571609 : Nat := 4983230072969 + 3 ^ 40 * 3571609 * 2
def baseEnd_3571609 : Nat := 611317375641407265687325

theorem tailTrace_3571609 : CollatzResearch.WordTrace tailWord_3571609 prefixEnd_3571609 611317375641407265687325 := by
  unfold tailWord_3571609
  simp only [CollatzResearch.WordTrace]
  refine ⟨130267282117678050099141881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86844854745118700066094587 130267282117678050099141881)
  ·
    refine ⟨97700461588258537574356411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130267282117678050099141881 97700461588258537574356411)
    ·
      refine ⟨146550692382387806361534617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97700461588258537574356411 146550692382387806361534617)
      ·
        refine ⟨109913019286790854771150963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146550692382387806361534617 109913019286790854771150963)
        ·
          refine ⟨164869528930186282156726445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109913019286790854771150963 164869528930186282156726445)
          ·
            refine ⟨61826073348819855808772417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 164869528930186282156726445 61826073348819855808772417)
            ·
              refine ⟨46369555011614891856579313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61826073348819855808772417 46369555011614891856579313)
              ·
                refine ⟨34777166258711168892434485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46369555011614891856579313 34777166258711168892434485)
                ·
                  refine ⟨3260359336754172083665733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 34777166258711168892434485 3260359336754172083665733)
                  ·
                    refine ⟨611317375641407265687325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3260359336754172083665733 611317375641407265687325)
                    ·
                      rfl

theorem cell23_3571609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 2, 5, 4].length) (baseStart_3571609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3571609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3571609 prefixEnd_3571609 := by exact prefixLift 3571609
  have htrace : WordTrace (prefixWord ++ tailWord_3571609) baseStart_3571609 baseEnd_3571609 := by
    simpa [prefixWord, tailWord_3571609, baseEnd_3571609] using wordTrace_append hprefix tailTrace_3571609
  have hstable : (prefixWord ++ tailWord_3571609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3571609).length < 2 ^ (prefixWord ++ tailWord_3571609).sum := by decide
  have hdescent : baseEnd_3571609 < baseStart_3571609 := by decide
  rcases family_descends (prefixWord ++ tailWord_3571609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3571710 : List Nat := [4, 2, 2, 2, 1, 2, 1, 1, 1, 5, 2]
def baseStart_3571710 : Nat := 118140960795 + 3571710 * 2 ^ 59
def prefixEnd_3571710 : Nat := 4983230072969 + 3 ^ 40 * 3571710 * 2
def baseEnd_3571710 : Nat := 1834003988470325901899011

theorem tailTrace_3571710 : CollatzResearch.WordTrace tailWord_3571710 prefixEnd_3571710 1834003988470325901899011 := by
  unfold tailWord_3571710
  simp only [CollatzResearch.WordTrace]
  refine ⟨16283870736289018043571073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 86847310593541429565712389 16283870736289018043571073)
  ·
    refine ⟨12212903052216763532678305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16283870736289018043571073 12212903052216763532678305)
    ·
      refine ⟨9159677289162572649508729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12212903052216763532678305 9159677289162572649508729)
      ·
        refine ⟨6869757966871929487131547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9159677289162572649508729 6869757966871929487131547)
        ·
          refine ⟨10304636950307894230697321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6869757966871929487131547 10304636950307894230697321)
          ·
            refine ⟨7728477712730920673022991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10304636950307894230697321 7728477712730920673022991)
            ·
              refine ⟨11592716569096381009534487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7728477712730920673022991 11592716569096381009534487)
              ·
                refine ⟨17389074853644571514301731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11592716569096381009534487 17389074853644571514301731)
                ·
                  refine ⟨26083612280466857271452597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17389074853644571514301731 26083612280466857271452597)
                  ·
                    refine ⟨2445338651293767869198681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 26083612280466857271452597 2445338651293767869198681)
                    ·
                      refine ⟨1834003988470325901899011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2445338651293767869198681 1834003988470325901899011)
                      ·
                        rfl

theorem cell23_3571710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 1, 1, 1, 5, 2].length) (baseStart_3571710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3571710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3571710 prefixEnd_3571710 := by exact prefixLift 3571710
  have htrace : WordTrace (prefixWord ++ tailWord_3571710) baseStart_3571710 baseEnd_3571710 := by
    simpa [prefixWord, tailWord_3571710, baseEnd_3571710] using wordTrace_append hprefix tailTrace_3571710
  have hstable : (prefixWord ++ tailWord_3571710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3571710).length < 2 ^ (prefixWord ++ tailWord_3571710).sum := by decide
  have hdescent : baseEnd_3571710 < baseStart_3571710 := by decide
  rcases family_descends (prefixWord ++ tailWord_3571710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3571723 : List Nat := [1, 1, 1, 1, 6, 1, 1, 2, 5, 2, 2]
def baseStart_3571723 : Nat := 118140960795 + 3571723 * 2 ^ 59
def prefixEnd_3571723 : Nat := 4983230072969 + 3 ^ 40 * 3571723 * 2
def baseEnd_3571723 : Nat := 1834010663718834351036451

theorem tailTrace_3571723 : CollatzResearch.WordTrace tailWord_3571723 prefixEnd_3571723 1834010663718834351036451 := by
  unfold tailWord_3571723
  simp only [CollatzResearch.WordTrace]
  refine ⟨130271440039265047568791823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86847626692843365045861215 130271440039265047568791823)
  ·
    refine ⟨195407160058897571353187735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130271440039265047568791823 195407160058897571353187735)
    ·
      refine ⟨293110740088346357029781603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195407160058897571353187735 293110740088346357029781603)
      ·
        refine ⟨439666110132519535544672405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 293110740088346357029781603 439666110132519535544672405)
        ·
          refine ⟨20609348912461853228656519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 439666110132519535544672405 20609348912461853228656519)
          ·
            refine ⟨30914023368692779842984779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20609348912461853228656519 30914023368692779842984779)
            ·
              refine ⟨46371035053039169764477169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30914023368692779842984779 46371035053039169764477169)
              ·
                refine ⟨34778276289779377323357877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46371035053039169764477169 34778276289779377323357877)
                ·
                  refine ⟨3260463402166816624064801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 34778276289779377323357877 3260463402166816624064801)
                  ·
                    refine ⟨2445347551625112468048601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3260463402166816624064801 2445347551625112468048601)
                    ·
                      refine ⟨1834010663718834351036451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2445347551625112468048601 1834010663718834351036451)
                      ·
                        rfl

theorem cell23_3571723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 2, 5, 2, 2].length) (baseStart_3571723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3571723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3571723 prefixEnd_3571723 := by exact prefixLift 3571723
  have htrace : WordTrace (prefixWord ++ tailWord_3571723) baseStart_3571723 baseEnd_3571723 := by
    simpa [prefixWord, tailWord_3571723, baseEnd_3571723] using wordTrace_append hprefix tailTrace_3571723
  have hstable : (prefixWord ++ tailWord_3571723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3571723).length < 2 ^ (prefixWord ++ tailWord_3571723).sum := by decide
  have hdescent : baseEnd_3571723 < baseStart_3571723 := by decide
  rcases family_descends (prefixWord ++ tailWord_3571723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3571726 : List Nat := [4, 1, 1, 2, 2, 1, 2, 3, 1, 1, 5]
def baseStart_3571726 : Nat := 118140960795 + 3571726 * 2 ^ 59
def prefixEnd_3571726 : Nat := 4983230072969 + 3 ^ 40 * 3571726 * 2
def baseEnd_3571726 : Nat := 1834012204160797839298937

theorem tailTrace_3571726 : CollatzResearch.WordTrace tailWord_3571726 prefixEnd_3571726 1834012204160797839298937 := by
  unfold tailWord_3571726
  simp only [CollatzResearch.WordTrace]
  refine ⟨16283943682281772385143879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 86847699638836119387434021 16283943682281772385143879)
  ·
    refine ⟨24425915523422658577715819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16283943682281772385143879 24425915523422658577715819)
    ·
      refine ⟨36638873285133987866573729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24425915523422658577715819 36638873285133987866573729)
      ·
        refine ⟨27479154963850490899930297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36638873285133987866573729 27479154963850490899930297)
        ·
          refine ⟨20609366222887868174947723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27479154963850490899930297 20609366222887868174947723)
          ·
            refine ⟨30914049334331802262421585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20609366222887868174947723 30914049334331802262421585)
            ·
              refine ⟨23185537000748851696816189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30914049334331802262421585 23185537000748851696816189)
              ·
                refine ⟨8694576375280819386306071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23185537000748851696816189 8694576375280819386306071)
                ·
                  refine ⟨13041864562921229079459107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8694576375280819386306071 13041864562921229079459107)
                  ·
                    refine ⟨19562796844381843619188661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13041864562921229079459107 19562796844381843619188661)
                    ·
                      refine ⟨1834012204160797839298937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19562796844381843619188661 1834012204160797839298937)
                      ·
                        rfl

theorem cell23_3571726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 2, 3, 1, 1, 5].length) (baseStart_3571726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3571726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3571726 prefixEnd_3571726 := by exact prefixLift 3571726
  have htrace : WordTrace (prefixWord ++ tailWord_3571726) baseStart_3571726 baseEnd_3571726 := by
    simpa [prefixWord, tailWord_3571726, baseEnd_3571726] using wordTrace_append hprefix tailTrace_3571726
  have hstable : (prefixWord ++ tailWord_3571726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3571726).length < 2 ^ (prefixWord ++ tailWord_3571726).sum := by decide
  have hdescent : baseEnd_3571726 < baseStart_3571726 := by decide
  rcases family_descends (prefixWord ++ tailWord_3571726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3571733 : List Nat := [1, 3, 2, 1, 5, 1, 1, 1, 4, 4]
def baseStart_3571733 : Nat := 118140960795 + 3571733 * 2 ^ 59
def prefixEnd_3571733 : Nat := 4983230072969 + 3 ^ 40 * 3571733 * 2
def baseEnd_3571733 : Nat := 611338599508459770637135

theorem tailTrace_3571733 : CollatzResearch.WordTrace tailWord_3571733 prefixEnd_3571733 611338599508459770637135 := by
  unfold tailWord_3571733
  simp only [CollatzResearch.WordTrace]
  refine ⟨130271804769228819276655853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86847869846152546184437235 130271804769228819276655853)
  ·
    refine ⟨48851926788460807228745945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130271804769228819276655853 48851926788460807228745945)
    ·
      refine ⟨36638945091345605421559459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48851926788460807228745945 36638945091345605421559459)
      ·
        refine ⟨54958417637018408132339189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36638945091345605421559459 54958417637018408132339189)
        ·
          refine ⟨5152351653470475762406799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 54958417637018408132339189 5152351653470475762406799)
          ·
            refine ⟨7728527480205713643610199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5152351653470475762406799 7728527480205713643610199)
            ·
              refine ⟨11592791220308570465415299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7728527480205713643610199 11592791220308570465415299)
              ·
                refine ⟨17389186830462855698122949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11592791220308570465415299 17389186830462855698122949)
                ·
                  refine ⟨3260472530711785443398053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17389186830462855698122949 3260472530711785443398053)
                  ·
                    refine ⟨611338599508459770637135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3260472530711785443398053 611338599508459770637135)
                    ·
                      rfl

theorem cell23_3571733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 1, 1, 4, 4].length) (baseStart_3571733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3571733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3571733 prefixEnd_3571733 := by exact prefixLift 3571733
  have htrace : WordTrace (prefixWord ++ tailWord_3571733) baseStart_3571733 baseEnd_3571733 := by
    simpa [prefixWord, tailWord_3571733, baseEnd_3571733] using wordTrace_append hprefix tailTrace_3571733
  have hstable : (prefixWord ++ tailWord_3571733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3571733).length < 2 ^ (prefixWord ++ tailWord_3571733).sum := by decide
  have hdescent : baseEnd_3571733 < baseStart_3571733 := by decide
  rcases family_descends (prefixWord ++ tailWord_3571733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3571740 : List Nat := [2, 2, 3, 1, 3, 1, 1, 3, 3, 2, 2]
def baseStart_3571740 : Nat := 118140960795 + 3571740 * 2 ^ 59
def prefixEnd_3571740 : Nat := 4983230072969 + 3 ^ 40 * 3571740 * 2
def baseEnd_3571740 : Nat := 1834019392889960784523873

theorem tailTrace_3571740 : CollatzResearch.WordTrace tailWord_3571740 prefixEnd_3571740 1834019392889960784523873 := by
  unfold tailWord_3571740
  simp only [CollatzResearch.WordTrace]
  refine ⟨65136030040101729736080337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86848040053468972981440449 65136030040101729736080337)
  ·
    refine ⟨48852022530076297302060253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65136030040101729736080337 48852022530076297302060253)
    ·
      refine ⟨18319508448778611488272595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48852022530076297302060253 18319508448778611488272595)
      ·
        refine ⟨27479262673167917232408893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18319508448778611488272595 27479262673167917232408893)
        ·
          refine ⟨10304723502437968962153335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27479262673167917232408893 10304723502437968962153335)
          ·
            refine ⟨15457085253656953443230003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10304723502437968962153335 15457085253656953443230003)
            ·
              refine ⟨23185627880485430164845005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15457085253656953443230003 23185627880485430164845005)
              ·
                refine ⟨8694610455182036311816877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23185627880485430164845005 8694610455182036311816877)
                ·
                  refine ⟨3260478920693263616931329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8694610455182036311816877 3260478920693263616931329)
                  ·
                    refine ⟨2445359190519947712698497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3260478920693263616931329 2445359190519947712698497)
                    ·
                      refine ⟨1834019392889960784523873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2445359190519947712698497 1834019392889960784523873)
                      ·
                        rfl

theorem cell23_3571740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 1, 3, 3, 2, 2].length) (baseStart_3571740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3571740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3571740 prefixEnd_3571740 := by exact prefixLift 3571740
  have htrace : WordTrace (prefixWord ++ tailWord_3571740) baseStart_3571740 baseEnd_3571740 := by
    simpa [prefixWord, tailWord_3571740, baseEnd_3571740] using wordTrace_append hprefix tailTrace_3571740
  have hstable : (prefixWord ++ tailWord_3571740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3571740).length < 2 ^ (prefixWord ++ tailWord_3571740).sum := by decide
  have hdescent : baseEnd_3571740 < baseStart_3571740 := by decide
  rcases family_descends (prefixWord ++ tailWord_3571740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3571756 : List Nat := [2, 2, 1, 1, 1, 2, 2, 5, 1, 3, 3]
def baseStart_3571756 : Nat := 118140960795 + 3571756 * 2 ^ 59
def prefixEnd_3571756 : Nat := 4983230072969 + 3 ^ 40 * 3571756 * 2
def baseEnd_3571756 : Nat := 1834027608580432721923799

theorem tailTrace_3571756 : CollatzResearch.WordTrace tailWord_3571756 prefixEnd_3571756 1834027608580432721923799 := by
  unfold tailWord_3571756
  simp only [CollatzResearch.WordTrace]
  refine ⟨65136321824072747102371561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86848429098763662803162081 65136321824072747102371561)
  ·
    refine ⟨48852241368054560326778671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65136321824072747102371561 48852241368054560326778671)
    ·
      refine ⟨73278362052081840490168007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48852241368054560326778671 73278362052081840490168007)
      ·
        refine ⟨109917543078122760735252011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73278362052081840490168007 109917543078122760735252011)
        ·
          refine ⟨164876314617184141102878017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109917543078122760735252011 164876314617184141102878017)
          ·
            refine ⟨123657235962888105827158513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 164876314617184141102878017 123657235962888105827158513)
            ·
              refine ⟨92742926972166079370368885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 123657235962888105827158513 92742926972166079370368885)
              ·
                refine ⟨8694649403640569940972083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 92742926972166079370368885 8694649403640569940972083)
                ·
                  refine ⟨13041974105460854911458125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8694649403640569940972083 13041974105460854911458125)
                  ·
                    refine ⟨4890740289547820591796797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13041974105460854911458125 4890740289547820591796797)
                    ·
                      refine ⟨1834027608580432721923799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4890740289547820591796797 1834027608580432721923799)
                      ·
                        rfl

theorem cell23_3571756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 3, 3].length) (baseStart_3571756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3571756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3571756 prefixEnd_3571756 := by exact prefixLift 3571756
  have htrace : WordTrace (prefixWord ++ tailWord_3571756) baseStart_3571756 baseEnd_3571756 := by
    simpa [prefixWord, tailWord_3571756, baseEnd_3571756] using wordTrace_append hprefix tailTrace_3571756
  have hstable : (prefixWord ++ tailWord_3571756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3571756).length < 2 ^ (prefixWord ++ tailWord_3571756).sum := by decide
  have hdescent : baseEnd_3571756 < baseStart_3571756 := by decide
  rcases family_descends (prefixWord ++ tailWord_3571756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3571773 : List Nat := [1, 4, 1, 3, 1, 1, 1, 1, 6, 1, 3]
def baseStart_3571773 : Nat := 118140960795 + 3571773 * 2 ^ 59
def prefixEnd_3571773 : Nat := 4983230072969 + 3 ^ 40 * 3571773 * 2
def baseEnd_3571773 : Nat := 1834036337751559155411221

theorem tailTrace_3571773 : CollatzResearch.WordTrace tailWord_3571773 prefixEnd_3571773 1834036337751559155411221 := by
  unfold tailWord_3571773
  simp only [CollatzResearch.WordTrace]
  refine ⟨130273263689083906108111973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86848842459389270738741315 130273263689083906108111973)
  ·
    refine ⟨24426236941703232395270995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 130273263689083906108111973 24426236941703232395270995)
    ·
      refine ⟨36639355412554848592906493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24426236941703232395270995 36639355412554848592906493)
      ·
        refine ⟨13739758279708068222339935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36639355412554848592906493 13739758279708068222339935)
        ·
          refine ⟨20609637419562102333509903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13739758279708068222339935 20609637419562102333509903)
          ·
            refine ⟨30914456129343153500264855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20609637419562102333509903 30914456129343153500264855)
            ·
              refine ⟨46371684194014730250397283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30914456129343153500264855 46371684194014730250397283)
              ·
                refine ⟨69557526291022095375595925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46371684194014730250397283 69557526291022095375595925)
                ·
                  refine ⟨3260509044891660720731059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 69557526291022095375595925 3260509044891660720731059)
                  ·
                    refine ⟨4890763567337491081096589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3260509044891660720731059 4890763567337491081096589)
                    ·
                      refine ⟨1834036337751559155411221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4890763567337491081096589 1834036337751559155411221)
                      ·
                        rfl

theorem cell23_3571773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 1, 6, 1, 3].length) (baseStart_3571773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3571773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3571773 prefixEnd_3571773 := by exact prefixLift 3571773
  have htrace : WordTrace (prefixWord ++ tailWord_3571773) baseStart_3571773 baseEnd_3571773 := by
    simpa [prefixWord, tailWord_3571773, baseEnd_3571773] using wordTrace_append hprefix tailTrace_3571773
  have hstable : (prefixWord ++ tailWord_3571773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3571773).length < 2 ^ (prefixWord ++ tailWord_3571773).sum := by decide
  have hdescent : baseEnd_3571773 < baseStart_3571773 := by decide
  rcases family_descends (prefixWord ++ tailWord_3571773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3571796 : List Nat := [2, 4, 1, 1, 1, 1, 1, 3, 2, 3, 4]
def baseStart_3571796 : Nat := 118140960795 + 3571796 * 2 ^ 59
def prefixEnd_3571796 : Nat := 4983230072969 + 3 ^ 40 * 3571796 * 2
def baseEnd_3571796 : Nat := 1834048147806612565423615

theorem tailTrace_3571796 : CollatzResearch.WordTrace tailWord_3571796 prefixEnd_3571796 1834048147806612565423615 := by
  unfold tailWord_3571796
  simp only [CollatzResearch.WordTrace]
  refine ⟨65137051284000290518099621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86849401712000387357466161 65137051284000290518099621)
  ·
    refine ⟨12213197115750054472143679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 65137051284000290518099621 12213197115750054472143679)
    ·
      refine ⟨18319795673625081708215519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12213197115750054472143679 18319795673625081708215519)
      ·
        refine ⟨27479693510437622562323279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18319795673625081708215519 27479693510437622562323279)
        ·
          refine ⟨41219540265656433843484919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27479693510437622562323279 41219540265656433843484919)
          ·
            refine ⟨61829310398484650765227379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41219540265656433843484919 61829310398484650765227379)
            ·
              refine ⟨92743965597726976147841069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61829310398484650765227379 92743965597726976147841069)
              ·
                refine ⟨34778987099147616055440401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 92743965597726976147841069 34778987099147616055440401)
                ·
                  refine ⟨26084240324360712041580301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34778987099147616055440401 26084240324360712041580301)
                  ·
                    refine ⟨9781590121635267015592613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26084240324360712041580301 9781590121635267015592613)
                    ·
                      refine ⟨1834048147806612565423615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9781590121635267015592613 1834048147806612565423615)
                      ·
                        rfl

theorem cell23_3571796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 3, 2, 3, 4].length) (baseStart_3571796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3571796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3571796 prefixEnd_3571796 := by exact prefixLift 3571796
  have htrace : WordTrace (prefixWord ++ tailWord_3571796) baseStart_3571796 baseEnd_3571796 := by
    simpa [prefixWord, tailWord_3571796, baseEnd_3571796] using wordTrace_append hprefix tailTrace_3571796
  have hstable : (prefixWord ++ tailWord_3571796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3571796).length < 2 ^ (prefixWord ++ tailWord_3571796).sum := by decide
  have hdescent : baseEnd_3571796 < baseStart_3571796 := by decide
  rcases family_descends (prefixWord ++ tailWord_3571796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3571830 : List Nat := [5, 1, 1, 2, 1, 2, 1, 1, 3, 4, 2]
def baseStart_3571830 : Nat := 118140960795 + 3571830 * 2 ^ 59
def prefixEnd_3571830 : Nat := 4983230072969 + 3 ^ 40 * 3571830 * 2
def baseEnd_3571830 : Nat := 1834065606148865432398459

theorem tailTrace_3571830 : CollatzResearch.WordTrace tailWord_3571830 prefixEnd_3571830 1834065606148865432398459 := by
  unfold tailWord_3571830
  simp only [CollatzResearch.WordTrace]
  refine ⟨8142208915617337802683559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 86850228433251603228624629 8142208915617337802683559)
  ·
    refine ⟨12213313373426006704025339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8142208915617337802683559 12213313373426006704025339)
    ·
      refine ⟨18319970060139010056038009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12213313373426006704025339 18319970060139010056038009)
      ·
        refine ⟨13739977545104257542028507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18319970060139010056038009 13739977545104257542028507)
        ·
          refine ⟨20609966317656386313042761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13739977545104257542028507 20609966317656386313042761)
          ·
            refine ⟨15457474738242289734782071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20609966317656386313042761 15457474738242289734782071)
            ·
              refine ⟨23186212107363434602173107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15457474738242289734782071 23186212107363434602173107)
              ·
                refine ⟨34779318161045151903259661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23186212107363434602173107 34779318161045151903259661)
                ·
                  refine ⟨13042244310391931963722373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34779318161045151903259661 13042244310391931963722373)
                  ·
                    refine ⟨2445420808198487243197945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13042244310391931963722373 2445420808198487243197945)
                    ·
                      refine ⟨1834065606148865432398459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2445420808198487243197945 1834065606148865432398459)
                      ·
                        rfl

theorem cell23_3571830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 1, 1, 3, 4, 2].length) (baseStart_3571830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3571830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3571830 prefixEnd_3571830 := by exact prefixLift 3571830
  have htrace : WordTrace (prefixWord ++ tailWord_3571830) baseStart_3571830 baseEnd_3571830 := by
    simpa [prefixWord, tailWord_3571830, baseEnd_3571830] using wordTrace_append hprefix tailTrace_3571830
  have hstable : (prefixWord ++ tailWord_3571830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3571830).length < 2 ^ (prefixWord ++ tailWord_3571830).sum := by decide
  have hdescent : baseEnd_3571830 < baseStart_3571830 := by decide
  rcases family_descends (prefixWord ++ tailWord_3571830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3571870 : List Nat := [4, 3, 1, 1, 3, 1, 1, 2, 7]
def baseStart_3571870 : Nat := 118140960795 + 3571870 * 2 ^ 59
def prefixEnd_3571870 : Nat := 4983230072969 + 3 ^ 40 * 3571870 * 2
def baseEnd_3571870 : Nat := 203787349486116141766475

theorem tailTrace_3571870 : CollatzResearch.WordTrace tailWord_3571870 prefixEnd_3571870 203787349486116141766475 := by
  unfold tailWord_3571870
  simp only [CollatzResearch.WordTrace]
  refine ⟨16284600196216561459299133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 86851201046488327782928709 16284600196216561459299133)
  ·
    refine ⟨6106725073581210547237175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16284600196216561459299133 6106725073581210547237175)
    ·
      refine ⟨9160087610371815820855763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6106725073581210547237175 9160087610371815820855763)
      ·
        refine ⟨13740131415557723731283645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9160087610371815820855763 13740131415557723731283645)
        ·
          refine ⟨5152549280834146399231367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13740131415557723731283645 5152549280834146399231367)
          ·
            refine ⟨7728823921251219598847051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5152549280834146399231367 7728823921251219598847051)
            ·
              refine ⟨11593235881876829398270577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7728823921251219598847051 11593235881876829398270577)
              ·
                refine ⟨8694926911407622048702933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11593235881876829398270577 8694926911407622048702933)
                ·
                  refine ⟨203787349486116141766475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8694926911407622048702933 203787349486116141766475)
                  ·
                    rfl

theorem cell23_3571870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 1, 2, 7].length) (baseStart_3571870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3571870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3571870 prefixEnd_3571870 := by exact prefixLift 3571870
  have htrace : WordTrace (prefixWord ++ tailWord_3571870) baseStart_3571870 baseEnd_3571870 := by
    simpa [prefixWord, tailWord_3571870, baseEnd_3571870] using wordTrace_append hprefix tailTrace_3571870
  have hstable : (prefixWord ++ tailWord_3571870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3571870).length < 2 ^ (prefixWord ++ tailWord_3571870).sum := by decide
  have hdescent : baseEnd_3571870 < baseStart_3571870 := by decide
  rcases family_descends (prefixWord ++ tailWord_3571870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3571938 : List Nat := [3, 3, 4, 1, 2, 1, 1, 3, 5]
def baseStart_3571938 : Nat := 118140960795 + 3571938 * 2 ^ 59
def prefixEnd_3571938 : Nat := 4983230072969 + 3 ^ 40 * 3571938 * 2
def baseEnd_3571938 : Nat := 203791229117727889983107

theorem tailTrace_3571938 : CollatzResearch.WordTrace tailWord_3571938 prefixEnd_3571938 203791229117727889983107 := by
  unfold tailWord_3571938
  simp only [CollatzResearch.WordTrace]
  refine ⟨32569820433371534821967117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86852854488990759525245645 32569820433371534821967117)
  ·
    refine ⟨12213682662514325558237669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32569820433371534821967117 12213682662514325558237669)
    ·
      refine ⟨2290065499221436042169563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12213682662514325558237669 2290065499221436042169563)
      ·
        refine ⟨3435098248832154063254345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2290065499221436042169563 3435098248832154063254345)
        ·
          refine ⟨2576323686624115547440759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3435098248832154063254345 2576323686624115547440759)
          ·
            refine ⟨3864485529936173321161139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2576323686624115547440759 3864485529936173321161139)
            ·
              refine ⟨5796728294904259981741709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3864485529936173321161139 5796728294904259981741709)
              ·
                refine ⟨2173773110589097493153141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5796728294904259981741709 2173773110589097493153141)
                ·
                  refine ⟨203791229117727889983107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2173773110589097493153141 203791229117727889983107)
                  ·
                    rfl

theorem cell23_3571938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 2, 1, 1, 3, 5].length) (baseStart_3571938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3571938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3571938 prefixEnd_3571938 := by exact prefixLift 3571938
  have htrace : WordTrace (prefixWord ++ tailWord_3571938) baseStart_3571938 baseEnd_3571938 := by
    simpa [prefixWord, tailWord_3571938, baseEnd_3571938] using wordTrace_append hprefix tailTrace_3571938
  have hstable : (prefixWord ++ tailWord_3571938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3571938).length < 2 ^ (prefixWord ++ tailWord_3571938).sum := by decide
  have hdescent : baseEnd_3571938 < baseStart_3571938 := by decide
  rcases family_descends (prefixWord ++ tailWord_3571938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3571943 : List Nat := [1, 1, 5, 3, 1, 1, 1, 2, 8]
def baseStart_3571943 : Nat := 118140960795 + 3571943 * 2 ^ 59
def prefixEnd_3571943 : Nat := 4983230072969 + 3 ^ 40 * 3571943 * 2
def baseEnd_3571943 : Nat := 203791514384758165587271

theorem tailTrace_3571943 : CollatzResearch.WordTrace tailWord_3571943 prefixEnd_3571943 203791514384758165587271 := by
  unfold tailWord_3571943
  simp only [CollatzResearch.WordTrace]
  refine ⟨130279464098468025141800483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86852976065645350094533655 130279464098468025141800483)
  ·
    refine ⟨195419196147702037712700725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130279464098468025141800483 195419196147702037712700725)
    ·
      refine ⟨18320549638847066035565693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 195419196147702037712700725 18320549638847066035565693)
      ·
        refine ⟨6870206114567649763337135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18320549638847066035565693 6870206114567649763337135)
        ·
          refine ⟨10305309171851474645005703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6870206114567649763337135 10305309171851474645005703)
          ·
            refine ⟨15457963757777211967508555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10305309171851474645005703 15457963757777211967508555)
            ·
              refine ⟨23186945636665817951262833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15457963757777211967508555 23186945636665817951262833)
              ·
                refine ⟨17390209227499363463447125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23186945636665817951262833 17390209227499363463447125)
                ·
                  refine ⟨203791514384758165587271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 17390209227499363463447125 203791514384758165587271)
                  ·
                    rfl

theorem cell23_3571943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 1, 2, 8].length) (baseStart_3571943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3571943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3571943 prefixEnd_3571943 := by exact prefixLift 3571943
  have htrace : WordTrace (prefixWord ++ tailWord_3571943) baseStart_3571943 baseEnd_3571943 := by
    simpa [prefixWord, tailWord_3571943, baseEnd_3571943] using wordTrace_append hprefix tailTrace_3571943
  have hstable : (prefixWord ++ tailWord_3571943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3571943).length < 2 ^ (prefixWord ++ tailWord_3571943).sum := by decide
  have hdescent : baseEnd_3571943 < baseStart_3571943 := by decide
  rcases family_descends (prefixWord ++ tailWord_3571943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3571963 : List Nat := [1, 1, 1, 1, 1, 3, 1, 1, 2, 9, 2]
def baseStart_3571963 : Nat := 118140960795 + 3571963 * 2 ^ 59
def prefixEnd_3571963 : Nat := 4983230072969 + 3 ^ 40 * 3571963 * 2
def baseEnd_3571963 : Nat := 1834133899075913412035347

theorem tailTrace_3571963 : CollatzResearch.WordTrace tailWord_3571963 prefixEnd_3571963 1834133899075913412035347 := by
  unfold tailWord_3571963
  simp only [CollatzResearch.WordTrace]
  refine ⟨130280193558395568557528543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86853462372263712371685695 130280193558395568557528543)
  ·
    refine ⟨195420290337593352836292815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130280193558395568557528543 195420290337593352836292815)
    ·
      refine ⟨293130435506390029254439223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195420290337593352836292815 293130435506390029254439223)
      ·
        refine ⟨439695653259585043881658835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 293130435506390029254439223 439695653259585043881658835)
        ·
          refine ⟨659543479889377565822488253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 439695653259585043881658835 659543479889377565822488253)
          ·
            refine ⟨247328804958516587183433095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 659543479889377565822488253 247328804958516587183433095)
            ·
              refine ⟨370993207437774880775149643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 247328804958516587183433095 370993207437774880775149643)
              ·
                refine ⟨556489811156662321162724465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 370993207437774880775149643 556489811156662321162724465)
                ·
                  refine ⟨417367358367496740872043349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 556489811156662321162724465 417367358367496740872043349)
                  ·
                    refine ⟨2445511865434551216047129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 417367358367496740872043349 2445511865434551216047129)
                    ·
                      refine ⟨1834133899075913412035347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2445511865434551216047129 1834133899075913412035347)
                      ·
                        rfl

theorem cell23_3571963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 2, 9, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 2, 9, 2].length) (baseStart_3571963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3571963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3571963 prefixEnd_3571963 := by exact prefixLift 3571963
  have htrace : WordTrace (prefixWord ++ tailWord_3571963) baseStart_3571963 baseEnd_3571963 := by
    simpa [prefixWord, tailWord_3571963, baseEnd_3571963] using wordTrace_append hprefix tailTrace_3571963
  have hstable : (prefixWord ++ tailWord_3571963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3571963).length < 2 ^ (prefixWord ++ tailWord_3571963).sum := by decide
  have hdescent : baseEnd_3571963 < baseStart_3571963 := by decide
  rcases family_descends (prefixWord ++ tailWord_3571963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3571964 : List Nat := [2, 2, 2, 1, 4, 2, 3, 2, 1, 4]
def baseStart_3571964 : Nat := 118140960795 + 3571964 * 2 ^ 59
def prefixEnd_3571964 : Nat := 4983230072969 + 3 ^ 40 * 3571964 * 2
def baseEnd_3571964 : Nat := 611378137518855969374281

theorem tailTrace_3571964 : CollatzResearch.WordTrace tailWord_3571964 prefixEnd_3571964 611378137518855969374281 := by
  unfold tailWord_3571964
  simp only [CollatzResearch.WordTrace]
  refine ⟨65140115015695972864157473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86853486687594630485543297 65140115015695972864157473)
  ·
    refine ⟨48855086261771979648118105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65140115015695972864157473 48855086261771979648118105)
    ·
      refine ⟨36641314696328984736088579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48855086261771979648118105 36641314696328984736088579)
      ·
        refine ⟨54961972044493477104132869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36641314696328984736088579 54961972044493477104132869)
        ·
          refine ⟨10305369758342526957024913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 54961972044493477104132869 10305369758342526957024913)
          ·
            refine ⟨7729027318756895217768685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10305369758342526957024913 7729027318756895217768685)
            ·
              refine ⟨2898385244533835706663257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7729027318756895217768685 2898385244533835706663257)
              ·
                refine ⟨2173788933400376779997443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2898385244533835706663257 2173788933400376779997443)
                ·
                  refine ⟨3260683400100565169996165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2173788933400376779997443 3260683400100565169996165)
                  ·
                    refine ⟨611378137518855969374281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3260683400100565169996165 611378137518855969374281)
                    ·
                      rfl

theorem cell23_3571964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 3, 2, 1, 4].length) (baseStart_3571964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3571964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3571964 prefixEnd_3571964 := by exact prefixLift 3571964
  have htrace : WordTrace (prefixWord ++ tailWord_3571964) baseStart_3571964 baseEnd_3571964 := by
    simpa [prefixWord, tailWord_3571964, baseEnd_3571964] using wordTrace_append hprefix tailTrace_3571964
  have hstable : (prefixWord ++ tailWord_3571964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3571964).length < 2 ^ (prefixWord ++ tailWord_3571964).sum := by decide
  have hdescent : baseEnd_3571964 < baseStart_3571964 := by decide
  rcases family_descends (prefixWord ++ tailWord_3571964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3571980 : List Nat := [2, 2, 1, 2, 2, 2, 1, 2, 4, 3, 2]
def baseStart_3571980 : Nat := 118140960795 + 3571980 * 2 ^ 59
def prefixEnd_3571980 : Nat := 4983230072969 + 3 ^ 40 * 3571980 * 2
def baseEnd_3571980 : Nat := 1834142628247039845522769

theorem tailTrace_3571980 : CollatzResearch.WordTrace tailWord_3571980 prefixEnd_3571980 1834142628247039845522769 := by
  unfold tailWord_3571980
  simp only [CollatzResearch.WordTrace]
  refine ⟨65140406799666990230448697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86853875732889320307264929 65140406799666990230448697)
  ·
    refine ⟨48855305099750242672836523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65140406799666990230448697 48855305099750242672836523)
    ·
      refine ⟨73282957649625364009254785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48855305099750242672836523 73282957649625364009254785)
      ·
        refine ⟨54962218237219023006941089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73282957649625364009254785 54962218237219023006941089)
        ·
          refine ⟨41221663677914267255205817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54962218237219023006941089 41221663677914267255205817)
          ·
            refine ⟨30916247758435700441404363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41221663677914267255205817 30916247758435700441404363)
            ·
              refine ⟨46374371637653550662106545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30916247758435700441404363 46374371637653550662106545)
              ·
                refine ⟨34780778728240162996579909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46374371637653550662106545 34780778728240162996579909)
                ·
                  refine ⟨6521396011545030561858733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34780778728240162996579909 6521396011545030561858733)
                  ·
                    refine ⟨2445523504329386460697025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6521396011545030561858733 2445523504329386460697025)
                    ·
                      refine ⟨1834142628247039845522769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2445523504329386460697025 1834142628247039845522769)
                      ·
                        rfl

theorem cell23_3571980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 2, 4, 3, 2].length) (baseStart_3571980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3571980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3571980 prefixEnd_3571980 := by exact prefixLift 3571980
  have htrace : WordTrace (prefixWord ++ tailWord_3571980) baseStart_3571980 baseEnd_3571980 := by
    simpa [prefixWord, tailWord_3571980, baseEnd_3571980] using wordTrace_append hprefix tailTrace_3571980
  have hstable : (prefixWord ++ tailWord_3571980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3571980).length < 2 ^ (prefixWord ++ tailWord_3571980).sum := by decide
  have hdescent : baseEnd_3571980 < baseStart_3571980 := by decide
  rcases family_descends (prefixWord ++ tailWord_3571980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3572003 : List Nat := [1, 1, 1, 4, 2, 2, 3, 2, 1, 6]
def baseStart_3572003 : Nat := 118140960795 + 3572003 * 2 ^ 59
def prefixEnd_3572003 : Nat := 4983230072969 + 3 ^ 40 * 3572003 * 2
def baseEnd_3572003 : Nat := 611384812767364418511721

theorem tailTrace_3572003 : CollatzResearch.WordTrace tailWord_3572003 prefixEnd_3572003 611384812767364418511721 := by
  unfold tailWord_3572003
  simp only [CollatzResearch.WordTrace]
  refine ⟨130281652478250655388984663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86854434985500436925989775 130281652478250655388984663)
  ·
    refine ⟨195422478717375983083476995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130281652478250655388984663 195422478717375983083476995)
    ·
      refine ⟨293133718076063974625215493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195422478717375983083476995 293133718076063974625215493)
      ·
        refine ⟨54962572139261995242227905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 293133718076063974625215493 54962572139261995242227905)
        ·
          refine ⟨41221929104446496431670929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54962572139261995242227905 41221929104446496431670929)
          ·
            refine ⟨30916446828334872323753197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41221929104446496431670929 30916446828334872323753197)
            ·
              refine ⟨11593667560625577121407449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30916446828334872323753197 11593667560625577121407449)
              ·
                refine ⟨8695250670469182841055587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11593667560625577121407449 8695250670469182841055587)
                ·
                  refine ⟨13042876005703774261583381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8695250670469182841055587 13042876005703774261583381)
                  ·
                    refine ⟨611384812767364418511721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13042876005703774261583381 611384812767364418511721)
                    ·
                      rfl

theorem cell23_3572003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 3, 2, 1, 6].length) (baseStart_3572003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3572003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3572003 prefixEnd_3572003 := by exact prefixLift 3572003
  have htrace : WordTrace (prefixWord ++ tailWord_3572003) baseStart_3572003 baseEnd_3572003 := by
    simpa [prefixWord, tailWord_3572003, baseEnd_3572003] using wordTrace_append hprefix tailTrace_3572003
  have hstable : (prefixWord ++ tailWord_3572003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3572003).length < 2 ^ (prefixWord ++ tailWord_3572003).sum := by decide
  have hdescent : baseEnd_3572003 < baseStart_3572003 := by decide
  rcases family_descends (prefixWord ++ tailWord_3572003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3572077 : List Nat := [1, 5, 1, 1, 1, 2, 3, 1, 4, 1, 3]
def baseStart_3572077 : Nat := 118140960795 + 3572077 * 2 ^ 59
def prefixEnd_3572077 : Nat := 4983230072969 + 3 ^ 40 * 3572077 * 2
def baseEnd_3572077 : Nat := 1834192435870525966009823

theorem tailTrace_3572077 : CollatzResearch.WordTrace tailWord_3572077 prefixEnd_3572077 1834192435870525966009823 := by
  unfold tailWord_3572077
  simp only [CollatzResearch.WordTrace]
  refine ⟨130284351479982566027178485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86856234319988377351452323 130284351479982566027178485)
  ·
    refine ⟨12214157951248365565047983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 130284351479982566027178485 12214157951248365565047983)
    ·
      refine ⟨18321236926872548347571975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12214157951248365565047983 18321236926872548347571975)
      ·
        refine ⟨27481855390308822521357963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18321236926872548347571975 27481855390308822521357963)
        ·
          refine ⟨41222783085463233782036945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27481855390308822521357963 41222783085463233782036945)
          ·
            refine ⟨30917087314097425336527709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41222783085463233782036945 30917087314097425336527709)
            ·
              refine ⟨11593907742786534501197891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30917087314097425336527709 11593907742786534501197891)
              ·
                refine ⟨17390861614179801751796837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11593907742786534501197891 17390861614179801751796837)
                ·
                  refine ⟨3260786552658712828461907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17390861614179801751796837 3260786552658712828461907)
                  ·
                    refine ⟨4891179828988069242692861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3260786552658712828461907 4891179828988069242692861)
                    ·
                      refine ⟨1834192435870525966009823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4891179828988069242692861 1834192435870525966009823)
                      ·
                        rfl

theorem cell23_3572077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 3, 1, 4, 1, 3].length) (baseStart_3572077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3572077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3572077 prefixEnd_3572077 := by exact prefixLift 3572077
  have htrace : WordTrace (prefixWord ++ tailWord_3572077) baseStart_3572077 baseEnd_3572077 := by
    simpa [prefixWord, tailWord_3572077, baseEnd_3572077] using wordTrace_append hprefix tailTrace_3572077
  have hstable : (prefixWord ++ tailWord_3572077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3572077).length < 2 ^ (prefixWord ++ tailWord_3572077).sum := by decide
  have hdescent : baseEnd_3572077 < baseStart_3572077 := by decide
  rcases family_descends (prefixWord ++ tailWord_3572077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3572104 : List Nat := [2, 1, 3, 3, 1, 1, 4, 2, 1, 3, 2]
def baseStart_3572104 : Nat := 118140960795 + 3572104 * 2 ^ 59
def prefixEnd_3572104 : Nat := 4983230072969 + 3 ^ 40 * 3572104 * 2
def baseEnd_3572104 : Nat := 1834206299848197360372199

theorem tailTrace_3572104 : CollatzResearch.WordTrace tailWord_3572104 prefixEnd_3572104 1834206299848197360372199 := by
  unfold tailWord_3572104
  simp only [CollatzResearch.WordTrace]
  refine ⟨65142668125442374819205683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86856890833923166425607577 65142668125442374819205683)
  ·
    refine ⟨97714002188163562228808525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65142668125442374819205683 97714002188163562228808525)
    ·
      refine ⟨36642750820561335835803197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 97714002188163562228808525 36642750820561335835803197)
      ·
        refine ⟨13741031557710500938426199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36642750820561335835803197 13741031557710500938426199)
        ·
          refine ⟨20611547336565751407639299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13741031557710500938426199 20611547336565751407639299)
          ·
            refine ⟨30917321004848627111458949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20611547336565751407639299 30917321004848627111458949)
            ·
              refine ⟨5796997688409117583398553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30917321004848627111458949 5796997688409117583398553)
              ·
                refine ⟨4347748266306838187548915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5796997688409117583398553 4347748266306838187548915)
                ·
                  refine ⟨6521622399460257281323373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4347748266306838187548915 6521622399460257281323373)
                  ·
                    refine ⟨2445608399797596480496265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6521622399460257281323373 2445608399797596480496265)
                    ·
                      refine ⟨1834206299848197360372199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2445608399797596480496265 1834206299848197360372199)
                      ·
                        rfl

theorem cell23_3572104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 4, 2, 1, 3, 2].length) (baseStart_3572104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3572104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3572104 prefixEnd_3572104 := by exact prefixLift 3572104
  have htrace : WordTrace (prefixWord ++ tailWord_3572104) baseStart_3572104 baseEnd_3572104 := by
    simpa [prefixWord, tailWord_3572104, baseEnd_3572104] using wordTrace_append hprefix tailTrace_3572104
  have hstable : (prefixWord ++ tailWord_3572104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3572104).length < 2 ^ (prefixWord ++ tailWord_3572104).sum := by decide
  have hdescent : baseEnd_3572104 < baseStart_3572104 := by decide
  rcases family_descends (prefixWord ++ tailWord_3572104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3572120 : List Nat := [2, 1, 2, 5, 1, 1, 1, 1, 1, 3, 5]
def baseStart_3572120 : Nat := 118140960795 + 3572120 * 2 ^ 59
def prefixEnd_3572120 : Nat := 4983230072969 + 3 ^ 40 * 3572120 * 2
def baseEnd_3572120 : Nat := 1834214515538669297772125

theorem tailTrace_3572120 : CollatzResearch.WordTrace tailWord_3572120 prefixEnd_3572120 1834214515538669297772125 := by
  unfold tailWord_3572120
  simp only [CollatzResearch.WordTrace]
  refine ⟨65142959909413392185496907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86857279879217856247329209 65142959909413392185496907)
  ·
    refine ⟨97714439864120088278245361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65142959909413392185496907 97714439864120088278245361)
    ·
      refine ⟨73285829898090066208684021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97714439864120088278245361 73285829898090066208684021)
      ·
        refine ⟨6870546552945943707064127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 73285829898090066208684021 6870546552945943707064127)
        ·
          refine ⟨10305819829418915560596191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6870546552945943707064127 10305819829418915560596191)
          ·
            refine ⟨15458729744128373340894287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10305819829418915560596191 15458729744128373340894287)
            ·
              refine ⟨23188094616192560011341431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15458729744128373340894287 23188094616192560011341431)
              ·
                refine ⟨34782141924288840017012147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23188094616192560011341431 34782141924288840017012147)
                ·
                  refine ⟨52173212886433260025518221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34782141924288840017012147 52173212886433260025518221)
                  ·
                    refine ⟨19564954832412472509569333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 52173212886433260025518221 19564954832412472509569333)
                    ·
                      refine ⟨1834214515538669297772125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19564954832412472509569333 1834214515538669297772125)
                      ·
                        rfl

theorem cell23_3572120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 1, 1, 1, 3, 5].length) (baseStart_3572120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3572120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3572120 prefixEnd_3572120 := by exact prefixLift 3572120
  have htrace : WordTrace (prefixWord ++ tailWord_3572120) baseStart_3572120 baseEnd_3572120 := by
    simpa [prefixWord, tailWord_3572120, baseEnd_3572120] using wordTrace_append hprefix tailTrace_3572120
  have hstable : (prefixWord ++ tailWord_3572120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3572120).length < 2 ^ (prefixWord ++ tailWord_3572120).sum := by decide
  have hdescent : baseEnd_3572120 < baseStart_3572120 := by decide
  rcases family_descends (prefixWord ++ tailWord_3572120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3572133 : List Nat := [1, 3, 1, 2, 1, 1, 3, 1, 1, 2, 7]
def baseStart_3572133 : Nat := 118140960795 + 3572133 * 2 ^ 59
def prefixEnd_3572133 : Nat := 4983230072969 + 3 ^ 40 * 3572133 * 2
def baseEnd_3572133 : Nat := 1834221190787177746909565

theorem tailTrace_3572133 : CollatzResearch.WordTrace tailWord_3572133 prefixEnd_3572133 1834221190787177746909565 := by
  unfold tailWord_3572133
  simp only [CollatzResearch.WordTrace]
  refine ⟨130286393967779687591217053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86857595978519791727478035 130286393967779687591217053)
  ·
    refine ⟨48857397737917382846706395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130286393967779687591217053 48857397737917382846706395)
    ·
      refine ⟨73286096606876074270059593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48857397737917382846706395 73286096606876074270059593)
      ·
        refine ⟨54964572455157055702544695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73286096606876074270059593 54964572455157055702544695)
        ·
          refine ⟨82446858682735583553817043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54964572455157055702544695 82446858682735583553817043)
          ·
            refine ⟨123670288024103375330725565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82446858682735583553817043 123670288024103375330725565)
            ·
              refine ⟨46376358009038765749022087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 123670288024103375330725565 46376358009038765749022087)
              ·
                refine ⟨69564537013558148623533131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46376358009038765749022087 69564537013558148623533131)
                ·
                  refine ⟨104346805520337222935299697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 69564537013558148623533131 104346805520337222935299697)
                  ·
                    refine ⟨78260104140252917201474773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 104346805520337222935299697 78260104140252917201474773)
                    ·
                      refine ⟨1834221190787177746909565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 78260104140252917201474773 1834221190787177746909565)
                      ·
                        rfl

theorem cell23_3572133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 1, 1, 2, 7].length) (baseStart_3572133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3572133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3572133 prefixEnd_3572133 := by exact prefixLift 3572133
  have htrace : WordTrace (prefixWord ++ tailWord_3572133) baseStart_3572133 baseEnd_3572133 := by
    simpa [prefixWord, tailWord_3572133, baseEnd_3572133] using wordTrace_append hprefix tailTrace_3572133
  have hstable : (prefixWord ++ tailWord_3572133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3572133).length < 2 ^ (prefixWord ++ tailWord_3572133).sum := by decide
  have hdescent : baseEnd_3572133 < baseStart_3572133 := by decide
  rcases family_descends (prefixWord ++ tailWord_3572133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3572151 : List Nat := [1, 1, 3, 1, 3, 3, 4, 1, 2, 2, 2]
def baseStart_3572151 : Nat := 118140960795 + 3572151 * 2 ^ 59
def prefixEnd_3572151 : Nat := 4983230072969 + 3 ^ 40 * 3572151 * 2
def baseEnd_3572151 : Nat := 1834230433438958676484483

theorem tailTrace_3572151 : CollatzResearch.WordTrace tailWord_3572151 prefixEnd_3572151 1834230433438958676484483 := by
  unfold tailWord_3572151
  simp only [CollatzResearch.WordTrace]
  refine ⟨130287050481714476665372307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86858033654476317776914871 130287050481714476665372307)
  ·
    refine ⟨195430575722571714998058461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130287050481714476665372307 195430575722571714998058461)
    ·
      refine ⟨73286465895964393124271923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 195430575722571714998058461 73286465895964393124271923)
      ·
        refine ⟨109929698843946589686407885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73286465895964393124271923 109929698843946589686407885)
        ·
          refine ⟨41223637066479971132402957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 109929698843946589686407885 41223637066479971132402957)
          ·
            refine ⟨15458863899929989174651109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41223637066479971132402957 15458863899929989174651109)
            ·
              refine ⟨2898536981236872970247083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15458863899929989174651109 2898536981236872970247083)
              ·
                refine ⟨4347805471855309455370625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2898536981236872970247083 4347805471855309455370625)
                ·
                  refine ⟨3260854103891482091527969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4347805471855309455370625 3260854103891482091527969)
                  ·
                    refine ⟨2445640577918611568645977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3260854103891482091527969 2445640577918611568645977)
                    ·
                      refine ⟨1834230433438958676484483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2445640577918611568645977 1834230433438958676484483)
                      ·
                        rfl

theorem cell23_3572151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 4, 1, 2, 2, 2].length) (baseStart_3572151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3572151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3572151 prefixEnd_3572151 := by exact prefixLift 3572151
  have htrace : WordTrace (prefixWord ++ tailWord_3572151) baseStart_3572151 baseEnd_3572151 := by
    simpa [prefixWord, tailWord_3572151, baseEnd_3572151] using wordTrace_append hprefix tailTrace_3572151
  have hstable : (prefixWord ++ tailWord_3572151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3572151).length < 2 ^ (prefixWord ++ tailWord_3572151).sum := by decide
  have hdescent : baseEnd_3572151 < baseStart_3572151 := by decide
  rcases family_descends (prefixWord ++ tailWord_3572151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
