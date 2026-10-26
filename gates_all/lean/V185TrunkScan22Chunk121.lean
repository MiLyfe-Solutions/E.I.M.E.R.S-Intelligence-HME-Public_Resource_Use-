import V185TrunkScan22Chunk120

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_1082979 : List Nat := [1, 1, 1, 5, 1, 4, 2, 3, 1, 3]
def baseStart_1082979 : Nat := 118140960795 + 1082979 * 2 ^ 59
def prefixEnd_1082979 : Nat := 4983230072969 + 3 ^ 40 * 1082979 * 2
def baseEnd_1082979 : Nat := 370725843817082382254651

theorem tailTrace_1082979 : CollatzResearch.WordTrace tailWord_1082979 prefixEnd_1082979 370725843817082382254651 := by
  unfold tailWord_1082979
  simp only [CollatzResearch.WordTrace]
  refine ⟨39499489143559515933043991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26332992762373010622029327 39499489143559515933043991)
  ·
    refine ⟨59249233715339273899565987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39499489143559515933043991 59249233715339273899565987)
    ·
      refine ⟨88873850573008910849348981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59249233715339273899565987 88873850573008910849348981)
      ·
        refine ⟨8331923491219585392126467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 88873850573008910849348981 8331923491219585392126467)
        ·
          refine ⟨12497885236829378088189701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8331923491219585392126467 12497885236829378088189701)
          ·
            refine ⟨2343353481905508391535569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12497885236829378088189701 2343353481905508391535569)
            ·
              refine ⟨1757515111429131293651677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2343353481905508391535569 1757515111429131293651677)
              ·
                refine ⟨659068166785924235119379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1757515111429131293651677 659068166785924235119379)
                ·
                  refine ⟨988602250178886352679069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 659068166785924235119379 988602250178886352679069)
                  ·
                    refine ⟨370725843817082382254651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 988602250178886352679069 370725843817082382254651)
                    ·
                      rfl

theorem cell22_1082979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 2, 3, 1, 3].length) (baseStart_1082979 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1082979 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1082979 prefixEnd_1082979 := by exact prefixLift 1082979
  have htrace : WordTrace (prefixWord ++ tailWord_1082979) baseStart_1082979 baseEnd_1082979 := by
    simpa [prefixWord, tailWord_1082979, baseEnd_1082979] using wordTrace_append hprefix tailTrace_1082979
  have hstable : (prefixWord ++ tailWord_1082979).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1082979).length < 2 ^ (prefixWord ++ tailWord_1082979).sum := by decide
  have hdescent : baseEnd_1082979 < baseStart_1082979 := by decide
  rcases family_descends (prefixWord ++ tailWord_1082979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1082992 : List Nat := [2, 1, 1, 1, 6, 3, 1, 2, 5]
def baseStart_1082992 : Nat := 118140960795 + 1082992 * 2 ^ 59
def prefixEnd_1082992 : Nat := 4983230072969 + 3 ^ 40 * 1082992 * 2
def baseEnd_1082992 : Nat := 123576764660918227226537

theorem tailTrace_1082992 : CollatzResearch.WordTrace tailWord_1082992 prefixEnd_1082992 123576764660918227226537 := by
  unfold tailWord_1082992
  simp only [CollatzResearch.WordTrace]
  refine ⟨19749981646256209576633615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26333308861674946102178153 19749981646256209576633615)
  ·
    refine ⟨29624972469384314364950423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19749981646256209576633615 29624972469384314364950423)
    ·
      refine ⟨44437458704076471547425635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29624972469384314364950423 44437458704076471547425635)
      ·
        refine ⟨66656188056114707321138453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44437458704076471547425635 66656188056114707321138453)
        ·
          refine ⟨3124508815130376905678365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 66656188056114707321138453 3124508815130376905678365)
          ·
            refine ⟨1171690805673891339629387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3124508815130376905678365 1171690805673891339629387)
            ·
              refine ⟨1757536208510837009444081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1171690805673891339629387 1757536208510837009444081)
              ·
                refine ⟨1318152156383127757083061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1757536208510837009444081 1318152156383127757083061)
                ·
                  refine ⟨123576764660918227226537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1318152156383127757083061 123576764660918227226537)
                  ·
                    rfl

theorem cell22_1082992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 3, 1, 2, 5].length) (baseStart_1082992 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1082992 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1082992 prefixEnd_1082992 := by exact prefixLift 1082992
  have htrace : WordTrace (prefixWord ++ tailWord_1082992) baseStart_1082992 baseEnd_1082992 := by
    simpa [prefixWord, tailWord_1082992, baseEnd_1082992] using wordTrace_append hprefix tailTrace_1082992
  have hstable : (prefixWord ++ tailWord_1082992).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1082992).length < 2 ^ (prefixWord ++ tailWord_1082992).sum := by decide
  have hdescent : baseEnd_1082992 < baseStart_1082992 := by decide
  rcases family_descends (prefixWord ++ tailWord_1082992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1083022 : List Nat := [4, 1, 1, 3, 1, 2, 1, 4, 1, 4]
def baseStart_1083022 : Nat := 118140960795 + 1083022 * 2 ^ 59
def prefixEnd_1083022 : Nat := 4983230072969 + 3 ^ 40 * 1083022 * 2
def baseEnd_1083022 : Nat := 370740563595844603429519

theorem tailTrace_1083022 : CollatzResearch.WordTrace tailWord_1083022 prefixEnd_1083022 370740563595844603429519 := by
  unfold tailWord_1083022
  simp only [CollatzResearch.WordTrace]
  refine ⟨4937632185300466784607415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26334038321602489517906213 4937632185300466784607415)
  ·
    refine ⟨7406448277950700176911123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4937632185300466784607415 7406448277950700176911123)
    ·
      refine ⟨11109672416926050265366685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7406448277950700176911123 11109672416926050265366685)
      ·
        refine ⟨4166127156347268849512507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11109672416926050265366685 4166127156347268849512507)
        ·
          refine ⟨6249190734520903274268761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4166127156347268849512507 6249190734520903274268761)
          ·
            refine ⟨4686893050890677455701571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6249190734520903274268761 4686893050890677455701571)
            ·
              refine ⟨7030339576336016183552357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4686893050890677455701571 7030339576336016183552357)
              ·
                refine ⟨1318188670563003034416067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7030339576336016183552357 1318188670563003034416067)
                ·
                  refine ⟨1977283005844504551624101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1318188670563003034416067 1977283005844504551624101)
                  ·
                    refine ⟨370740563595844603429519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1977283005844504551624101 370740563595844603429519)
                    ·
                      rfl

theorem cell22_1083022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 1, 4, 1, 4].length) (baseStart_1083022 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1083022 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1083022 prefixEnd_1083022 := by exact prefixLift 1083022
  have htrace : WordTrace (prefixWord ++ tailWord_1083022) baseStart_1083022 baseEnd_1083022 := by
    simpa [prefixWord, tailWord_1083022, baseEnd_1083022] using wordTrace_append hprefix tailTrace_1083022
  have hstable : (prefixWord ++ tailWord_1083022).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1083022).length < 2 ^ (prefixWord ++ tailWord_1083022).sum := by decide
  have hdescent : baseEnd_1083022 < baseStart_1083022 := by decide
  rcases family_descends (prefixWord ++ tailWord_1083022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1083084 : List Nat := [2, 2, 1, 5, 2, 1, 2, 1, 2, 4]
def baseStart_1083084 : Nat := 118140960795 + 1083084 * 2 ^ 59
def prefixEnd_1083084 : Nat := 4983230072969 + 3 ^ 40 * 1083084 * 2
def baseEnd_1083084 : Nat := 370761787462897108379329

theorem tailTrace_1083084 : CollatzResearch.WordTrace tailWord_1083084 prefixEnd_1083084 370761787462897108379329 := by
  unfold tailWord_1083084
  simp only [CollatzResearch.WordTrace]
  refine ⟨19751659404089559432808153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26335545872119412577077537 19751659404089559432808153)
  ·
    refine ⟨14813744553067169574606115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19751659404089559432808153 14813744553067169574606115)
    ·
      refine ⟨22220616829600754361909173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14813744553067169574606115 22220616829600754361909173)
      ·
        refine ⟨2083182827775070721428985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 22220616829600754361909173 2083182827775070721428985)
        ·
          refine ⟨1562387120831303041071739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2083182827775070721428985 1562387120831303041071739)
          ·
            refine ⟨2343580681246954561607609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1562387120831303041071739 2343580681246954561607609)
            ·
              refine ⟨1757685510935215921205707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2343580681246954561607609 1757685510935215921205707)
              ·
                refine ⟨2636528266402823881808561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1757685510935215921205707 2636528266402823881808561)
                ·
                  refine ⟨1977396199802117911356421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2636528266402823881808561 1977396199802117911356421)
                  ·
                    refine ⟨370761787462897108379329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1977396199802117911356421 370761787462897108379329)
                    ·
                      rfl

theorem cell22_1083084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 2, 1, 2, 4].length) (baseStart_1083084 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1083084 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1083084 prefixEnd_1083084 := by exact prefixLift 1083084
  have htrace : WordTrace (prefixWord ++ tailWord_1083084) baseStart_1083084 baseEnd_1083084 := by
    simpa [prefixWord, tailWord_1083084, baseEnd_1083084] using wordTrace_append hprefix tailTrace_1083084
  have hstable : (prefixWord ++ tailWord_1083084).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1083084).length < 2 ^ (prefixWord ++ tailWord_1083084).sum := by decide
  have hdescent : baseEnd_1083084 < baseStart_1083084 := by decide
  rcases family_descends (prefixWord ++ tailWord_1083084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1083172 : List Nat := [2, 3, 1, 3, 2, 1, 1, 3, 6]
def baseStart_1083172 : Nat := 118140960795 + 1083172 * 2 ^ 59
def prefixEnd_1083172 : Nat := 4983230072969 + 3 ^ 40 * 1083172 * 2
def baseEnd_1083172 : Nat := 123597303887098070726353

theorem tailTrace_1083172 : CollatzResearch.WordTrace tailWord_1083172 prefixEnd_1083172 123597303887098070726353 := by
  unfold tailWord_1083172
  simp only [CollatzResearch.WordTrace]
  refine ⟨19753264215930154947409885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26337685621240206596546513 19753264215930154947409885)
  ·
    refine ⟨7407474080973808105278707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19753264215930154947409885 7407474080973808105278707)
    ·
      refine ⟨11111211121460712157918061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7407474080973808105278707 11111211121460712157918061)
      ·
        refine ⟨4166704170547767059219273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11111211121460712157918061 4166704170547767059219273)
        ·
          refine ⟨3125028127910825294414455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4166704170547767059219273 3125028127910825294414455)
          ·
            refine ⟨4687542191866237941621683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3125028127910825294414455 4687542191866237941621683)
            ·
              refine ⟨7031313287799356912432525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4687542191866237941621683 7031313287799356912432525)
              ·
                refine ⟨2636742482924758842162197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7031313287799356912432525 2636742482924758842162197)
                ·
                  refine ⟨123597303887098070726353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2636742482924758842162197 123597303887098070726353)
                  ·
                    rfl

theorem cell22_1083172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 1, 3, 6].length) (baseStart_1083172 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1083172 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1083172 prefixEnd_1083172 := by exact prefixLift 1083172
  have htrace : WordTrace (prefixWord ++ tailWord_1083172) baseStart_1083172 baseEnd_1083172 := by
    simpa [prefixWord, tailWord_1083172, baseEnd_1083172] using wordTrace_append hprefix tailTrace_1083172
  have hstable : (prefixWord ++ tailWord_1083172).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1083172).length < 2 ^ (prefixWord ++ tailWord_1083172).sum := by decide
  have hdescent : baseEnd_1083172 < baseStart_1083172 := by decide
  rcases family_descends (prefixWord ++ tailWord_1083172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1083217 : List Nat := [1, 2, 2, 1, 5, 3, 8]
def baseStart_1083217 : Nat := 118140960795 + 1083217 * 2 ^ 59
def prefixEnd_1083217 : Nat := 4983230072969 + 3 ^ 40 * 1083217 * 2
def baseEnd_1083217 : Nat := 13733604299293670177923

theorem tailTrace_1083217 : CollatzResearch.WordTrace tailWord_1083217 prefixEnd_1083217 13733604299293670177923 := by
  unfold tailWord_1083217
  simp only [CollatzResearch.WordTrace]
  refine ⟨39508169716697282580207905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26338779811131521720138603 39508169716697282580207905)
  ·
    refine ⟨29631127287522961935155929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39508169716697282580207905 29631127287522961935155929)
    ·
      refine ⟨22223345465642221451366947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29631127287522961935155929 22223345465642221451366947)
      ·
        refine ⟨33335018198463332177050421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22223345465642221451366947 33335018198463332177050421)
        ·
          refine ⟨3125157956105937391598477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 33335018198463332177050421 3125157956105937391598477)
          ·
            refine ⟨1171934233539726521849429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3125157956105937391598477 1171934233539726521849429)
            ·
              refine ⟨13733604299293670177923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1171934233539726521849429 13733604299293670177923)
              ·
                rfl

theorem cell22_1083217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 3, 8].length) (baseStart_1083217 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1083217 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1083217 prefixEnd_1083217 := by exact prefixLift 1083217
  have htrace : WordTrace (prefixWord ++ tailWord_1083217) baseStart_1083217 baseEnd_1083217 := by
    simpa [prefixWord, tailWord_1083217, baseEnd_1083217] using wordTrace_append hprefix tailTrace_1083217
  have hstable : (prefixWord ++ tailWord_1083217).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1083217).length < 2 ^ (prefixWord ++ tailWord_1083217).sum := by decide
  have hdescent : baseEnd_1083217 < baseStart_1083217 := by decide
  rcases family_descends (prefixWord ++ tailWord_1083217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1083234 : List Nat := [3, 3, 2, 1, 2, 2, 2, 7]
def baseStart_1083234 : Nat := 118140960795 + 1083234 * 2 ^ 59
def prefixEnd_1083234 : Nat := 4983230072969 + 3 ^ 40 * 1083234 * 2
def baseEnd_1083234 : Nat := 41201459503149635236541

theorem tailTrace_1083234 : CollatzResearch.WordTrace tailWord_1083234 prefixEnd_1083234 41201459503149635236541 := by
  unfold tailWord_1083234
  simp only [CollatzResearch.WordTrace]
  refine ⟨9877197439408923620894189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26339193171757129655717837 9877197439408923620894189)
  ·
    refine ⟨3703949039778346357835321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9877197439408923620894189 3703949039778346357835321)
    ·
      refine ⟨2777961779833759768376491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3703949039778346357835321 2777961779833759768376491)
      ·
        refine ⟨4166942669750639652564737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2777961779833759768376491 4166942669750639652564737)
        ·
          refine ⟨3125207002312979739423553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4166942669750639652564737 3125207002312979739423553)
          ·
            refine ⟨2343905251734734804567665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3125207002312979739423553 2343905251734734804567665)
            ·
              refine ⟨1757928938801051103425749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2343905251734734804567665 1757928938801051103425749)
              ·
                refine ⟨41201459503149635236541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1757928938801051103425749 41201459503149635236541)
                ·
                  rfl

theorem cell22_1083234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 2, 7].length) (baseStart_1083234 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1083234 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1083234 prefixEnd_1083234 := by exact prefixLift 1083234
  have htrace : WordTrace (prefixWord ++ tailWord_1083234) baseStart_1083234 baseEnd_1083234 := by
    simpa [prefixWord, tailWord_1083234, baseEnd_1083234] using wordTrace_append hprefix tailTrace_1083234
  have hstable : (prefixWord ++ tailWord_1083234).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1083234).length < 2 ^ (prefixWord ++ tailWord_1083234).sum := by decide
  have hdescent : baseEnd_1083234 < baseStart_1083234 := by decide
  rcases family_descends (prefixWord ++ tailWord_1083234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1083322 : List Nat := [3, 1, 1, 1, 2, 1, 2, 3, 3, 5]
def baseStart_1083322 : Nat := 118140960795 + 1083322 * 2 ^ 59
def prefixEnd_1083322 : Nat := 4983230072969 + 3 ^ 40 * 1083322 * 2
def baseEnd_1083322 : Nat := 370843259726743820928599

theorem tailTrace_1083322 : CollatzResearch.WordTrace tailWord_1083322 prefixEnd_1083322 370843259726743820928599 := by
  unfold tailWord_1083322
  simp only [CollatzResearch.WordTrace]
  refine ⟨9877999845329221378195055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26341332920877923675186813 9877999845329221378195055)
  ·
    refine ⟨14816999767993832067292583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9877999845329221378195055 14816999767993832067292583)
    ·
      refine ⟨22225499651990748100938875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14816999767993832067292583 22225499651990748100938875)
      ·
        refine ⟨33338249477986122151408313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22225499651990748100938875 33338249477986122151408313)
        ·
          refine ⟨25003687108489591613556235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33338249477986122151408313 25003687108489591613556235)
          ·
            refine ⟨37505530662734387420334353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25003687108489591613556235 37505530662734387420334353)
            ·
              refine ⟨28129147997050790565250765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37505530662734387420334353 28129147997050790565250765)
              ·
                refine ⟨10548430498894046461969037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28129147997050790565250765 10548430498894046461969037)
                ·
                  refine ⟨3955661437085267423238389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10548430498894046461969037 3955661437085267423238389)
                  ·
                    refine ⟨370843259726743820928599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3955661437085267423238389 370843259726743820928599)
                    ·
                      rfl

theorem cell22_1083322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 3, 3, 5].length) (baseStart_1083322 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1083322 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1083322 prefixEnd_1083322 := by exact prefixLift 1083322
  have htrace : WordTrace (prefixWord ++ tailWord_1083322) baseStart_1083322 baseEnd_1083322 := by
    simpa [prefixWord, tailWord_1083322, baseEnd_1083322] using wordTrace_append hprefix tailTrace_1083322
  have hstable : (prefixWord ++ tailWord_1083322).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1083322).length < 2 ^ (prefixWord ++ tailWord_1083322).sum := by decide
  have hdescent : baseEnd_1083322 < baseStart_1083322 := by decide
  rcases family_descends (prefixWord ++ tailWord_1083322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1083326 : List Nat := [4, 2, 1, 1, 1, 4, 1, 3, 1, 4]
def baseStart_1083326 : Nat := 118140960795 + 1083326 * 2 ^ 59
def prefixEnd_1083326 : Nat := 4983230072969 + 3 ^ 40 * 1083326 * 2
def baseEnd_1083326 : Nat := 370844629008489143828587

theorem tailTrace_1083326 : CollatzResearch.WordTrace tailWord_1083326 prefixEnd_1083326 370844629008489143828587 := by
  unfold tailWord_1083326
  simp only [CollatzResearch.WordTrace]
  refine ⟨4939018159162799274490729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26341430182201596130617221 4939018159162799274490729)
  ·
    refine ⟨3704263619372099455868047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4939018159162799274490729 3704263619372099455868047)
    ·
      refine ⟨5556395429058149183802071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3704263619372099455868047 5556395429058149183802071)
      ·
        refine ⟨8334593143587223775703107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5556395429058149183802071 8334593143587223775703107)
        ·
          refine ⟨12501889715380835663554661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8334593143587223775703107 12501889715380835663554661)
          ·
            refine ⟨2344104321633906686916499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12501889715380835663554661 2344104321633906686916499)
            ·
              refine ⟨3516156482450860030374749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2344104321633906686916499 3516156482450860030374749)
              ·
                refine ⟨1318558680919072511390531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3516156482450860030374749 1318558680919072511390531)
                ·
                  refine ⟨1977838021378608767085797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1318558680919072511390531 1977838021378608767085797)
                  ·
                    refine ⟨370844629008489143828587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1977838021378608767085797 370844629008489143828587)
                    ·
                      rfl

theorem cell22_1083326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 1, 3, 1, 4].length) (baseStart_1083326 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1083326 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1083326 prefixEnd_1083326 := by exact prefixLift 1083326
  have htrace : WordTrace (prefixWord ++ tailWord_1083326) baseStart_1083326 baseEnd_1083326 := by
    simpa [prefixWord, tailWord_1083326, baseEnd_1083326] using wordTrace_append hprefix tailTrace_1083326
  have hstable : (prefixWord ++ tailWord_1083326).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1083326).length < 2 ^ (prefixWord ++ tailWord_1083326).sum := by decide
  have hdescent : baseEnd_1083326 < baseStart_1083326 := by decide
  rcases family_descends (prefixWord ++ tailWord_1083326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1083339 : List Nat := [1, 1, 1, 1, 3, 4, 3, 1, 4, 3]
def baseStart_1083339 : Nat := 118140960795 + 1083339 * 2 ^ 59
def prefixEnd_1083339 : Nat := 4983230072969 + 3 ^ 40 * 1083339 * 2
def baseEnd_1083339 : Nat := 370849079174161443253547

theorem tailTrace_1083339 : CollatzResearch.WordTrace tailWord_1083339 prefixEnd_1083339 370849079174161443253547 := by
  unfold tailWord_1083339
  simp only [CollatzResearch.WordTrace]
  refine ⟨39512619422255297416149071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26341746281503531610766047 39512619422255297416149071)
  ·
    refine ⟨59268929133382946124223607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39512619422255297416149071 59268929133382946124223607)
    ·
      refine ⟨88903393700074419186335411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59268929133382946124223607 88903393700074419186335411)
      ·
        refine ⟨133355090550111628779503117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88903393700074419186335411 133355090550111628779503117)
        ·
          refine ⟨50008158956291860792313669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 133355090550111628779503117 50008158956291860792313669)
          ·
            refine ⟨9376529804304723898558813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 50008158956291860792313669 9376529804304723898558813)
            ·
              refine ⟨3516198676614271461959555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9376529804304723898558813 3516198676614271461959555)
              ·
                refine ⟨5274298014921407192939333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3516198676614271461959555 5274298014921407192939333)
                ·
                  refine ⟨988930877797763848676125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5274298014921407192939333 988930877797763848676125)
                  ·
                    refine ⟨370849079174161443253547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 988930877797763848676125 370849079174161443253547)
                    ·
                      rfl

theorem cell22_1083339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 3, 1, 4, 3].length) (baseStart_1083339 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1083339 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1083339 prefixEnd_1083339 := by exact prefixLift 1083339
  have htrace : WordTrace (prefixWord ++ tailWord_1083339) baseStart_1083339 baseEnd_1083339 := by
    simpa [prefixWord, tailWord_1083339, baseEnd_1083339] using wordTrace_append hprefix tailTrace_1083339
  have hstable : (prefixWord ++ tailWord_1083339).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1083339).length < 2 ^ (prefixWord ++ tailWord_1083339).sum := by decide
  have hdescent : baseEnd_1083339 < baseStart_1083339 := by decide
  rcases family_descends (prefixWord ++ tailWord_1083339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1083352 : List Nat := [2, 1, 2, 2, 2, 2, 2, 9]
def baseStart_1083352 : Nat := 118140960795 + 1083352 * 2 ^ 59
def prefixEnd_1083352 : Nat := 4983230072969 + 3 ^ 40 * 1083352 * 2
def baseEnd_1083352 : Nat := 41205947704425971408723

theorem tailTrace_1083352 : CollatzResearch.WordTrace tailWord_1083352 prefixEnd_1083352 41205947704425971408723 := by
  unfold tailWord_1083352
  simp only [CollatzResearch.WordTrace]
  refine ⟨19756546785604100318186155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26342062380805467090914873 19756546785604100318186155)
  ·
    refine ⟨29634820178406150477279233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19756546785604100318186155 29634820178406150477279233)
    ·
      refine ⟨22226115133804612857959425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29634820178406150477279233 22226115133804612857959425)
      ·
        refine ⟨16669586350353459643469569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22226115133804612857959425 16669586350353459643469569)
        ·
          refine ⟨12502189762765094732602177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16669586350353459643469569 12502189762765094732602177)
          ·
            refine ⟨9376642322073821049451633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12502189762765094732602177 9376642322073821049451633)
            ·
              refine ⟨7032481741555365787088725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9376642322073821049451633 7032481741555365787088725)
              ·
                refine ⟨41205947704425971408723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 7032481741555365787088725 41205947704425971408723)
                ·
                  rfl

theorem cell22_1083352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 2, 9].length) (baseStart_1083352 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1083352 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1083352 prefixEnd_1083352 := by exact prefixLift 1083352
  have htrace : WordTrace (prefixWord ++ tailWord_1083352) baseStart_1083352 baseEnd_1083352 := by
    simpa [prefixWord, tailWord_1083352, baseEnd_1083352] using wordTrace_append hprefix tailTrace_1083352
  have hstable : (prefixWord ++ tailWord_1083352).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1083352).length < 2 ^ (prefixWord ++ tailWord_1083352).sum := by decide
  have hdescent : baseEnd_1083352 < baseStart_1083352 := by decide
  rcases family_descends (prefixWord ++ tailWord_1083352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1083384 : List Nat := [2, 1, 2, 1, 1, 3, 2, 2, 5, 3]
def baseStart_1083384 : Nat := 118140960795 + 1083384 * 2 ^ 59
def prefixEnd_1083384 : Nat := 4983230072969 + 3 ^ 40 * 1083384 * 2
def baseEnd_1083384 : Nat := 370864483593796325878409

theorem tailTrace_1083384 : CollatzResearch.WordTrace tailWord_1083384 prefixEnd_1083384 370864483593796325878409 := by
  unfold tailWord_1083384
  simp only [CollatzResearch.WordTrace]
  refine ⟨19757130353546135050768603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26342840471394846734358137 19757130353546135050768603)
  ·
    refine ⟨29635695530319202576152905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19757130353546135050768603 29635695530319202576152905)
    ·
      refine ⟨22226771647739401932114679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29635695530319202576152905 22226771647739401932114679)
      ·
        refine ⟨33340157471609102898172019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22226771647739401932114679 33340157471609102898172019)
        ·
          refine ⟨50010236207413654347258029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33340157471609102898172019 50010236207413654347258029)
          ·
            refine ⟨18753838577780120380221761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50010236207413654347258029 18753838577780120380221761)
            ·
              refine ⟨14065378933335090285166321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18753838577780120380221761 14065378933335090285166321)
              ·
                refine ⟨10549034200001317713874741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14065378933335090285166321 10549034200001317713874741)
                ·
                  refine ⟨988971956250123535675757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 10549034200001317713874741 988971956250123535675757)
                  ·
                    refine ⟨370864483593796325878409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 988971956250123535675757 370864483593796325878409)
                    ·
                      rfl

theorem cell22_1083384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 2, 5, 3].length) (baseStart_1083384 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1083384 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1083384 prefixEnd_1083384 := by exact prefixLift 1083384
  have htrace : WordTrace (prefixWord ++ tailWord_1083384) baseStart_1083384 baseEnd_1083384 := by
    simpa [prefixWord, tailWord_1083384, baseEnd_1083384] using wordTrace_append hprefix tailTrace_1083384
  have hstable : (prefixWord ++ tailWord_1083384).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1083384).length < 2 ^ (prefixWord ++ tailWord_1083384).sum := by decide
  have hdescent : baseEnd_1083384 < baseStart_1083384 := by decide
  rcases family_descends (prefixWord ++ tailWord_1083384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1083446 : List Nat := [5, 1, 2, 1, 1, 1, 2, 2, 2, 5]
def baseStart_1083446 : Nat := 118140960795 + 1083446 * 2 ^ 59
def prefixEnd_1083446 : Nat := 4983230072969 + 3 ^ 40 * 1083446 * 2
def baseEnd_1083446 : Nat := 370885707460848830828219

theorem tailTrace_1083446 : CollatzResearch.WordTrace tailWord_1083446 prefixEnd_1083446 370885707460848830828219 := by
  unfold tailWord_1083446
  simp only [CollatzResearch.WordTrace]
  refine ⟨2469782627054228418143387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 26344348021911769793529461 2469782627054228418143387)
  ·
    refine ⟨3704673940581342627215081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2469782627054228418143387 3704673940581342627215081)
    ·
      refine ⟨2778505455436006970411311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3704673940581342627215081 2778505455436006970411311)
      ·
        refine ⟨4167758183154010455616967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2778505455436006970411311 4167758183154010455616967)
        ·
          refine ⟨6251637274731015683425451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4167758183154010455616967 6251637274731015683425451)
          ·
            refine ⟨9377455912096523525138177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6251637274731015683425451 9377455912096523525138177)
            ·
              refine ⟨7033091934072392643853633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9377455912096523525138177 7033091934072392643853633)
              ·
                refine ⟨5274818950554294482890225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7033091934072392643853633 5274818950554294482890225)
                ·
                  refine ⟨3956114212915720862167669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5274818950554294482890225 3956114212915720862167669)
                  ·
                    refine ⟨370885707460848830828219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3956114212915720862167669 370885707460848830828219)
                    ·
                      rfl

theorem cell22_1083446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 2, 2, 2, 5].length) (baseStart_1083446 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1083446 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1083446 prefixEnd_1083446 := by exact prefixLift 1083446
  have htrace : WordTrace (prefixWord ++ tailWord_1083446) baseStart_1083446 baseEnd_1083446 := by
    simpa [prefixWord, tailWord_1083446, baseEnd_1083446] using wordTrace_append hprefix tailTrace_1083446
  have hstable : (prefixWord ++ tailWord_1083446).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1083446).length < 2 ^ (prefixWord ++ tailWord_1083446).sum := by decide
  have hdescent : baseEnd_1083446 < baseStart_1083446 := by decide
  rcases family_descends (prefixWord ++ tailWord_1083446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1083493 : List Nat := [1, 3, 1, 3, 2, 3, 2, 3, 4]
def baseStart_1083493 : Nat := 118140960795 + 1083493 * 2 ^ 59
def prefixEnd_1083493 : Nat := 4983230072969 + 3 ^ 40 * 1083493 * 2
def baseEnd_1083493 : Nat := 123633932173785458301025

theorem tailTrace_1083493 : CollatzResearch.WordTrace tailWord_1083493 prefixEnd_1083493 123633932173785458301025 := by
  unfold tailWord_1083493
  simp only [CollatzResearch.WordTrace]
  refine ⟨39518236263697381717255133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26345490842464921144836755 39518236263697381717255133)
  ·
    refine ⟨14819338598886518143970675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39518236263697381717255133 14819338598886518143970675)
    ·
      refine ⟨22229007898329777215956013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14819338598886518143970675 22229007898329777215956013)
      ·
        refine ⟨8335877961873666455983505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22229007898329777215956013 8335877961873666455983505)
        ·
          refine ⟨6251908471405249841987629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8335877961873666455983505 6251908471405249841987629)
          ·
            refine ⟨2344465676776968690745361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6251908471405249841987629 2344465676776968690745361)
            ·
              refine ⟨1758349257582726518059021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2344465676776968690745361 1758349257582726518059021)
              ·
                refine ⟨659380971593522444272133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1758349257582726518059021 659380971593522444272133)
                ·
                  refine ⟨123633932173785458301025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 659380971593522444272133 123633932173785458301025)
                  ·
                    rfl

theorem cell22_1083493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 2, 3, 4].length) (baseStart_1083493 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1083493 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1083493 prefixEnd_1083493 := by exact prefixLift 1083493
  have htrace : WordTrace (prefixWord ++ tailWord_1083493) baseStart_1083493 baseEnd_1083493 := by
    simpa [prefixWord, tailWord_1083493, baseEnd_1083493] using wordTrace_append hprefix tailTrace_1083493
  have hstable : (prefixWord ++ tailWord_1083493).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1083493).length < 2 ^ (prefixWord ++ tailWord_1083493).sum := by decide
  have hdescent : baseEnd_1083493 < baseStart_1083493 := by decide
  rcases family_descends (prefixWord ++ tailWord_1083493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1083504 : List Nat := [2, 1, 1, 1, 5, 3, 9]
def baseStart_1083504 : Nat := 118140960795 + 1083504 * 2 ^ 59
def prefixEnd_1083504 : Nat := 4983230072969 + 3 ^ 40 * 1083504 * 2
def baseEnd_1083504 : Nat := 13737243038746518995483

theorem tailTrace_1083504 : CollatzResearch.WordTrace tailWord_1083504 prefixEnd_1083504 13737243038746518995483 := by
  unfold tailWord_1083504
  simp only [CollatzResearch.WordTrace]
  refine ⟨19759318733328765297952783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26345758311105020397270377 19759318733328765297952783)
  ·
    refine ⟨29638978099993147946929175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19759318733328765297952783 29638978099993147946929175)
    ·
      refine ⟨44458467149989721920393763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29638978099993147946929175 44458467149989721920393763)
      ·
        refine ⟨66687700724984582880590645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44458467149989721920393763 66687700724984582880590645)
        ·
          refine ⟨6251971942967304645055373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 66687700724984582880590645 6251971942967304645055373)
          ·
            refine ⟨2344489478612739241895765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6251971942967304645055373 2344489478612739241895765)
            ·
              refine ⟨13737243038746518995483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2344489478612739241895765 13737243038746518995483)
              ·
                rfl

theorem cell22_1083504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 9].length) (baseStart_1083504 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1083504 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1083504 prefixEnd_1083504 := by exact prefixLift 1083504
  have htrace : WordTrace (prefixWord ++ tailWord_1083504) baseStart_1083504 baseEnd_1083504 := by
    simpa [prefixWord, tailWord_1083504, baseEnd_1083504] using wordTrace_append hprefix tailTrace_1083504
  have hstable : (prefixWord ++ tailWord_1083504).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1083504).length < 2 ^ (prefixWord ++ tailWord_1083504).sum := by decide
  have hdescent : baseEnd_1083504 < baseStart_1083504 := by decide
  rcases family_descends (prefixWord ++ tailWord_1083504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1083525 : List Nat := [1, 3, 1, 1, 5, 2, 3, 1, 2, 3]
def baseStart_1083525 : Nat := 118140960795 + 1083525 * 2 ^ 59
def prefixEnd_1083525 : Nat := 4983230072969 + 3 ^ 40 * 1083525 * 2
def baseEnd_1083525 : Nat := 370912750775318958102977

theorem tailTrace_1083525 : CollatzResearch.WordTrace tailWord_1083525 prefixEnd_1083525 370912750775318958102977 := by
  unfold tailWord_1083525
  simp only [CollatzResearch.WordTrace]
  refine ⟨39519403399581451182420029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26346268933054300788280019 39519403399581451182420029)
  ·
    refine ⟨14819776274843044193407511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39519403399581451182420029 14819776274843044193407511)
    ·
      refine ⟨22229664412264566290111267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14819776274843044193407511 22229664412264566290111267)
      ·
        refine ⟨33344496618396849435166901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22229664412264566290111267 33344496618396849435166901)
        ·
          refine ⟨3126046557974704634546897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 33344496618396849435166901 3126046557974704634546897)
          ·
            refine ⟨2344534918481028475910173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3126046557974704634546897 2344534918481028475910173)
            ·
              refine ⟨879200594430385678466315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2344534918481028475910173 879200594430385678466315)
              ·
                refine ⟨1318800891645578517699473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 879200594430385678466315 1318800891645578517699473)
                ·
                  refine ⟨989100668734183888274605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1318800891645578517699473 989100668734183888274605)
                  ·
                    refine ⟨370912750775318958102977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 989100668734183888274605 370912750775318958102977)
                    ·
                      rfl

theorem cell22_1083525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 3, 1, 2, 3].length) (baseStart_1083525 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1083525 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1083525 prefixEnd_1083525 := by exact prefixLift 1083525
  have htrace : WordTrace (prefixWord ++ tailWord_1083525) baseStart_1083525 baseEnd_1083525 := by
    simpa [prefixWord, tailWord_1083525, baseEnd_1083525] using wordTrace_append hprefix tailTrace_1083525
  have hstable : (prefixWord ++ tailWord_1083525).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1083525).length < 2 ^ (prefixWord ++ tailWord_1083525).sum := by decide
  have hdescent : baseEnd_1083525 < baseStart_1083525 := by decide
  rcases family_descends (prefixWord ++ tailWord_1083525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1083536 : List Nat := [2, 1, 1, 1, 1, 1, 5, 4, 3, 3]
def baseStart_1083536 : Nat := 118140960795 + 1083536 * 2 ^ 59
def prefixEnd_1083536 : Nat := 4983230072969 + 3 ^ 40 * 1083536 * 2
def baseEnd_1083536 : Nat := 370916516300118596077943

theorem tailTrace_1083536 : CollatzResearch.WordTrace tailWord_1083536 prefixEnd_1083536 370916516300118596077943 := by
  unfold tailWord_1083536
  simp only [CollatzResearch.WordTrace]
  refine ⟨19759902301270800030535231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26346536401694400040713641 19759902301270800030535231)
  ·
    refine ⟨29639853451906200045802847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19759902301270800030535231 29639853451906200045802847)
    ·
      refine ⟨44459780177859300068704271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29639853451906200045802847 44459780177859300068704271)
      ·
        refine ⟨66689670266788950103056407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44459780177859300068704271 66689670266788950103056407)
        ·
          refine ⟨100034505400183425154584611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66689670266788950103056407 100034505400183425154584611)
          ·
            refine ⟨150051758100275137731876917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 100034505400183425154584611 150051758100275137731876917)
            ·
              refine ⟨14067352321900794162363461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 150051758100275137731876917 14067352321900794162363461)
              ·
                refine ⟨2637628560356398905443149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14067352321900794162363461 2637628560356398905443149)
                ·
                  refine ⟨989110710133649589541181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2637628560356398905443149 989110710133649589541181)
                  ·
                    refine ⟨370916516300118596077943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 989110710133649589541181 370916516300118596077943)
                    ·
                      rfl

theorem cell22_1083536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 4, 3, 3].length) (baseStart_1083536 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1083536 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1083536 prefixEnd_1083536 := by exact prefixLift 1083536
  have htrace : WordTrace (prefixWord ++ tailWord_1083536) baseStart_1083536 baseEnd_1083536 := by
    simpa [prefixWord, tailWord_1083536, baseEnd_1083536] using wordTrace_append hprefix tailTrace_1083536
  have hstable : (prefixWord ++ tailWord_1083536).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1083536).length < 2 ^ (prefixWord ++ tailWord_1083536).sum := by decide
  have hdescent : baseEnd_1083536 < baseStart_1083536 := by decide
  rcases family_descends (prefixWord ++ tailWord_1083536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1083572 : List Nat := [2, 5, 3, 1, 1, 1, 2, 7]
def baseStart_1083572 : Nat := 118140960795 + 1083572 * 2 ^ 59
def prefixEnd_1083572 : Nat := 4983230072969 + 3 ^ 40 * 1083572 * 2
def baseEnd_1083572 : Nat := 41214315537314055797537

theorem tailTrace_1083572 : CollatzResearch.WordTrace tailWord_1083572 prefixEnd_1083572 41214315537314055797537 := by
  unfold tailWord_1083572
  simp only [CollatzResearch.WordTrace]
  refine ⟨19760558815205589104690485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26347411753607452139587313 19760558815205589104690485)
  ·
    refine ⟨1852552388925523978564733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 19760558815205589104690485 1852552388925523978564733)
    ·
      refine ⟨694707145847071491961775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1852552388925523978564733 694707145847071491961775)
      ·
        refine ⟨1042060718770607237942663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 694707145847071491961775 1042060718770607237942663)
        ·
          refine ⟨1563091078155910856913995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1042060718770607237942663 1563091078155910856913995)
          ·
            refine ⟨2344636617233866285370993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1563091078155910856913995 2344636617233866285370993)
            ·
              refine ⟨1758477462925399714028245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2344636617233866285370993 1758477462925399714028245)
              ·
                refine ⟨41214315537314055797537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1758477462925399714028245 41214315537314055797537)
                ·
                  rfl

theorem cell22_1083572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 2, 7].length) (baseStart_1083572 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1083572 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1083572 prefixEnd_1083572 := by exact prefixLift 1083572
  have htrace : WordTrace (prefixWord ++ tailWord_1083572) baseStart_1083572 baseEnd_1083572 := by
    simpa [prefixWord, tailWord_1083572, baseEnd_1083572] using wordTrace_append hprefix tailTrace_1083572
  have hstable : (prefixWord ++ tailWord_1083572).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1083572).length < 2 ^ (prefixWord ++ tailWord_1083572).sum := by decide
  have hdescent : baseEnd_1083572 < baseStart_1083572 := by decide
  rcases family_descends (prefixWord ++ tailWord_1083572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1083626 : List Nat := [3, 1, 3, 1, 1, 2, 1, 2, 3, 5]
def baseStart_1083626 : Nat := 118140960795 + 1083626 * 2 ^ 59
def prefixEnd_1083626 : Nat := 4983230072969 + 3 ^ 40 * 1083626 * 2
def baseEnd_1083626 : Nat := 370947325139388361327667

theorem tailTrace_1083626 : CollatzResearch.WordTrace tailWord_1083626 prefixEnd_1083626 370947325139388361327667 := by
  unfold tailWord_1083626
  simp only [CollatzResearch.WordTrace]
  refine ⟨9880771793053886357961683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26348724781477030287897821 9880771793053886357961683)
  ·
    refine ⟨14821157689580829536942525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9880771793053886357961683 14821157689580829536942525)
    ·
      refine ⟨5557934133592811076353447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14821157689580829536942525 5557934133592811076353447)
      ·
        refine ⟨8336901200389216614530171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5557934133592811076353447 8336901200389216614530171)
        ·
          refine ⟨12505351800583824921795257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8336901200389216614530171 12505351800583824921795257)
          ·
            refine ⟨9379013850437868691346443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12505351800583824921795257 9379013850437868691346443)
            ·
              refine ⟨14068520775656803037019665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9379013850437868691346443 14068520775656803037019665)
              ·
                refine ⟨10551390581742602277764749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14068520775656803037019665 10551390581742602277764749)
                ·
                  refine ⟨3956771468153475854161781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10551390581742602277764749 3956771468153475854161781)
                  ·
                    refine ⟨370947325139388361327667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3956771468153475854161781 370947325139388361327667)
                    ·
                      rfl

theorem cell22_1083626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 2, 3, 5].length) (baseStart_1083626 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1083626 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1083626 prefixEnd_1083626 := by exact prefixLift 1083626
  have htrace : WordTrace (prefixWord ++ tailWord_1083626) baseStart_1083626 baseEnd_1083626 := by
    simpa [prefixWord, tailWord_1083626, baseEnd_1083626] using wordTrace_append hprefix tailTrace_1083626
  have hstable : (prefixWord ++ tailWord_1083626).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1083626).length < 2 ^ (prefixWord ++ tailWord_1083626).sum := by decide
  have hdescent : baseEnd_1083626 < baseStart_1083626 := by decide
  rcases family_descends (prefixWord ++ tailWord_1083626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1083628 : List Nat := [2, 2, 1, 1, 2, 3, 3, 4, 4]
def baseStart_1083628 : Nat := 118140960795 + 1083628 * 2 ^ 59
def prefixEnd_1083628 : Nat := 4983230072969 + 3 ^ 40 * 1083628 * 2
def baseEnd_1083628 : Nat := 123649336593420340925887

theorem tailTrace_1083628 : CollatzResearch.WordTrace tailWord_1083628 prefixEnd_1083628 123649336593420340925887 := by
  unfold tailWord_1083628
  simp only [CollatzResearch.WordTrace]
  refine ⟨19761580059104149886709769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26348773412138866515613025 19761580059104149886709769)
  ·
    refine ⟨14821185044328112415032327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19761580059104149886709769 14821185044328112415032327)
    ·
      refine ⟨22231777566492168622548491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14821185044328112415032327 22231777566492168622548491)
      ·
        refine ⟨33347666349738252933822737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22231777566492168622548491 33347666349738252933822737)
        ·
          refine ⟨25010749762303689700367053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33347666349738252933822737 25010749762303689700367053)
          ·
            refine ⟨9379031160863883637637645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25010749762303689700367053 9379031160863883637637645)
            ·
              refine ⟨3517136685323956364114117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9379031160863883637637645 3517136685323956364114117)
              ·
                refine ⟨659463128498241818271397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3517136685323956364114117 659463128498241818271397)
                ·
                  refine ⟨123649336593420340925887, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 659463128498241818271397 123649336593420340925887)
                  ·
                    rfl

theorem cell22_1083628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 3, 4, 4].length) (baseStart_1083628 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1083628 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1083628 prefixEnd_1083628 := by exact prefixLift 1083628
  have htrace : WordTrace (prefixWord ++ tailWord_1083628) baseStart_1083628 baseEnd_1083628 := by
    simpa [prefixWord, tailWord_1083628, baseEnd_1083628] using wordTrace_append hprefix tailTrace_1083628
  have hstable : (prefixWord ++ tailWord_1083628).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1083628).length < 2 ^ (prefixWord ++ tailWord_1083628).sum := by decide
  have hdescent : baseEnd_1083628 < baseStart_1083628 := by decide
  rcases family_descends (prefixWord ++ tailWord_1083628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1083658 : List Nat := [3, 1, 2, 2, 1, 1, 5, 1, 2, 4]
def baseStart_1083658 : Nat := 118140960795 + 1083658 * 2 ^ 59
def prefixEnd_1083658 : Nat := 4983230072969 + 3 ^ 40 * 1083658 * 2
def baseEnd_1083658 : Nat := 370958279393350944527569

theorem tailTrace_1083658 : CollatzResearch.WordTrace tailWord_1083658 prefixEnd_1083658 370958279393350944527569 := by
  unfold tailWord_1083658
  simp only [CollatzResearch.WordTrace]
  refine ⟨9881063577024903724252907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26349502872066409931341085 9881063577024903724252907)
  ·
    refine ⟨14821595365537355586379361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9881063577024903724252907 14821595365537355586379361)
    ·
      refine ⟨11116196524153016689784521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14821595365537355586379361 11116196524153016689784521)
      ·
        refine ⟨8337147393114762517338391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11116196524153016689784521 8337147393114762517338391)
        ·
          refine ⟨12505721089672143776007587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8337147393114762517338391 12505721089672143776007587)
          ·
            refine ⟨18758581634508215664011381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12505721089672143776007587 18758581634508215664011381)
            ·
              refine ⟨1758617028235145218501067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 18758581634508215664011381 1758617028235145218501067)
              ·
                refine ⟨2637925542352717827751601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1758617028235145218501067 2637925542352717827751601)
                ·
                  refine ⟨1978444156764538370813701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2637925542352717827751601 1978444156764538370813701)
                  ·
                    refine ⟨370958279393350944527569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1978444156764538370813701 370958279393350944527569)
                    ·
                      rfl

theorem cell22_1083658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 5, 1, 2, 4].length) (baseStart_1083658 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1083658 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1083658 prefixEnd_1083658 := by exact prefixLift 1083658
  have htrace : WordTrace (prefixWord ++ tailWord_1083658) baseStart_1083658 baseEnd_1083658 := by
    simpa [prefixWord, tailWord_1083658, baseEnd_1083658] using wordTrace_append hprefix tailTrace_1083658
  have hstable : (prefixWord ++ tailWord_1083658).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1083658).length < 2 ^ (prefixWord ++ tailWord_1083658).sum := by decide
  have hdescent : baseEnd_1083658 < baseStart_1083658 := by decide
  rcases family_descends (prefixWord ++ tailWord_1083658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1083694 : List Nat := [4, 1, 3, 3, 2, 1, 1, 1, 1, 5]
def baseStart_1083694 : Nat := 118140960795 + 1083694 * 2 ^ 59
def prefixEnd_1083694 : Nat := 4983230072969 + 3 ^ 40 * 1083694 * 2
def baseEnd_1083694 : Nat := 370970602929058850627459

theorem tailTrace_1083694 : CollatzResearch.WordTrace tailWord_1083694 prefixEnd_1083694 370970602929058850627459 := by
  unfold tailWord_1083694
  simp only [CollatzResearch.WordTrace]
  refine ⟨4940695916996149130665267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26350378223979462030214757 4940695916996149130665267)
  ·
    refine ⟨7411043875494223695997901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4940695916996149130665267 7411043875494223695997901)
    ·
      refine ⟨2779141453310333885999213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7411043875494223695997901 2779141453310333885999213)
      ·
        refine ⟨1042178044991375207249705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2779141453310333885999213 1042178044991375207249705)
        ·
          refine ⟨781633533743531405437279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1042178044991375207249705 781633533743531405437279)
          ·
            refine ⟨1172450300615297108155919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 781633533743531405437279 1172450300615297108155919)
            ·
              refine ⟨1758675450922945662233879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1172450300615297108155919 1758675450922945662233879)
              ·
                refine ⟨2638013176384418493350819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1758675450922945662233879 2638013176384418493350819)
                ·
                  refine ⟨3957019764576627740026229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2638013176384418493350819 3957019764576627740026229)
                  ·
                    refine ⟨370970602929058850627459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3957019764576627740026229 370970602929058850627459)
                    ·
                      rfl

theorem cell22_1083694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 2, 1, 1, 1, 1, 5].length) (baseStart_1083694 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1083694 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1083694 prefixEnd_1083694 := by exact prefixLift 1083694
  have htrace : WordTrace (prefixWord ++ tailWord_1083694) baseStart_1083694 baseEnd_1083694 := by
    simpa [prefixWord, tailWord_1083694, baseEnd_1083694] using wordTrace_append hprefix tailTrace_1083694
  have hstable : (prefixWord ++ tailWord_1083694).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1083694).length < 2 ^ (prefixWord ++ tailWord_1083694).sum := by decide
  have hdescent : baseEnd_1083694 < baseStart_1083694 := by decide
  rcases family_descends (prefixWord ++ tailWord_1083694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1083705 : List Nat := [1, 2, 1, 6, 1, 1, 2, 2, 3, 3]
def baseStart_1083705 : Nat := 118140960795 + 1083705 * 2 ^ 59
def prefixEnd_1083705 : Nat := 4983230072969 + 3 ^ 40 * 1083705 * 2
def baseEnd_1083705 : Nat := 370974368453858488602425

theorem tailTrace_1083705 : CollatzResearch.WordTrace tailWord_1083705 prefixEnd_1083705 370974368453858488602425 := by
  unfold tailWord_1083705
  simp only [CollatzResearch.WordTrace]
  refine ⟨39525968538929341923972569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26350645692619561282648379 39525968538929341923972569)
  ·
    refine ⟨29644476404197006442979427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39525968538929341923972569 29644476404197006442979427)
    ·
      refine ⟨44466714606295509664469141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29644476404197006442979427 44466714606295509664469141)
      ·
        refine ⟨2084377247170102015521991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 44466714606295509664469141 2084377247170102015521991)
        ·
          refine ⟨3126565870755153023282987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2084377247170102015521991 3126565870755153023282987)
          ·
            refine ⟨4689848806132729534924481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3126565870755153023282987 4689848806132729534924481)
            ·
              refine ⟨3517386604599547151193361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4689848806132729534924481 3517386604599547151193361)
              ·
                refine ⟨2638039953449660363395021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3517386604599547151193361 2638039953449660363395021)
                ·
                  refine ⟨989264982543622636273133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2638039953449660363395021 989264982543622636273133)
                  ·
                    refine ⟨370974368453858488602425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 989264982543622636273133 370974368453858488602425)
                    ·
                      rfl

theorem cell22_1083705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 2, 2, 3, 3].length) (baseStart_1083705 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1083705 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1083705 prefixEnd_1083705 := by exact prefixLift 1083705
  have htrace : WordTrace (prefixWord ++ tailWord_1083705) baseStart_1083705 baseEnd_1083705 := by
    simpa [prefixWord, tailWord_1083705, baseEnd_1083705] using wordTrace_append hprefix tailTrace_1083705
  have hstable : (prefixWord ++ tailWord_1083705).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1083705).length < 2 ^ (prefixWord ++ tailWord_1083705).sum := by decide
  have hdescent : baseEnd_1083705 < baseStart_1083705 := by decide
  rcases family_descends (prefixWord ++ tailWord_1083705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1083748 : List Nat := [2, 3, 1, 1, 3, 1, 2, 2, 3, 4]
def baseStart_1083748 : Nat := 118140960795 + 1083748 * 2 ^ 59
def prefixEnd_1083748 : Nat := 4983230072969 + 3 ^ 40 * 1083748 * 2
def baseEnd_1083748 : Nat := 370989088232620709777293

theorem tailTrace_1083748 : CollatzResearch.WordTrace tailWord_1083748 prefixEnd_1083748 370989088232620709777293 := by
  unfold tailWord_1083748
  simp only [CollatzResearch.WordTrace]
  refine ⟨19763768438886780133893949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26351691251849040178525265 19763768438886780133893949)
  ·
    refine ⟨7411413164582542550210231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19763768438886780133893949 7411413164582542550210231)
    ·
      refine ⟨11117119746873813825315347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7411413164582542550210231 11117119746873813825315347)
      ·
        refine ⟨16675679620310720737973021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11117119746873813825315347 16675679620310720737973021)
        ·
          refine ⟨6253379857616520276739883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16675679620310720737973021 6253379857616520276739883)
          ·
            refine ⟨9380069786424780415109825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6253379857616520276739883 9380069786424780415109825)
            ·
              refine ⟨7035052339818585311332369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9380069786424780415109825 7035052339818585311332369)
              ·
                refine ⟨5276289254863938983499277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7035052339818585311332369 5276289254863938983499277)
                ·
                  refine ⟨1978608470573977118812229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5276289254863938983499277 1978608470573977118812229)
                  ·
                    refine ⟨370989088232620709777293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1978608470573977118812229 370989088232620709777293)
                    ·
                      rfl

theorem cell22_1083748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 2, 2, 3, 4].length) (baseStart_1083748 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1083748 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1083748 prefixEnd_1083748 := by exact prefixLift 1083748
  have htrace : WordTrace (prefixWord ++ tailWord_1083748) baseStart_1083748 baseEnd_1083748 := by
    simpa [prefixWord, tailWord_1083748, baseEnd_1083748] using wordTrace_append hprefix tailTrace_1083748
  have hstable : (prefixWord ++ tailWord_1083748).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1083748).length < 2 ^ (prefixWord ++ tailWord_1083748).sum := by decide
  have hdescent : baseEnd_1083748 < baseStart_1083748 := by decide
  rcases family_descends (prefixWord ++ tailWord_1083748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1083752 : List Nat := [2, 1, 4, 2, 2, 3, 2, 1, 5]
def baseStart_1083752 : Nat := 118140960795 + 1083752 * 2 ^ 59
def prefixEnd_1083752 : Nat := 4983230072969 + 3 ^ 40 * 1083752 * 2
def baseEnd_1083752 : Nat := 123663485838122010892427

theorem tailTrace_1083752 : CollatzResearch.WordTrace tailWord_1083752 prefixEnd_1083752 123663485838122010892427 := by
  unfold tailWord_1083752
  simp only [CollatzResearch.WordTrace]
  refine ⟨19763841384879534475466755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26351788513172712633955673 19763841384879534475466755)
  ·
    refine ⟨29645762077319301713200133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19763841384879534475466755 29645762077319301713200133)
    ·
      refine ⟨5558580389497369071225025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29645762077319301713200133 5558580389497369071225025)
      ·
        refine ⟨4168935292123026803418769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5558580389497369071225025 4168935292123026803418769)
        ·
          refine ⟨3126701469092270102564077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4168935292123026803418769 3126701469092270102564077)
          ·
            refine ⟨1172513050909601288461529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3126701469092270102564077 1172513050909601288461529)
            ·
              refine ⟨879384788182200966346147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1172513050909601288461529 879384788182200966346147)
              ·
                refine ⟨1319077182273301449519221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 879384788182200966346147 1319077182273301449519221)
                ·
                  refine ⟨123663485838122010892427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1319077182273301449519221 123663485838122010892427)
                  ·
                    rfl

theorem cell22_1083752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 3, 2, 1, 5].length) (baseStart_1083752 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1083752 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1083752 prefixEnd_1083752 := by exact prefixLift 1083752
  have htrace : WordTrace (prefixWord ++ tailWord_1083752) baseStart_1083752 baseEnd_1083752 := by
    simpa [prefixWord, tailWord_1083752, baseEnd_1083752] using wordTrace_append hprefix tailTrace_1083752
  have hstable : (prefixWord ++ tailWord_1083752).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1083752).length < 2 ^ (prefixWord ++ tailWord_1083752).sum := by decide
  have hdescent : baseEnd_1083752 < baseStart_1083752 := by decide
  rcases family_descends (prefixWord ++ tailWord_1083752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1083765 : List Nat := [1, 3, 4, 1, 2, 2, 1, 1, 3, 4]
def baseStart_1083765 : Nat := 118140960795 + 1083765 * 2 ^ 59
def prefixEnd_1083765 : Nat := 4983230072969 + 3 ^ 40 * 1083765 * 2
def baseEnd_1083765 : Nat := 370994907680038332102241

theorem tailTrace_1083765 : CollatzResearch.WordTrace tailWord_1083765 prefixEnd_1083765 370994907680038332102241 := by
  unfold tailWord_1083765
  simp only [CollatzResearch.WordTrace]
  refine ⟨39528156918711972171156749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26352104612474648114104499 39528156918711972171156749)
  ·
    refine ⟨14823058844516989564183781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39528156918711972171156749 14823058844516989564183781)
    ·
      refine ⟨2779323533346935543284459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14823058844516989564183781 2779323533346935543284459)
      ·
        refine ⟨4168985300020403314926689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2779323533346935543284459 4168985300020403314926689)
        ·
          refine ⟨3126738975015302486195017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4168985300020403314926689 3126738975015302486195017)
          ·
            refine ⟨2345054231261476864646263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3126738975015302486195017 2345054231261476864646263)
            ·
              refine ⟨3517581346892215296969395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2345054231261476864646263 3517581346892215296969395)
              ·
                refine ⟨5276372020338322945454093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3517581346892215296969395 5276372020338322945454093)
                ·
                  refine ⟨1978639507626871104545285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5276372020338322945454093 1978639507626871104545285)
                  ·
                    refine ⟨370994907680038332102241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1978639507626871104545285 370994907680038332102241)
                    ·
                      rfl

theorem cell22_1083765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 1, 1, 3, 4].length) (baseStart_1083765 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1083765 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1083765 prefixEnd_1083765 := by exact prefixLift 1083765
  have htrace : WordTrace (prefixWord ++ tailWord_1083765) baseStart_1083765 baseEnd_1083765 := by
    simpa [prefixWord, tailWord_1083765, baseEnd_1083765] using wordTrace_append hprefix tailTrace_1083765
  have hstable : (prefixWord ++ tailWord_1083765).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1083765).length < 2 ^ (prefixWord ++ tailWord_1083765).sum := by decide
  have hdescent : baseEnd_1083765 < baseStart_1083765 := by decide
  rcases family_descends (prefixWord ++ tailWord_1083765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1083780 : List Nat := [2, 3, 2, 1, 1, 2, 2, 5, 4]
def baseStart_1083780 : Nat := 118140960795 + 1083780 * 2 ^ 59
def prefixEnd_1083780 : Nat := 4983230072969 + 3 ^ 40 * 1083780 * 2
def baseEnd_1083780 : Nat := 123666680828861097659065

theorem tailTrace_1083780 : CollatzResearch.WordTrace tailWord_1083780 prefixEnd_1083780 123666680828861097659065 := by
  unfold tailWord_1083780
  simp only [CollatzResearch.WordTrace]
  refine ⟨19764352006828814866476397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26352469342438419821968529 19764352006828814866476397)
  ·
    refine ⟨7411632002560805574928649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19764352006828814866476397 7411632002560805574928649)
    ·
      refine ⟨5558724001920604181196487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7411632002560805574928649 5558724001920604181196487)
      ·
        refine ⟨8338086002880906271794731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5558724001920604181196487 8338086002880906271794731)
        ·
          refine ⟨12507129004321359407692097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8338086002880906271794731 12507129004321359407692097)
          ·
            refine ⟨9380346753241019555769073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12507129004321359407692097 9380346753241019555769073)
            ·
              refine ⟨7035260064930764666826805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9380346753241019555769073 7035260064930764666826805)
              ·
                refine ⟨659555631087259187515013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7035260064930764666826805 659555631087259187515013)
                ·
                  refine ⟨123666680828861097659065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 659555631087259187515013 123666680828861097659065)
                  ·
                    rfl

theorem cell22_1083780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 2, 5, 4].length) (baseStart_1083780 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1083780 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1083780 prefixEnd_1083780 := by exact prefixLift 1083780
  have htrace : WordTrace (prefixWord ++ tailWord_1083780) baseStart_1083780 baseEnd_1083780 := by
    simpa [prefixWord, tailWord_1083780, baseEnd_1083780] using wordTrace_append hprefix tailTrace_1083780
  have hstable : (prefixWord ++ tailWord_1083780).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1083780).length < 2 ^ (prefixWord ++ tailWord_1083780).sum := by decide
  have hdescent : baseEnd_1083780 < baseStart_1083780 := by decide
  rcases family_descends (prefixWord ++ tailWord_1083780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1083808 : List Nat := [2, 1, 1, 4, 1, 3, 3, 7]
def baseStart_1083808 : Nat := 118140960795 + 1083808 * 2 ^ 59
def prefixEnd_1083808 : Nat := 4983230072969 + 3 ^ 40 * 1083808 * 2
def baseEnd_1083808 : Nat := 41223291939866728141901

theorem tailTrace_1083808 : CollatzResearch.WordTrace tailWord_1083808 prefixEnd_1083808 41223291939866728141901 := by
  unfold tailWord_1083808
  simp only [CollatzResearch.WordTrace]
  refine ⟨19764862628778095257486039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26353150171704127009981385 19764862628778095257486039)
  ·
    refine ⟨29647293943167142886229059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19764862628778095257486039 29647293943167142886229059)
    ·
      refine ⟨44470940914750714329343589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29647293943167142886229059 44470940914750714329343589)
      ·
        refine ⟨8338301421515758936751923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 44470940914750714329343589 8338301421515758936751923)
        ·
          refine ⟨12507452132273638405127885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8338301421515758936751923 12507452132273638405127885)
          ·
            refine ⟨4690294549602614401922957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12507452132273638405127885 4690294549602614401922957)
            ·
              refine ⟨1758860456100980400721109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4690294549602614401922957 1758860456100980400721109)
              ·
                refine ⟨41223291939866728141901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1758860456100980400721109 41223291939866728141901)
                ·
                  rfl

theorem cell22_1083808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 3, 7].length) (baseStart_1083808 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1083808 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1083808 prefixEnd_1083808 := by exact prefixLift 1083808
  have htrace : WordTrace (prefixWord ++ tailWord_1083808) baseStart_1083808 baseEnd_1083808 := by
    simpa [prefixWord, tailWord_1083808, baseEnd_1083808] using wordTrace_append hprefix tailTrace_1083808
  have hstable : (prefixWord ++ tailWord_1083808).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1083808).length < 2 ^ (prefixWord ++ tailWord_1083808).sum := by decide
  have hdescent : baseEnd_1083808 < baseStart_1083808 := by decide
  rcases family_descends (prefixWord ++ tailWord_1083808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1083825 : List Nat := [1, 2, 2, 4, 1, 3, 3, 6]
def baseStart_1083825 : Nat := 118140960795 + 1083825 * 2 ^ 59
def prefixEnd_1083825 : Nat := 4983230072969 + 3 ^ 40 * 1083825 * 2
def baseEnd_1083825 : Nat := 41223938545135352844673

theorem tailTrace_1083825 : CollatzResearch.WordTrace tailWord_1083825 prefixEnd_1083825 41223938545135352844673 := by
  unfold tailWord_1083825
  simp only [CollatzResearch.WordTrace]
  refine ⟨39530345298494602418340929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26353563532329734945560619 39530345298494602418340929)
  ·
    refine ⟨29647758973870951813755697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39530345298494602418340929 29647758973870951813755697)
    ·
      refine ⟨22235819230403213860316773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29647758973870951813755697 22235819230403213860316773)
      ·
        refine ⟨4169216105700602598809395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22235819230403213860316773 4169216105700602598809395)
        ·
          refine ⟨6253824158550903898214093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4169216105700602598809395 6253824158550903898214093)
          ·
            refine ⟨2345184059456588961830285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6253824158550903898214093 2345184059456588961830285)
            ·
              refine ⟨879444022296220860686357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2345184059456588961830285 879444022296220860686357)
              ·
                refine ⟨41223938545135352844673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 879444022296220860686357 41223938545135352844673)
                ·
                  rfl

theorem cell22_1083825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 3, 6].length) (baseStart_1083825 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1083825 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1083825 prefixEnd_1083825 := by exact prefixLift 1083825
  have htrace : WordTrace (prefixWord ++ tailWord_1083825) baseStart_1083825 baseEnd_1083825 := by
    simpa [prefixWord, tailWord_1083825, baseEnd_1083825] using wordTrace_append hprefix tailTrace_1083825
  have hstable : (prefixWord ++ tailWord_1083825).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1083825).length < 2 ^ (prefixWord ++ tailWord_1083825).sum := by decide
  have hdescent : baseEnd_1083825 < baseStart_1083825 := by decide
  rcases family_descends (prefixWord ++ tailWord_1083825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1083913 : List Nat := [1, 2, 1, 1, 3, 1, 2, 1, 5, 5]
def baseStart_1083913 : Nat := 118140960795 + 1083913 * 2 ^ 59
def prefixEnd_1083913 : Nat := 4983230072969 + 3 ^ 40 * 1083913 * 2
def baseEnd_1083913 : Nat := 371045571104615279401787

theorem tailTrace_1083913 : CollatzResearch.WordTrace tailWord_1083913 prefixEnd_1083913 371045571104615279401787 := by
  unfold tailWord_1083913
  simp only [CollatzResearch.WordTrace]
  refine ⟨39533554922175793447544393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26355703281450528965029595 39533554922175793447544393)
  ·
    refine ⟨29650166191631845085658295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39533554922175793447544393 29650166191631845085658295)
    ·
      refine ⟨44475249287447767628487443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29650166191631845085658295 44475249287447767628487443)
      ·
        refine ⟨66712873931171651442731165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44475249287447767628487443 66712873931171651442731165)
        ·
          refine ⟨25017327724189369291024187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 66712873931171651442731165 25017327724189369291024187)
          ·
            refine ⟨37525991586284053936536281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25017327724189369291024187 37525991586284053936536281)
            ·
              refine ⟨28144493689713040452402211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37525991586284053936536281 28144493689713040452402211)
              ·
                refine ⟨42216740534569560678603317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28144493689713040452402211 42216740534569560678603317)
                ·
                  refine ⟨3957819425115896313619061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 42216740534569560678603317 3957819425115896313619061)
                  ·
                    refine ⟨371045571104615279401787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3957819425115896313619061 371045571104615279401787)
                    ·
                      rfl

theorem cell22_1083913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 1, 5, 5].length) (baseStart_1083913 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1083913 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1083913 prefixEnd_1083913 := by exact prefixLift 1083913
  have htrace : WordTrace (prefixWord ++ tailWord_1083913) baseStart_1083913 baseEnd_1083913 := by
    simpa [prefixWord, tailWord_1083913, baseEnd_1083913] using wordTrace_append hprefix tailTrace_1083913
  have hstable : (prefixWord ++ tailWord_1083913).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1083913).length < 2 ^ (prefixWord ++ tailWord_1083913).sum := by decide
  have hdescent : baseEnd_1083913 < baseStart_1083913 := by decide
  rcases family_descends (prefixWord ++ tailWord_1083913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1083915 : List Nat := [1, 1, 1, 1, 7, 1, 3, 1, 6]
def baseStart_1083915 : Nat := 118140960795 + 1083915 * 2 ^ 59
def prefixEnd_1083915 : Nat := 4983230072969 + 3 ^ 40 * 1083915 * 2
def baseEnd_1083915 : Nat := 123682085248495980283927

theorem tailTrace_1083915 : CollatzResearch.WordTrace tailWord_1083915 prefixEnd_1083915 123682085248495980283927 := by
  unfold tailWord_1083915
  simp only [CollatzResearch.WordTrace]
  refine ⟨39533627868168547789117199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26355751912112365192744799 39533627868168547789117199)
  ·
    refine ⟨59300441802252821683675799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39533627868168547789117199 59300441802252821683675799)
    ·
      refine ⟨88950662703379232525513699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59300441802252821683675799 88950662703379232525513699)
      ·
        refine ⟨133425994055068848788270549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88950662703379232525513699 133425994055068848788270549)
        ·
          refine ⟨3127171735665676143475091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 133425994055068848788270549 3127171735665676143475091)
          ·
            refine ⟨4690757603498514215212637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3127171735665676143475091 4690757603498514215212637)
            ·
              refine ⟨1759034101311942830704739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4690757603498514215212637 1759034101311942830704739)
              ·
                refine ⟨2638551151967914246057109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1759034101311942830704739 2638551151967914246057109)
                ·
                  refine ⟨123682085248495980283927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2638551151967914246057109 123682085248495980283927)
                  ·
                    rfl

theorem cell22_1083915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 3, 1, 6].length) (baseStart_1083915 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1083915 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1083915 prefixEnd_1083915 := by exact prefixLift 1083915
  have htrace : WordTrace (prefixWord ++ tailWord_1083915) baseStart_1083915 baseEnd_1083915 := by
    simpa [prefixWord, tailWord_1083915, baseEnd_1083915] using wordTrace_append hprefix tailTrace_1083915
  have hstable : (prefixWord ++ tailWord_1083915).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1083915).length < 2 ^ (prefixWord ++ tailWord_1083915).sum := by decide
  have hdescent : baseEnd_1083915 < baseStart_1083915 := by decide
  rcases family_descends (prefixWord ++ tailWord_1083915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1083964 : List Nat := [2, 2, 2, 2, 3, 2, 2, 2, 2, 3]
def baseStart_1083964 : Nat := 118140960795 + 1083964 * 2 ^ 59
def prefixEnd_1083964 : Nat := 4983230072969 + 3 ^ 40 * 1083964 * 2
def baseEnd_1083964 : Nat := 371063029446868146376631

theorem tailTrace_1083964 : CollatzResearch.WordTrace tailWord_1083964 prefixEnd_1083964 371063029446868146376631 := by
  unfold tailWord_1083964
  simp only [CollatzResearch.WordTrace]
  refine ⟨19767707522495514578825473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26356943363327352771767297 19767707522495514578825473)
  ·
    refine ⟨14825780641871635934119105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19767707522495514578825473 14825780641871635934119105)
    ·
      refine ⟨11119335481403726950589329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14825780641871635934119105 11119335481403726950589329)
      ·
        refine ⟨8339501611052795212941997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11119335481403726950589329 8339501611052795212941997)
        ·
          refine ⟨3127313104144798204853249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8339501611052795212941997 3127313104144798204853249)
          ·
            refine ⟨2345484828108598653639937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3127313104144798204853249 2345484828108598653639937)
            ·
              refine ⟨1759113621081448990229953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2345484828108598653639937 1759113621081448990229953)
              ·
                refine ⟨1319335215811086742672465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1759113621081448990229953 1319335215811086742672465)
                ·
                  refine ⟨989501411858315057004349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1319335215811086742672465 989501411858315057004349)
                  ·
                    refine ⟨371063029446868146376631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 989501411858315057004349 371063029446868146376631)
                    ·
                      rfl

theorem cell22_1083964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 2, 2, 2, 3].length) (baseStart_1083964 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1083964 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1083964 prefixEnd_1083964 := by exact prefixLift 1083964
  have htrace : WordTrace (prefixWord ++ tailWord_1083964) baseStart_1083964 baseEnd_1083964 := by
    simpa [prefixWord, tailWord_1083964, baseEnd_1083964] using wordTrace_append hprefix tailTrace_1083964
  have hstable : (prefixWord ++ tailWord_1083964).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1083964).length < 2 ^ (prefixWord ++ tailWord_1083964).sum := by decide
  have hdescent : baseEnd_1083964 < baseStart_1083964 := by decide
  rcases family_descends (prefixWord ++ tailWord_1083964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1083966 : List Nat := [4, 2, 1, 4, 1, 1, 1, 4, 4]
def baseStart_1083966 : Nat := 118140960795 + 1083966 * 2 ^ 59
def prefixEnd_1083966 : Nat := 4983230072969 + 3 ^ 40 * 1083966 * 2
def baseEnd_1083966 : Nat := 123687904695913602608875

theorem tailTrace_1083966 : CollatzResearch.WordTrace tailWord_1083966 prefixEnd_1083966 123687904695913602608875 := by
  unfold tailWord_1083966
  simp only [CollatzResearch.WordTrace]
  refine ⟨4941935998872972937402969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26356991993989188999482501 4941935998872972937402969)
  ·
    refine ⟨3706451999154729703052227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4941935998872972937402969 3706451999154729703052227)
    ·
      refine ⟨5559677998732094554578341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3706451999154729703052227 5559677998732094554578341)
      ·
        refine ⟨1042439624762267728983439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5559677998732094554578341 1042439624762267728983439)
        ·
          refine ⟨1563659437143401593475159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1042439624762267728983439 1563659437143401593475159)
          ·
            refine ⟨2345489155715102390212739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1563659437143401593475159 2345489155715102390212739)
            ·
              refine ⟨3518233733572653585319109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2345489155715102390212739 3518233733572653585319109)
              ·
                refine ⟨659668825044872547247333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3518233733572653585319109 659668825044872547247333)
                ·
                  refine ⟨123687904695913602608875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 659668825044872547247333 123687904695913602608875)
                  ·
                    rfl

theorem cell22_1083966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 1, 4, 4].length) (baseStart_1083966 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1083966 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1083966 prefixEnd_1083966 := by exact prefixLift 1083966
  have htrace : WordTrace (prefixWord ++ tailWord_1083966) baseStart_1083966 baseEnd_1083966 := by
    simpa [prefixWord, tailWord_1083966, baseEnd_1083966] using wordTrace_append hprefix tailTrace_1083966
  have hstable : (prefixWord ++ tailWord_1083966).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1083966).length < 2 ^ (prefixWord ++ tailWord_1083966).sum := by decide
  have hdescent : baseEnd_1083966 < baseStart_1083966 := by decide
  rcases family_descends (prefixWord ++ tailWord_1083966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1083996 : List Nat := [2, 2, 4, 1, 4, 1, 1, 1, 2, 4]
def baseStart_1083996 : Nat := 118140960795 + 1083996 * 2 ^ 59
def prefixEnd_1083996 : Nat := 4983230072969 + 3 ^ 40 * 1083996 * 2
def baseEnd_1083996 : Nat := 371073983700830729576533

theorem tailTrace_1083996 : CollatzResearch.WordTrace tailWord_1083996 prefixEnd_1083996 371073983700830729576533 := by
  unfold tailWord_1083996
  simp only [CollatzResearch.WordTrace]
  refine ⟨19768291090437549311407921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26357721453916732415210561 19768291090437549311407921)
  ·
    refine ⟨14826218317828161983555941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19768291090437549311407921 14826218317828161983555941)
    ·
      refine ⟨2779915934592780371916739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14826218317828161983555941 2779915934592780371916739)
      ·
        refine ⟨4169873901889170557875109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2779915934592780371916739 4169873901889170557875109)
        ·
          refine ⟨781851356604219479601583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4169873901889170557875109 781851356604219479601583)
          ·
            refine ⟨1172777034906329219402375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 781851356604219479601583 1172777034906329219402375)
            ·
              refine ⟨1759165552359493829103563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1172777034906329219402375 1759165552359493829103563)
              ·
                refine ⟨2638748328539240743655345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1759165552359493829103563 2638748328539240743655345)
                ·
                  refine ⟨1979061246404430557741509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2638748328539240743655345 1979061246404430557741509)
                  ·
                    refine ⟨371073983700830729576533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1979061246404430557741509 371073983700830729576533)
                    ·
                      rfl

theorem cell22_1083996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 4, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 4, 1, 1, 1, 2, 4].length) (baseStart_1083996 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1083996 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1083996 prefixEnd_1083996 := by exact prefixLift 1083996
  have htrace : WordTrace (prefixWord ++ tailWord_1083996) baseStart_1083996 baseEnd_1083996 := by
    simpa [prefixWord, tailWord_1083996, baseEnd_1083996] using wordTrace_append hprefix tailTrace_1083996
  have hstable : (prefixWord ++ tailWord_1083996).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1083996).length < 2 ^ (prefixWord ++ tailWord_1083996).sum := by decide
  have hdescent : baseEnd_1083996 < baseStart_1083996 := by decide
  rcases family_descends (prefixWord ++ tailWord_1083996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1084035 : List Nat := [1, 1, 1, 3, 3, 1, 2, 1, 5, 4]
def baseStart_1084035 : Nat := 118140960795 + 1084035 * 2 ^ 59
def prefixEnd_1084035 : Nat := 4983230072969 + 3 ^ 40 * 1084035 * 2
def baseEnd_1084035 : Nat := 371087334197847627851413

theorem tailTrace_1084035 : CollatzResearch.WordTrace tailWord_1084035 prefixEnd_1084035 371087334197847627851413 := by
  unfold tailWord_1084035
  simp only [CollatzResearch.WordTrace]
  refine ⟨39538004627733808283485559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26358669751822538855657039 39538004627733808283485559)
  ·
    refine ⟨59307006941600712425228339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39538004627733808283485559 59307006941600712425228339)
    ·
      refine ⟨88960510412401068637842509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59307006941600712425228339 88960510412401068637842509)
      ·
        refine ⟨33360191404650400739190941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 88960510412401068637842509 33360191404650400739190941)
        ·
          refine ⟨12510071776743900277196603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33360191404650400739190941 12510071776743900277196603)
          ·
            refine ⟨18765107665115850415794905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12510071776743900277196603 18765107665115850415794905)
            ·
              refine ⟨14073830748836887811846179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18765107665115850415794905 14073830748836887811846179)
              ·
                refine ⟨21110746123255331717769269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14073830748836887811846179 21110746123255331717769269)
                ·
                  refine ⟨1979132449055187348540869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 21110746123255331717769269 1979132449055187348540869)
                  ·
                    refine ⟨371087334197847627851413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1979132449055187348540869 371087334197847627851413)
                    ·
                      rfl

theorem cell22_1084035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 1, 5, 4].length) (baseStart_1084035 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1084035 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1084035 prefixEnd_1084035 := by exact prefixLift 1084035
  have htrace : WordTrace (prefixWord ++ tailWord_1084035) baseStart_1084035 baseEnd_1084035 := by
    simpa [prefixWord, tailWord_1084035, baseEnd_1084035] using wordTrace_append hprefix tailTrace_1084035
  have hstable : (prefixWord ++ tailWord_1084035).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1084035).length < 2 ^ (prefixWord ++ tailWord_1084035).sum := by decide
  have hdescent : baseEnd_1084035 < baseStart_1084035 := by decide
  rcases family_descends (prefixWord ++ tailWord_1084035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1084067 : List Nat := [1, 1, 1, 4, 1, 1, 2, 7, 4]
def baseStart_1084067 : Nat := 118140960795 + 1084067 * 2 ^ 59
def prefixEnd_1084067 : Nat := 4983230072969 + 3 ^ 40 * 1084067 * 2
def baseEnd_1084067 : Nat := 123699429483936737017105

theorem tailTrace_1084067 : CollatzResearch.WordTrace tailWord_1084067 prefixEnd_1084067 123699429483936737017105 := by
  unfold tailWord_1084067
  simp only [CollatzResearch.WordTrace]
  refine ⟨39539171763617877748650455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26359447842411918499100303 39539171763617877748650455)
  ·
    refine ⟨59308757645426816622975683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39539171763617877748650455 59308757645426816622975683)
    ·
      refine ⟨88963136468140224934463525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59308757645426816622975683 88963136468140224934463525)
      ·
        refine ⟨16680588087776292175211911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 88963136468140224934463525 16680588087776292175211911)
        ·
          refine ⟨25020882131664438262817867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16680588087776292175211911 25020882131664438262817867)
          ·
            refine ⟨37531323197496657394226801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25020882131664438262817867 37531323197496657394226801)
            ·
              refine ⟨28148492398122493045670101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37531323197496657394226801 28148492398122493045670101)
              ·
                refine ⟨659730290580995930757893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 28148492398122493045670101 659730290580995930757893)
                ·
                  refine ⟨123699429483936737017105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 659730290580995930757893 123699429483936737017105)
                  ·
                    rfl

theorem cell22_1084067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 7, 4].length) (baseStart_1084067 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1084067 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1084067 prefixEnd_1084067 := by exact prefixLift 1084067
  have htrace : WordTrace (prefixWord ++ tailWord_1084067) baseStart_1084067 baseEnd_1084067 := by
    simpa [prefixWord, tailWord_1084067, baseEnd_1084067] using wordTrace_append hprefix tailTrace_1084067
  have hstable : (prefixWord ++ tailWord_1084067).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1084067).length < 2 ^ (prefixWord ++ tailWord_1084067).sum := by decide
  have hdescent : baseEnd_1084067 < baseStart_1084067 := by decide
  rcases family_descends (prefixWord ++ tailWord_1084067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1084095 : List Nat := [1, 1, 2, 2, 2, 4, 1, 9]
def baseStart_1084095 : Nat := 118140960795 + 1084095 * 2 ^ 59
def prefixEnd_1084095 : Nat := 4983230072969 + 3 ^ 40 * 1084095 * 2
def baseEnd_1084095 : Nat := 41234208158225274594581

theorem tailTrace_1084095 : CollatzResearch.WordTrace tailWord_1084095 prefixEnd_1084095 41234208158225274594581 := by
  unfold tailWord_1084095
  simp only [CollatzResearch.WordTrace]
  refine ⟨39540193007516438530669739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26360128671677625687113159 39540193007516438530669739)
  ·
    refine ⟨59310289511274657796004609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39540193007516438530669739 59310289511274657796004609)
    ·
      refine ⟨44482717133455993347003457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59310289511274657796004609 44482717133455993347003457)
      ·
        refine ⟨33362037850091995010252593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44482717133455993347003457 33362037850091995010252593)
        ·
          refine ⟨25021528387568996257689445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33362037850091995010252593 25021528387568996257689445)
          ·
            refine ⟨4691536572669186798316771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25021528387568996257689445 4691536572669186798316771)
            ·
              refine ⟨7037304859003780197475157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4691536572669186798316771 7037304859003780197475157)
              ·
                refine ⟨41234208158225274594581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 7037304859003780197475157 41234208158225274594581)
                ·
                  rfl

theorem cell22_1084095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 1, 9].length) (baseStart_1084095 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1084095 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1084095 prefixEnd_1084095 := by exact prefixLift 1084095
  have htrace : WordTrace (prefixWord ++ tailWord_1084095) baseStart_1084095 baseEnd_1084095 := by
    simpa [prefixWord, tailWord_1084095, baseEnd_1084095] using wordTrace_append hprefix tailTrace_1084095
  have hstable : (prefixWord ++ tailWord_1084095).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1084095).length < 2 ^ (prefixWord ++ tailWord_1084095).sum := by decide
  have hdescent : baseEnd_1084095 < baseStart_1084095 := by decide
  rcases family_descends (prefixWord ++ tailWord_1084095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1084142 : List Nat := [4, 1, 2, 1, 1, 3, 1, 1, 2, 6]
def baseStart_1084142 : Nat := 118140960795 + 1084142 * 2 ^ 59
def prefixEnd_1084142 : Nat := 4983230072969 + 3 ^ 40 * 1084142 * 2
def baseEnd_1084142 : Nat := 371123962484535015426085

theorem tailTrace_1084142 : CollatzResearch.WordTrace tailWord_1084142 prefixEnd_1084142 371123962484535015426085 := by
  unfold tailWord_1084142
  simp only [CollatzResearch.WordTrace]
  refine ⟨4942738404793270694703835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26361271492230777038420453 4942738404793270694703835)
  ·
    refine ⟨7414107607189906042055753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4942738404793270694703835 7414107607189906042055753)
    ·
      refine ⟨5560580705392429531541815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7414107607189906042055753 5560580705392429531541815)
      ·
        refine ⟨8340871058088644297312723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5560580705392429531541815 8340871058088644297312723)
        ·
          refine ⟨12511306587132966445969085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8340871058088644297312723 12511306587132966445969085)
          ·
            refine ⟨4691739970174862417238407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12511306587132966445969085 4691739970174862417238407)
            ·
              refine ⟨7037609955262293625857611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4691739970174862417238407 7037609955262293625857611)
              ·
                refine ⟨10556414932893440438786417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7037609955262293625857611 10556414932893440438786417)
                ·
                  refine ⟨7917311199670080329089813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10556414932893440438786417 7917311199670080329089813)
                  ·
                    refine ⟨371123962484535015426085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7917311199670080329089813 371123962484535015426085)
                    ·
                      rfl

theorem cell22_1084142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 1, 1, 2, 6].length) (baseStart_1084142 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1084142 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1084142 prefixEnd_1084142 := by exact prefixLift 1084142
  have htrace : WordTrace (prefixWord ++ tailWord_1084142) baseStart_1084142 baseEnd_1084142 := by
    simpa [prefixWord, tailWord_1084142, baseEnd_1084142] using wordTrace_append hprefix tailTrace_1084142
  have hstable : (prefixWord ++ tailWord_1084142).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1084142).length < 2 ^ (prefixWord ++ tailWord_1084142).sum := by decide
  have hdescent : baseEnd_1084142 < baseStart_1084142 := by decide
  rcases family_descends (prefixWord ++ tailWord_1084142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1084157 : List Nat := [1, 4, 1, 1, 1, 1, 3, 5, 5]
def baseStart_1084157 : Nat := 118140960795 + 1084157 * 2 ^ 59
def prefixEnd_1084157 : Nat := 4983230072969 + 3 ^ 40 * 1084157 * 2
def baseEnd_1084157 : Nat := 123709699097026658767013

theorem tailTrace_1084157 : CollatzResearch.WordTrace tailWord_1084157 prefixEnd_1084157 123709699097026658767013 := by
  unfold tailWord_1084157
  simp only [CollatzResearch.WordTrace]
  refine ⟨39542454333291823119426725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26361636222194548746284483 39542454333291823119426725)
  ·
    refine ⟨7414210187492216834892511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 39542454333291823119426725 7414210187492216834892511)
    ·
      refine ⟨11121315281238325252338767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7414210187492216834892511 11121315281238325252338767)
      ·
        refine ⟨16681972921857487878508151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11121315281238325252338767 16681972921857487878508151)
        ·
          refine ⟨25022959382786231817762227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16681972921857487878508151 25022959382786231817762227)
          ·
            refine ⟨37534439074179347726643341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25022959382786231817762227 37534439074179347726643341)
            ·
              refine ⟨14075414652817255397491253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37534439074179347726643341 14075414652817255397491253)
              ·
                refine ⟨1319570123701617693514805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14075414652817255397491253 1319570123701617693514805)
                ·
                  refine ⟨123709699097026658767013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1319570123701617693514805 123709699097026658767013)
                  ·
                    rfl

theorem cell22_1084157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 5, 5].length) (baseStart_1084157 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1084157 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1084157 prefixEnd_1084157 := by exact prefixLift 1084157
  have htrace : WordTrace (prefixWord ++ tailWord_1084157) baseStart_1084157 baseEnd_1084157 := by
    simpa [prefixWord, tailWord_1084157, baseEnd_1084157] using wordTrace_append hprefix tailTrace_1084157
  have hstable : (prefixWord ++ tailWord_1084157).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1084157).length < 2 ^ (prefixWord ++ tailWord_1084157).sum := by decide
  have hdescent : baseEnd_1084157 < baseStart_1084157 := by decide
  rcases family_descends (prefixWord ++ tailWord_1084157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1084232 : List Nat := [2, 1, 3, 1, 1, 3, 1, 3, 1, 6]
def baseStart_1084232 : Nat := 118140960795 + 1084232 * 2 ^ 59
def prefixEnd_1084232 : Nat := 4983230072969 + 3 ^ 40 * 1084232 * 2
def baseEnd_1084232 : Nat := 371154771323804780675809

theorem tailTrace_1084232 : CollatzResearch.WordTrace tailWord_1084232 prefixEnd_1084232 371154771323804780675809 := by
  unfold tailWord_1084232
  simp only [CollatzResearch.WordTrace]
  refine ⟨19772594904010055464203475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26363459872013407285604633 19772594904010055464203475)
  ·
    refine ⟨29658892356015083196305213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19772594904010055464203475 29658892356015083196305213)
    ·
      refine ⟨11122084633505656198614455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29658892356015083196305213 11122084633505656198614455)
      ·
        refine ⟨16683126950258484297921683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11122084633505656198614455 16683126950258484297921683)
        ·
          refine ⟨25024690425387726446882525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16683126950258484297921683 25024690425387726446882525)
          ·
            refine ⟨9384258909520397417580947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25024690425387726446882525 9384258909520397417580947)
            ·
              refine ⟨14076388364280596126371421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9384258909520397417580947 14076388364280596126371421)
              ·
                refine ⟨5278645636605223547389283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14076388364280596126371421 5278645636605223547389283)
                ·
                  refine ⟨7917968454907835321083925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5278645636605223547389283 7917968454907835321083925)
                  ·
                    refine ⟨371154771323804780675809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7917968454907835321083925 371154771323804780675809)
                    ·
                      rfl

theorem cell22_1084232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 3, 1, 6].length) (baseStart_1084232 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1084232 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1084232 prefixEnd_1084232 := by exact prefixLift 1084232
  have htrace : WordTrace (prefixWord ++ tailWord_1084232) baseStart_1084232 baseEnd_1084232 := by
    simpa [prefixWord, tailWord_1084232, baseEnd_1084232] using wordTrace_append hprefix tailTrace_1084232
  have hstable : (prefixWord ++ tailWord_1084232).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1084232).length < 2 ^ (prefixWord ++ tailWord_1084232).sum := by decide
  have hdescent : baseEnd_1084232 < baseStart_1084232 := by decide
  rcases family_descends (prefixWord ++ tailWord_1084232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1084236 : List Nat := [2, 2, 1, 3, 3, 1, 3, 3, 4]
def baseStart_1084236 : Nat := 118140960795 + 1084236 * 2 ^ 59
def prefixEnd_1084236 : Nat := 4983230072969 + 3 ^ 40 * 1084236 * 2
def baseEnd_1084236 : Nat := 123718713535183367858599

theorem tailTrace_1084236 : CollatzResearch.WordTrace tailWord_1084236 prefixEnd_1084236 123718713535183367858599 := by
  unfold tailWord_1084236
  simp only [CollatzResearch.WordTrace]
  refine ⟨19772667850002809805776281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26363557133337079741035041 19772667850002809805776281)
  ·
    refine ⟨14829500887502107354332211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19772667850002809805776281 14829500887502107354332211)
    ·
      refine ⟨22244251331253161031498317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14829500887502107354332211 22244251331253161031498317)
      ·
        refine ⟨8341594249219935386811869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22244251331253161031498317 8341594249219935386811869)
        ·
          refine ⟨3128097843457475770054451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8341594249219935386811869 3128097843457475770054451)
          ·
            refine ⟨4692146765186213655081677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3128097843457475770054451 4692146765186213655081677)
            ·
              refine ⟨1759555036944830120655629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4692146765186213655081677 1759555036944830120655629)
              ·
                refine ⟨659833138854311295245861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1759555036944830120655629 659833138854311295245861)
                ·
                  refine ⟨123718713535183367858599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 659833138854311295245861 123718713535183367858599)
                  ·
                    rfl

theorem cell22_1084236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 3, 3, 4].length) (baseStart_1084236 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1084236 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1084236 prefixEnd_1084236 := by exact prefixLift 1084236
  have htrace : WordTrace (prefixWord ++ tailWord_1084236) baseStart_1084236 baseEnd_1084236 := by
    simpa [prefixWord, tailWord_1084236, baseEnd_1084236] using wordTrace_append hprefix tailTrace_1084236
  have hstable : (prefixWord ++ tailWord_1084236).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1084236).length < 2 ^ (prefixWord ++ tailWord_1084236).sum := by decide
  have hdescent : baseEnd_1084236 < baseStart_1084236 := by decide
  rcases family_descends (prefixWord ++ tailWord_1084236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1084247 : List Nat := [1, 1, 3, 2, 4, 1, 10]
def baseStart_1084247 : Nat := 118140960795 + 1084247 * 2 ^ 59
def prefixEnd_1084247 : Nat := 4983230072969 + 3 ^ 40 * 1084247 * 2
def baseEnd_1084247 : Nat := 13746663190012953390769

theorem tailTrace_1084247 : CollatzResearch.WordTrace tailWord_1084247 prefixEnd_1084247 13746663190012953390769 := by
  unfold tailWord_1084247
  simp only [CollatzResearch.WordTrace]
  refine ⟨39545736902965768490202995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26363824601977178993468663 39545736902965768490202995)
  ·
    refine ⟨59318605354448652735304493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39545736902965768490202995 59318605354448652735304493)
    ·
      refine ⟨22244477007918244775739185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59318605354448652735304493 22244477007918244775739185)
      ·
        refine ⟨16683357755938683581804389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22244477007918244775739185 16683357755938683581804389)
        ·
          refine ⟨3128129579238503171588323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16683357755938683581804389 3128129579238503171588323)
          ·
            refine ⟨4692194368857754757382485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3128129579238503171588323 4692194368857754757382485)
            ·
              refine ⟨13746663190012953390769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 4692194368857754757382485 13746663190012953390769)
              ·
                rfl

theorem cell22_1084247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 10].length) (baseStart_1084247 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1084247 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1084247 prefixEnd_1084247 := by exact prefixLift 1084247
  have htrace : WordTrace (prefixWord ++ tailWord_1084247) baseStart_1084247 baseEnd_1084247 := by
    simpa [prefixWord, tailWord_1084247, baseEnd_1084247] using wordTrace_append hprefix tailTrace_1084247
  have hstable : (prefixWord ++ tailWord_1084247).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1084247).length < 2 ^ (prefixWord ++ tailWord_1084247).sum := by decide
  have hdescent : baseEnd_1084247 < baseStart_1084247 := by decide
  rcases family_descends (prefixWord ++ tailWord_1084247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1084249 : List Nat := [1, 2, 1, 2, 2, 5, 1, 2, 2, 4]
def baseStart_1084249 : Nat := 118140960795 + 1084249 * 2 ^ 59
def prefixEnd_1084249 : Nat := 4983230072969 + 3 ^ 40 * 1084249 * 2
def baseEnd_1084249 : Nat := 371160590771222403000757

theorem tailTrace_1084249 : CollatzResearch.WordTrace tailWord_1084249 prefixEnd_1084249 371160590771222403000757 := by
  unfold tailWord_1084249
  simp only [CollatzResearch.WordTrace]
  refine ⟨39545809848958522831775801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26363873232639015221183867 39545809848958522831775801)
  ·
    refine ⟨29659357386718892123831851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39545809848958522831775801 29659357386718892123831851)
    ·
      refine ⟨44489036080078338185747777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29659357386718892123831851 44489036080078338185747777)
      ·
        refine ⟨33366777060058753639310833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44489036080078338185747777 33366777060058753639310833)
        ·
          refine ⟨25025082795044065229483125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33366777060058753639310833 25025082795044065229483125)
          ·
            refine ⟨2346101512035381115264043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 25025082795044065229483125 2346101512035381115264043)
            ·
              refine ⟨3519152268053071672896065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2346101512035381115264043 3519152268053071672896065)
              ·
                refine ⟨2639364201039803754672049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3519152268053071672896065 2639364201039803754672049)
                ·
                  refine ⟨1979523150779852816004037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2639364201039803754672049 1979523150779852816004037)
                  ·
                    refine ⟨371160590771222403000757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1979523150779852816004037 371160590771222403000757)
                    ·
                      rfl

theorem cell22_1084249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 1, 2, 2, 4].length) (baseStart_1084249 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1084249 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1084249 prefixEnd_1084249 := by exact prefixLift 1084249
  have htrace : WordTrace (prefixWord ++ tailWord_1084249) baseStart_1084249 baseEnd_1084249 := by
    simpa [prefixWord, tailWord_1084249, baseEnd_1084249] using wordTrace_append hprefix tailTrace_1084249
  have hstable : (prefixWord ++ tailWord_1084249).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1084249).length < 2 ^ (prefixWord ++ tailWord_1084249).sum := by decide
  have hdescent : baseEnd_1084249 < baseStart_1084249 := by decide
  rcases family_descends (prefixWord ++ tailWord_1084249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1084264 : List Nat := [2, 1, 4, 2, 1, 3, 2, 7]
def baseStart_1084264 : Nat := 118140960795 + 1084264 * 2 ^ 59
def prefixEnd_1084264 : Nat := 4983230072969 + 3 ^ 40 * 1084264 * 2
def baseEnd_1084264 : Nat := 41240636175307484875079

theorem tailTrace_1084264 : CollatzResearch.WordTrace tailWord_1084264 prefixEnd_1084264 41240636175307484875079 := by
  unfold tailWord_1084264
  simp only [CollatzResearch.WordTrace]
  refine ⟨19773178471952090196785923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26364237962602786929047897 19773178471952090196785923)
  ·
    refine ⟨29659767707928135295178885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19773178471952090196785923 29659767707928135295178885)
    ·
      refine ⟨5561206445236525367846041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29659767707928135295178885 5561206445236525367846041)
      ·
        refine ⟨4170904833927394025884531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5561206445236525367846041 4170904833927394025884531)
        ·
          refine ⟨6256357250891091038826797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4170904833927394025884531 6256357250891091038826797)
          ·
            refine ⟨2346133969084159139560049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6256357250891091038826797 2346133969084159139560049)
            ·
              refine ⟨1759600476813119354670037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2346133969084159139560049 1759600476813119354670037)
              ·
                refine ⟨41240636175307484875079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1759600476813119354670037 41240636175307484875079)
                ·
                  rfl

theorem cell22_1084264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 2, 7].length) (baseStart_1084264 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1084264 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1084264 prefixEnd_1084264 := by exact prefixLift 1084264
  have htrace : WordTrace (prefixWord ++ tailWord_1084264) baseStart_1084264 baseEnd_1084264 := by
    simpa [prefixWord, tailWord_1084264, baseEnd_1084264] using wordTrace_append hprefix tailTrace_1084264
  have hstable : (prefixWord ++ tailWord_1084264).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1084264).length < 2 ^ (prefixWord ++ tailWord_1084264).sum := by decide
  have hdescent : baseEnd_1084264 < baseStart_1084264 := by decide
  rcases family_descends (prefixWord ++ tailWord_1084264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1084279 : List Nat := [1, 1, 3, 1, 1, 2, 1, 6, 3, 3]
def baseStart_1084279 : Nat := 118140960795 + 1084279 * 2 ^ 59
def prefixEnd_1084279 : Nat := 4983230072969 + 3 ^ 40 * 1084279 * 2
def baseEnd_1084279 : Nat := 371170860384312324750665

theorem tailTrace_1084279 : CollatzResearch.WordTrace tailWord_1084279 prefixEnd_1084279 371170860384312324750665 := by
  unfold tailWord_1084279
  simp only [CollatzResearch.WordTrace]
  refine ⟨39546904038849837955367891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26364602692566558636911927 39546904038849837955367891)
  ·
    refine ⟨59320356058274756933051837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39546904038849837955367891 59320356058274756933051837)
    ·
      refine ⟨22245133521853033849894439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59320356058274756933051837 22245133521853033849894439)
      ·
        refine ⟨33367700282779550774841659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22245133521853033849894439 33367700282779550774841659)
        ·
          refine ⟨50051550424169326162262489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33367700282779550774841659 50051550424169326162262489)
          ·
            refine ⟨37538662818126994621696867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50051550424169326162262489 37538662818126994621696867)
            ·
              refine ⟨56307994227190491932545301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37538662818126994621696867 56307994227190491932545301)
              ·
                refine ⟨2639437229399554309338061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 56307994227190491932545301 2639437229399554309338061)
                ·
                  refine ⟨989788961024832866001773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2639437229399554309338061 989788961024832866001773)
                  ·
                    refine ⟨371170860384312324750665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 989788961024832866001773 371170860384312324750665)
                    ·
                      rfl

theorem cell22_1084279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 6, 3, 3].length) (baseStart_1084279 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1084279 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1084279 prefixEnd_1084279 := by exact prefixLift 1084279
  have htrace : WordTrace (prefixWord ++ tailWord_1084279) baseStart_1084279 baseEnd_1084279 := by
    simpa [prefixWord, tailWord_1084279, baseEnd_1084279] using wordTrace_append hprefix tailTrace_1084279
  have hstable : (prefixWord ++ tailWord_1084279).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1084279).length < 2 ^ (prefixWord ++ tailWord_1084279).sum := by decide
  have hdescent : baseEnd_1084279 < baseStart_1084279 := by decide
  rcases family_descends (prefixWord ++ tailWord_1084279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1084309 : List Nat := [1, 3, 2, 1, 1, 4, 1, 4, 5]
def baseStart_1084309 : Nat := 118140960795 + 1084309 * 2 ^ 59
def prefixEnd_1084309 : Nat := 4983230072969 + 3 ^ 40 * 1084309 * 2
def baseEnd_1084309 : Nat := 123727043332467415500191

theorem tailTrace_1084309 : CollatzResearch.WordTrace tailWord_1084309 prefixEnd_1084309 123727043332467415500191 := by
  unfold tailWord_1084309
  simp only [CollatzResearch.WordTrace]
  refine ⟨39547998228741153078959981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26365332152494102052639987 39547998228741153078959981)
  ·
    refine ⟨14830499335777932404609993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39547998228741153078959981 14830499335777932404609993)
    ·
      refine ⟨11122874501833449303457495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14830499335777932404609993 11122874501833449303457495)
      ·
        refine ⟨16684311752750173955186243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11122874501833449303457495 16684311752750173955186243)
        ·
          refine ⟨25026467629125260932779365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16684311752750173955186243 25026467629125260932779365)
          ·
            refine ⟨4692462680460986424896131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25026467629125260932779365 4692462680460986424896131)
            ·
              refine ⟨7038694020691479637344197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4692462680460986424896131 7038694020691479637344197)
              ·
                refine ⟨1319755128879652432002037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7038694020691479637344197 1319755128879652432002037)
                ·
                  refine ⟨123727043332467415500191, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1319755128879652432002037 123727043332467415500191)
                  ·
                    rfl

theorem cell22_1084309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 1, 4, 5].length) (baseStart_1084309 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1084309 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1084309 prefixEnd_1084309 := by exact prefixLift 1084309
  have htrace : WordTrace (prefixWord ++ tailWord_1084309) baseStart_1084309 baseEnd_1084309 := by
    simpa [prefixWord, tailWord_1084309, baseEnd_1084309] using wordTrace_append hprefix tailTrace_1084309
  have hstable : (prefixWord ++ tailWord_1084309).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1084309).length < 2 ^ (prefixWord ++ tailWord_1084309).sum := by decide
  have hdescent : baseEnd_1084309 < baseStart_1084309 := by decide
  rcases family_descends (prefixWord ++ tailWord_1084309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1084324 : List Nat := [2, 3, 1, 2, 1, 2, 3, 1, 2, 5]
def baseStart_1084324 : Nat := 118140960795 + 1084324 * 2 ^ 59
def prefixEnd_1084324 : Nat := 4983230072969 + 3 ^ 40 * 1084324 * 2
def baseEnd_1084324 : Nat := 371186264803947207375527

theorem tailTrace_1084324 : CollatzResearch.WordTrace tailWord_1084324 prefixEnd_1084324 371186264803947207375527 := by
  unfold tailWord_1084324
  simp only [CollatzResearch.WordTrace]
  refine ⟨19774272661843405320378013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26365696882457873760504017 19774272661843405320378013)
  ·
    refine ⟨7415352248191276995141755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19774272661843405320378013 7415352248191276995141755)
    ·
      refine ⟨11123028372286915492712633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7415352248191276995141755 11123028372286915492712633)
      ·
        refine ⟨8342271279215186619534475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11123028372286915492712633 8342271279215186619534475)
        ·
          refine ⟨12513406918822779929301713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8342271279215186619534475 12513406918822779929301713)
          ·
            refine ⟨9385055189117084946976285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12513406918822779929301713 9385055189117084946976285)
            ·
              refine ⟨3519395695918906855116107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9385055189117084946976285 3519395695918906855116107)
              ·
                refine ⟨5279093543878360282674161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3519395695918906855116107 5279093543878360282674161)
                ·
                  refine ⟨3959320157908770212005621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5279093543878360282674161 3959320157908770212005621)
                  ·
                    refine ⟨371186264803947207375527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3959320157908770212005621 371186264803947207375527)
                    ·
                      rfl

theorem cell22_1084324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 3, 1, 2, 5].length) (baseStart_1084324 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1084324 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1084324 prefixEnd_1084324 := by exact prefixLift 1084324
  have htrace : WordTrace (prefixWord ++ tailWord_1084324) baseStart_1084324 baseEnd_1084324 := by
    simpa [prefixWord, tailWord_1084324, baseEnd_1084324] using wordTrace_append hprefix tailTrace_1084324
  have hstable : (prefixWord ++ tailWord_1084324).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1084324).length < 2 ^ (prefixWord ++ tailWord_1084324).sum := by decide
  have hdescent : baseEnd_1084324 < baseStart_1084324 := by decide
  rcases family_descends (prefixWord ++ tailWord_1084324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1084399 : List Nat := [1, 1, 2, 1, 4, 4, 1, 8]
def baseStart_1084399 : Nat := 118140960795 + 1084399 * 2 ^ 59
def prefixEnd_1084399 : Nat := 4983230072969 + 3 ^ 40 * 1084399 * 2
def baseEnd_1084399 : Nat := 41245770981852445750033

theorem tailTrace_1084399 : CollatzResearch.WordTrace tailWord_1084399 prefixEnd_1084399 41245770981852445750033 := by
  unfold tailWord_1084399
  simp only [CollatzResearch.WordTrace]
  refine ⟨39551280798415098449736251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26367520532276732299824167 39551280798415098449736251)
  ·
    refine ⟨59326921197622647674604377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39551280798415098449736251 59326921197622647674604377)
    ·
      refine ⟨44495190898216985755953283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59326921197622647674604377 44495190898216985755953283)
      ·
        refine ⟨66742786347325478633929925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44495190898216985755953283 66742786347325478633929925)
        ·
          refine ⟨12514272440123527243861861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 66742786347325478633929925 12514272440123527243861861)
          ·
            refine ⟨2346426082523161358224099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12514272440123527243861861 2346426082523161358224099)
            ·
              refine ⟨3519639123784742037336149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2346426082523161358224099 3519639123784742037336149)
              ·
                refine ⟨41245770981852445750033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3519639123784742037336149 41245770981852445750033)
                ·
                  rfl

theorem cell22_1084399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 1, 8].length) (baseStart_1084399 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1084399 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1084399 prefixEnd_1084399 := by exact prefixLift 1084399
  have htrace : WordTrace (prefixWord ++ tailWord_1084399) baseStart_1084399 baseEnd_1084399 := by
    simpa [prefixWord, tailWord_1084399, baseEnd_1084399] using wordTrace_append hprefix tailTrace_1084399
  have hstable : (prefixWord ++ tailWord_1084399).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1084399).length < 2 ^ (prefixWord ++ tailWord_1084399).sum := by decide
  have hdescent : baseEnd_1084399 < baseStart_1084399 := by decide
  rcases family_descends (prefixWord ++ tailWord_1084399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1084478 : List Nat := [4, 2, 1, 3, 1, 1, 1, 4, 5]
def baseStart_1084478 : Nat := 118140960795 + 1084478 * 2 ^ 59
def prefixEnd_1084478 : Nat := 4983230072969 + 3 ^ 40 * 1084478 * 2
def baseEnd_1084478 : Nat := 123746327383714046341685

theorem tailTrace_1084478 : CollatzResearch.WordTrace tailWord_1084478 prefixEnd_1084478 123746327383714046341685 := by
  unfold tailWord_1084478
  simp only [CollatzResearch.WordTrace]
  refine ⟨4944270270641111867732761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26369441443419263294574725 4944270270641111867732761)
  ·
    refine ⟨3708202702980833900799571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4944270270641111867732761 3708202702980833900799571)
    ·
      refine ⟨5562304054471250851199357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3708202702980833900799571 5562304054471250851199357)
      ·
        refine ⟨2085864020426719069199759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5562304054471250851199357 2085864020426719069199759)
        ·
          refine ⟨3128796030640078603799639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2085864020426719069199759 3128796030640078603799639)
          ·
            refine ⟨4693194045960117905699459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3128796030640078603799639 4693194045960117905699459)
            ·
              refine ⟨7039791068940176858549189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4693194045960117905699459 7039791068940176858549189)
              ·
                refine ⟨1319960825426283160977973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7039791068940176858549189 1319960825426283160977973)
                ·
                  refine ⟨123746327383714046341685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1319960825426283160977973 123746327383714046341685)
                  ·
                    rfl

theorem cell22_1084478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 1, 4, 5].length) (baseStart_1084478 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1084478 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1084478 prefixEnd_1084478 := by exact prefixLift 1084478
  have htrace : WordTrace (prefixWord ++ tailWord_1084478) baseStart_1084478 baseEnd_1084478 := by
    simpa [prefixWord, tailWord_1084478, baseEnd_1084478] using wordTrace_append hprefix tailTrace_1084478
  have hstable : (prefixWord ++ tailWord_1084478).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1084478).length < 2 ^ (prefixWord ++ tailWord_1084478).sum := by decide
  have hdescent : baseEnd_1084478 < baseStart_1084478 := by decide
  rcases family_descends (prefixWord ++ tailWord_1084478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1084493 : List Nat := [1, 6, 1, 1, 1, 3, 1, 1, 2, 5]
def baseStart_1084493 : Nat := 118140960795 + 1084493 * 2 ^ 59
def prefixEnd_1084493 : Nat := 4983230072969 + 3 ^ 40 * 1084493 * 2
def baseEnd_1084493 : Nat := 371244116957687099900009

theorem tailTrace_1084493 : CollatzResearch.WordTrace tailWord_1084493 prefixEnd_1084493 371244116957687099900009 := by
  unfold tailWord_1084493
  simp only [CollatzResearch.WordTrace]
  refine ⟨39554709260074552503658133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26369806173383035002438755 39554709260074552503658133)
  ·
    refine ⟨1854126996565994648608975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 39554709260074552503658133 1854126996565994648608975)
    ·
      refine ⟨2781190494848991972913463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1854126996565994648608975 2781190494848991972913463)
      ·
        refine ⟨4171785742273487959370195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2781190494848991972913463 4171785742273487959370195)
        ·
          refine ⟨6257678613410231939055293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4171785742273487959370195 6257678613410231939055293)
          ·
            refine ⟨2346629480028836977145735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6257678613410231939055293 2346629480028836977145735)
            ·
              refine ⟨3519944220043255465718603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2346629480028836977145735 3519944220043255465718603)
              ·
                refine ⟨5279916330064883198577905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3519944220043255465718603 5279916330064883198577905)
                ·
                  refine ⟨3959937247548662398933429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5279916330064883198577905 3959937247548662398933429)
                  ·
                    refine ⟨371244116957687099900009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3959937247548662398933429 371244116957687099900009)
                    ·
                      rfl

theorem cell22_1084493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 1, 1, 2, 5].length) (baseStart_1084493 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1084493 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1084493 prefixEnd_1084493 := by exact prefixLift 1084493
  have htrace : WordTrace (prefixWord ++ tailWord_1084493) baseStart_1084493 baseEnd_1084493 := by
    simpa [prefixWord, tailWord_1084493, baseEnd_1084493] using wordTrace_append hprefix tailTrace_1084493
  have hstable : (prefixWord ++ tailWord_1084493).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1084493).length < 2 ^ (prefixWord ++ tailWord_1084493).sum := by decide
  have hdescent : baseEnd_1084493 < baseStart_1084493 := by decide
  rcases family_descends (prefixWord ++ tailWord_1084493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1084508 : List Nat := [2, 2, 4, 1, 1, 1, 2, 4, 1, 4]
def baseStart_1084508 : Nat := 118140960795 + 1084508 * 2 ^ 59
def prefixEnd_1084508 : Nat := 4983230072969 + 3 ^ 40 * 1084508 * 2
def baseEnd_1084508 : Nat := 371249251764232060774963

theorem tailTrace_1084508 : CollatzResearch.WordTrace tailWord_1084508 prefixEnd_1084508 371249251764232060774963 := by
  unfold tailWord_1084508
  simp only [CollatzResearch.WordTrace]
  refine ⟨19777628177510105032727089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26370170903346806710302785 19777628177510105032727089)
  ·
    refine ⟨14833221133132578774545317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19777628177510105032727089 14833221133132578774545317)
    ·
      refine ⟨2781228962462358520227247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14833221133132578774545317 2781228962462358520227247)
      ·
        refine ⟨4171843443693537780340871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2781228962462358520227247 4171843443693537780340871)
        ·
          refine ⟨6257765165540306670511307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4171843443693537780340871 6257765165540306670511307)
          ·
            refine ⟨9386647748310460005766961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6257765165540306670511307 9386647748310460005766961)
            ·
              refine ⟨7039985811232845004325221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9386647748310460005766961 7039985811232845004325221)
              ·
                refine ⟨1319997339606158438310979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7039985811232845004325221 1319997339606158438310979)
                ·
                  refine ⟨1979996009409237657466469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1319997339606158438310979 1979996009409237657466469)
                  ·
                    refine ⟨371249251764232060774963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1979996009409237657466469 371249251764232060774963)
                    ·
                      rfl

theorem cell22_1084508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 2, 4, 1, 4].length) (baseStart_1084508 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1084508 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1084508 prefixEnd_1084508 := by exact prefixLift 1084508
  have htrace : WordTrace (prefixWord ++ tailWord_1084508) baseStart_1084508 baseEnd_1084508 := by
    simpa [prefixWord, tailWord_1084508, baseEnd_1084508] using wordTrace_append hprefix tailTrace_1084508
  have hstable : (prefixWord ++ tailWord_1084508).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1084508).length < 2 ^ (prefixWord ++ tailWord_1084508).sum := by decide
  have hdescent : baseEnd_1084508 < baseStart_1084508 := by decide
  rcases family_descends (prefixWord ++ tailWord_1084508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1084521 : List Nat := [1, 2, 1, 1, 1, 6, 2, 2, 1, 5]
def baseStart_1084521 : Nat := 118140960795 + 1084521 * 2 ^ 59
def prefixEnd_1084521 : Nat := 4983230072969 + 3 ^ 40 * 1084521 * 2
def baseEnd_1084521 : Nat := 371253701929904360199923

theorem tailTrace_1084521 : CollatzResearch.WordTrace tailWord_1084521 prefixEnd_1084521 371253701929904360199923 := by
  unfold tailWord_1084521
  simp only [CollatzResearch.WordTrace]
  refine ⟨39555730503973113285677417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26370487002648742190451611 39555730503973113285677417)
  ·
    refine ⟨29666797877979834964258063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39555730503973113285677417 29666797877979834964258063)
    ·
      refine ⟨44500196816969752446387095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29666797877979834964258063 44500196816969752446387095)
      ·
        refine ⟨66750295225454628669580643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44500196816969752446387095 66750295225454628669580643)
        ·
          refine ⟨100125442838181943004370965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66750295225454628669580643 100125442838181943004370965)
          ·
            refine ⟨4693380133039778578329889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 100125442838181943004370965 4693380133039778578329889)
            ·
              refine ⟨3520035099779833933747417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4693380133039778578329889 3520035099779833933747417)
              ·
                refine ⟨2640026324834875450310563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3520035099779833933747417 2640026324834875450310563)
                ·
                  refine ⟨3960039487252313175465845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2640026324834875450310563 3960039487252313175465845)
                  ·
                    refine ⟨371253701929904360199923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3960039487252313175465845 371253701929904360199923)
                    ·
                      rfl

theorem cell22_1084521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 2, 2, 1, 5].length) (baseStart_1084521 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1084521 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1084521 prefixEnd_1084521 := by exact prefixLift 1084521
  have htrace : WordTrace (prefixWord ++ tailWord_1084521) baseStart_1084521 baseEnd_1084521 := by
    simpa [prefixWord, tailWord_1084521, baseEnd_1084521] using wordTrace_append hprefix tailTrace_1084521
  have hstable : (prefixWord ++ tailWord_1084521).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1084521).length < 2 ^ (prefixWord ++ tailWord_1084521).sum := by decide
  have hdescent : baseEnd_1084521 < baseStart_1084521 := by decide
  rcases family_descends (prefixWord ++ tailWord_1084521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1084525 : List Nat := [1, 5, 1, 1, 2, 2, 4, 1, 1, 4]
def baseStart_1084525 : Nat := 118140960795 + 1084525 * 2 ^ 59
def prefixEnd_1084525 : Nat := 4983230072969 + 3 ^ 40 * 1084525 * 2
def baseEnd_1084525 : Nat := 371255071211649683099911

theorem tailTrace_1084525 : CollatzResearch.WordTrace tailWord_1084525 prefixEnd_1084525 371255071211649683099911 := by
  unfold tailWord_1084525
  simp only [CollatzResearch.WordTrace]
  refine ⟨39555876395958621968823029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26370584263972414645882019 39555876395958621968823029)
  ·
    refine ⟨3708363412121120809577159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 39555876395958621968823029 3708363412121120809577159)
    ·
      refine ⟨5562545118181681214365739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3708363412121120809577159 5562545118181681214365739)
      ·
        refine ⟨8343817677272521821548609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5562545118181681214365739 8343817677272521821548609)
        ·
          refine ⟨6257863257954391366161457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8343817677272521821548609 6257863257954391366161457)
          ·
            refine ⟨4693397443465793524621093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6257863257954391366161457 4693397443465793524621093)
            ·
              refine ⟨880012020649836285866455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4693397443465793524621093 880012020649836285866455)
              ·
                refine ⟨1320018030974754428799683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 880012020649836285866455 1320018030974754428799683)
                ·
                  refine ⟨1980027046462131643199525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1320018030974754428799683 1980027046462131643199525)
                  ·
                    refine ⟨371255071211649683099911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1980027046462131643199525 371255071211649683099911)
                    ·
                      rfl

theorem cell22_1084525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 4, 1, 1, 4].length) (baseStart_1084525 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1084525 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1084525 prefixEnd_1084525 := by exact prefixLift 1084525
  have htrace : WordTrace (prefixWord ++ tailWord_1084525) baseStart_1084525 baseEnd_1084525 := by
    simpa [prefixWord, tailWord_1084525, baseEnd_1084525] using wordTrace_append hprefix tailTrace_1084525
  have hstable : (prefixWord ++ tailWord_1084525).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1084525).length < 2 ^ (prefixWord ++ tailWord_1084525).sum := by decide
  have hdescent : baseEnd_1084525 < baseStart_1084525 := by decide
  rcases family_descends (prefixWord ++ tailWord_1084525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1084536 : List Nat := [2, 1, 2, 1, 1, 1, 4, 4, 2, 4]
def baseStart_1084536 : Nat := 118140960795 + 1084536 * 2 ^ 59
def prefixEnd_1084536 : Nat := 4983230072969 + 3 ^ 40 * 1084536 * 2
def baseEnd_1084536 : Nat := 371258836736449321074877

theorem tailTrace_1084536 : CollatzResearch.WordTrace tailWord_1084536 prefixEnd_1084536 371258836736449321074877 := by
  unfold tailWord_1084536
  simp only [CollatzResearch.WordTrace]
  refine ⟨19778138799459385423736731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26370851732612513898315641 19778138799459385423736731)
  ·
    refine ⟨29667208199189078135605097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19778138799459385423736731 29667208199189078135605097)
    ·
      refine ⟨22250406149391808601703823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29667208199189078135605097 22250406149391808601703823)
      ·
        refine ⟨33375609224087712902555735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22250406149391808601703823 33375609224087712902555735)
        ·
          refine ⟨50063413836131569353833603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33375609224087712902555735 50063413836131569353833603)
          ·
            refine ⟨75095120754197354030750405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50063413836131569353833603 75095120754197354030750405)
            ·
              refine ⟨14080335141412003880765701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 75095120754197354030750405 14080335141412003880765701)
              ·
                refine ⟨2640062839014750727643569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14080335141412003880765701 2640062839014750727643569)
                ·
                  refine ⟨1980047129261063045732677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2640062839014750727643569 1980047129261063045732677)
                  ·
                    refine ⟨371258836736449321074877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1980047129261063045732677 371258836736449321074877)
                    ·
                      rfl

theorem cell22_1084536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 4, 2, 4].length) (baseStart_1084536 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1084536 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1084536 prefixEnd_1084536 := by exact prefixLift 1084536
  have htrace : WordTrace (prefixWord ++ tailWord_1084536) baseStart_1084536 baseEnd_1084536 := by
    simpa [prefixWord, tailWord_1084536, baseEnd_1084536] using wordTrace_append hprefix tailTrace_1084536
  have hstable : (prefixWord ++ tailWord_1084536).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1084536).length < 2 ^ (prefixWord ++ tailWord_1084536).sum := by decide
  have hdescent : baseEnd_1084536 < baseStart_1084536 := by decide
  rcases family_descends (prefixWord ++ tailWord_1084536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1084568 : List Nat := [2, 1, 2, 4, 2, 1, 4, 6]
def baseStart_1084568 : Nat := 118140960795 + 1084568 * 2 ^ 59
def prefixEnd_1084568 : Nat := 4983230072969 + 3 ^ 40 * 1084568 * 2
def baseEnd_1084568 : Nat := 41252198998934656030531

theorem tailTrace_1084568 : CollatzResearch.WordTrace tailWord_1084568 prefixEnd_1084568 41252198998934656030531 := by
  unfold tailWord_1084568
  simp only [CollatzResearch.WordTrace]
  refine ⟨19778722367401420156319179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26371629823201893541758905 19778722367401420156319179)
  ·
    refine ⟨29668083551102130234478769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19778722367401420156319179 29668083551102130234478769)
    ·
      refine ⟨22251062663326597675859077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29668083551102130234478769 22251062663326597675859077)
      ·
        refine ⟨4172074249373737064223577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22251062663326597675859077 4172074249373737064223577)
        ·
          refine ⟨3129055687030302798167683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4172074249373737064223577 3129055687030302798167683)
          ·
            refine ⟨4693583530545454197251525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3129055687030302798167683 4693583530545454197251525)
            ·
              refine ⟨880046911977272661984661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4693583530545454197251525 880046911977272661984661)
              ·
                refine ⟨41252198998934656030531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 880046911977272661984661 41252198998934656030531)
                ·
                  rfl

theorem cell22_1084568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 4, 6].length) (baseStart_1084568 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1084568 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1084568 prefixEnd_1084568 := by exact prefixLift 1084568
  have htrace : WordTrace (prefixWord ++ tailWord_1084568) baseStart_1084568 baseEnd_1084568 := by
    simpa [prefixWord, tailWord_1084568, baseEnd_1084568] using wordTrace_append hprefix tailTrace_1084568
  have hstable : (prefixWord ++ tailWord_1084568).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1084568).length < 2 ^ (prefixWord ++ tailWord_1084568).sum := by decide
  have hdescent : baseEnd_1084568 < baseStart_1084568 := by decide
  rcases family_descends (prefixWord ++ tailWord_1084568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1084673 : List Nat := [1, 2, 4, 1, 1, 3, 1, 3, 1, 5]
def baseStart_1084673 : Nat := 118140960795 + 1084673 * 2 ^ 59
def prefixEnd_1084673 : Nat := 4983230072969 + 3 ^ 40 * 1084673 * 2
def baseEnd_1084673 : Nat := 371305734636226630399457

theorem tailTrace_1084673 : CollatzResearch.WordTrace tailWord_1084673 prefixEnd_1084673 371305734636226630399457 := by
  unfold tailWord_1084673
  simp only [CollatzResearch.WordTrace]
  refine ⟨39561274399422443245210673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26374182932948295496807115 39561274399422443245210673)
  ·
    refine ⟨29670955799566832433908005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39561274399422443245210673 29670955799566832433908005)
    ·
      refine ⟨5563304212418781081357751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29670955799566832433908005 5563304212418781081357751)
      ·
        refine ⟨8344956318628171622036627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5563304212418781081357751 8344956318628171622036627)
        ·
          refine ⟨12517434477942257433054941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8344956318628171622036627 12517434477942257433054941)
          ·
            refine ⟨4694037929228346537395603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12517434477942257433054941 4694037929228346537395603)
            ·
              refine ⟨7041056893842519806093405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4694037929228346537395603 7041056893842519806093405)
              ·
                refine ⟨2640396335190944927285027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7041056893842519806093405 2640396335190944927285027)
                ·
                  refine ⟨3960594502786417390927541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2640396335190944927285027 3960594502786417390927541)
                  ·
                    refine ⟨371305734636226630399457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3960594502786417390927541 371305734636226630399457)
                    ·
                      rfl

theorem cell22_1084673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 1, 3, 1, 5].length) (baseStart_1084673 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1084673 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1084673 prefixEnd_1084673 := by exact prefixLift 1084673
  have htrace : WordTrace (prefixWord ++ tailWord_1084673) baseStart_1084673 baseEnd_1084673 := by
    simpa [prefixWord, tailWord_1084673, baseEnd_1084673] using wordTrace_append hprefix tailTrace_1084673
  have hstable : (prefixWord ++ tailWord_1084673).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1084673).length < 2 ^ (prefixWord ++ tailWord_1084673).sum := by decide
  have hdescent : baseEnd_1084673 < baseStart_1084673 := by decide
  rcases family_descends (prefixWord ++ tailWord_1084673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1084703 : List Nat := [1, 1, 2, 4, 4, 1, 9]
def baseStart_1084703 : Nat := 118140960795 + 1084703 * 2 ^ 59
def prefixEnd_1084703 : Nat := 4983230072969 + 3 ^ 40 * 1084703 * 2
def baseEnd_1084703 : Nat := 13752444601826538968495

theorem tailTrace_1084703 : CollatzResearch.WordTrace tailWord_1084703 prefixEnd_1084703 13752444601826538968495 := by
  unfold tailWord_1084703
  simp only [CollatzResearch.WordTrace]
  refine ⟨39562368589313758368802763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26374912392875838912535175 39562368589313758368802763)
  ·
    refine ⟨59343552883970637553204145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39562368589313758368802763 59343552883970637553204145)
    ·
      refine ⟨44507664662977978164903109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59343552883970637553204145 44507664662977978164903109)
      ·
        refine ⟨8345187124308370905919333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 44507664662977978164903109 8345187124308370905919333)
        ·
          refine ⟨1564722585807819544859875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8345187124308370905919333 1564722585807819544859875)
          ·
            refine ⟨2347083878711729317289813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1564722585807819544859875 2347083878711729317289813)
            ·
              refine ⟨13752444601826538968495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2347083878711729317289813 13752444601826538968495)
              ·
                rfl

theorem cell22_1084703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 9].length) (baseStart_1084703 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1084703 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1084703 prefixEnd_1084703 := by exact prefixLift 1084703
  have htrace : WordTrace (prefixWord ++ tailWord_1084703) baseStart_1084703 baseEnd_1084703 := by
    simpa [prefixWord, tailWord_1084703, baseEnd_1084703] using wordTrace_append hprefix tailTrace_1084703
  have hstable : (prefixWord ++ tailWord_1084703).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1084703).length < 2 ^ (prefixWord ++ tailWord_1084703).sum := by decide
  have hdescent : baseEnd_1084703 < baseStart_1084703 := by decide
  rcases family_descends (prefixWord ++ tailWord_1084703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1084707 : List Nat := [1, 1, 1, 4, 2, 5, 1, 2, 2, 3]
def baseStart_1084707 : Nat := 118140960795 + 1084707 * 2 ^ 59
def prefixEnd_1084707 : Nat := 4983230072969 + 3 ^ 40 * 1084707 * 2
def baseEnd_1084707 : Nat := 371317373531061875049353

theorem tailTrace_1084707 : CollatzResearch.WordTrace tailWord_1084707 prefixEnd_1084707 371317373531061875049353 := by
  unfold tailWord_1084707
  simp only [CollatzResearch.WordTrace]
  refine ⟨39562514481299267051948375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26375009654199511367965583 39562514481299267051948375)
  ·
    refine ⟨59343771721948900577922563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39562514481299267051948375 59343771721948900577922563)
    ·
      refine ⟨89015657582923350866883845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59343771721948900577922563 89015657582923350866883845)
      ·
        refine ⟨16690435796798128287540721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 89015657582923350866883845 16690435796798128287540721)
        ·
          refine ⟨12517826847598596215655541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16690435796798128287540721 12517826847598596215655541)
          ·
            refine ⟨1173546266962368395217707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 12517826847598596215655541 1173546266962368395217707)
            ·
              refine ⟨1760319400443552592826561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1173546266962368395217707 1760319400443552592826561)
              ·
                refine ⟨1320239550332664444619921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1760319400443552592826561 1320239550332664444619921)
                ·
                  refine ⟨990179662749498333464941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1320239550332664444619921 990179662749498333464941)
                  ·
                    refine ⟨371317373531061875049353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 990179662749498333464941 371317373531061875049353)
                    ·
                      rfl

theorem cell22_1084707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 5, 1, 2, 2, 3].length) (baseStart_1084707 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1084707 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1084707 prefixEnd_1084707 := by exact prefixLift 1084707
  have htrace : WordTrace (prefixWord ++ tailWord_1084707) baseStart_1084707 baseEnd_1084707 := by
    simpa [prefixWord, tailWord_1084707, baseEnd_1084707] using wordTrace_append hprefix tailTrace_1084707
  have hstable : (prefixWord ++ tailWord_1084707).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1084707).length < 2 ^ (prefixWord ++ tailWord_1084707).sum := by decide
  have hdescent : baseEnd_1084707 < baseStart_1084707 := by decide
  rcases family_descends (prefixWord ++ tailWord_1084707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1084724 : List Nat := [2, 5, 1, 1, 1, 1, 5, 1, 2, 3]
def baseStart_1084724 : Nat := 118140960795 + 1084724 * 2 ^ 59
def prefixEnd_1084724 : Nat := 4983230072969 + 3 ^ 40 * 1084724 * 2
def baseEnd_1084724 : Nat := 371323192978479497374301

theorem tailTrace_1084724 : CollatzResearch.WordTrace tailWord_1084724 prefixEnd_1084724 371323192978479497374301 := by
  unfold tailWord_1084724
  simp only [CollatzResearch.WordTrace]
  refine ⟨19781567261118839477658613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26375423014825119303544817 19781567261118839477658613)
  ·
    refine ⟨1854521930729891201030495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 19781567261118839477658613 1854521930729891201030495)
    ·
      refine ⟨2781782896094836801545743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1854521930729891201030495 2781782896094836801545743)
      ·
        refine ⟨4172674344142255202318615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2781782896094836801545743 4172674344142255202318615)
        ·
          refine ⟨6259011516213382803477923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4172674344142255202318615 6259011516213382803477923)
          ·
            refine ⟨9388517274320074205216885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6259011516213382803477923 9388517274320074205216885)
            ·
              refine ⟨880173494467506956739083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9388517274320074205216885 880173494467506956739083)
              ·
                refine ⟨1320260241701260435108625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 880173494467506956739083 1320260241701260435108625)
                ·
                  refine ⟨990195181275945326331469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1320260241701260435108625 990195181275945326331469)
                  ·
                    refine ⟨371323192978479497374301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 990195181275945326331469 371323192978479497374301)
                    ·
                      rfl

theorem cell22_1084724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 5, 1, 2, 3].length) (baseStart_1084724 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1084724 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1084724 prefixEnd_1084724 := by exact prefixLift 1084724
  have htrace : WordTrace (prefixWord ++ tailWord_1084724) baseStart_1084724 baseEnd_1084724 := by
    simpa [prefixWord, tailWord_1084724, baseEnd_1084724] using wordTrace_append hprefix tailTrace_1084724
  have hstable : (prefixWord ++ tailWord_1084724).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1084724).length < 2 ^ (prefixWord ++ tailWord_1084724).sum := by decide
  have hdescent : baseEnd_1084724 < baseStart_1084724 := by decide
  rcases family_descends (prefixWord ++ tailWord_1084724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1084735 : List Nat := [1, 1, 2, 2, 4, 2, 2, 2, 3, 3]
def baseStart_1084735 : Nat := 118140960795 + 1084735 * 2 ^ 59
def prefixEnd_1084735 : Nat := 4983230072969 + 3 ^ 40 * 1084735 * 2
def baseEnd_1084735 : Nat := 371326958503279135349267

theorem tailTrace_1084735 : CollatzResearch.WordTrace tailWord_1084735 prefixEnd_1084735 371326958503279135349267 := by
  unfold tailWord_1084735
  simp only [CollatzResearch.WordTrace]
  refine ⟨39563535725197827833967659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26375690483465218555978439 39563535725197827833967659)
  ·
    refine ⟨59345303587796741750951489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39563535725197827833967659 59345303587796741750951489)
    ·
      refine ⟨44508977690847556313213617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59345303587796741750951489 44508977690847556313213617)
      ·
        refine ⟨33381733268135667234910213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44508977690847556313213617 33381733268135667234910213)
        ·
          refine ⟨6259074987775437606545665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 33381733268135667234910213 6259074987775437606545665)
          ·
            refine ⟨4694306240831578204909249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6259074987775437606545665 4694306240831578204909249)
            ·
              refine ⟨3520729680623683653681937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4694306240831578204909249 3520729680623683653681937)
              ·
                refine ⟨2640547260467762740261453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3520729680623683653681937 2640547260467762740261453)
                ·
                  refine ⟨990205222675411027598045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2640547260467762740261453 990205222675411027598045)
                  ·
                    refine ⟨371326958503279135349267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 990205222675411027598045 371326958503279135349267)
                    ·
                      rfl

theorem cell22_1084735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 2, 2, 3, 3].length) (baseStart_1084735 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1084735 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1084735 prefixEnd_1084735 := by exact prefixLift 1084735
  have htrace : WordTrace (prefixWord ++ tailWord_1084735) baseStart_1084735 baseEnd_1084735 := by
    simpa [prefixWord, tailWord_1084735, baseEnd_1084735] using wordTrace_append hprefix tailTrace_1084735
  have hstable : (prefixWord ++ tailWord_1084735).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1084735).length < 2 ^ (prefixWord ++ tailWord_1084735).sum := by decide
  have hdescent : baseEnd_1084735 < baseStart_1084735 := by decide
  rcases family_descends (prefixWord ++ tailWord_1084735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1084737 : List Nat := [1, 2, 5, 2, 1, 3, 2, 6]
def baseStart_1084737 : Nat := 118140960795 + 1084737 * 2 ^ 59
def prefixEnd_1084737 : Nat := 4983230072969 + 3 ^ 40 * 1084737 * 2
def baseEnd_1084737 : Nat := 41258627016016866311029

theorem tailTrace_1084737 : CollatzResearch.WordTrace tailWord_1084737 prefixEnd_1084737 41258627016016866311029 := by
  unfold tailWord_1084737
  simp only [CollatzResearch.WordTrace]
  refine ⟨39563608671190582175540465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26375739114127054783693643 39563608671190582175540465)
  ·
    refine ⟨29672706503392936631655349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39563608671190582175540465 29672706503392936631655349)
    ·
      refine ⟨2781816234693087809217689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 29672706503392936631655349 2781816234693087809217689)
      ·
        refine ⟨2086362176019815856913267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2781816234693087809217689 2086362176019815856913267)
        ·
          refine ⟨3129543264029723785369901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2086362176019815856913267 3129543264029723785369901)
          ·
            refine ⟨1173578724011146419513713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3129543264029723785369901 1173578724011146419513713)
            ·
              refine ⟨880184043008359814635285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1173578724011146419513713 880184043008359814635285)
              ·
                refine ⟨41258627016016866311029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 880184043008359814635285 41258627016016866311029)
                ·
                  rfl

theorem cell22_1084737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 3, 2, 6].length) (baseStart_1084737 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1084737 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1084737 prefixEnd_1084737 := by exact prefixLift 1084737
  have htrace : WordTrace (prefixWord ++ tailWord_1084737) baseStart_1084737 baseEnd_1084737 := by
    simpa [prefixWord, tailWord_1084737, baseEnd_1084737] using wordTrace_append hprefix tailTrace_1084737
  have hstable : (prefixWord ++ tailWord_1084737).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1084737).length < 2 ^ (prefixWord ++ tailWord_1084737).sum := by decide
  have hdescent : baseEnd_1084737 < baseStart_1084737 := by decide
  rcases family_descends (prefixWord ++ tailWord_1084737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1084748 : List Nat := [2, 2, 1, 3, 2, 2, 1, 2, 7]
def baseStart_1084748 : Nat := 118140960795 + 1084748 * 2 ^ 59
def prefixEnd_1084748 : Nat := 4983230072969 + 3 ^ 40 * 1084748 * 2
def baseEnd_1084748 : Nat := 123777136222983811591409

theorem tailTrace_1084748 : CollatzResearch.WordTrace tailWord_1084748 prefixEnd_1084748 123777136222983811591409 := by
  unfold tailWord_1084748
  simp only [CollatzResearch.WordTrace]
  refine ⟨19782004937075365527095449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26376006582767154036127265 19782004937075365527095449)
  ·
    refine ⟨14836503702806524145321587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19782004937075365527095449 14836503702806524145321587)
    ·
      refine ⟨22254755554209786217982381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14836503702806524145321587 22254755554209786217982381)
      ·
        refine ⟨8345533332828669831743393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22254755554209786217982381 8345533332828669831743393)
        ·
          refine ⟨6259149999621502373807545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8345533332828669831743393 6259149999621502373807545)
          ·
            refine ⟨4694362499716126780355659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6259149999621502373807545 4694362499716126780355659)
            ·
              refine ⟨7041543749574190170533489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4694362499716126780355659 7041543749574190170533489)
              ·
                refine ⟨5281157812180642627900117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7041543749574190170533489 5281157812180642627900117)
                ·
                  refine ⟨123777136222983811591409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5281157812180642627900117 123777136222983811591409)
                  ·
                    rfl

theorem cell22_1084748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 1, 2, 7].length) (baseStart_1084748 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1084748 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1084748 prefixEnd_1084748 := by exact prefixLift 1084748
  have htrace : WordTrace (prefixWord ++ tailWord_1084748) baseStart_1084748 baseEnd_1084748 := by
    simpa [prefixWord, tailWord_1084748, baseEnd_1084748] using wordTrace_append hprefix tailTrace_1084748
  have hstable : (prefixWord ++ tailWord_1084748).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1084748).length < 2 ^ (prefixWord ++ tailWord_1084748).sum := by decide
  have hdescent : baseEnd_1084748 < baseStart_1084748 := by decide
  rcases family_descends (prefixWord ++ tailWord_1084748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1084793 : List Nat := [1, 2, 1, 3, 2, 1, 2, 4, 6]
def baseStart_1084793 : Nat := 118140960795 + 1084793 * 2 ^ 59
def prefixEnd_1084793 : Nat := 4983230072969 + 3 ^ 40 * 1084793 * 2
def baseEnd_1084793 : Nat := 123782271029528772466363

theorem tailTrace_1084793 : CollatzResearch.WordTrace tailWord_1084793 prefixEnd_1084793 123782271029528772466363 := by
  unfold tailWord_1084793
  simp only [CollatzResearch.WordTrace]
  refine ⟨39565651158987703739579033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26377100772658469159719355 39565651158987703739579033)
  ·
    refine ⟨29674238369240777804684275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39565651158987703739579033 29674238369240777804684275)
    ·
      refine ⟨44511357553861166707026413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29674238369240777804684275 44511357553861166707026413)
      ·
        refine ⟨16691759082697937515134905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44511357553861166707026413 16691759082697937515134905)
        ·
          refine ⟨12518819312023453136351179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16691759082697937515134905 12518819312023453136351179)
          ·
            refine ⟨18778228968035179704526769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12518819312023453136351179 18778228968035179704526769)
            ·
              refine ⟨14083671726026384778395077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18778228968035179704526769 14083671726026384778395077)
              ·
                refine ⟨2640688448629947145949077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14083671726026384778395077 2640688448629947145949077)
                ·
                  refine ⟨123782271029528772466363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2640688448629947145949077 123782271029528772466363)
                  ·
                    rfl

theorem cell22_1084793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 4, 6].length) (baseStart_1084793 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1084793 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1084793 prefixEnd_1084793 := by exact prefixLift 1084793
  have htrace : WordTrace (prefixWord ++ tailWord_1084793) baseStart_1084793 baseEnd_1084793 := by
    simpa [prefixWord, tailWord_1084793, baseEnd_1084793] using wordTrace_append hprefix tailTrace_1084793
  have hstable : (prefixWord ++ tailWord_1084793).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1084793).length < 2 ^ (prefixWord ++ tailWord_1084793).sum := by decide
  have hdescent : baseEnd_1084793 < baseStart_1084793 := by decide
  rcases family_descends (prefixWord ++ tailWord_1084793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1084812 : List Nat := [2, 2, 1, 2, 1, 3, 5, 1, 1, 4]
def baseStart_1084812 : Nat := 118140960795 + 1084812 * 2 ^ 59
def prefixEnd_1084812 : Nat := 4983230072969 + 3 ^ 40 * 1084812 * 2
def baseEnd_1084812 : Nat := 371353317176876601174031

theorem tailTrace_1084812 : CollatzResearch.WordTrace tailWord_1084812 prefixEnd_1084812 371353317176876601174031 := by
  unfold tailWord_1084812
  simp only [CollatzResearch.WordTrace]
  refine ⟨19783172072959434992260345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26377562763945913323013793 19783172072959434992260345)
  ·
    refine ⟨14837379054719576244195259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19783172072959434992260345 14837379054719576244195259)
    ·
      refine ⟨22256068582079364366292889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14837379054719576244195259 22256068582079364366292889)
      ·
        refine ⟨16692051436559523274719667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22256068582079364366292889 16692051436559523274719667)
        ·
          refine ⟨25038077154839284912079501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16692051436559523274719667 25038077154839284912079501)
          ·
            refine ⟨9389278933064731842029813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25038077154839284912079501 9389278933064731842029813)
            ·
              refine ⟨880244899974818610190295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9389278933064731842029813 880244899974818610190295)
              ·
                refine ⟨1320367349962227915285443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 880244899974818610190295 1320367349962227915285443)
                ·
                  refine ⟨1980551024943341872928165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1320367349962227915285443 1980551024943341872928165)
                  ·
                    refine ⟨371353317176876601174031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1980551024943341872928165 371353317176876601174031)
                    ·
                      rfl

theorem cell22_1084812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 5, 1, 1, 4].length) (baseStart_1084812 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1084812 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1084812 prefixEnd_1084812 := by exact prefixLift 1084812
  have htrace : WordTrace (prefixWord ++ tailWord_1084812) baseStart_1084812 baseEnd_1084812 := by
    simpa [prefixWord, tailWord_1084812, baseEnd_1084812] using wordTrace_append hprefix tailTrace_1084812
  have hstable : (prefixWord ++ tailWord_1084812).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1084812).length < 2 ^ (prefixWord ++ tailWord_1084812).sum := by decide
  have hdescent : baseEnd_1084812 < baseStart_1084812 := by decide
  rcases family_descends (prefixWord ++ tailWord_1084812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1084823 : List Nat := [1, 1, 3, 3, 1, 1, 1, 2, 3, 6]
def baseStart_1084823 : Nat := 118140960795 + 1084823 * 2 ^ 59
def prefixEnd_1084823 : Nat := 4983230072969 + 3 ^ 40 * 1084823 * 2
def baseEnd_1084823 : Nat := 371357082701676239148997

theorem tailTrace_1084823 : CollatzResearch.WordTrace tailWord_1084823 prefixEnd_1084823 371357082701676239148997 := by
  unfold tailWord_1084823
  simp only [CollatzResearch.WordTrace]
  refine ⟨39566745348879018863171123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26377830232586012575447415 39566745348879018863171123)
  ·
    refine ⟨59350118023318528294756685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39566745348879018863171123 59350118023318528294756685)
    ·
      refine ⟨22256294258744448110533757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59350118023318528294756685 22256294258744448110533757)
      ·
        refine ⟨8346110347029168041450159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22256294258744448110533757 8346110347029168041450159)
        ·
          refine ⟨12519165520543752062175239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8346110347029168041450159 12519165520543752062175239)
          ·
            refine ⟨18778748280815628093262859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12519165520543752062175239 18778748280815628093262859)
            ·
              refine ⟨28168122421223442139894289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18778748280815628093262859 28168122421223442139894289)
              ·
                refine ⟨21126091815917581604920717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28168122421223442139894289 21126091815917581604920717)
                ·
                  refine ⟨7922284430969093101845269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21126091815917581604920717 7922284430969093101845269)
                  ·
                    refine ⟨371357082701676239148997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7922284430969093101845269 371357082701676239148997)
                    ·
                      rfl

theorem cell22_1084823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 2, 3, 6].length) (baseStart_1084823 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1084823 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1084823 prefixEnd_1084823 := by exact prefixLift 1084823
  have htrace : WordTrace (prefixWord ++ tailWord_1084823) baseStart_1084823 baseEnd_1084823 := by
    simpa [prefixWord, tailWord_1084823, baseEnd_1084823] using wordTrace_append hprefix tailTrace_1084823
  have hstable : (prefixWord ++ tailWord_1084823).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1084823).length < 2 ^ (prefixWord ++ tailWord_1084823).sum := by decide
  have hdescent : baseEnd_1084823 < baseStart_1084823 := by decide
  rcases family_descends (prefixWord ++ tailWord_1084823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1084855 : List Nat := [1, 1, 3, 1, 3, 2, 5, 6]
def baseStart_1084855 : Nat := 118140960795 + 1084855 * 2 ^ 59
def prefixEnd_1084855 : Nat := 4983230072969 + 3 ^ 40 * 1084855 * 2
def baseEnd_1084855 : Nat := 41263115217293202483211

theorem tailTrace_1084855 : CollatzResearch.WordTrace tailWord_1084855 prefixEnd_1084855 41263115217293202483211 := by
  unfold tailWord_1084855
  simp only [CollatzResearch.WordTrace]
  refine ⟨39567912484763088328336019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26378608323175392218890679 39567912484763088328336019)
  ·
    refine ⟨59351868727144632492504029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39567912484763088328336019 59351868727144632492504029)
    ·
      refine ⟨22256950772679237184689011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59351868727144632492504029 22256950772679237184689011)
      ·
        refine ⟨33385426159018855777033517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22256950772679237184689011 33385426159018855777033517)
        ·
          refine ⟨12519534809632070916387569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33385426159018855777033517 12519534809632070916387569)
          ·
            refine ⟨9389651107224053187290677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12519534809632070916387569 9389651107224053187290677)
            ·
              refine ⟨880279791302254986308501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9389651107224053187290677 880279791302254986308501)
              ·
                refine ⟨41263115217293202483211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 880279791302254986308501 41263115217293202483211)
                ·
                  rfl

theorem cell22_1084855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 5, 6].length) (baseStart_1084855 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1084855 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1084855 prefixEnd_1084855 := by exact prefixLift 1084855
  have htrace : WordTrace (prefixWord ++ tailWord_1084855) baseStart_1084855 baseEnd_1084855 := by
    simpa [prefixWord, tailWord_1084855, baseEnd_1084855] using wordTrace_append hprefix tailTrace_1084855
  have hstable : (prefixWord ++ tailWord_1084855).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1084855).length < 2 ^ (prefixWord ++ tailWord_1084855).sum := by decide
  have hdescent : baseEnd_1084855 < baseStart_1084855 := by decide
  rcases family_descends (prefixWord ++ tailWord_1084855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1084900 : List Nat := [2, 3, 1, 1, 1, 1, 1, 7, 5]
def baseStart_1084900 : Nat := 118140960795 + 1084900 * 2 ^ 59
def prefixEnd_1084900 : Nat := 4983230072969 + 3 ^ 40 * 1084900 * 2
def baseEnd_1084900 : Nat := 123794480458424568324587

theorem tailTrace_1084900 : CollatzResearch.WordTrace tailWord_1084900 prefixEnd_1084900 123794480458424568324587 := by
  unfold tailWord_1084900
  simp only [CollatzResearch.WordTrace]
  refine ⟨19784776884800030506862077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26379702513066707342482769 19784776884800030506862077)
  ·
    refine ⟨7419291331800011440073279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19784776884800030506862077 7419291331800011440073279)
    ·
      refine ⟨11128936997700017160109919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7419291331800011440073279 11128936997700017160109919)
      ·
        refine ⟨16693405496550025740164879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11128936997700017160109919 16693405496550025740164879)
        ·
          refine ⟨25040108244825038610247319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16693405496550025740164879 25040108244825038610247319)
          ·
            refine ⟨37560162367237557915370979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25040108244825038610247319 37560162367237557915370979)
            ·
              refine ⟨56340243550856336873056469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37560162367237557915370979 56340243550856336873056469)
              ·
                refine ⟨1320474458223195395462261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 56340243550856336873056469 1320474458223195395462261)
                ·
                  refine ⟨123794480458424568324587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1320474458223195395462261 123794480458424568324587)
                  ·
                    rfl

theorem cell22_1084900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 7, 5].length) (baseStart_1084900 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1084900 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1084900 prefixEnd_1084900 := by exact prefixLift 1084900
  have htrace : WordTrace (prefixWord ++ tailWord_1084900) baseStart_1084900 baseEnd_1084900 := by
    simpa [prefixWord, tailWord_1084900, baseEnd_1084900] using wordTrace_append hprefix tailTrace_1084900
  have hstable : (prefixWord ++ tailWord_1084900).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1084900).length < 2 ^ (prefixWord ++ tailWord_1084900).sum := by decide
  have hdescent : baseEnd_1084900 < baseStart_1084900 := by decide
  rcases family_descends (prefixWord ++ tailWord_1084900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1084917 : List Nat := [1, 3, 5, 1, 1, 1, 1, 2, 7]
def baseStart_1084917 : Nat := 118140960795 + 1084917 * 2 ^ 59
def prefixEnd_1084917 : Nat := 4983230072969 + 3 ^ 40 * 1084917 * 2
def baseEnd_1084917 : Nat := 123796420274230442432903

theorem tailTrace_1084917 : CollatzResearch.WordTrace tailWord_1084917 prefixEnd_1084917 123796420274230442432903 := by
  unfold tailWord_1084917
  simp only [CollatzResearch.WordTrace]
  refine ⟨39570173810538472917093005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26380115873692315278062003 39570173810538472917093005)
  ·
    refine ⟨14838815178951927343909877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39570173810538472917093005 14838815178951927343909877)
    ·
      refine ⟨1391138923026743188491551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 14838815178951927343909877 1391138923026743188491551)
      ·
        refine ⟨2086708384540114782737327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1391138923026743188491551 2086708384540114782737327)
        ·
          refine ⟨3130062576810172174105991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2086708384540114782737327 3130062576810172174105991)
          ·
            refine ⟨4695093865215258261158987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3130062576810172174105991 4695093865215258261158987)
            ·
              refine ⟨7042640797822887391738481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4695093865215258261158987 7042640797822887391738481)
              ·
                refine ⟨5281980598367165543803861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7042640797822887391738481 5281980598367165543803861)
                ·
                  refine ⟨123796420274230442432903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5281980598367165543803861 123796420274230442432903)
                  ·
                    rfl

theorem cell22_1084917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 1, 2, 7].length) (baseStart_1084917 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1084917 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1084917 prefixEnd_1084917 := by exact prefixLift 1084917
  have htrace : WordTrace (prefixWord ++ tailWord_1084917) baseStart_1084917 baseEnd_1084917 := by
    simpa [prefixWord, tailWord_1084917, baseEnd_1084917] using wordTrace_append hprefix tailTrace_1084917
  have hstable : (prefixWord ++ tailWord_1084917).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1084917).length < 2 ^ (prefixWord ++ tailWord_1084917).sum := by decide
  have hdescent : baseEnd_1084917 < baseStart_1084917 := by decide
  rcases family_descends (prefixWord ++ tailWord_1084917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1084990 : List Nat := [4, 2, 1, 15]
def baseStart_1084990 : Nat := 118140960795 + 1084990 * 2 ^ 59
def prefixEnd_1084990 : Nat := 4983230072969 + 3 ^ 40 * 1084990 * 2
def baseEnd_1084990 : Nat := 509484568195532880965

theorem tailTrace_1084990 : CollatzResearch.WordTrace tailWord_1084990 prefixEnd_1084990 509484568195532880965 := by
  unfold tailWord_1084990
  simp only [CollatzResearch.WordTrace]
  refine ⟨4946604542409250798062553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26381890892849337589666949 4946604542409250798062553)
  ·
    refine ⟨3709953406806938098546915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4946604542409250798062553 3709953406806938098546915)
    ·
      refine ⟨5564930110210407147820373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3709953406806938098546915 5564930110210407147820373)
      ·
        refine ⟨509484568195532880965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 15 5564930110210407147820373 509484568195532880965)
        ·
          rfl

theorem cell22_1084990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 15].length) (baseStart_1084990 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1084990 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1084990 prefixEnd_1084990 := by exact prefixLift 1084990
  have htrace : WordTrace (prefixWord ++ tailWord_1084990) baseStart_1084990 baseEnd_1084990 := by
    simpa [prefixWord, tailWord_1084990, baseEnd_1084990] using wordTrace_append hprefix tailTrace_1084990
  have hstable : (prefixWord ++ tailWord_1084990).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1084990).length < 2 ^ (prefixWord ++ tailWord_1084990).sum := by decide
  have hdescent : baseEnd_1084990 < baseStart_1084990 := by decide
  rcases family_descends (prefixWord ++ tailWord_1084990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1085114 : List Nat := [3, 1, 1, 1, 2, 6, 1, 1, 6]
def baseStart_1085114 : Nat := 118140960795 + 1085114 * 2 ^ 59
def prefixEnd_1085114 : Nat := 4983230072969 + 3 ^ 40 * 1085114 * 2
def baseEnd_1085114 : Nat := 123818899316216160041035

theorem tailTrace_1085114 : CollatzResearch.WordTrace tailWord_1085114 prefixEnd_1085114 123818899316216160041035 := by
  unfold tailWord_1085114
  simp only [CollatzResearch.WordTrace]
  refine ⟨9894339747706193890503599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26384905993883183708009597 9894339747706193890503599)
  ·
    refine ⟨14841509621559290835755399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9894339747706193890503599 14841509621559290835755399)
    ·
      refine ⟨22262264432338936253633099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14841509621559290835755399 22262264432338936253633099)
      ·
        refine ⟨33393396648508404380449649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22262264432338936253633099 33393396648508404380449649)
        ·
          refine ⟨25045047486381303285337237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33393396648508404380449649 25045047486381303285337237)
          ·
            refine ⟨1173986600924123591500183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 25045047486381303285337237 1173986600924123591500183)
            ·
              refine ⟨1760979901386185387250275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1173986600924123591500183 1760979901386185387250275)
              ·
                refine ⟨2641469852079278080875413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1760979901386185387250275 2641469852079278080875413)
                ·
                  refine ⟨123818899316216160041035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2641469852079278080875413 123818899316216160041035)
                  ·
                    rfl

theorem cell22_1085114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 6, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 6, 1, 1, 6].length) (baseStart_1085114 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1085114 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1085114 prefixEnd_1085114 := by exact prefixLift 1085114
  have htrace : WordTrace (prefixWord ++ tailWord_1085114) baseStart_1085114 baseEnd_1085114 := by
    simpa [prefixWord, tailWord_1085114, baseEnd_1085114] using wordTrace_append hprefix tailTrace_1085114
  have hstable : (prefixWord ++ tailWord_1085114).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1085114).length < 2 ^ (prefixWord ++ tailWord_1085114).sum := by decide
  have hdescent : baseEnd_1085114 < baseStart_1085114 := by decide
  rcases family_descends (prefixWord ++ tailWord_1085114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1085127 : List Nat := [1, 1, 4, 1, 1, 1, 3, 2, 4, 4]
def baseStart_1085127 : Nat := 118140960795 + 1085127 * 2 ^ 59
def prefixEnd_1085127 : Nat := 4983230072969 + 3 ^ 40 * 1085127 * 2
def baseEnd_1085127 : Nat := 371461148114320779548065

theorem tailTrace_1085127 : CollatzResearch.WordTrace tailWord_1085127 prefixEnd_1085127 371461148114320779548065 := by
  unfold tailWord_1085127
  simp only [CollatzResearch.WordTrace]
  refine ⟨39577833139777678782237635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26385222093185119188158423 39577833139777678782237635)
  ·
    refine ⟨59366749709666518173356453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39577833139777678782237635 59366749709666518173356453)
    ·
      refine ⟨11131265570562472157504335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 59366749709666518173356453 11131265570562472157504335)
      ·
        refine ⟨16696898355843708236256503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11131265570562472157504335 16696898355843708236256503)
        ·
          refine ⟨25045347533765562354384755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16696898355843708236256503 25045347533765562354384755)
          ·
            refine ⟨37568021300648343531577133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25045347533765562354384755 37568021300648343531577133)
            ·
              refine ⟨14088007987743128824341425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37568021300648343531577133 14088007987743128824341425)
              ·
                refine ⟨10566005990807346618256069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14088007987743128824341425 10566005990807346618256069)
                ·
                  refine ⟨1981126123276377490923013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10566005990807346618256069 1981126123276377490923013)
                  ·
                    refine ⟨371461148114320779548065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1981126123276377490923013 371461148114320779548065)
                    ·
                      rfl

theorem cell22_1085127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 2, 4, 4].length) (baseStart_1085127 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1085127 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1085127 prefixEnd_1085127 := by exact prefixLift 1085127
  have htrace : WordTrace (prefixWord ++ tailWord_1085127) baseStart_1085127 baseEnd_1085127 := by
    simpa [prefixWord, tailWord_1085127, baseEnd_1085127] using wordTrace_append hprefix tailTrace_1085127
  have hstable : (prefixWord ++ tailWord_1085127).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1085127).length < 2 ^ (prefixWord ++ tailWord_1085127).sum := by decide
  have hdescent : baseEnd_1085127 < baseStart_1085127 := by decide
  rcases family_descends (prefixWord ++ tailWord_1085127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1085133 : List Nat := [1, 6, 2, 1, 1, 1, 3, 2, 1, 4]
def baseStart_1085133 : Nat := 118140960795 + 1085133 * 2 ^ 59
def prefixEnd_1085133 : Nat := 4983230072969 + 3 ^ 40 * 1085133 * 2
def baseEnd_1085133 : Nat := 371463202036938763898047

theorem tailTrace_1085133 : CollatzResearch.WordTrace tailWord_1085133 prefixEnd_1085133 371463202036938763898047 := by
  unfold tailWord_1085133
  simp only [CollatzResearch.WordTrace]
  refine ⟨39578051977755941806956053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26385367985170627871304035 39578051977755941806956053)
  ·
    refine ⟨1855221186457309772201065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 39578051977755941806956053 1855221186457309772201065)
    ·
      refine ⟨1391415889842982329150799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1855221186457309772201065 1391415889842982329150799)
      ·
        refine ⟨2087123834764473493726199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1391415889842982329150799 2087123834764473493726199)
        ·
          refine ⟨3130685752146710240589299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2087123834764473493726199 3130685752146710240589299)
          ·
            refine ⟨4696028628220065360883949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3130685752146710240589299 4696028628220065360883949)
            ·
              refine ⟨1761010735582524510331481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4696028628220065360883949 1761010735582524510331481)
              ·
                refine ⟨1320758051686893382748611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1761010735582524510331481 1320758051686893382748611)
                ·
                  refine ⟨1981137077530340074122917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1320758051686893382748611 1981137077530340074122917)
                  ·
                    refine ⟨371463202036938763898047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1981137077530340074122917 371463202036938763898047)
                    ·
                      rfl

theorem cell22_1085133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 3, 2, 1, 4].length) (baseStart_1085133 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1085133 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1085133 prefixEnd_1085133 := by exact prefixLift 1085133
  have htrace : WordTrace (prefixWord ++ tailWord_1085133) baseStart_1085133 baseEnd_1085133 := by
    simpa [prefixWord, tailWord_1085133, baseEnd_1085133] using wordTrace_append hprefix tailTrace_1085133
  have hstable : (prefixWord ++ tailWord_1085133).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1085133).length < 2 ^ (prefixWord ++ tailWord_1085133).sum := by decide
  have hdescent : baseEnd_1085133 < baseStart_1085133 := by decide
  rcases family_descends (prefixWord ++ tailWord_1085133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1085144 : List Nat := [2, 1, 2, 2, 3, 1, 4, 1, 2, 4]
def baseStart_1085144 : Nat := 118140960795 + 1085144 * 2 ^ 59
def prefixEnd_1085144 : Nat := 4983230072969 + 3 ^ 40 * 1085144 * 2
def baseEnd_1085144 : Nat := 371466967561738401873013

theorem tailTrace_1085144 : CollatzResearch.WordTrace tailWord_1085144 prefixEnd_1085144 371466967561738401873013 := by
  unfold tailWord_1085144
  simp only [CollatzResearch.WordTrace]
  refine ⟨19789226590358045342803243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26385635453810727123737657 19789226590358045342803243)
  ·
    refine ⟨29683839885537068014204865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19789226590358045342803243 29683839885537068014204865)
    ·
      refine ⟨22262879914152801010653649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29683839885537068014204865 22262879914152801010653649)
      ·
        refine ⟨16697159935614600757990237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22262879914152801010653649 16697159935614600757990237)
        ·
          refine ⟨6261434975855475284246339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16697159935614600757990237 6261434975855475284246339)
          ·
            refine ⟨9392152463783212926369509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6261434975855475284246339 9392152463783212926369509)
            ·
              refine ⟨1761028586959352423694283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9392152463783212926369509 1761028586959352423694283)
              ·
                refine ⟨2641542880439028635541425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1761028586959352423694283 2641542880439028635541425)
                ·
                  refine ⟨1981157160329271476656069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2641542880439028635541425 1981157160329271476656069)
                  ·
                    refine ⟨371466967561738401873013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1981157160329271476656069 371466967561738401873013)
                    ·
                      rfl

theorem cell22_1085144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 4, 1, 2, 4].length) (baseStart_1085144 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1085144 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1085144 prefixEnd_1085144 := by exact prefixLift 1085144
  have htrace : WordTrace (prefixWord ++ tailWord_1085144) baseStart_1085144 baseEnd_1085144 := by
    simpa [prefixWord, tailWord_1085144, baseEnd_1085144] using wordTrace_append hprefix tailTrace_1085144
  have hstable : (prefixWord ++ tailWord_1085144).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1085144).length < 2 ^ (prefixWord ++ tailWord_1085144).sum := by decide
  have hdescent : baseEnd_1085144 < baseStart_1085144 := by decide
  rcases family_descends (prefixWord ++ tailWord_1085144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1085159 : List Nat := [1, 1, 5, 4, 1, 10]
def baseStart_1085159 : Nat := 118140960795 + 1085159 * 2 ^ 59
def prefixEnd_1085159 : Nat := 4983230072969 + 3 ^ 40 * 1085159 * 2
def baseEnd_1085159 : Nat := 4586075337880041515407

theorem tailTrace_1085159 : CollatzResearch.WordTrace tailWord_1085159 prefixEnd_1085159 4586075337880041515407 := by
  unfold tailWord_1085159
  simp only [CollatzResearch.WordTrace]
  refine ⟨39579000275661748247402531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26386000183774498831601687 39579000275661748247402531)
  ·
    refine ⟨59368500413492622371103797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39579000275661748247402531 59368500413492622371103797)
    ·
      refine ⟨5565796913764933347290981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 59368500413492622371103797 5565796913764933347290981)
      ·
        refine ⟨1043586921330925002617059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5565796913764933347290981 1043586921330925002617059)
        ·
          refine ⟨1565380381996387503925589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1043586921330925002617059 1565380381996387503925589)
          ·
            refine ⟨4586075337880041515407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 1565380381996387503925589 4586075337880041515407)
            ·
              rfl

theorem cell22_1085159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 10].length) (baseStart_1085159 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1085159 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1085159 prefixEnd_1085159 := by exact prefixLift 1085159
  have htrace : WordTrace (prefixWord ++ tailWord_1085159) baseStart_1085159 baseEnd_1085159 := by
    simpa [prefixWord, tailWord_1085159, baseEnd_1085159] using wordTrace_append hprefix tailTrace_1085159
  have hstable : (prefixWord ++ tailWord_1085159).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1085159).length < 2 ^ (prefixWord ++ tailWord_1085159).sum := by decide
  have hdescent : baseEnd_1085159 < baseStart_1085159 := by decide
  rcases family_descends (prefixWord ++ tailWord_1085159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1085214 : List Nat := [4, 3, 2, 2, 2, 1, 1, 2, 2, 3]
def baseStart_1085214 : Nat := 118140960795 + 1085214 * 2 ^ 59
def prefixEnd_1085214 : Nat := 4983230072969 + 3 ^ 40 * 1085214 * 2
def baseEnd_1085214 : Nat := 371490929992281552622799

theorem tailTrace_1085214 : CollatzResearch.WordTrace tailWord_1085214 prefixEnd_1085214 371490929992281552622799 := by
  unfold tailWord_1085214
  simp only [CollatzResearch.WordTrace]
  refine ⟨4947625786307811580081837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26387337526974995093769797 4947625786307811580081837)
  ·
    refine ⟨1855359669865429342530689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4947625786307811580081837 1855359669865429342530689)
    ·
      refine ⟨1391519752399072006898017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1855359669865429342530689 1391519752399072006898017)
      ·
        refine ⟨1043639814299304005173513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1391519752399072006898017 1043639814299304005173513)
        ·
          refine ⟨782729860724478003880135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1043639814299304005173513 782729860724478003880135)
          ·
            refine ⟨1174094791086717005820203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 782729860724478003880135 1174094791086717005820203)
            ·
              refine ⟨1761142186630075508730305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1174094791086717005820203 1761142186630075508730305)
              ·
                refine ⟨1320856639972556631547729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1761142186630075508730305 1320856639972556631547729)
                ·
                  refine ⟨990642479979417473660797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1320856639972556631547729 990642479979417473660797)
                  ·
                    refine ⟨371490929992281552622799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 990642479979417473660797 371490929992281552622799)
                    ·
                      rfl

theorem cell22_1085214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 2, 1, 1, 2, 2, 3].length) (baseStart_1085214 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1085214 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1085214 prefixEnd_1085214 := by exact prefixLift 1085214
  have htrace : WordTrace (prefixWord ++ tailWord_1085214) baseStart_1085214 baseEnd_1085214 := by
    simpa [prefixWord, tailWord_1085214, baseEnd_1085214] using wordTrace_append hprefix tailTrace_1085214
  have hstable : (prefixWord ++ tailWord_1085214).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1085214).length < 2 ^ (prefixWord ++ tailWord_1085214).sum := by decide
  have hdescent : baseEnd_1085214 < baseStart_1085214 := by decide
  rcases family_descends (prefixWord ++ tailWord_1085214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1085221 : List Nat := [1, 3, 1, 2, 3, 4, 1, 2, 5]
def baseStart_1085221 : Nat := 118140960795 + 1085221 * 2 ^ 59
def prefixEnd_1085221 : Nat := 4983230072969 + 3 ^ 40 * 1085221 * 2
def baseEnd_1085221 : Nat := 123831108745111955899259

theorem tailTrace_1085221 : CollatzResearch.WordTrace tailWord_1085221 prefixEnd_1085221 123831108745111955899259 := by
  unfold tailWord_1085221
  simp only [CollatzResearch.WordTrace]
  refine ⟨39581261601437132836159517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26387507734291421890773011 39581261601437132836159517)
  ·
    refine ⟨14842973100538924813559819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39581261601437132836159517 14842973100538924813559819)
    ·
      refine ⟨22264459650808387220339729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14842973100538924813559819 22264459650808387220339729)
      ·
        refine ⟨16698344738106290415254797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22264459650808387220339729 16698344738106290415254797)
        ·
          refine ⟨6261879276789858905720549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16698344738106290415254797 6261879276789858905720549)
          ·
            refine ⟨1174102364398098544822603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6261879276789858905720549 1174102364398098544822603)
            ·
              refine ⟨1761153546597147817233905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1174102364398098544822603 1761153546597147817233905)
              ·
                refine ⟨1320865159947860862925429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1761153546597147817233905 1320865159947860862925429)
                ·
                  refine ⟨123831108745111955899259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1320865159947860862925429 123831108745111955899259)
                  ·
                    rfl

theorem cell22_1085221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 4, 1, 2, 5].length) (baseStart_1085221 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1085221 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1085221 prefixEnd_1085221 := by exact prefixLift 1085221
  have htrace : WordTrace (prefixWord ++ tailWord_1085221) baseStart_1085221 baseEnd_1085221 := by
    simpa [prefixWord, tailWord_1085221, baseEnd_1085221] using wordTrace_append hprefix tailTrace_1085221
  have hstable : (prefixWord ++ tailWord_1085221).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1085221).length < 2 ^ (prefixWord ++ tailWord_1085221).sum := by decide
  have hdescent : baseEnd_1085221 < baseStart_1085221 := by decide
  rcases family_descends (prefixWord ++ tailWord_1085221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1085236 : List Nat := [2, 5, 1, 1, 2, 1, 2, 1, 2, 5]
def baseStart_1085236 : Nat := 118140960795 + 1085236 * 2 ^ 59
def prefixEnd_1085236 : Nat := 4983230072969 + 3 ^ 40 * 1085236 * 2
def baseEnd_1085236 : Nat := 371498461041880828572731

theorem tailTrace_1085236 : CollatzResearch.WordTrace tailWord_1085236 prefixEnd_1085236 371498461041880828572731 := by
  unfold tailWord_1085236
  simp only [CollatzResearch.WordTrace]
  refine ⟨19790904348191395198977781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26387872464255193598637041 19790904348191395198977781)
  ·
    refine ⟨1855397282642943299904167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 19790904348191395198977781 1855397282642943299904167)
    ·
      refine ⟨2783095923964414949856251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1855397282642943299904167 2783095923964414949856251)
      ·
        refine ⟨4174643885946622424784377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2783095923964414949856251 4174643885946622424784377)
        ·
          refine ⟨3130982914459966818588283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4174643885946622424784377 3130982914459966818588283)
          ·
            refine ⟨4696474371689950227882425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3130982914459966818588283 4696474371689950227882425)
            ·
              refine ⟨3522355778767462670911819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4696474371689950227882425 3522355778767462670911819)
              ·
                refine ⟨5283533668151194006367729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3522355778767462670911819 5283533668151194006367729)
                ·
                  refine ⟨3962650251113395504775797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5283533668151194006367729 3962650251113395504775797)
                  ·
                    refine ⟨371498461041880828572731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3962650251113395504775797 371498461041880828572731)
                    ·
                      rfl

theorem cell22_1085236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 2, 1, 2, 5].length) (baseStart_1085236 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1085236 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1085236 prefixEnd_1085236 := by exact prefixLift 1085236
  have htrace : WordTrace (prefixWord ++ tailWord_1085236) baseStart_1085236 baseEnd_1085236 := by
    simpa [prefixWord, tailWord_1085236, baseEnd_1085236] using wordTrace_append hprefix tailTrace_1085236
  have hstable : (prefixWord ++ tailWord_1085236).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1085236).length < 2 ^ (prefixWord ++ tailWord_1085236).sum := by decide
  have hdescent : baseEnd_1085236 < baseStart_1085236 := by decide
  rcases family_descends (prefixWord ++ tailWord_1085236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1085251 : List Nat := [1, 1, 1, 3, 1, 6, 2, 2, 1, 4]
def baseStart_1085251 : Nat := 118140960795 + 1085251 * 2 ^ 59
def prefixEnd_1085251 : Nat := 4983230072969 + 3 ^ 40 * 1085251 * 2
def baseEnd_1085251 : Nat := 371503595848425789447685

theorem tailTrace_1085251 : CollatzResearch.WordTrace tailWord_1085251 prefixEnd_1085251 371503595848425789447685 := by
  unfold tailWord_1085251
  simp only [CollatzResearch.WordTrace]
  refine ⟨39582355791328447959751607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26388237194218965306501071 39582355791328447959751607)
  ·
    refine ⟨59373533686992671939627411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39582355791328447959751607 59373533686992671939627411)
    ·
      refine ⟨89060300530489007909441117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59373533686992671939627411 89060300530489007909441117)
      ·
        refine ⟨33397612698933377966040419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 89060300530489007909441117 33397612698933377966040419)
        ·
          refine ⟨50096419048400066949060629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33397612698933377966040419 50096419048400066949060629)
          ·
            refine ⟨2348269642893753138237217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 50096419048400066949060629 2348269642893753138237217)
            ·
              refine ⟨1761202232170314853677913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2348269642893753138237217 1761202232170314853677913)
              ·
                refine ⟨1320901674127736140258435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1761202232170314853677913 1320901674127736140258435)
                ·
                  refine ⟨1981352511191604210387653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1320901674127736140258435 1981352511191604210387653)
                  ·
                    refine ⟨371503595848425789447685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1981352511191604210387653 371503595848425789447685)
                    ·
                      rfl

theorem cell22_1085251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 2, 2, 1, 4].length) (baseStart_1085251 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1085251 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1085251 prefixEnd_1085251 := by exact prefixLift 1085251
  have htrace : WordTrace (prefixWord ++ tailWord_1085251) baseStart_1085251 baseEnd_1085251 := by
    simpa [prefixWord, tailWord_1085251, baseEnd_1085251] using wordTrace_append hprefix tailTrace_1085251
  have hstable : (prefixWord ++ tailWord_1085251).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1085251).length < 2 ^ (prefixWord ++ tailWord_1085251).sum := by decide
  have hdescent : baseEnd_1085251 < baseStart_1085251 := by decide
  rcases family_descends (prefixWord ++ tailWord_1085251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1085279 : List Nat := [1, 1, 2, 3, 1, 4, 1, 1, 4, 4]
def baseStart_1085279 : Nat := 118140960795 + 1085279 * 2 ^ 59
def prefixEnd_1085279 : Nat := 4983230072969 + 3 ^ 40 * 1085279 * 2
def baseEnd_1085279 : Nat := 371513180820643049747599

theorem tailTrace_1085279 : CollatzResearch.WordTrace tailWord_1085279 prefixEnd_1085279 371513180820643049747599 := by
  unfold tailWord_1085279
  simp only [CollatzResearch.WordTrace]
  refine ⟨39583377035227008741770891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26388918023484672494513927 39583377035227008741770891)
  ·
    refine ⟨59375065552840513112656337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39583377035227008741770891 59375065552840513112656337)
    ·
      refine ⟨44531299164630384834492253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59375065552840513112656337 44531299164630384834492253)
      ·
        refine ⟨16699237186736394312934595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44531299164630384834492253 16699237186736394312934595)
        ·
          refine ⟨25048855780104591469401893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16699237186736394312934595 25048855780104591469401893)
          ·
            refine ⟨4696660458769610900512855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25048855780104591469401893 4696660458769610900512855)
            ·
              refine ⟨7044990688154416350769283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4696660458769610900512855 7044990688154416350769283)
              ·
                refine ⟨10567486032231624526153925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7044990688154416350769283 10567486032231624526153925)
                ·
                  refine ⟨1981403631043429598653861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10567486032231624526153925 1981403631043429598653861)
                  ·
                    refine ⟨371513180820643049747599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1981403631043429598653861 371513180820643049747599)
                    ·
                      rfl

theorem cell22_1085279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 1, 1, 4, 4].length) (baseStart_1085279 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1085279 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1085279 prefixEnd_1085279 := by exact prefixLift 1085279
  have htrace : WordTrace (prefixWord ++ tailWord_1085279) baseStart_1085279 baseEnd_1085279 := by
    simpa [prefixWord, tailWord_1085279, baseEnd_1085279] using wordTrace_append hprefix tailTrace_1085279
  have hstable : (prefixWord ++ tailWord_1085279).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1085279).length < 2 ^ (prefixWord ++ tailWord_1085279).sum := by decide
  have hdescent : baseEnd_1085279 < baseStart_1085279 := by decide
  rcases family_descends (prefixWord ++ tailWord_1085279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1085281 : List Nat := [1, 2, 3, 1, 1, 1, 4, 4, 2, 3]
def baseStart_1085281 : Nat := 118140960795 + 1085281 * 2 ^ 59
def prefixEnd_1085281 : Nat := 4983230072969 + 3 ^ 40 * 1085281 * 2
def baseEnd_1085281 : Nat := 371513865461515711197593

theorem tailTrace_1085281 : CollatzResearch.WordTrace tailWord_1085281 prefixEnd_1085281 371513865461515711197593 := by
  unfold tailWord_1085281
  simp only [CollatzResearch.WordTrace]
  refine ⟨39583449981219763083343697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26388966654146508722229131 39583449981219763083343697)
  ·
    refine ⟨29687587485914822312507773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39583449981219763083343697 29687587485914822312507773)
    ·
      refine ⟨11132845307218058367190415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29687587485914822312507773 11132845307218058367190415)
      ·
        refine ⟨16699267960827087550785623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11132845307218058367190415 16699267960827087550785623)
        ·
          refine ⟨25048901941240631326178435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16699267960827087550785623 25048901941240631326178435)
          ·
            refine ⟨37573352911860946989267653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25048901941240631326178435 37573352911860946989267653)
            ·
              refine ⟨7045003670973927560487685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 37573352911860946989267653 7045003670973927560487685)
              ·
                refine ⟨1320938188307611417591441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7045003670973927560487685 1320938188307611417591441)
                ·
                  refine ⟨990703641230708563193581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1320938188307611417591441 990703641230708563193581)
                  ·
                    refine ⟨371513865461515711197593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 990703641230708563193581 371513865461515711197593)
                    ·
                      rfl

theorem cell22_1085281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 4, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 4, 4, 2, 3].length) (baseStart_1085281 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1085281 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1085281 prefixEnd_1085281 := by exact prefixLift 1085281
  have htrace : WordTrace (prefixWord ++ tailWord_1085281) baseStart_1085281 baseEnd_1085281 := by
    simpa [prefixWord, tailWord_1085281, baseEnd_1085281] using wordTrace_append hprefix tailTrace_1085281
  have hstable : (prefixWord ++ tailWord_1085281).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1085281).length < 2 ^ (prefixWord ++ tailWord_1085281).sum := by decide
  have hdescent : baseEnd_1085281 < baseStart_1085281 := by decide
  rcases family_descends (prefixWord ++ tailWord_1085281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1085283 : List Nat := [1, 1, 1, 5, 5, 1, 1, 1, 6]
def baseStart_1085283 : Nat := 118140960795 + 1085283 * 2 ^ 59
def prefixEnd_1085283 : Nat := 4983230072969 + 3 ^ 40 * 1085283 * 2
def baseEnd_1085283 : Nat := 123838183367462790882529

theorem tailTrace_1085283 : CollatzResearch.WordTrace tailWord_1085283 prefixEnd_1085283 123838183367462790882529 := by
  unfold tailWord_1085283
  simp only [CollatzResearch.WordTrace]
  refine ⟨39583522927212517424916503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26389015284808344949944335 39583522927212517424916503)
  ·
    refine ⟨59375284390818776137374755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39583522927212517424916503 59375284390818776137374755)
    ·
      refine ⟨89062926586228164206062133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59375284390818776137374755 89062926586228164206062133)
      ·
        refine ⟨8349649367458890394318325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 89062926586228164206062133 8349649367458890394318325)
        ·
          refine ⟨782779628199270974467343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 8349649367458890394318325 782779628199270974467343)
          ·
            refine ⟨1174169442298906461701015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 782779628199270974467343 1174169442298906461701015)
            ·
              refine ⟨1761254163448359692551523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1174169442298906461701015 1761254163448359692551523)
              ·
                refine ⟨2641881245172539538827285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1761254163448359692551523 2641881245172539538827285)
                ·
                  refine ⟨123838183367462790882529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2641881245172539538827285 123838183367462790882529)
                  ·
                    rfl

theorem cell22_1085283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 5, 1, 1, 1, 6].length) (baseStart_1085283 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1085283 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1085283 prefixEnd_1085283 := by exact prefixLift 1085283
  have htrace : WordTrace (prefixWord ++ tailWord_1085283) baseStart_1085283 baseEnd_1085283 := by
    simpa [prefixWord, tailWord_1085283, baseEnd_1085283] using wordTrace_append hprefix tailTrace_1085283
  have hstable : (prefixWord ++ tailWord_1085283).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1085283).length < 2 ^ (prefixWord ++ tailWord_1085283).sum := by decide
  have hdescent : baseEnd_1085283 < baseStart_1085283 := by decide
  rcases family_descends (prefixWord ++ tailWord_1085283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1085302 : List Nat := [5, 1, 1, 3, 3, 1, 1, 2, 1, 4]
def baseStart_1085302 : Nat := 118140960795 + 1085302 * 2 ^ 59
def prefixEnd_1085302 : Nat := 4983230072969 + 3 ^ 40 * 1085302 * 2
def baseEnd_1085302 : Nat := 371521054190678656422529

theorem tailTrace_1085302 : CollatzResearch.WordTrace tailWord_1085302 prefixEnd_1085302 371521054190678656422529 := by
  unfold tailWord_1085302
  simp only [CollatzResearch.WordTrace]
  refine ⟨2474013494633980229366135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 26389477276095789113238773 2474013494633980229366135)
  ·
    refine ⟨3711020241950970344049203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2474013494633980229366135 3711020241950970344049203)
    ·
      refine ⟨5566530362926455516073805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3711020241950970344049203 5566530362926455516073805)
      ·
        refine ⟨2087448886097420818527677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5566530362926455516073805 2087448886097420818527677)
        ·
          refine ⟨782793332286532806947879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2087448886097420818527677 782793332286532806947879)
          ·
            refine ⟨1174189998429799210421819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 782793332286532806947879 1174189998429799210421819)
            ·
              refine ⟨1761284997644698815632729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1174189998429799210421819 1761284997644698815632729)
              ·
                refine ⟨1320963748233524111724547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1761284997644698815632729 1320963748233524111724547)
                ·
                  refine ⟨1981445622350286167586821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1320963748233524111724547 1981445622350286167586821)
                  ·
                    refine ⟨371521054190678656422529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1981445622350286167586821 371521054190678656422529)
                    ·
                      rfl

theorem cell22_1085302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 3, 1, 1, 2, 1, 4].length) (baseStart_1085302 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1085302 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1085302 prefixEnd_1085302 := by exact prefixLift 1085302
  have htrace : WordTrace (prefixWord ++ tailWord_1085302) baseStart_1085302 baseEnd_1085302 := by
    simpa [prefixWord, tailWord_1085302, baseEnd_1085302] using wordTrace_append hprefix tailTrace_1085302
  have hstable : (prefixWord ++ tailWord_1085302).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1085302).length < 2 ^ (prefixWord ++ tailWord_1085302).sum := by decide
  have hdescent : baseEnd_1085302 < baseStart_1085302 := by decide
  rcases family_descends (prefixWord ++ tailWord_1085302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1085463 : List Nat := [1, 1, 3, 5, 2, 1, 2, 7]
def baseStart_1085463 : Nat := 118140960795 + 1085463 * 2 ^ 59
def prefixEnd_1085463 : Nat := 4983230072969 + 3 ^ 40 * 1085463 * 2
def baseEnd_1085463 : Nat := 41286240864547544794115

theorem tailTrace_1085463 : CollatzResearch.WordTrace tailWord_1085463 prefixEnd_1085463 41286240864547544794115 := by
  unfold tailWord_1085463
  simp only [CollatzResearch.WordTrace]
  refine ⟨39590088066560408166469043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26393392044373605444312695 39590088066560408166469043)
  ·
    refine ⟨59385132099840612249703565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39590088066560408166469043 59385132099840612249703565)
    ·
      refine ⟨22269424537440229593638837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59385132099840612249703565 22269424537440229593638837)
      ·
        refine ⟨2087758550385021524403641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 22269424537440229593638837 2087758550385021524403641)
        ·
          refine ⟨1565818912788766143302731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2087758550385021524403641 1565818912788766143302731)
          ·
            refine ⟨2348728369183149214954097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1565818912788766143302731 2348728369183149214954097)
            ·
              refine ⟨1761546276887361911215573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2348728369183149214954097 1761546276887361911215573)
              ·
                refine ⟨41286240864547544794115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1761546276887361911215573 41286240864547544794115)
                ·
                  rfl

theorem cell22_1085463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 2, 7].length) (baseStart_1085463 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1085463 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1085463 prefixEnd_1085463 := by exact prefixLift 1085463
  have htrace : WordTrace (prefixWord ++ tailWord_1085463) baseStart_1085463 baseEnd_1085463 := by
    simpa [prefixWord, tailWord_1085463, baseEnd_1085463] using wordTrace_append hprefix tailTrace_1085463
  have hstable : (prefixWord ++ tailWord_1085463).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1085463).length < 2 ^ (prefixWord ++ tailWord_1085463).sum := by decide
  have hdescent : baseEnd_1085463 < baseStart_1085463 := by decide
  rcases family_descends (prefixWord ++ tailWord_1085463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1085536 : List Nat := [2, 1, 1, 3, 2, 3, 1, 1, 8]
def baseStart_1085536 : Nat := 118140960795 + 1085536 * 2 ^ 59
def prefixEnd_1085536 : Nat := 4983230072969 + 3 ^ 40 * 1085536 * 2
def baseEnd_1085536 : Nat := 123867052390926682023937

theorem tailTrace_1085536 : CollatzResearch.WordTrace tailWord_1085536 prefixEnd_1085536 123867052390926682023937 := by
  unfold tailWord_1085536
  simp only [CollatzResearch.WordTrace]
  refine ⟨19796375297647970816938231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26395167063530627755917641 19796375297647970816938231)
  ·
    refine ⟨29694562946471956225407347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19796375297647970816938231 29694562946471956225407347)
    ·
      refine ⟨44541844419707934338111021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29694562946471956225407347 44541844419707934338111021)
      ·
        refine ⟨16703191657390475376791633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44541844419707934338111021 16703191657390475376791633)
        ·
          refine ⟨12527393743042856532593725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16703191657390475376791633 12527393743042856532593725)
          ·
            refine ⟨4697772653641071199722647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12527393743042856532593725 4697772653641071199722647)
            ·
              refine ⟨7046658980461606799583971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4697772653641071199722647 7046658980461606799583971)
              ·
                refine ⟨10569988470692410199375957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7046658980461606799583971 10569988470692410199375957)
                ·
                  refine ⟨123867052390926682023937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 10569988470692410199375957 123867052390926682023937)
                  ·
                    rfl

theorem cell22_1085536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 1, 1, 8].length) (baseStart_1085536 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1085536 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1085536 prefixEnd_1085536 := by exact prefixLift 1085536
  have htrace : WordTrace (prefixWord ++ tailWord_1085536) baseStart_1085536 baseEnd_1085536 := by
    simpa [prefixWord, tailWord_1085536, baseEnd_1085536] using wordTrace_append hprefix tailTrace_1085536
  have hstable : (prefixWord ++ tailWord_1085536).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1085536).length < 2 ^ (prefixWord ++ tailWord_1085536).sum := by decide
  have hdescent : baseEnd_1085536 < baseStart_1085536 := by decide
  rcases family_descends (prefixWord ++ tailWord_1085536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1085604 : List Nat := [2, 3, 1, 2, 5, 1, 1, 3, 4]
def baseStart_1085604 : Nat := 118140960795 + 1085604 * 2 ^ 59
def prefixEnd_1085604 : Nat := 4983230072969 + 3 ^ 40 * 1085604 * 2
def baseEnd_1085604 : Nat := 123874811654150178457201

theorem tailTrace_1085604 : CollatzResearch.WordTrace tailWord_1085604 prefixEnd_1085604 123874811654150178457201 := by
  unfold tailWord_1085604
  simp only [CollatzResearch.WordTrace]
  refine ⟨19797615379524794623675933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26396820506033059498234577 19797615379524794623675933)
  ·
    refine ⟨7424105767321797983878475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19797615379524794623675933 7424105767321797983878475)
    ·
      refine ⟨11136158650982696975817713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7424105767321797983878475 11136158650982696975817713)
      ·
        refine ⟨8352118988237022731863285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11136158650982696975817713 8352118988237022731863285)
        ·
          refine ⟨783011155147220881112183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 8352118988237022731863285 783011155147220881112183)
          ·
            refine ⟨1174516732720831321668275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 783011155147220881112183 1174516732720831321668275)
            ·
              refine ⟨1761775099081246982502413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1174516732720831321668275 1761775099081246982502413)
              ·
                refine ⟨660665662155467618438405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1761775099081246982502413 660665662155467618438405)
                ·
                  refine ⟨123874811654150178457201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 660665662155467618438405 123874811654150178457201)
                  ·
                    rfl

theorem cell22_1085604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 5, 1, 1, 3, 4].length) (baseStart_1085604 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1085604 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1085604 prefixEnd_1085604 := by exact prefixLift 1085604
  have htrace : WordTrace (prefixWord ++ tailWord_1085604) baseStart_1085604 baseEnd_1085604 := by
    simpa [prefixWord, tailWord_1085604, baseEnd_1085604] using wordTrace_append hprefix tailTrace_1085604
  have hstable : (prefixWord ++ tailWord_1085604).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1085604).length < 2 ^ (prefixWord ++ tailWord_1085604).sum := by decide
  have hdescent : baseEnd_1085604 < baseStart_1085604 := by decide
  rcases family_descends (prefixWord ++ tailWord_1085604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1085643 : List Nat := [1, 1, 1, 1, 3, 2, 5, 3, 5]
def baseStart_1085643 : Nat := 118140960795 + 1085643 * 2 ^ 59
def prefixEnd_1085643 : Nat := 4983230072969 + 3 ^ 40 * 1085643 * 2
def baseEnd_1085643 : Nat := 123879261819822477882161

theorem tailTrace_1085643 : CollatzResearch.WordTrace tailWord_1085643 prefixEnd_1085643 123879261819822477882161 := by
  unfold tailWord_1085643
  simp only [CollatzResearch.WordTrace]
  refine ⟨39596653205908298908021583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26397768803938865938681055 39596653205908298908021583)
  ·
    refine ⟨59394979808862448362032375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39596653205908298908021583 59394979808862448362032375)
    ·
      refine ⟨89092469713293672543048563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59394979808862448362032375 89092469713293672543048563)
      ·
        refine ⟨133638704569940508814572845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89092469713293672543048563 133638704569940508814572845)
        ·
          refine ⟨50114514213727690805464817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 133638704569940508814572845 50114514213727690805464817)
          ·
            refine ⟨37585885660295768104098613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50114514213727690805464817 37585885660295768104098613)
            ·
              refine ⟨3523676780652728259759245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 37585885660295768104098613 3523676780652728259759245)
              ·
                refine ⟨1321378792744773097409717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3523676780652728259759245 1321378792744773097409717)
                ·
                  refine ⟨123879261819822477882161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1321378792744773097409717 123879261819822477882161)
                  ·
                    rfl

theorem cell22_1085643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 5, 3, 5].length) (baseStart_1085643 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1085643 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1085643 prefixEnd_1085643 := by exact prefixLift 1085643
  have htrace : WordTrace (prefixWord ++ tailWord_1085643) baseStart_1085643 baseEnd_1085643 := by
    simpa [prefixWord, tailWord_1085643, baseEnd_1085643] using wordTrace_append hprefix tailTrace_1085643
  have hstable : (prefixWord ++ tailWord_1085643).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1085643).length < 2 ^ (prefixWord ++ tailWord_1085643).sum := by decide
  have hdescent : baseEnd_1085643 < baseStart_1085643 := by decide
  rcases family_descends (prefixWord ++ tailWord_1085643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1085677 : List Nat := [1, 5, 1, 2, 3, 1, 2, 2, 5]
def baseStart_1085677 : Nat := 118140960795 + 1085677 * 2 ^ 59
def prefixEnd_1085677 : Nat := 4983230072969 + 3 ^ 40 * 1085677 * 2
def baseEnd_1085677 : Nat := 123883141451434226098793

theorem tailTrace_1085677 : CollatzResearch.WordTrace tailWord_1085677 prefixEnd_1085677 123883141451434226098793 := by
  unfold tailWord_1085677
  simp only [CollatzResearch.WordTrace]
  refine ⟨39597893287785122714759285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26398595525190081809839523 39597893287785122714759285)
  ·
    refine ⟨3712302495729855254508683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 39597893287785122714759285 3712302495729855254508683)
    ·
      refine ⟨5568453743594782881763025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3712302495729855254508683 5568453743594782881763025)
      ·
        refine ⟨4176340307696087161322269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5568453743594782881763025 4176340307696087161322269)
        ·
          refine ⟨1566127615386032685495851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4176340307696087161322269 1566127615386032685495851)
          ·
            refine ⟨2349191423079049028243777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1566127615386032685495851 2349191423079049028243777)
            ·
              refine ⟨1761893567309286771182833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2349191423079049028243777 1761893567309286771182833)
              ·
                refine ⟨1321420175481965078387125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1761893567309286771182833 1321420175481965078387125)
                ·
                  refine ⟨123883141451434226098793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1321420175481965078387125 123883141451434226098793)
                  ·
                    rfl

theorem cell22_1085677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 2, 2, 5].length) (baseStart_1085677 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1085677 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1085677 prefixEnd_1085677 := by exact prefixLift 1085677
  have htrace : WordTrace (prefixWord ++ tailWord_1085677) baseStart_1085677 baseEnd_1085677 := by
    simpa [prefixWord, tailWord_1085677, baseEnd_1085677] using wordTrace_append hprefix tailTrace_1085677
  have hstable : (prefixWord ++ tailWord_1085677).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1085677).length < 2 ^ (prefixWord ++ tailWord_1085677).sum := by decide
  have hdescent : baseEnd_1085677 < baseStart_1085677 := by decide
  rcases family_descends (prefixWord ++ tailWord_1085677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1085720 : List Nat := [2, 1, 2, 3, 1, 2, 2, 2, 4, 3]
def baseStart_1085720 : Nat := 118140960795 + 1085720 * 2 ^ 59
def prefixEnd_1085720 : Nat := 4983230072969 + 3 ^ 40 * 1085720 * 2
def baseEnd_1085720 : Nat := 371664144133064899471247

theorem tailTrace_1085720 : CollatzResearch.WordTrace tailWord_1085720 prefixEnd_1085720 371664144133064899471247 := by
  unfold tailWord_1085720
  simp only [CollatzResearch.WordTrace]
  refine ⟨19799730813314670529287307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26399641084419560705716409 19799730813314670529287307)
  ·
    refine ⟨29699596219972005793930961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19799730813314670529287307 29699596219972005793930961)
    ·
      refine ⟨22274697164979004345448221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29699596219972005793930961 22274697164979004345448221)
      ·
        refine ⟨8353011436867126629543083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22274697164979004345448221 8353011436867126629543083)
        ·
          refine ⟨12529517155300689944314625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8353011436867126629543083 12529517155300689944314625)
          ·
            refine ⟨9397137866475517458235969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12529517155300689944314625 9397137866475517458235969)
            ·
              refine ⟨7047853399856638093676977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9397137866475517458235969 7047853399856638093676977)
              ·
                refine ⟨5285890049892478570257733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7047853399856638093676977 5285890049892478570257733)
                ·
                  refine ⟨991104384354839731923325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5285890049892478570257733 991104384354839731923325)
                  ·
                    refine ⟨371664144133064899471247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 991104384354839731923325 371664144133064899471247)
                    ·
                      rfl

theorem cell22_1085720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 2, 2, 4, 3].length) (baseStart_1085720 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1085720 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1085720 prefixEnd_1085720 := by exact prefixLift 1085720
  have htrace : WordTrace (prefixWord ++ tailWord_1085720) baseStart_1085720 baseEnd_1085720 := by
    simpa [prefixWord, tailWord_1085720, baseEnd_1085720] using wordTrace_append hprefix tailTrace_1085720
  have hstable : (prefixWord ++ tailWord_1085720).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1085720).length < 2 ^ (prefixWord ++ tailWord_1085720).sum := by decide
  have hdescent : baseEnd_1085720 < baseStart_1085720 := by decide
  rcases family_descends (prefixWord ++ tailWord_1085720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1085754 : List Nat := [3, 1, 1, 1, 4, 3, 3, 1, 2, 3]
def baseStart_1085754 : Nat := 118140960795 + 1085754 * 2 ^ 59
def prefixEnd_1085754 : Nat := 4983230072969 + 3 ^ 40 * 1085754 * 2
def baseEnd_1085754 : Nat := 371675783027900144121143

theorem tailTrace_1085754 : CollatzResearch.WordTrace tailWord_1085754 prefixEnd_1085754 371675783027900144121143 := by
  unfold tailWord_1085754
  simp only [CollatzResearch.WordTrace]
  refine ⟨9900175427126541216328079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26400467805670776576874877 9900175427126541216328079)
  ·
    refine ⟨14850263140689811824492119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9900175427126541216328079 14850263140689811824492119)
    ·
      refine ⟨22275394711034717736738179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14850263140689811824492119 22275394711034717736738179)
      ·
        refine ⟨33413092066552076605107269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22275394711034717736738179 33413092066552076605107269)
        ·
          refine ⟨6264954762478514363457613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 33413092066552076605107269 6264954762478514363457613)
          ·
            refine ⟨2349358035929442886296605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6264954762478514363457613 2349358035929442886296605)
            ·
              refine ⟨881009263473541082361227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2349358035929442886296605 881009263473541082361227)
              ·
                refine ⟨1321513895210311623541841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 881009263473541082361227 1321513895210311623541841)
                ·
                  refine ⟨991135421407733717656381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1321513895210311623541841 991135421407733717656381)
                  ·
                    refine ⟨371675783027900144121143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 991135421407733717656381 371675783027900144121143)
                    ·
                      rfl

theorem cell22_1085754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 3, 1, 2, 3].length) (baseStart_1085754 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1085754 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1085754 prefixEnd_1085754 := by exact prefixLift 1085754
  have htrace : WordTrace (prefixWord ++ tailWord_1085754) baseStart_1085754 baseEnd_1085754 := by
    simpa [prefixWord, tailWord_1085754, baseEnd_1085754] using wordTrace_append hprefix tailTrace_1085754
  have hstable : (prefixWord ++ tailWord_1085754).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1085754).length < 2 ^ (prefixWord ++ tailWord_1085754).sum := by decide
  have hdescent : baseEnd_1085754 < baseStart_1085754 := by decide
  rcases family_descends (prefixWord ++ tailWord_1085754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1085763 : List Nat := [1, 1, 1, 3, 1, 3, 2, 2, 2, 6]
def baseStart_1085763 : Nat := 118140960795 + 1085763 * 2 ^ 59
def prefixEnd_1085763 : Nat := 4983230072969 + 3 ^ 40 * 1085763 * 2
def baseEnd_1085763 : Nat := 371678863911827120646115

theorem tailTrace_1085763 : CollatzResearch.WordTrace tailWord_1085763 prefixEnd_1085763 371678863911827120646115 := by
  unfold tailWord_1085763
  simp only [CollatzResearch.WordTrace]
  refine ⟨39601029965473559402389943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26400686643649039601593295 39601029965473559402389943)
  ·
    refine ⟨59401544948210339103584915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39601029965473559402389943 59401544948210339103584915)
    ·
      refine ⟨89102317422315508655377373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59401544948210339103584915 89102317422315508655377373)
      ·
        refine ⟨33413369033368315745766515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 89102317422315508655377373 33413369033368315745766515)
        ·
          refine ⟨50120053550052473618649773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33413369033368315745766515 50120053550052473618649773)
          ·
            refine ⟨18795020081269677606993665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50120053550052473618649773 18795020081269677606993665)
            ·
              refine ⟨14096265060952258205245249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18795020081269677606993665 14096265060952258205245249)
              ·
                refine ⟨10572198795714193653933937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14096265060952258205245249 10572198795714193653933937)
                ·
                  refine ⟨7929149096785645240450453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10572198795714193653933937 7929149096785645240450453)
                  ·
                    refine ⟨371678863911827120646115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7929149096785645240450453 371678863911827120646115)
                    ·
                      rfl

theorem cell22_1085763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 2, 2, 6].length) (baseStart_1085763 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1085763 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1085763 prefixEnd_1085763 := by exact prefixLift 1085763
  have htrace : WordTrace (prefixWord ++ tailWord_1085763) baseStart_1085763 baseEnd_1085763 := by
    simpa [prefixWord, tailWord_1085763, baseEnd_1085763] using wordTrace_append hprefix tailTrace_1085763
  have hstable : (prefixWord ++ tailWord_1085763).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1085763).length < 2 ^ (prefixWord ++ tailWord_1085763).sum := by decide
  have hdescent : baseEnd_1085763 < baseStart_1085763 := by decide
  rcases family_descends (prefixWord ++ tailWord_1085763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1085790 : List Nat := [4, 4, 2, 1, 2, 1, 1, 1, 6]
def baseStart_1085790 : Nat := 118140960795 + 1085790 * 2 ^ 59
def prefixEnd_1085790 : Nat := 4983230072969 + 3 ^ 40 * 1085790 * 2
def baseEnd_1085790 : Nat := 123896035521202683407011

theorem tailTrace_1085790 : CollatzResearch.WordTrace tailWord_1085790 prefixEnd_1085790 123896035521202683407011 := by
  unfold tailWord_1085790
  simp only [CollatzResearch.WordTrace]
  refine ⟨4950251842046967876702853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26401343157583828675748549 4950251842046967876702853)
  ·
    refine ⟨928172220383806476881785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4950251842046967876702853 928172220383806476881785)
    ·
      refine ⟨696129165287854857661339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 928172220383806476881785 696129165287854857661339)
      ·
        refine ⟨1044193747931782286492009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 696129165287854857661339 1044193747931782286492009)
        ·
          refine ⟨783145310948836714869007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1044193747931782286492009 783145310948836714869007)
          ·
            refine ⟨1174717966423255072303511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 783145310948836714869007 1174717966423255072303511)
            ·
              refine ⟨1762076949634882608455267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1174717966423255072303511 1762076949634882608455267)
              ·
                refine ⟨2643115424452323912682901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1762076949634882608455267 2643115424452323912682901)
                ·
                  refine ⟨123896035521202683407011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2643115424452323912682901 123896035521202683407011)
                  ·
                    rfl

theorem cell22_1085790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 2, 1, 1, 1, 6].length) (baseStart_1085790 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1085790 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1085790 prefixEnd_1085790 := by exact prefixLift 1085790
  have htrace : WordTrace (prefixWord ++ tailWord_1085790) baseStart_1085790 baseEnd_1085790 := by
    simpa [prefixWord, tailWord_1085790, baseEnd_1085790] using wordTrace_append hprefix tailTrace_1085790
  have hstable : (prefixWord ++ tailWord_1085790).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1085790).length < 2 ^ (prefixWord ++ tailWord_1085790).sum := by decide
  have hdescent : baseEnd_1085790 < baseStart_1085790 := by decide
  rcases family_descends (prefixWord ++ tailWord_1085790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1085795 : List Nat := [1, 1, 1, 5, 2, 1, 2, 4, 5]
def baseStart_1085795 : Nat := 118140960795 + 1085795 * 2 ^ 59
def prefixEnd_1085795 : Nat := 4983230072969 + 3 ^ 40 * 1085795 * 2
def baseEnd_1085795 : Nat := 123896606055263234615339

theorem tailTrace_1085795 : CollatzResearch.WordTrace tailWord_1085795 prefixEnd_1085795 123896606055263234615339 := by
  unfold tailWord_1085795
  simp only [CollatzResearch.WordTrace]
  refine ⟨39602197101357628867554839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26401464734238419245036559 39602197101357628867554839)
  ·
    refine ⟨59403295652036443301332259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39602197101357628867554839 59403295652036443301332259)
    ·
      refine ⟨89104943478054664951998389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59403295652036443301332259 89104943478054664951998389)
      ·
        refine ⟨8353588451067624839249849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 89104943478054664951998389 8353588451067624839249849)
        ·
          refine ⟨6265191338300718629437387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8353588451067624839249849 6265191338300718629437387)
          ·
            refine ⟨9397787007451077944156081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6265191338300718629437387 9397787007451077944156081)
            ·
              refine ⟨7048340255588308458117061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9397787007451077944156081 7048340255588308458117061)
              ·
                refine ⟨1321563797922807835896949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7048340255588308458117061 1321563797922807835896949)
                ·
                  refine ⟨123896606055263234615339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1321563797922807835896949 123896606055263234615339)
                  ·
                    rfl

theorem cell22_1085795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 2, 4, 5].length) (baseStart_1085795 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1085795 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1085795 prefixEnd_1085795 := by exact prefixLift 1085795
  have htrace : WordTrace (prefixWord ++ tailWord_1085795) baseStart_1085795 baseEnd_1085795 := by
    simpa [prefixWord, tailWord_1085795, baseEnd_1085795] using wordTrace_append hprefix tailTrace_1085795
  have hstable : (prefixWord ++ tailWord_1085795).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1085795).length < 2 ^ (prefixWord ++ tailWord_1085795).sum := by decide
  have hdescent : baseEnd_1085795 < baseStart_1085795 := by decide
  rcases family_descends (prefixWord ++ tailWord_1085795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1085799 : List Nat := [1, 1, 5, 1, 3, 3, 1, 1, 3, 3]
def baseStart_1085799 : Nat := 118140960795 + 1085799 * 2 ^ 59
def prefixEnd_1085799 : Nat := 4983230072969 + 3 ^ 40 * 1085799 * 2
def baseEnd_1085799 : Nat := 371691187447535026746005

theorem tailTrace_1085799 : CollatzResearch.WordTrace tailWord_1085799 prefixEnd_1085799 371691187447535026746005 := by
  unfold tailWord_1085799
  simp only [CollatzResearch.WordTrace]
  refine ⟨39602342993343137550700451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26401561995562091700466967 39602342993343137550700451)
  ·
    refine ⟨59403514490014706326050677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39602342993343137550700451 59403514490014706326050677)
    ·
      refine ⟨5569079483438878718067251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 59403514490014706326050677 5569079483438878718067251)
      ·
        refine ⟨8353619225158318077100877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5569079483438878718067251 8353619225158318077100877)
        ·
          refine ⟨3132607209434369278912829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8353619225158318077100877 3132607209434369278912829)
          ·
            refine ⟨1174727703537888479592311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3132607209434369278912829 1174727703537888479592311)
            ·
              refine ⟨1762091555306832719388467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1174727703537888479592311 1762091555306832719388467)
              ·
                refine ⟨2643137332960249079082701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1762091555306832719388467 2643137332960249079082701)
                ·
                  refine ⟨991176499860093404656013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2643137332960249079082701 991176499860093404656013)
                  ·
                    refine ⟨371691187447535026746005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 991176499860093404656013 371691187447535026746005)
                    ·
                      rfl

theorem cell22_1085799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 3, 1, 1, 3, 3].length) (baseStart_1085799 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1085799 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1085799 prefixEnd_1085799 := by exact prefixLift 1085799
  have htrace : WordTrace (prefixWord ++ tailWord_1085799) baseStart_1085799 baseEnd_1085799 := by
    simpa [prefixWord, tailWord_1085799, baseEnd_1085799] using wordTrace_append hprefix tailTrace_1085799
  have hstable : (prefixWord ++ tailWord_1085799).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1085799).length < 2 ^ (prefixWord ++ tailWord_1085799).sum := by decide
  have hdescent : baseEnd_1085799 < baseStart_1085799 := by decide
  rcases family_descends (prefixWord ++ tailWord_1085799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1085855 : List Nat := [1, 1, 2, 5, 1, 1, 1, 2, 3, 5]
def baseStart_1085855 : Nat := 118140960795 + 1085855 * 2 ^ 59
def prefixEnd_1085855 : Nat := 4983230072969 + 3 ^ 40 * 1085855 * 2
def baseEnd_1085855 : Nat := 371710357391969547345833

theorem tailTrace_1085855 : CollatzResearch.WordTrace tailWord_1085855 prefixEnd_1085855 371710357391969547345833 := by
  unfold tailWord_1085855
  simp only [CollatzResearch.WordTrace]
  refine ⟨39604385481140259114739019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26402923654093506076492679 39604385481140259114739019)
  ·
    refine ⟨59406578221710388672108529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39604385481140259114739019 59406578221710388672108529)
    ·
      refine ⟨44554933666282791504081397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59406578221710388672108529 44554933666282791504081397)
      ·
        refine ⟨4177025031214011703507631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 44554933666282791504081397 4177025031214011703507631)
        ·
          refine ⟨6265537546821017555261447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4177025031214011703507631 6265537546821017555261447)
          ·
            refine ⟨9398306320231526332892171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6265537546821017555261447 9398306320231526332892171)
            ·
              refine ⟨14097459480347289499338257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9398306320231526332892171 14097459480347289499338257)
              ·
                refine ⟨10573094610260467124503693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14097459480347289499338257 10573094610260467124503693)
                ·
                  refine ⟨3964910478847675171688885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10573094610260467124503693 3964910478847675171688885)
                  ·
                    refine ⟨371710357391969547345833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3964910478847675171688885 371710357391969547345833)
                    ·
                      rfl

theorem cell22_1085855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 2, 3, 5].length) (baseStart_1085855 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1085855 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1085855 prefixEnd_1085855 := by exact prefixLift 1085855
  have htrace : WordTrace (prefixWord ++ tailWord_1085855) baseStart_1085855 baseEnd_1085855 := by
    simpa [prefixWord, tailWord_1085855, baseEnd_1085855] using wordTrace_append hprefix tailTrace_1085855
  have hstable : (prefixWord ++ tailWord_1085855).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1085855).length < 2 ^ (prefixWord ++ tailWord_1085855).sum := by decide
  have hdescent : baseEnd_1085855 < baseStart_1085855 := by decide
  rcases family_descends (prefixWord ++ tailWord_1085855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1085906 : List Nat := [3, 2, 2, 4, 1, 1, 1, 1, 4, 3]
def baseStart_1085906 : Nat := 118140960795 + 1085906 * 2 ^ 59
def prefixEnd_1085906 : Nat := 4983230072969 + 3 ^ 40 * 1085906 * 2
def baseEnd_1085906 : Nat := 371727815734222414320677

theorem tailTrace_1085906 : CollatzResearch.WordTrace tailWord_1085906 prefixEnd_1085906 371727815734222414320677 := by
  unfold tailWord_1085906
  simp only [CollatzResearch.WordTrace]
  refine ⟨9901561400988873706211393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26404163735970329883230381 9901561400988873706211393)
  ·
    refine ⟨7426171050741655279658545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9901561400988873706211393 7426171050741655279658545)
    ·
      refine ⟨5569628288056241459743909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7426171050741655279658545 5569628288056241459743909)
      ·
        refine ⟨1044305304010545273701983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5569628288056241459743909 1044305304010545273701983)
        ·
          refine ⟨1566457956015817910552975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1044305304010545273701983 1566457956015817910552975)
          ·
            refine ⟨2349686934023726865829463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1566457956015817910552975 2349686934023726865829463)
            ·
              refine ⟨3524530401035590298744195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2349686934023726865829463 3524530401035590298744195)
              ·
                refine ⟨5286795601553385448116293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3524530401035590298744195 5286795601553385448116293)
                ·
                  refine ⟨991274175291259771521805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5286795601553385448116293 991274175291259771521805)
                  ·
                    refine ⟨371727815734222414320677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 991274175291259771521805 371727815734222414320677)
                    ·
                      rfl

theorem cell22_1085906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 1, 1, 4, 3].length) (baseStart_1085906 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1085906 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1085906 prefixEnd_1085906 := by exact prefixLift 1085906
  have htrace : WordTrace (prefixWord ++ tailWord_1085906) baseStart_1085906 baseEnd_1085906 := by
    simpa [prefixWord, tailWord_1085906, baseEnd_1085906] using wordTrace_append hprefix tailTrace_1085906
  have hstable : (prefixWord ++ tailWord_1085906).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1085906).length < 2 ^ (prefixWord ++ tailWord_1085906).sum := by decide
  have hdescent : baseEnd_1085906 < baseStart_1085906 := by decide
  rcases family_descends (prefixWord ++ tailWord_1085906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1085934 : List Nat := [4, 1, 2, 1, 2, 2, 2, 2, 3, 3]
def baseStart_1085934 : Nat := 118140960795 + 1085934 * 2 ^ 59
def prefixEnd_1085934 : Nat := 4983230072969 + 3 ^ 40 * 1085934 * 2
def baseEnd_1085934 : Nat := 371737400706439674620591

theorem tailTrace_1085934 : CollatzResearch.WordTrace tailWord_1085934 prefixEnd_1085934 371737400706439674620591 := by
  unfold tailWord_1085934
  simp only [CollatzResearch.WordTrace]
  refine ⟨4950908355981756950858107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26404844565236037071243237 4950908355981756950858107)
  ·
    refine ⟨7426362533972635426287161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4950908355981756950858107 7426362533972635426287161)
    ·
      refine ⟨5569771900479476569715371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7426362533972635426287161 5569771900479476569715371)
      ·
        refine ⟨8354657850719214854573057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5569771900479476569715371 8354657850719214854573057)
        ·
          refine ⟨6265993388039411140929793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8354657850719214854573057 6265993388039411140929793)
          ·
            refine ⟨4699495041029558355697345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6265993388039411140929793 4699495041029558355697345)
            ·
              refine ⟨3524621280772168766773009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4699495041029558355697345 3524621280772168766773009)
              ·
                refine ⟨2643465960579126575079757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3524621280772168766773009 2643465960579126575079757)
                ·
                  refine ⟨991299735217172465654909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2643465960579126575079757 991299735217172465654909)
                  ·
                    refine ⟨371737400706439674620591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 991299735217172465654909 371737400706439674620591)
                    ·
                      rfl

theorem cell22_1085934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 2, 2, 3, 3].length) (baseStart_1085934 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1085934 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1085934 prefixEnd_1085934 := by exact prefixLift 1085934
  have htrace : WordTrace (prefixWord ++ tailWord_1085934) baseStart_1085934 baseEnd_1085934 := by
    simpa [prefixWord, tailWord_1085934, baseEnd_1085934] using wordTrace_append hprefix tailTrace_1085934
  have hstable : (prefixWord ++ tailWord_1085934).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1085934).length < 2 ^ (prefixWord ++ tailWord_1085934).sum := by decide
  have hdescent : baseEnd_1085934 < baseStart_1085934 := by decide
  rcases family_descends (prefixWord ++ tailWord_1085934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1085945 : List Nat := [1, 2, 1, 3, 1, 2, 2, 2, 1, 7]
def baseStart_1085945 : Nat := 118140960795 + 1085945 * 2 ^ 59
def prefixEnd_1085945 : Nat := 4983230072969 + 3 ^ 40 * 1085945 * 2
def baseEnd_1085945 : Nat := 371741166231239312595557

theorem tailTrace_1085945 : CollatzResearch.WordTrace tailWord_1085945 prefixEnd_1085945 371741166231239312595557 := by
  unfold tailWord_1085945
  simp only [CollatzResearch.WordTrace]
  refine ⟨39607668050814204485515289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26405112033876136323676859 39607668050814204485515289)
  ·
    refine ⟨29705751038110653364136467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39607668050814204485515289 29705751038110653364136467)
    ·
      refine ⟨44558626557165980046204701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29705751038110653364136467 44558626557165980046204701)
      ·
        refine ⟨16709484958937242517326763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44558626557165980046204701 16709484958937242517326763)
        ·
          refine ⟨25064227438405863775990145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16709484958937242517326763 25064227438405863775990145)
          ·
            refine ⟨18798170578804397831992609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25064227438405863775990145 18798170578804397831992609)
            ·
              refine ⟨14098627934103298373994457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18798170578804397831992609 14098627934103298373994457)
              ·
                refine ⟨10573970950577473780495843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14098627934103298373994457 10573970950577473780495843)
                ·
                  refine ⟨15860956425866210670743765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10573970950577473780495843 15860956425866210670743765)
                  ·
                    refine ⟨371741166231239312595557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 15860956425866210670743765 371741166231239312595557)
                    ·
                      rfl

theorem cell22_1085945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 2, 1, 7].length) (baseStart_1085945 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1085945 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1085945 prefixEnd_1085945 := by exact prefixLift 1085945
  have htrace : WordTrace (prefixWord ++ tailWord_1085945) baseStart_1085945 baseEnd_1085945 := by
    simpa [prefixWord, tailWord_1085945, baseEnd_1085945] using wordTrace_append hprefix tailTrace_1085945
  have hstable : (prefixWord ++ tailWord_1085945).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1085945).length < 2 ^ (prefixWord ++ tailWord_1085945).sum := by decide
  have hdescent : baseEnd_1085945 < baseStart_1085945 := by decide
  rcases family_descends (prefixWord ++ tailWord_1085945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1085981 : List Nat := [1, 4, 2, 2, 1, 4, 2, 1, 5]
def baseStart_1085981 : Nat := 118140960795 + 1085981 * 2 ^ 59
def prefixEnd_1085981 : Nat := 4983230072969 + 3 ^ 40 * 1085981 * 2
def baseEnd_1085981 : Nat := 123917829922315739565149

theorem tailTrace_1085981 : CollatzResearch.WordTrace tailWord_1085981 prefixEnd_1085981 123917829922315739565149 := by
  unfold tailWord_1085981
  simp only [CollatzResearch.WordTrace]
  refine ⟨39608981078683782633825797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26405987385789188422550531 39608981078683782633825797)
  ·
    refine ⟨7426683952253209243842337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 39608981078683782633825797 7426683952253209243842337)
    ·
      refine ⟨5570012964189906932881753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7426683952253209243842337 5570012964189906932881753)
      ·
        refine ⟨4177509723142430199661315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5570012964189906932881753 4177509723142430199661315)
        ·
          refine ⟨6266264584713645299491973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4177509723142430199661315 6266264584713645299491973)
          ·
            refine ⟨1174924609633808493654745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6266264584713645299491973 1174924609633808493654745)
            ·
              refine ⟨881193457225356370241059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1174924609633808493654745 881193457225356370241059)
              ·
                refine ⟨1321790185838034555361589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 881193457225356370241059 1321790185838034555361589)
                ·
                  refine ⟨123917829922315739565149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1321790185838034555361589 123917829922315739565149)
                  ·
                    rfl

theorem cell22_1085981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 4, 2, 1, 5].length) (baseStart_1085981 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1085981 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1085981 prefixEnd_1085981 := by exact prefixLift 1085981
  have htrace : WordTrace (prefixWord ++ tailWord_1085981) baseStart_1085981 baseEnd_1085981 := by
    simpa [prefixWord, tailWord_1085981, baseEnd_1085981] using wordTrace_append hprefix tailTrace_1085981
  have hstable : (prefixWord ++ tailWord_1085981).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1085981).length < 2 ^ (prefixWord ++ tailWord_1085981).sum := by decide
  have hdescent : baseEnd_1085981 < baseStart_1085981 := by decide
  rcases family_descends (prefixWord ++ tailWord_1085981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1085994 : List Nat := [3, 1, 4, 1, 1, 3, 1, 1, 3, 4]
def baseStart_1085994 : Nat := 118140960795 + 1085994 * 2 ^ 59
def prefixEnd_1085994 : Nat := 4983230072969 + 3 ^ 40 * 1085994 * 2
def baseEnd_1085994 : Nat := 371757939932619518120407

theorem tailTrace_1085994 : CollatzResearch.WordTrace tailWord_1085994 prefixEnd_1085994 371757939932619518120407 := by
  unfold tailWord_1085994
  simp only [CollatzResearch.WordTrace]
  refine ⟨9902363806909171463512259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26406303485091123902699357 9902363806909171463512259)
  ·
    refine ⟨14853545710363757195268389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9902363806909171463512259 14853545710363757195268389)
    ·
      refine ⟨2785039820693204474112823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14853545710363757195268389 2785039820693204474112823)
      ·
        refine ⟨4177559731039806711169235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2785039820693204474112823 4177559731039806711169235)
        ·
          refine ⟨6266339596559710066753853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4177559731039806711169235 6266339596559710066753853)
          ·
            refine ⟨2349877348709891275032695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6266339596559710066753853 2349877348709891275032695)
            ·
              refine ⟨3524816023064836912549043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2349877348709891275032695 3524816023064836912549043)
              ·
                refine ⟨5287224034597255368823565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3524816023064836912549043 5287224034597255368823565)
                ·
                  refine ⟨1982709012973970763308837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5287224034597255368823565 1982709012973970763308837)
                  ·
                    refine ⟨371757939932619518120407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1982709012973970763308837 371757939932619518120407)
                    ·
                      rfl

theorem cell22_1085994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 1, 1, 3, 4].length) (baseStart_1085994 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1085994 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1085994 prefixEnd_1085994 := by exact prefixLift 1085994
  have htrace : WordTrace (prefixWord ++ tailWord_1085994) baseStart_1085994 baseEnd_1085994 := by
    simpa [prefixWord, tailWord_1085994, baseEnd_1085994] using wordTrace_append hprefix tailTrace_1085994
  have hstable : (prefixWord ++ tailWord_1085994).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1085994).length < 2 ^ (prefixWord ++ tailWord_1085994).sum := by decide
  have hdescent : baseEnd_1085994 < baseStart_1085994 := by decide
  rcases family_descends (prefixWord ++ tailWord_1085994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1086007 : List Nat := [1, 1, 3, 1, 2, 3, 3, 2, 1, 5]
def baseStart_1086007 : Nat := 118140960795 + 1086007 * 2 ^ 59
def prefixEnd_1086007 : Nat := 4983230072969 + 3 ^ 40 * 1086007 * 2
def baseEnd_1086007 : Nat := 371762390098291817545367

theorem tailTrace_1086007 : CollatzResearch.WordTrace tailWord_1086007 prefixEnd_1086007 371762390098291817545367 := by
  unfold tailWord_1086007
  simp only [CollatzResearch.WordTrace]
  refine ⟨39609929376589589074272275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26406619584393059382848183 39609929376589589074272275)
  ·
    refine ⟨59414894064884383611408413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39609929376589589074272275 59414894064884383611408413)
    ·
      refine ⟨22280585274331643854278155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59414894064884383611408413 22280585274331643854278155)
      ·
        refine ⟨33420877911497465781417233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22280585274331643854278155 33420877911497465781417233)
        ·
          refine ⟨25065658433623099336062925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33420877911497465781417233 25065658433623099336062925)
          ·
            refine ⟨9399621912608662251023597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25065658433623099336062925 9399621912608662251023597)
            ·
              refine ⟨3524858217228248344133849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9399621912608662251023597 3524858217228248344133849)
              ·
                refine ⟨2643643662921186258100387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3524858217228248344133849 2643643662921186258100387)
                ·
                  refine ⟨3965465494381779387150581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2643643662921186258100387 3965465494381779387150581)
                  ·
                    refine ⟨371762390098291817545367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3965465494381779387150581 371762390098291817545367)
                    ·
                      rfl

theorem cell22_1086007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 3, 2, 1, 5].length) (baseStart_1086007 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1086007 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1086007 prefixEnd_1086007 := by exact prefixLift 1086007
  have htrace : WordTrace (prefixWord ++ tailWord_1086007) baseStart_1086007 baseEnd_1086007 := by
    simpa [prefixWord, tailWord_1086007, baseEnd_1086007] using wordTrace_append hprefix tailTrace_1086007
  have hstable : (prefixWord ++ tailWord_1086007).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1086007).length < 2 ^ (prefixWord ++ tailWord_1086007).sum := by decide
  have hdescent : baseEnd_1086007 < baseStart_1086007 := by decide
  rcases family_descends (prefixWord ++ tailWord_1086007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1086009 : List Nat := [1, 2, 1, 5, 1, 1, 2, 5, 4]
def baseStart_1086009 : Nat := 118140960795 + 1086009 * 2 ^ 59
def prefixEnd_1086009 : Nat := 4983230072969 + 3 ^ 40 * 1086009 * 2
def baseEnd_1086009 : Nat := 123921024913054826331787

theorem tailTrace_1086009 : CollatzResearch.WordTrace tailWord_1086009 prefixEnd_1086009 123921024913054826331787 := by
  unfold tailWord_1086009
  simp only [CollatzResearch.WordTrace]
  refine ⟨39610002322582343415845081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26406668215054895610563387 39610002322582343415845081)
  ·
    refine ⟨29707501741936757561883811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39610002322582343415845081 29707501741936757561883811)
    ·
      refine ⟨44561252612905136342825717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29707501741936757561883811 44561252612905136342825717)
      ·
        refine ⟨4177617432459856532139911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 44561252612905136342825717 4177617432459856532139911)
        ·
          refine ⟨6266426148689784798209867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4177617432459856532139911 6266426148689784798209867)
          ·
            refine ⟨9399639223034677197314801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6266426148689784798209867 9399639223034677197314801)
            ·
              refine ⟨7049729417276007897986101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9399639223034677197314801 7049729417276007897986101)
              ·
                refine ⟨660912132869625740436197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7049729417276007897986101 660912132869625740436197)
                ·
                  refine ⟨123921024913054826331787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 660912132869625740436197 123921024913054826331787)
                  ·
                    rfl

theorem cell22_1086009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 2, 5, 4].length) (baseStart_1086009 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1086009 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1086009 prefixEnd_1086009 := by exact prefixLift 1086009
  have htrace : WordTrace (prefixWord ++ tailWord_1086009) baseStart_1086009 baseEnd_1086009 := by
    simpa [prefixWord, tailWord_1086009, baseEnd_1086009] using wordTrace_append hprefix tailTrace_1086009
  have hstable : (prefixWord ++ tailWord_1086009).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1086009).length < 2 ^ (prefixWord ++ tailWord_1086009).sum := by decide
  have hdescent : baseEnd_1086009 < baseStart_1086009 := by decide
  rcases family_descends (prefixWord ++ tailWord_1086009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1086026 : List Nat := [3, 1, 2, 1, 1, 4, 4, 2, 4]
def baseStart_1086026 : Nat := 118140960795 + 1086026 * 2 ^ 59
def prefixEnd_1086026 : Nat := 4983230072969 + 3 ^ 40 * 1086026 * 2
def baseEnd_1086026 : Nat := 123922964728860700440103

theorem tailTrace_1086026 : CollatzResearch.WordTrace tailWord_1086026 prefixEnd_1086026 123922964728860700440103 := by
  unfold tailWord_1086026
  simp only [CollatzResearch.WordTrace]
  refine ⟨9902655590880188829803483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26407081575680503546142621 9902655590880188829803483)
  ·
    refine ⟨14853983386320283244705225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9902655590880188829803483 14853983386320283244705225)
    ·
      refine ⟨11140487539740212433528919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14853983386320283244705225 11140487539740212433528919)
      ·
        refine ⟨16710731309610318650293379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11140487539740212433528919 16710731309610318650293379)
        ·
          refine ⟨25066096964415477975440069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16710731309610318650293379 25066096964415477975440069)
          ·
            refine ⟨4699893180827902120395013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25066096964415477975440069 4699893180827902120395013)
            ·
              refine ⟨881229971405231647574065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4699893180827902120395013 881229971405231647574065)
              ·
                refine ⟨660922478553923735680549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 881229971405231647574065 660922478553923735680549)
                ·
                  refine ⟨123922964728860700440103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 660922478553923735680549 123922964728860700440103)
                  ·
                    rfl

theorem cell22_1086026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 4, 2, 4].length) (baseStart_1086026 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1086026 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1086026 prefixEnd_1086026 := by exact prefixLift 1086026
  have htrace : WordTrace (prefixWord ++ tailWord_1086026) baseStart_1086026 baseEnd_1086026 := by
    simpa [prefixWord, tailWord_1086026, baseEnd_1086026] using wordTrace_append hprefix tailTrace_1086026
  have hstable : (prefixWord ++ tailWord_1086026).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1086026).length < 2 ^ (prefixWord ++ tailWord_1086026).sum := by decide
  have hdescent : baseEnd_1086026 < baseStart_1086026 := by decide
  rcases family_descends (prefixWord ++ tailWord_1086026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1086037 : List Nat := [1, 3, 2, 2, 1, 1, 5, 7]
def baseStart_1086037 : Nat := 118140960795 + 1086037 * 2 ^ 59
def prefixEnd_1086037 : Nat := 4983230072969 + 3 ^ 40 * 1086037 * 2
def baseEnd_1086037 : Nat := 41308073301264637699475

theorem tailTrace_1086037 : CollatzResearch.WordTrace tailWord_1086037 prefixEnd_1086037 41308073301264637699475 := by
  unfold tailWord_1086037
  simp only [CollatzResearch.WordTrace]
  refine ⟨39611023566480904197864365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26407349044320602798576243 39611023566480904197864365)
  ·
    refine ⟨14854133837430339074199137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39611023566480904197864365 14854133837430339074199137)
    ·
      refine ⟨11140600378072754305649353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14854133837430339074199137 11140600378072754305649353)
      ·
        refine ⟨8355450283554565729237015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11140600378072754305649353 8355450283554565729237015)
        ·
          refine ⟨12533175425331848593855523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8355450283554565729237015 12533175425331848593855523)
          ·
            refine ⟨18799763137997772890783285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12533175425331848593855523 18799763137997772890783285)
            ·
              refine ⟨1762477794187291208510933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 18799763137997772890783285 1762477794187291208510933)
              ·
                refine ⟨41308073301264637699475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1762477794187291208510933 41308073301264637699475)
                ·
                  rfl

theorem cell22_1086037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 5, 7].length) (baseStart_1086037 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1086037 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1086037 prefixEnd_1086037 := by exact prefixLift 1086037
  have htrace : WordTrace (prefixWord ++ tailWord_1086037) baseStart_1086037 baseEnd_1086037 := by
    simpa [prefixWord, tailWord_1086037, baseEnd_1086037] using wordTrace_append hprefix tailTrace_1086037
  have hstable : (prefixWord ++ tailWord_1086037).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1086037).length < 2 ^ (prefixWord ++ tailWord_1086037).sum := by decide
  have hdescent : baseEnd_1086037 < baseStart_1086037 := by decide
  rcases family_descends (prefixWord ++ tailWord_1086037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1086144 : List Nat := [2, 1, 1, 2, 4, 2, 3, 1, 6]
def baseStart_1086144 : Nat := 118140960795 + 1086144 * 2 ^ 59
def prefixEnd_1086144 : Nat := 4983230072969 + 3 ^ 40 * 1086144 * 2
def baseEnd_1086144 : Nat := 123936429332689708956649

theorem tailTrace_1086144 : CollatzResearch.WordTrace tailWord_1086144 prefixEnd_1086144 123936429332689708956649 := by
  unfold tailWord_1086144
  simp only [CollatzResearch.WordTrace]
  refine ⟨19807463088546630736004743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26409950784728840981339657 19807463088546630736004743)
  ·
    refine ⟨29711194632819946104007115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19807463088546630736004743 29711194632819946104007115)
    ·
      refine ⟨44566791949229919156010673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29711194632819946104007115 44566791949229919156010673)
      ·
        refine ⟨33425093961922439367008005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44566791949229919156010673 33425093961922439367008005)
        ·
          refine ⟨6267205117860457381314001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 33425093961922439367008005 6267205117860457381314001)
          ·
            refine ⟨4700403838395343035985501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6267205117860457381314001 4700403838395343035985501)
            ·
              refine ⟨1762651439398253638494563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4700403838395343035985501 1762651439398253638494563)
              ·
                refine ⟨2643977159097380457741845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1762651439398253638494563 2643977159097380457741845)
                ·
                  refine ⟨123936429332689708956649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2643977159097380457741845 123936429332689708956649)
                  ·
                    rfl

theorem cell22_1086144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 3, 1, 6].length) (baseStart_1086144 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1086144 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1086144 prefixEnd_1086144 := by exact prefixLift 1086144
  have htrace : WordTrace (prefixWord ++ tailWord_1086144) baseStart_1086144 baseEnd_1086144 := by
    simpa [prefixWord, tailWord_1086144, baseEnd_1086144] using wordTrace_append hprefix tailTrace_1086144
  have hstable : (prefixWord ++ tailWord_1086144).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1086144).length < 2 ^ (prefixWord ++ tailWord_1086144).sum := by decide
  have hdescent : baseEnd_1086144 < baseStart_1086144 := by decide
  rcases family_descends (prefixWord ++ tailWord_1086144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1086150 : List Nat := [6, 1, 2, 1, 2, 1, 1, 3, 5]
def baseStart_1086150 : Nat := 118140960795 + 1086150 * 2 ^ 59
def prefixEnd_1086150 : Nat := 4983230072969 + 3 ^ 40 * 1086150 * 2
def baseEnd_1086150 : Nat := 123937113973562370406643

theorem tailTrace_1086150 : CollatzResearch.WordTrace tailWord_1086150 prefixEnd_1086150 123937113973562370406643 := by
  unfold tailWord_1086150
  simp only [CollatzResearch.WordTrace]
  refine ⟨1237973281720985140522747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 26410096676714349664485269 1237973281720985140522747)
  ·
    refine ⟨1856959922581477710784121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1237973281720985140522747 1856959922581477710784121)
    ·
      refine ⟨1392719941936108283088091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1856959922581477710784121 1392719941936108283088091)
      ·
        refine ⟨2089079912904162424632137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1392719941936108283088091 2089079912904162424632137)
        ·
          refine ⟨1566809934678121818474103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2089079912904162424632137 1566809934678121818474103)
          ·
            refine ⟨2350214902017182727711155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1566809934678121818474103 2350214902017182727711155)
            ·
              refine ⟨3525322353025774091566733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2350214902017182727711155 3525322353025774091566733)
              ·
                refine ⟨1321995882384665284337525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3525322353025774091566733 1321995882384665284337525)
                ·
                  refine ⟨123937113973562370406643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1321995882384665284337525 123937113973562370406643)
                  ·
                    rfl

theorem cell22_1086150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 1, 3, 5].length) (baseStart_1086150 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1086150 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1086150 prefixEnd_1086150 := by exact prefixLift 1086150
  have htrace : WordTrace (prefixWord ++ tailWord_1086150) baseStart_1086150 baseEnd_1086150 := by
    simpa [prefixWord, tailWord_1086150, baseEnd_1086150] using wordTrace_append hprefix tailTrace_1086150
  have hstable : (prefixWord ++ tailWord_1086150).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1086150).length < 2 ^ (prefixWord ++ tailWord_1086150).sum := by decide
  have hdescent : baseEnd_1086150 < baseStart_1086150 := by decide
  rcases family_descends (prefixWord ++ tailWord_1086150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1086206 : List Nat := [4, 2, 2, 1, 2, 1, 3, 7]
def baseStart_1086206 : Nat := 118140960795 + 1086206 * 2 ^ 59
def prefixEnd_1086206 : Nat := 4983230072969 + 3 ^ 40 * 1086206 * 2
def baseEnd_1086206 : Nat := 41314501318346847979973

theorem tailTrace_1086206 : CollatzResearch.WordTrace tailWord_1086206 prefixEnd_1086206 41314501318346847979973 := by
  unfold tailWord_1086206
  simp only [CollatzResearch.WordTrace]
  refine ⟨4952148437858580757595809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26411458335245764040510981 4952148437858580757595809)
  ·
    refine ⟨3714111328393935568196857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4952148437858580757595809 3714111328393935568196857)
    ·
      refine ⟨2785583496295451676147643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3714111328393935568196857 2785583496295451676147643)
      ·
        refine ⟨4178375244443177514221465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2785583496295451676147643 4178375244443177514221465)
        ·
          refine ⟨3133781433332383135666099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4178375244443177514221465 3133781433332383135666099)
          ·
            refine ⟨4700672149998574703499149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3133781433332383135666099 4700672149998574703499149)
            ·
              refine ⟨1762752056249465513812181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4700672149998574703499149 1762752056249465513812181)
              ·
                refine ⟨41314501318346847979973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1762752056249465513812181 41314501318346847979973)
                ·
                  rfl

theorem cell22_1086206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 3, 7].length) (baseStart_1086206 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1086206 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1086206 prefixEnd_1086206 := by exact prefixLift 1086206
  have htrace : WordTrace (prefixWord ++ tailWord_1086206) baseStart_1086206 baseEnd_1086206 := by
    simpa [prefixWord, tailWord_1086206, baseEnd_1086206] using wordTrace_append hprefix tailTrace_1086206
  have hstable : (prefixWord ++ tailWord_1086206).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1086206).length < 2 ^ (prefixWord ++ tailWord_1086206).sum := by decide
  have hdescent : baseEnd_1086206 < baseStart_1086206 := by decide
  rcases family_descends (prefixWord ++ tailWord_1086206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1086234 : List Nat := [3, 1, 1, 3, 2, 1, 2, 2, 7]
def baseStart_1086234 : Nat := 118140960795 + 1086234 * 2 ^ 59
def prefixEnd_1086234 : Nat := 4983230072969 + 3 ^ 40 * 1086234 * 2
def baseEnd_1086234 : Nat := 123946698945779630706557

theorem tailTrace_1086234 : CollatzResearch.WordTrace tailWord_1086234 prefixEnd_1086234 123946698945779630706557 := by
  unfold tailWord_1086234
  simp only [CollatzResearch.WordTrace]
  refine ⟨9904552186691801710696439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26412139164511471228523837 9904552186691801710696439)
  ·
    refine ⟨14856828280037702566044659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9904552186691801710696439 14856828280037702566044659)
    ·
      refine ⟨22285242420056553849066989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14856828280037702566044659 22285242420056553849066989)
      ·
        refine ⟨8356965907521207693400121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22285242420056553849066989 8356965907521207693400121)
        ·
          refine ⟨6267724430640905770050091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8356965907521207693400121 6267724430640905770050091)
          ·
            refine ⟨9401586645961358655075137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6267724430640905770050091 9401586645961358655075137)
            ·
              refine ⟨7051189984471018991306353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9401586645961358655075137 7051189984471018991306353)
              ·
                refine ⟨5288392488353264243479765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7051189984471018991306353 5288392488353264243479765)
                ·
                  refine ⟨123946698945779630706557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5288392488353264243479765 123946698945779630706557)
                  ·
                    rfl

theorem cell22_1086234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 2, 2, 7].length) (baseStart_1086234 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1086234 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1086234 prefixEnd_1086234 := by exact prefixLift 1086234
  have htrace : WordTrace (prefixWord ++ tailWord_1086234) baseStart_1086234 baseEnd_1086234 := by
    simpa [prefixWord, tailWord_1086234, baseEnd_1086234] using wordTrace_append hprefix tailTrace_1086234
  have hstable : (prefixWord ++ tailWord_1086234).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1086234).length < 2 ^ (prefixWord ++ tailWord_1086234).sum := by decide
  have hdescent : baseEnd_1086234 < baseStart_1086234 := by decide
  rcases family_descends (prefixWord ++ tailWord_1086234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1086281 : List Nat := [1, 2, 1, 1, 2, 5, 1, 4, 1, 4]
def baseStart_1086281 : Nat := 118140960795 + 1086281 * 2 ^ 59
def prefixEnd_1086281 : Nat := 4983230072969 + 3 ^ 40 * 1086281 * 2
def baseEnd_1086281 : Nat := 371856185897846436194527

theorem tailTrace_1086281 : CollatzResearch.WordTrace tailWord_1086281 prefixEnd_1086281 371856185897846436194527 := by
  unfold tailWord_1086281
  simp only [CollatzResearch.WordTrace]
  refine ⟨39619922977596933869746697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26413281985064622579831131 39619922977596933869746697)
  ·
    refine ⟨29714942233197700402310023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39619922977596933869746697 29714942233197700402310023)
    ·
      refine ⟨44572413349796550603465035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29714942233197700402310023 44572413349796550603465035)
      ·
        refine ⟨66858620024694825905197553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44572413349796550603465035 66858620024694825905197553)
        ·
          refine ⟨50143965018521119428898165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66858620024694825905197553 50143965018521119428898165)
          ·
            refine ⟨4700996720486354946459203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 50143965018521119428898165 4700996720486354946459203)
            ·
              refine ⟨7051495080729532419688805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4700996720486354946459203 7051495080729532419688805)
              ·
                refine ⟨1322155327636787328691651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7051495080729532419688805 1322155327636787328691651)
                ·
                  refine ⟨1983232991455180993037477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1322155327636787328691651 1983232991455180993037477)
                  ·
                    refine ⟨371856185897846436194527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1983232991455180993037477 371856185897846436194527)
                    ·
                      rfl

theorem cell22_1086281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 1, 4, 1, 4].length) (baseStart_1086281 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1086281 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1086281 prefixEnd_1086281 := by exact prefixLift 1086281
  have htrace : WordTrace (prefixWord ++ tailWord_1086281) baseStart_1086281 baseEnd_1086281 := by
    simpa [prefixWord, tailWord_1086281, baseEnd_1086281] using wordTrace_append hprefix tailTrace_1086281
  have hstable : (prefixWord ++ tailWord_1086281).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1086281).length < 2 ^ (prefixWord ++ tailWord_1086281).sum := by decide
  have hdescent : baseEnd_1086281 < baseStart_1086281 := by decide
  rcases family_descends (prefixWord ++ tailWord_1086281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1086343 : List Nat := [1, 1, 4, 2, 3, 2, 2, 1, 2, 4]
def baseStart_1086343 : Nat := 118140960795 + 1086343 * 2 ^ 59
def prefixEnd_1086343 : Nat := 4983230072969 + 3 ^ 40 * 1086343 * 2
def baseEnd_1086343 : Nat := 371877409764898941144337

theorem tailTrace_1086343 : CollatzResearch.WordTrace tailWord_1086343 prefixEnd_1086343 371877409764898941144337 := by
  unfold tailWord_1086343
  simp only [CollatzResearch.WordTrace]
  refine ⟨39622184303372318458503683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26414789535581545639002455 39622184303372318458503683)
  ·
    refine ⟨59433276455058477687755525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39622184303372318458503683 59433276455058477687755525)
    ·
      refine ⟨11143739335323464566454161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 59433276455058477687755525 11143739335323464566454161)
      ·
        refine ⟨8357804501492598424840621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11143739335323464566454161 8357804501492598424840621)
        ·
          refine ⟨3134176688059724409315233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8357804501492598424840621 3134176688059724409315233)
          ·
            refine ⟨2350632516044793306986425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3134176688059724409315233 2350632516044793306986425)
            ·
              refine ⟨1762974387033594980239819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2350632516044793306986425 1762974387033594980239819)
              ·
                refine ⟨2644461580550392470359729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1762974387033594980239819 2644461580550392470359729)
                ·
                  refine ⟨1983346185412794352769797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2644461580550392470359729 1983346185412794352769797)
                  ·
                    refine ⟨371877409764898941144337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1983346185412794352769797 371877409764898941144337)
                    ·
                      rfl

theorem cell22_1086343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 2, 1, 2, 4].length) (baseStart_1086343 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1086343 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1086343 prefixEnd_1086343 := by exact prefixLift 1086343
  have htrace : WordTrace (prefixWord ++ tailWord_1086343) baseStart_1086343 baseEnd_1086343 := by
    simpa [prefixWord, tailWord_1086343, baseEnd_1086343] using wordTrace_append hprefix tailTrace_1086343
  have hstable : (prefixWord ++ tailWord_1086343).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1086343).length < 2 ^ (prefixWord ++ tailWord_1086343).sum := by decide
  have hdescent : baseEnd_1086343 < baseStart_1086343 := by decide
  rcases family_descends (prefixWord ++ tailWord_1086343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1086364 : List Nat := [2, 2, 3, 3, 3, 1, 2, 2, 4]
def baseStart_1086364 : Nat := 118140960795 + 1086364 * 2 ^ 59
def prefixEnd_1086364 : Nat := 4983230072969 + 3 ^ 40 * 1086364 * 2
def baseEnd_1086364 : Nat := 123961532831353962123091

theorem tailTrace_1086364 : CollatzResearch.WordTrace tailWord_1086364 prefixEnd_1086364 123961532831353962123091 := by
  unfold tailWord_1086364
  simp only [CollatzResearch.WordTrace]
  refine ⟨19811475118148119522509073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26415300157530826030012097 19811475118148119522509073)
  ·
    refine ⟨14858606338611089641881805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19811475118148119522509073 14858606338611089641881805)
    ·
      refine ⟨5571977376979158615705677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14858606338611089641881805 5571977376979158615705677)
      ·
        refine ⟨2089491516367184480889629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5571977376979158615705677 2089491516367184480889629)
        ·
          refine ⟨783559318637694180333611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2089491516367184480889629 783559318637694180333611)
          ·
            refine ⟨1175338977956541270500417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 783559318637694180333611 1175338977956541270500417)
            ·
              refine ⟨881504233467405952875313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1175338977956541270500417 881504233467405952875313)
              ·
                refine ⟨661128175100554464656485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 881504233467405952875313 661128175100554464656485)
                ·
                  refine ⟨123961532831353962123091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 661128175100554464656485 123961532831353962123091)
                  ·
                    rfl

theorem cell22_1086364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 3, 1, 2, 2, 4].length) (baseStart_1086364 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1086364 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1086364 prefixEnd_1086364 := by exact prefixLift 1086364
  have htrace : WordTrace (prefixWord ++ tailWord_1086364) baseStart_1086364 baseEnd_1086364 := by
    simpa [prefixWord, tailWord_1086364, baseEnd_1086364] using wordTrace_append hprefix tailTrace_1086364
  have hstable : (prefixWord ++ tailWord_1086364).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1086364).length < 2 ^ (prefixWord ++ tailWord_1086364).sum := by decide
  have hdescent : baseEnd_1086364 < baseStart_1086364 := by decide
  rcases family_descends (prefixWord ++ tailWord_1086364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1086375 : List Nat := [1, 1, 6, 1, 4, 1, 1, 7]
def baseStart_1086375 : Nat := 118140960795 + 1086375 * 2 ^ 59
def prefixEnd_1086375 : Nat := 4983230072969 + 3 ^ 40 * 1086375 * 2
def baseEnd_1086375 : Nat := 41320929335429058260471

theorem tailTrace_1086375 : CollatzResearch.WordTrace tailWord_1086375 prefixEnd_1086375 41320929335429058260471 := by
  unfold tailWord_1086375
  simp only [CollatzResearch.WordTrace]
  refine ⟨39623351439256387923668579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26415567626170925282445719 39623351439256387923668579)
  ·
    refine ⟨59435027158884581885502869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39623351439256387923668579 59435027158884581885502869)
    ·
      refine ⟨2786016898072714775882947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 59435027158884581885502869 2786016898072714775882947)
      ·
        refine ⟨4179025347109072163824421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2786016898072714775882947 4179025347109072163824421)
        ·
          refine ⟨783567252582951030717079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4179025347109072163824421 783567252582951030717079)
          ·
            refine ⟨1175350878874426546075619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 783567252582951030717079 1175350878874426546075619)
            ·
              refine ⟨1763026318311639819113429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1175350878874426546075619 1763026318311639819113429)
              ·
                refine ⟨41320929335429058260471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1763026318311639819113429 41320929335429058260471)
                ·
                  rfl

theorem cell22_1086375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 4, 1, 1, 7].length) (baseStart_1086375 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1086375 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1086375 prefixEnd_1086375 := by exact prefixLift 1086375
  have htrace : WordTrace (prefixWord ++ tailWord_1086375) baseStart_1086375 baseEnd_1086375 := by
    simpa [prefixWord, tailWord_1086375, baseEnd_1086375] using wordTrace_append hprefix tailTrace_1086375
  have hstable : (prefixWord ++ tailWord_1086375).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1086375).length < 2 ^ (prefixWord ++ tailWord_1086375).sum := by decide
  have hdescent : baseEnd_1086375 < baseStart_1086375 := by decide
  rcases family_descends (prefixWord ++ tailWord_1086375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1086413 : List Nat := [1, 6, 3, 1, 2, 1, 1, 2, 2, 3]
def baseStart_1086413 : Nat := 118140960795 + 1086413 * 2 ^ 59
def prefixEnd_1086413 : Nat := 4983230072969 + 3 ^ 40 * 1086413 * 2
def baseEnd_1086413 : Nat := 371901372195442091894123

theorem tailTrace_1086413 : CollatzResearch.WordTrace tailWord_1086413 prefixEnd_1086413 371901372195442091894123 := by
  unfold tailWord_1086413
  simp only [CollatzResearch.WordTrace]
  refine ⟨39624737413118720413551893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26416491608745813609034595 39624737413118720413551893)
  ·
    refine ⟨1857409566239940019385245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 39624737413118720413551893 1857409566239940019385245)
    ·
      refine ⟨696528587339977507269467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1857409566239940019385245 696528587339977507269467)
      ·
        refine ⟨1044792881009966260904201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 696528587339977507269467 1044792881009966260904201)
        ·
          refine ⟨783594660757474695678151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1044792881009966260904201 783594660757474695678151)
          ·
            refine ⟨1175391991136212043517227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 783594660757474695678151 1175391991136212043517227)
            ·
              refine ⟨1763087986704318065275841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1175391991136212043517227 1763087986704318065275841)
              ·
                refine ⟨1322315990028238548956881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1763087986704318065275841 1322315990028238548956881)
                ·
                  refine ⟨991736992521178911717661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1322315990028238548956881 991736992521178911717661)
                  ·
                    refine ⟨371901372195442091894123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 991736992521178911717661 371901372195442091894123)
                    ·
                      rfl

theorem cell22_1086413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 2, 1, 1, 2, 2, 3].length) (baseStart_1086413 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1086413 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1086413 prefixEnd_1086413 := by exact prefixLift 1086413
  have htrace : WordTrace (prefixWord ++ tailWord_1086413) baseStart_1086413 baseEnd_1086413 := by
    simpa [prefixWord, tailWord_1086413, baseEnd_1086413] using wordTrace_append hprefix tailTrace_1086413
  have hstable : (prefixWord ++ tailWord_1086413).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1086413).length < 2 ^ (prefixWord ++ tailWord_1086413).sum := by decide
  have hdescent : baseEnd_1086413 < baseStart_1086413 := by decide
  rcases family_descends (prefixWord ++ tailWord_1086413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1086418 : List Nat := [3, 2, 2, 3, 1, 1, 1, 2, 2, 5]
def baseStart_1086418 : Nat := 118140960795 + 1086418 * 2 ^ 59
def prefixEnd_1086418 : Nat := 4983230072969 + 3 ^ 40 * 1086418 * 2
def baseEnd_1086418 : Nat := 371903083797623745519107

theorem tailTrace_1086418 : CollatzResearch.WordTrace tailWord_1086418 prefixEnd_1086418 371903083797623745519107 := by
  unfold tailWord_1086418
  simp only [CollatzResearch.WordTrace]
  refine ⟨9906229944525151566870977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26416613185400404178322605 9906229944525151566870977)
  ·
    refine ⟨7429672458393863675153233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9906229944525151566870977 7429672458393863675153233)
    ·
      refine ⟨5572254343795397756364925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7429672458393863675153233 5572254343795397756364925)
      ·
        refine ⟨2089595378923274158636847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5572254343795397756364925 2089595378923274158636847)
        ·
          refine ⟨3134393068384911237955271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2089595378923274158636847 3134393068384911237955271)
          ·
            refine ⟨4701589602577366856932907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3134393068384911237955271 4701589602577366856932907)
            ·
              refine ⟨7052384403866050285399361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4701589602577366856932907 7052384403866050285399361)
              ·
                refine ⟨5289288302899537714049521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7052384403866050285399361 5289288302899537714049521)
                ·
                  refine ⟨3966966227174653285537141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5289288302899537714049521 3966966227174653285537141)
                  ·
                    refine ⟨371903083797623745519107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3966966227174653285537141 371903083797623745519107)
                    ·
                      rfl

theorem cell22_1086418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 1, 2, 2, 5].length) (baseStart_1086418 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1086418 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1086418 prefixEnd_1086418 := by exact prefixLift 1086418
  have htrace : WordTrace (prefixWord ++ tailWord_1086418) baseStart_1086418 baseEnd_1086418 := by
    simpa [prefixWord, tailWord_1086418, baseEnd_1086418] using wordTrace_append hprefix tailTrace_1086418
  have hstable : (prefixWord ++ tailWord_1086418).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1086418).length < 2 ^ (prefixWord ++ tailWord_1086418).sum := by decide
  have hdescent : baseEnd_1086418 < baseStart_1086418 := by decide
  rcases family_descends (prefixWord ++ tailWord_1086418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1086420 : List Nat := [2, 4, 1, 2, 1, 4, 1, 2, 5]
def baseStart_1086420 : Nat := 118140960795 + 1086420 * 2 ^ 59
def prefixEnd_1086420 : Nat := 4983230072969 + 3 ^ 40 * 1086420 * 2
def baseEnd_1086420 : Nat := 123967922812832135656367

theorem tailTrace_1086420 : CollatzResearch.WordTrace tailWord_1086420 prefixEnd_1086420 123967922812832135656367 := by
  unfold tailWord_1086420
  simp only [CollatzResearch.WordTrace]
  refine ⟨19812496362046680304528357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26416661816062240406037809 19812496362046680304528357)
  ·
    refine ⟨3714843067883752557099067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19812496362046680304528357 3714843067883752557099067)
    ·
      refine ⟨5572264601825628835648601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3714843067883752557099067 5572264601825628835648601)
      ·
        refine ⟨4179198451369221626736451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5572264601825628835648601 4179198451369221626736451)
        ·
          refine ⟨6268797677053832440104677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4179198451369221626736451 6268797677053832440104677)
          ·
            refine ⟨1175399564447593582519627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6268797677053832440104677 1175399564447593582519627)
            ·
              refine ⟨1763099346671390373779441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1175399564447593582519627 1763099346671390373779441)
              ·
                refine ⟨1322324510003542780334581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1763099346671390373779441 1322324510003542780334581)
                ·
                  refine ⟨123967922812832135656367, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1322324510003542780334581 123967922812832135656367)
                  ·
                    rfl

theorem cell22_1086420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 4, 1, 2, 5].length) (baseStart_1086420 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1086420 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1086420 prefixEnd_1086420 := by exact prefixLift 1086420
  have htrace : WordTrace (prefixWord ++ tailWord_1086420) baseStart_1086420 baseEnd_1086420 := by
    simpa [prefixWord, tailWord_1086420, baseEnd_1086420] using wordTrace_append hprefix tailTrace_1086420
  have hstable : (prefixWord ++ tailWord_1086420).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1086420).length < 2 ^ (prefixWord ++ tailWord_1086420).sum := by decide
  have hdescent : baseEnd_1086420 < baseStart_1086420 := by decide
  rcases family_descends (prefixWord ++ tailWord_1086420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1086437 : List Nat := [1, 3, 1, 6, 1, 1, 3, 1, 5]
def baseStart_1086437 : Nat := 118140960795 + 1086437 * 2 ^ 59
def prefixEnd_1086437 : Nat := 4983230072969 + 3 ^ 40 * 1086437 * 2
def baseEnd_1086437 : Nat := 123969862628638009764683

theorem tailTrace_1086437 : CollatzResearch.WordTrace tailWord_1086437 prefixEnd_1086437 123969862628638009764683 := by
  unfold tailWord_1086437
  simp only [CollatzResearch.WordTrace]
  refine ⟨39625612765031772512425565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26417075176687848341617043 39625612765031772512425565)
  ·
    refine ⟨14859604786886914692159587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39625612765031772512425565 14859604786886914692159587)
    ·
      refine ⟨22289407180330372038239381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14859604786886914692159587 22289407180330372038239381)
      ·
        refine ⟨1044815961577986189292471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 22289407180330372038239381 1044815961577986189292471)
        ·
          refine ⟨1567223942366979283938707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1044815961577986189292471 1567223942366979283938707)
          ·
            refine ⟨2350835913550468925908061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1567223942366979283938707 2350835913550468925908061)
            ·
              refine ⟨881563467581425847215523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2350835913550468925908061 881563467581425847215523)
              ·
                refine ⟨1322345201372138770823285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 881563467581425847215523 1322345201372138770823285)
                ·
                  refine ⟨123969862628638009764683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1322345201372138770823285 123969862628638009764683)
                  ·
                    rfl

theorem cell22_1086437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 3, 1, 5].length) (baseStart_1086437 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1086437 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1086437 prefixEnd_1086437 := by exact prefixLift 1086437
  have htrace : WordTrace (prefixWord ++ tailWord_1086437) baseStart_1086437 baseEnd_1086437 := by
    simpa [prefixWord, tailWord_1086437, baseEnd_1086437] using wordTrace_append hprefix tailTrace_1086437
  have hstable : (prefixWord ++ tailWord_1086437).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1086437).length < 2 ^ (prefixWord ++ tailWord_1086437).sum := by decide
  have hdescent : baseEnd_1086437 < baseStart_1086437 := by decide
  rcases family_descends (prefixWord ++ tailWord_1086437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1086465 : List Nat := [1, 2, 4, 1, 2, 2, 3, 3, 4]
def baseStart_1086465 : Nat := 118140960795 + 1086465 * 2 ^ 59
def prefixEnd_1086465 : Nat := 4983230072969 + 3 ^ 40 * 1086465 * 2
def baseEnd_1086465 : Nat := 123973057619377096531321

theorem tailTrace_1086465 : CollatzResearch.WordTrace tailWord_1086465 prefixEnd_1086465 123973057619377096531321 := by
  unfold tailWord_1086465
  simp only [CollatzResearch.WordTrace]
  refine ⟨39626634008930333294444849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26417756005953555529629899 39626634008930333294444849)
  ·
    refine ⟨29719975506697749970833637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39626634008930333294444849 29719975506697749970833637)
    ·
      refine ⟨5572495407505828119531307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29719975506697749970833637 5572495407505828119531307)
      ·
        refine ⟨8358743111258742179296961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5572495407505828119531307 8358743111258742179296961)
        ·
          refine ⟨6269057333444056634472721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8358743111258742179296961 6269057333444056634472721)
          ·
            refine ⟨4701793000083042475854541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6269057333444056634472721 4701793000083042475854541)
            ·
              refine ⟨1763172375031140928445453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4701793000083042475854541 1763172375031140928445453)
              ·
                refine ⟨661189640636677848167045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1763172375031140928445453 661189640636677848167045)
                ·
                  refine ⟨123973057619377096531321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 661189640636677848167045 123973057619377096531321)
                  ·
                    rfl

theorem cell22_1086465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 3, 3, 4].length) (baseStart_1086465 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1086465 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1086465 prefixEnd_1086465 := by exact prefixLift 1086465
  have htrace : WordTrace (prefixWord ++ tailWord_1086465) baseStart_1086465 baseEnd_1086465 := by
    simpa [prefixWord, tailWord_1086465, baseEnd_1086465] using wordTrace_append hprefix tailTrace_1086465
  have hstable : (prefixWord ++ tailWord_1086465).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1086465).length < 2 ^ (prefixWord ++ tailWord_1086465).sum := by decide
  have hdescent : baseEnd_1086465 < baseStart_1086465 := by decide
  rcases family_descends (prefixWord ++ tailWord_1086465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1086476 : List Nat := [2, 2, 1, 2, 3, 2, 10]
def baseStart_1086476 : Nat := 118140960795 + 1086476 * 2 ^ 59
def prefixEnd_1086476 : Nat := 4983230072969 + 3 ^ 40 * 1086476 * 2
def baseEnd_1086476 : Nat := 13774923643812256576627

theorem tailTrace_1086476 : CollatzResearch.WordTrace tailWord_1086476 prefixEnd_1086476 13774923643812256576627 := by
  unfold tailWord_1086476
  simp only [CollatzResearch.WordTrace]
  refine ⟨19813517605945241086547641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26418023474593654782063521 19813517605945241086547641)
  ·
    refine ⟨14860138204458930814910731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19813517605945241086547641 14860138204458930814910731)
    ·
      refine ⟨22290207306688396222366097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14860138204458930814910731 22290207306688396222366097)
      ·
        refine ⟨16717655480016297166774573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22290207306688396222366097 16717655480016297166774573)
        ·
          refine ⟨6269120805006111437540465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16717655480016297166774573 6269120805006111437540465)
          ·
            refine ⟨4701840603754583578155349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6269120805006111437540465 4701840603754583578155349)
            ·
              refine ⟨13774923643812256576627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 4701840603754583578155349 13774923643812256576627)
              ·
                rfl

theorem cell22_1086476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 10].length) (baseStart_1086476 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1086476 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1086476 prefixEnd_1086476 := by exact prefixLift 1086476
  have htrace : WordTrace (prefixWord ++ tailWord_1086476) baseStart_1086476 baseEnd_1086476 := by
    simpa [prefixWord, tailWord_1086476, baseEnd_1086476] using wordTrace_append hprefix tailTrace_1086476
  have hstable : (prefixWord ++ tailWord_1086476).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1086476).length < 2 ^ (prefixWord ++ tailWord_1086476).sum := by decide
  have hdescent : baseEnd_1086476 < baseStart_1086476 := by decide
  rcases family_descends (prefixWord ++ tailWord_1086476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1086478 : List Nat := [4, 1, 1, 2, 2, 2, 1, 1, 4, 4]
def baseStart_1086478 : Nat := 118140960795 + 1086478 * 2 ^ 59
def prefixEnd_1086478 : Nat := 4983230072969 + 3 ^ 40 * 1086478 * 2
def baseEnd_1086478 : Nat := 371923623023803589018923

theorem tailTrace_1086478 : CollatzResearch.WordTrace tailWord_1086478 prefixEnd_1086478 371923623023803589018923 := by
  unfold tailWord_1086478
  simp only [CollatzResearch.WordTrace]
  refine ⟨4953388519735404564333511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26418072105255491009778725 4953388519735404564333511)
  ·
    refine ⟨7430082779603106846500267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4953388519735404564333511 7430082779603106846500267)
    ·
      refine ⟨11145124169404660269750401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7430082779603106846500267 11145124169404660269750401)
      ·
        refine ⟨8358843127053495202312801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11145124169404660269750401 8358843127053495202312801)
        ·
          refine ⟨6269132345290121401734601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8358843127053495202312801 6269132345290121401734601)
          ·
            refine ⟨4701849258967591051300951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6269132345290121401734601 4701849258967591051300951)
            ·
              refine ⟨7052773888451386576951427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4701849258967591051300951 7052773888451386576951427)
              ·
                refine ⟨10579160832677079865427141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7052773888451386576951427 10579160832677079865427141)
                ·
                  refine ⟨1983592656126952474767589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10579160832677079865427141 1983592656126952474767589)
                  ·
                    refine ⟨371923623023803589018923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1983592656126952474767589 371923623023803589018923)
                    ·
                      rfl

theorem cell22_1086478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 1, 1, 4, 4].length) (baseStart_1086478 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1086478 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1086478 prefixEnd_1086478 := by exact prefixLift 1086478
  have htrace : WordTrace (prefixWord ++ tailWord_1086478) baseStart_1086478 baseEnd_1086478 := by
    simpa [prefixWord, tailWord_1086478, baseEnd_1086478] using wordTrace_append hprefix tailTrace_1086478
  have hstable : (prefixWord ++ tailWord_1086478).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1086478).length < 2 ^ (prefixWord ++ tailWord_1086478).sum := by decide
  have hdescent : baseEnd_1086478 < baseStart_1086478 := by decide
  rcases family_descends (prefixWord ++ tailWord_1086478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1086497 : List Nat := [1, 2, 3, 2, 3, 1, 4, 1, 2, 3]
def baseStart_1086497 : Nat := 118140960795 + 1086497 * 2 ^ 59
def prefixEnd_1086497 : Nat := 4983230072969 + 3 ^ 40 * 1086497 * 2
def baseEnd_1086497 : Nat := 371930127112093872793865

theorem tailTrace_1086497 : CollatzResearch.WordTrace tailWord_1086497 prefixEnd_1086497 371930127112093872793865 := by
  unfold tailWord_1086497
  simp only [CollatzResearch.WordTrace]
  refine ⟨39627801144814402759609745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26418534096542935173073163 39627801144814402759609745)
  ·
    refine ⟨29720850858610802069707309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39627801144814402759609745 29720850858610802069707309)
    ·
      refine ⟨11145319071979050776140241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29720850858610802069707309 11145319071979050776140241)
      ·
        refine ⟨8358989303984288082105181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11145319071979050776140241 8358989303984288082105181)
        ·
          refine ⟨3134620988994108030789443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8358989303984288082105181 3134620988994108030789443)
          ·
            refine ⟨4701931483491162046184165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3134620988994108030789443 4701931483491162046184165)
            ·
              refine ⟨881612153154592883659531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4701931483491162046184165 881612153154592883659531)
              ·
                refine ⟨1322418229731889325489297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 881612153154592883659531 1322418229731889325489297)
                ·
                  refine ⟨991813672298916994116973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1322418229731889325489297 991813672298916994116973)
                  ·
                    refine ⟨371930127112093872793865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 991813672298916994116973 371930127112093872793865)
                    ·
                      rfl

theorem cell22_1086497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 4, 1, 2, 3].length) (baseStart_1086497 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1086497 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1086497 prefixEnd_1086497 := by exact prefixLift 1086497
  have htrace : WordTrace (prefixWord ++ tailWord_1086497) baseStart_1086497 baseEnd_1086497 := by
    simpa [prefixWord, tailWord_1086497, baseEnd_1086497] using wordTrace_append hprefix tailTrace_1086497
  have hstable : (prefixWord ++ tailWord_1086497).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1086497).length < 2 ^ (prefixWord ++ tailWord_1086497).sum := by decide
  have hdescent : baseEnd_1086497 < baseStart_1086497 := by decide
  rcases family_descends (prefixWord ++ tailWord_1086497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1086508 : List Nat := [2, 2, 1, 1, 1, 2, 4, 1, 5, 3]
def baseStart_1086508 : Nat := 118140960795 + 1086508 * 2 ^ 59
def prefixEnd_1086508 : Nat := 4983230072969 + 3 ^ 40 * 1086508 * 2
def baseEnd_1086508 : Nat := 371933892636893510768831

theorem tailTrace_1086508 : CollatzResearch.WordTrace tailWord_1086508 prefixEnd_1086508 371933892636893510768831 := by
  unfold tailWord_1086508
  simp only [CollatzResearch.WordTrace]
  refine ⟨19814101173887275819130089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26418801565183034425506785 19814101173887275819130089)
  ·
    refine ⟨14860575880415456864347567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19814101173887275819130089 14860575880415456864347567)
    ·
      refine ⟨22290863820623185296521351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14860575880415456864347567 22290863820623185296521351)
      ·
        refine ⟨33436295730934777944782027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22290863820623185296521351 33436295730934777944782027)
        ·
          refine ⟨50154443596402166917173041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33436295730934777944782027 50154443596402166917173041)
          ·
            refine ⟨37615832697301625187879781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50154443596402166917173041 37615832697301625187879781)
            ·
              refine ⟨7052968630744054722727459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 37615832697301625187879781 7052968630744054722727459)
              ·
                refine ⟨10579452946116082084091189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7052968630744054722727459 10579452946116082084091189)
                ·
                  refine ⟨991823713698382695383549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 10579452946116082084091189 991823713698382695383549)
                  ·
                    refine ⟨371933892636893510768831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 991823713698382695383549 371933892636893510768831)
                    ·
                      rfl

theorem cell22_1086508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 5, 3].length) (baseStart_1086508 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1086508 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1086508 prefixEnd_1086508 := by exact prefixLift 1086508
  have htrace : WordTrace (prefixWord ++ tailWord_1086508) baseStart_1086508 baseEnd_1086508 := by
    simpa [prefixWord, tailWord_1086508, baseEnd_1086508] using wordTrace_append hprefix tailTrace_1086508
  have hstable : (prefixWord ++ tailWord_1086508).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1086508).length < 2 ^ (prefixWord ++ tailWord_1086508).sum := by decide
  have hdescent : baseEnd_1086508 < baseStart_1086508 := by decide
  rcases family_descends (prefixWord ++ tailWord_1086508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1086538 : List Nat := [3, 1, 2, 1, 1, 2, 3, 4, 5]
def baseStart_1086538 : Nat := 118140960795 + 1086538 * 2 ^ 59
def prefixEnd_1086538 : Nat := 4983230072969 + 3 ^ 40 * 1086538 * 2
def baseEnd_1086538 : Nat := 123981387416661144172913

theorem tailTrace_1086538 : CollatzResearch.WordTrace tailWord_1086538 prefixEnd_1086538 123981387416661144172913 := by
  unfold tailWord_1086538
  simp only [CollatzResearch.WordTrace]
  refine ⟨9907324134416466690463067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26419531025110577841234845 9907324134416466690463067)
  ·
    refine ⟨14860986201624700035694601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9907324134416466690463067 14860986201624700035694601)
    ·
      refine ⟨11145739651218525026770951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14860986201624700035694601 11145739651218525026770951)
      ·
        refine ⟨16718609476827787540156427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11145739651218525026770951 16718609476827787540156427)
        ·
          refine ⟨25077914215241681310234641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16718609476827787540156427 25077914215241681310234641)
          ·
            refine ⟨18808435661431260982675981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25077914215241681310234641 18808435661431260982675981)
            ·
              refine ⟨7053163373036722868503493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18808435661431260982675981 7053163373036722868503493)
              ·
                refine ⟨1322468132444385537844405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7053163373036722868503493 1322468132444385537844405)
                ·
                  refine ⟨123981387416661144172913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1322468132444385537844405 123981387416661144172913)
                  ·
                    rfl

theorem cell22_1086538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 3, 4, 5].length) (baseStart_1086538 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1086538 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1086538 prefixEnd_1086538 := by exact prefixLift 1086538
  have htrace : WordTrace (prefixWord ++ tailWord_1086538) baseStart_1086538 baseEnd_1086538 := by
    simpa [prefixWord, tailWord_1086538, baseEnd_1086538] using wordTrace_append hprefix tailTrace_1086538
  have hstable : (prefixWord ++ tailWord_1086538).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1086538).length < 2 ^ (prefixWord ++ tailWord_1086538).sum := by decide
  have hdescent : baseEnd_1086538 < baseStart_1086538 := by decide
  rcases family_descends (prefixWord ++ tailWord_1086538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1086542 : List Nat := [4, 1, 1, 1, 1, 3, 3, 4, 1, 3]
def baseStart_1086542 : Nat := 118140960795 + 1086542 * 2 ^ 59
def prefixEnd_1086542 : Nat := 4983230072969 + 3 ^ 40 * 1086542 * 2
def baseEnd_1086542 : Nat := 371945531531728755418727

theorem tailTrace_1086542 : CollatzResearch.WordTrace tailWord_1086542 prefixEnd_1086542 371945531531728755418727 := by
  unfold tailWord_1086542
  simp only [CollatzResearch.WordTrace]
  refine ⟨4953680303706421930624735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26419628286434250296665253 4953680303706421930624735)
  ·
    refine ⟨7430520455559632895937103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4953680303706421930624735 7430520455559632895937103)
    ·
      refine ⟨11145780683339449343905655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7430520455559632895937103 11145780683339449343905655)
      ·
        refine ⟨16718671025009174015858483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11145780683339449343905655 16718671025009174015858483)
        ·
          refine ⟨25078006537513761023787725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16718671025009174015858483 25078006537513761023787725)
          ·
            refine ⟨9404252451567660383920397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25078006537513761023787725 9404252451567660383920397)
            ·
              refine ⟨3526594669337872643970149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9404252451567660383920397 3526594669337872643970149)
              ·
                refine ⟨661236500500851120744403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3526594669337872643970149 661236500500851120744403)
                ·
                  refine ⟨991854750751276681116605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 661236500500851120744403 991854750751276681116605)
                  ·
                    refine ⟨371945531531728755418727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 991854750751276681116605 371945531531728755418727)
                    ·
                      rfl

theorem cell22_1086542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 3, 4, 1, 3].length) (baseStart_1086542 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1086542 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1086542 prefixEnd_1086542 := by exact prefixLift 1086542
  have htrace : WordTrace (prefixWord ++ tailWord_1086542) baseStart_1086542 baseEnd_1086542 := by
    simpa [prefixWord, tailWord_1086542, baseEnd_1086542] using wordTrace_append hprefix tailTrace_1086542
  have hstable : (prefixWord ++ tailWord_1086542).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1086542).length < 2 ^ (prefixWord ++ tailWord_1086542).sum := by decide
  have hdescent : baseEnd_1086542 < baseStart_1086542 := by decide
  rcases family_descends (prefixWord ++ tailWord_1086542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1086613 : List Nat := [1, 3, 2, 1, 1, 1, 2, 1, 6, 4]
def baseStart_1086613 : Nat := 118140960795 + 1086613 * 2 ^ 59
def prefixEnd_1086613 : Nat := 4983230072969 + 3 ^ 40 * 1086613 * 2
def baseEnd_1086613 : Nat := 371969836282708236893509

theorem tailTrace_1086613 : CollatzResearch.WordTrace tailWord_1086613 prefixEnd_1086613 371969836282708236893509 := by
  unfold tailWord_1086613
  simp only [CollatzResearch.WordTrace]
  refine ⟨39632032012394154570832493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26421354674929436380554995 39632032012394154570832493)
  ·
    refine ⟨14862012004647807964062185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39632032012394154570832493 14862012004647807964062185)
    ·
      refine ⟨11146509003485855973046639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14862012004647807964062185 11146509003485855973046639)
      ·
        refine ⟨16719763505228783959569959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11146509003485855973046639 16719763505228783959569959)
        ·
          refine ⟨25079645257843175939354939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16719763505228783959569959 25079645257843175939354939)
          ·
            refine ⟨37619467886764763909032409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25079645257843175939354939 37619467886764763909032409)
            ·
              refine ⟨28214600915073572931774307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37619467886764763909032409 28214600915073572931774307)
              ·
                refine ⟨42321901372610359397661461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28214600915073572931774307 42321901372610359397661461)
                ·
                  refine ⟨1983839126841110596765381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 42321901372610359397661461 1983839126841110596765381)
                  ·
                    refine ⟨371969836282708236893509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1983839126841110596765381 371969836282708236893509)
                    ·
                      rfl

theorem cell22_1086613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 1, 6, 4].length) (baseStart_1086613 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1086613 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1086613 prefixEnd_1086613 := by exact prefixLift 1086613
  have htrace : WordTrace (prefixWord ++ tailWord_1086613) baseStart_1086613 baseEnd_1086613 := by
    simpa [prefixWord, tailWord_1086613, baseEnd_1086613] using wordTrace_append hprefix tailTrace_1086613
  have hstable : (prefixWord ++ tailWord_1086613).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1086613).length < 2 ^ (prefixWord ++ tailWord_1086613).sum := by decide
  have hdescent : baseEnd_1086613 < baseStart_1086613 := by decide
  rcases family_descends (prefixWord ++ tailWord_1086613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1086615 : List Nat := [1, 1, 3, 3, 3, 1, 3, 1, 1, 5]
def baseStart_1086615 : Nat := 118140960795 + 1086615 * 2 ^ 59
def prefixEnd_1086615 : Nat := 4983230072969 + 3 ^ 40 * 1086615 * 2
def baseEnd_1086615 : Nat := 371970520923580898343503

theorem tailTrace_1086615 : CollatzResearch.WordTrace tailWord_1086615 prefixEnd_1086615 371970520923580898343503 := by
  unfold tailWord_1086615
  simp only [CollatzResearch.WordTrace]
  refine ⟨39632104958386908912405299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26421403305591272608270199 39632104958386908912405299)
  ·
    refine ⟨59448157437580363368607949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39632104958386908912405299 59448157437580363368607949)
    ·
      refine ⟨22293059039092636263227981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59448157437580363368607949 22293059039092636263227981)
      ·
        refine ⟨8359897139659738598710493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22293059039092636263227981 8359897139659738598710493)
        ·
          refine ⟨3134961427372401974516435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8359897139659738598710493 3134961427372401974516435)
          ·
            refine ⟨4702442141058602961774653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3134961427372401974516435 4702442141058602961774653)
            ·
              refine ⟨1763415802896976110665495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4702442141058602961774653 1763415802896976110665495)
              ·
                refine ⟨2645123704345464165998243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1763415802896976110665495 2645123704345464165998243)
                ·
                  refine ⟨3967685556518196248997365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2645123704345464165998243 3967685556518196248997365)
                  ·
                    refine ⟨371970520923580898343503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3967685556518196248997365 371970520923580898343503)
                    ·
                      rfl

theorem cell22_1086615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 3, 1, 1, 5].length) (baseStart_1086615 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1086615 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1086615 prefixEnd_1086615 := by exact prefixLift 1086615
  have htrace : WordTrace (prefixWord ++ tailWord_1086615) baseStart_1086615 baseEnd_1086615 := by
    simpa [prefixWord, tailWord_1086615, baseEnd_1086615] using wordTrace_append hprefix tailTrace_1086615
  have hstable : (prefixWord ++ tailWord_1086615).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1086615).length < 2 ^ (prefixWord ++ tailWord_1086615).sum := by decide
  have hdescent : baseEnd_1086615 < baseStart_1086615 := by decide
  rcases family_descends (prefixWord ++ tailWord_1086615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1086634 : List Nat := [3, 1, 5, 1, 1, 1, 3, 3, 4]
def baseStart_1086634 : Nat := 118140960795 + 1086634 * 2 ^ 59
def prefixEnd_1086634 : Nat := 4983230072969 + 3 ^ 40 * 1086634 * 2
def baseEnd_1086634 : Nat := 123992341670623727372815

theorem tailTrace_1086634 : CollatzResearch.WordTrace tailWord_1086634 prefixEnd_1086634 123992341670623727372815 := by
  unfold tailWord_1086634
  simp only [CollatzResearch.WordTrace]
  refine ⟨9908199486329518789336739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26421865296878716771564637 9908199486329518789336739)
  ·
    refine ⟨14862299229494278184005109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9908199486329518789336739 14862299229494278184005109)
    ·
      refine ⟨1393340552765088579750479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 14862299229494278184005109 1393340552765088579750479)
      ·
        refine ⟨2090010829147632869625719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1393340552765088579750479 2090010829147632869625719)
        ·
          refine ⟨3135016243721449304438579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2090010829147632869625719 3135016243721449304438579)
          ·
            refine ⟨4702524365582173956657869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3135016243721449304438579 4702524365582173956657869)
            ·
              refine ⟨1763446637093315233746701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4702524365582173956657869 1763446637093315233746701)
              ·
                refine ⟨661292488909993212655013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1763446637093315233746701 661292488909993212655013)
                ·
                  refine ⟨123992341670623727372815, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 661292488909993212655013 123992341670623727372815)
                  ·
                    rfl

theorem cell22_1086634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 3, 3, 4].length) (baseStart_1086634 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1086634 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1086634 prefixEnd_1086634 := by exact prefixLift 1086634
  have htrace : WordTrace (prefixWord ++ tailWord_1086634) baseStart_1086634 baseEnd_1086634 := by
    simpa [prefixWord, tailWord_1086634, baseEnd_1086634] using wordTrace_append hprefix tailTrace_1086634
  have hstable : (prefixWord ++ tailWord_1086634).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1086634).length < 2 ^ (prefixWord ++ tailWord_1086634).sum := by decide
  have hdescent : baseEnd_1086634 < baseStart_1086634 := by decide
  rcases family_descends (prefixWord ++ tailWord_1086634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1086754 : List Nat := [3, 3, 1, 1, 4, 1, 1, 3, 1, 4]
def baseStart_1086754 : Nat := 118140960795 + 1086754 * 2 ^ 59
def prefixEnd_1086754 : Nat := 4983230072969 + 3 ^ 40 * 1086754 * 2
def baseEnd_1086754 : Nat := 372018103464230869118077

theorem tailTrace_1086754 : CollatzResearch.WordTrace tailWord_1086754 prefixEnd_1086754 372018103464230869118077 := by
  unfold tailWord_1086754
  simp only [CollatzResearch.WordTrace]
  refine ⟨9909293676220833912928829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26424783136588890434476877 9909293676220833912928829)
  ·
    refine ⟨3715985128582812717348311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9909293676220833912928829 3715985128582812717348311)
    ·
      refine ⟨5573977692874219076022467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3715985128582812717348311 5573977692874219076022467)
      ·
        refine ⟨8360966539311328614033701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5573977692874219076022467 8360966539311328614033701)
        ·
          refine ⟨1567681226120874115131319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8360966539311328614033701 1567681226120874115131319)
          ·
            refine ⟨2351521839181311172696979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1567681226120874115131319 2351521839181311172696979)
            ·
              refine ⟨3527282758771966759045469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2351521839181311172696979 3527282758771966759045469)
              ·
                refine ⟨1322731034539487534642051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3527282758771966759045469 1322731034539487534642051)
                ·
                  refine ⟨1984096551809231301963077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1322731034539487534642051 1984096551809231301963077)
                  ·
                    refine ⟨372018103464230869118077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1984096551809231301963077 372018103464230869118077)
                    ·
                      rfl

theorem cell22_1086754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 1, 3, 1, 4].length) (baseStart_1086754 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1086754 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1086754 prefixEnd_1086754 := by exact prefixLift 1086754
  have htrace : WordTrace (prefixWord ++ tailWord_1086754) baseStart_1086754 baseEnd_1086754 := by
    simpa [prefixWord, tailWord_1086754, baseEnd_1086754] using wordTrace_append hprefix tailTrace_1086754
  have hstable : (prefixWord ++ tailWord_1086754).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1086754).length < 2 ^ (prefixWord ++ tailWord_1086754).sum := by decide
  have hdescent : baseEnd_1086754 < baseStart_1086754 := by decide
  rcases family_descends (prefixWord ++ tailWord_1086754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1086784 : List Nat := [2, 1, 1, 2, 2, 1, 7, 1, 2, 3]
def baseStart_1086784 : Nat := 118140960795 + 1086784 * 2 ^ 59
def prefixEnd_1086784 : Nat := 4983230072969 + 3 ^ 40 * 1086784 * 2
def baseEnd_1086784 : Nat := 372028373077320790867985

theorem tailTrace_1086784 : CollatzResearch.WordTrace tailWord_1086784 prefixEnd_1086784 372028373077320790867985 := by
  unfold tailWord_1086784
  simp only [CollatzResearch.WordTrace]
  refine ⟨19819134447387325387653703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26425512596516433850204937 19819134447387325387653703)
  ·
    refine ⟨29728701671080988081480555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19819134447387325387653703 29728701671080988081480555)
    ·
      refine ⟨44593052506621482122220833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29728701671080988081480555 44593052506621482122220833)
      ·
        refine ⟨33444789379966111591665625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44593052506621482122220833 33444789379966111591665625)
        ·
          refine ⟨25083592034974583693749219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33444789379966111591665625 25083592034974583693749219)
          ·
            refine ⟨37625388052461875540623829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25083592034974583693749219 37625388052461875540623829)
            ·
              refine ⟨881845032479575207983371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 37625388052461875540623829 881845032479575207983371)
              ·
                refine ⟨1322767548719362811975057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 881845032479575207983371 1322767548719362811975057)
                ·
                  refine ⟨992075661539522108981293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1322767548719362811975057 992075661539522108981293)
                  ·
                    refine ⟨372028373077320790867985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 992075661539522108981293 372028373077320790867985)
                    ·
                      rfl

theorem cell22_1086784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 7, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 7, 1, 2, 3].length) (baseStart_1086784 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1086784 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1086784 prefixEnd_1086784 := by exact prefixLift 1086784
  have htrace : WordTrace (prefixWord ++ tailWord_1086784) baseStart_1086784 baseEnd_1086784 := by
    simpa [prefixWord, tailWord_1086784, baseEnd_1086784] using wordTrace_append hprefix tailTrace_1086784
  have hstable : (prefixWord ++ tailWord_1086784).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1086784).length < 2 ^ (prefixWord ++ tailWord_1086784).sum := by decide
  have hdescent : baseEnd_1086784 < baseStart_1086784 := by decide
  rcases family_descends (prefixWord ++ tailWord_1086784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1086829 : List Nat := [1, 5, 1, 1, 1, 3, 3, 1, 3, 3]
def baseStart_1086829 : Nat := 118140960795 + 1086829 * 2 ^ 59
def prefixEnd_1086829 : Nat := 4983230072969 + 3 ^ 40 * 1086829 * 2
def baseEnd_1086829 : Nat := 372043777496955673492847

theorem tailTrace_1086829 : CollatzResearch.WordTrace tailWord_1086829 prefixEnd_1086829 372043777496955673492847 := by
  unfold tailWord_1086829
  simp only [CollatzResearch.WordTrace]
  refine ⟨39639910179611623460695541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26426606786407748973797027 39639910179611623460695541)
  ·
    refine ⟨3716241579338589699440207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 39639910179611623460695541 3716241579338589699440207)
    ·
      refine ⟨5574362369007884549160311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3716241579338589699440207 5574362369007884549160311)
      ·
        refine ⟨8361543553511826823740467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5574362369007884549160311 8361543553511826823740467)
        ·
          refine ⟨12542315330267740235610701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8361543553511826823740467 12542315330267740235610701)
          ·
            refine ⟨4703368248850402588354013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12542315330267740235610701 4703368248850402588354013)
            ·
              refine ⟨1763763093318900970632755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4703368248850402588354013 1763763093318900970632755)
              ·
                refine ⟨2645644639978351455949133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1763763093318900970632755 2645644639978351455949133)
                ·
                  refine ⟨992116739991881795980925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2645644639978351455949133 992116739991881795980925)
                  ·
                    refine ⟨372043777496955673492847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 992116739991881795980925 372043777496955673492847)
                    ·
                      rfl

theorem cell22_1086829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 3, 1, 3, 3].length) (baseStart_1086829 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1086829 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1086829 prefixEnd_1086829 := by exact prefixLift 1086829
  have htrace : WordTrace (prefixWord ++ tailWord_1086829) baseStart_1086829 baseEnd_1086829 := by
    simpa [prefixWord, tailWord_1086829, baseEnd_1086829] using wordTrace_append hprefix tailTrace_1086829
  have hstable : (prefixWord ++ tailWord_1086829).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1086829).length < 2 ^ (prefixWord ++ tailWord_1086829).sum := by decide
  have hdescent : baseEnd_1086829 < baseStart_1086829 := by decide
  rcases family_descends (prefixWord ++ tailWord_1086829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1086876 : List Nat := [2, 2, 3, 4, 1, 1, 2, 2, 5]
def baseStart_1086876 : Nat := 118140960795 + 1086876 * 2 ^ 59
def prefixEnd_1086876 : Nat := 4983230072969 + 3 ^ 40 * 1086876 * 2
def baseEnd_1086876 : Nat := 124019955519154405855901

theorem tailTrace_1086876 : CollatzResearch.WordTrace tailWord_1086876 prefixEnd_1086876 124019955519154405855901 := by
  unfold tailWord_1086876
  simp only [CollatzResearch.WordTrace]
  refine ⟨19820812205220675243828241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26427749606960900325104321 19820812205220675243828241)
  ·
    refine ⟨14865609153915506432871181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19820812205220675243828241 14865609153915506432871181)
    ·
      refine ⟨5574603432718314912326693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14865609153915506432871181 5574603432718314912326693)
      ·
        refine ⟨1045238143634684046061255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5574603432718314912326693 1045238143634684046061255)
        ·
          refine ⟨1567857215452026069091883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1045238143634684046061255 1567857215452026069091883)
          ·
            refine ⟨2351785823178039103637825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1567857215452026069091883 2351785823178039103637825)
            ·
              refine ⟨1763839367383529327728369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2351785823178039103637825 1763839367383529327728369)
              ·
                refine ⟨1322879525537646995796277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1763839367383529327728369 1322879525537646995796277)
                ·
                  refine ⟨124019955519154405855901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1322879525537646995796277 124019955519154405855901)
                  ·
                    rfl

theorem cell22_1086876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 2, 2, 5].length) (baseStart_1086876 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1086876 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1086876 prefixEnd_1086876 := by exact prefixLift 1086876
  have htrace : WordTrace (prefixWord ++ tailWord_1086876) baseStart_1086876 baseEnd_1086876 := by
    simpa [prefixWord, tailWord_1086876, baseEnd_1086876] using wordTrace_append hprefix tailTrace_1086876
  have hstable : (prefixWord ++ tailWord_1086876).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1086876).length < 2 ^ (prefixWord ++ tailWord_1086876).sum := by decide
  have hdescent : baseEnd_1086876 < baseStart_1086876 := by decide
  rcases family_descends (prefixWord ++ tailWord_1086876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1086887 : List Nat := [1, 1, 6, 1, 1, 1, 2, 3, 6]
def baseStart_1086887 : Nat := 118140960795 + 1086887 * 2 ^ 59
def prefixEnd_1086887 : Nat := 4983230072969 + 3 ^ 40 * 1086887 * 2
def baseEnd_1086887 : Nat := 124021210694087618514223

theorem tailTrace_1086887 : CollatzResearch.WordTrace tailWord_1086887 prefixEnd_1086887 124021210694087618514223 := by
  unfold tailWord_1086887
  simp only [CollatzResearch.WordTrace]
  refine ⟨39642025613401499366306915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26428017075600999577537943 39642025613401499366306915)
  ·
    refine ⟨59463038420102249049460373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39642025613401499366306915 59463038420102249049460373)
    ·
      refine ⟨2787329925942292924193455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 59463038420102249049460373 2787329925942292924193455)
      ·
        refine ⟨4180994888913439386290183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2787329925942292924193455 4180994888913439386290183)
        ·
          refine ⟨6271492333370159079435275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4180994888913439386290183 6271492333370159079435275)
          ·
            refine ⟨9407238500055238619152913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6271492333370159079435275 9407238500055238619152913)
            ·
              refine ⟨7055428875041428964364685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9407238500055238619152913 7055428875041428964364685)
              ·
                refine ⟨2645785828140535861636757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7055428875041428964364685 2645785828140535861636757)
                ·
                  refine ⟨124021210694087618514223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2645785828140535861636757 124021210694087618514223)
                  ·
                    rfl

theorem cell22_1086887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 2, 3, 6].length) (baseStart_1086887 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1086887 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1086887 prefixEnd_1086887 := by exact prefixLift 1086887
  have htrace : WordTrace (prefixWord ++ tailWord_1086887) baseStart_1086887 baseEnd_1086887 := by
    simpa [prefixWord, tailWord_1086887, baseEnd_1086887] using wordTrace_append hprefix tailTrace_1086887
  have hstable : (prefixWord ++ tailWord_1086887).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1086887).length < 2 ^ (prefixWord ++ tailWord_1086887).sum := by decide
  have hdescent : baseEnd_1086887 < baseStart_1086887 := by decide
  rcases family_descends (prefixWord ++ tailWord_1086887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1086914 : List Nat := [3, 5, 2, 1, 1, 1, 2, 3, 1, 3]
def baseStart_1086914 : Nat := 118140960795 + 1086914 * 2 ^ 59
def prefixEnd_1086914 : Nat := 4983230072969 + 3 ^ 40 * 1086914 * 2
def baseEnd_1086914 : Nat := 372072874734043785117587

theorem tailTrace_1086914 : CollatzResearch.WordTrace tailWord_1086914 prefixEnd_1086914 372072874734043785117587 := by
  unfold tailWord_1086914
  simp only [CollatzResearch.WordTrace]
  refine ⟨9910752596075920744384949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26428673589535788651693197 9910752596075920744384949)
  ·
    refine ⟨929133055882117569786089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 9910752596075920744384949 929133055882117569786089)
    ·
      refine ⟨696849791911588177339567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 929133055882117569786089 696849791911588177339567)
      ·
        refine ⟨1045274687867382266009351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 696849791911588177339567 1045274687867382266009351)
        ·
          refine ⟨1567912031801073399014027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1045274687867382266009351 1567912031801073399014027)
          ·
            refine ⟨2351868047701610098521041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1567912031801073399014027 2351868047701610098521041)
            ·
              refine ⟨1763901035776207573890781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2351868047701610098521041 1763901035776207573890781)
              ·
                refine ⟨661462888416077840209043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1763901035776207573890781 661462888416077840209043)
                ·
                  refine ⟨992194332624116760313565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 661462888416077840209043 992194332624116760313565)
                  ·
                    refine ⟨372072874734043785117587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 992194332624116760313565 372072874734043785117587)
                    ·
                      rfl

theorem cell22_1086914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 2, 3, 1, 3].length) (baseStart_1086914 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1086914 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1086914 prefixEnd_1086914 := by exact prefixLift 1086914
  have htrace : WordTrace (prefixWord ++ tailWord_1086914) baseStart_1086914 baseEnd_1086914 := by
    simpa [prefixWord, tailWord_1086914, baseEnd_1086914] using wordTrace_append hprefix tailTrace_1086914
  have hstable : (prefixWord ++ tailWord_1086914).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1086914).length < 2 ^ (prefixWord ++ tailWord_1086914).sum := by decide
  have hdescent : baseEnd_1086914 < baseStart_1086914 := by decide
  rcases family_descends (prefixWord ++ tailWord_1086914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1086915 : List Nat := [1, 1, 1, 3, 1, 1, 4, 10]
def baseStart_1086915 : Nat := 118140960795 + 1086915 * 2 ^ 59
def prefixEnd_1086915 : Nat := 4983230072969 + 3 ^ 40 * 1086915 * 2
def baseEnd_1086915 : Nat := 41341468561608901760287

theorem tailTrace_1086915 : CollatzResearch.WordTrace tailWord_1086915 prefixEnd_1086915 41341468561608901760287 := by
  unfold tailWord_1086915
  simp only [CollatzResearch.WordTrace]
  refine ⟨39643046857300060148326199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26428697904866706765550799 39643046857300060148326199)
  ·
    refine ⟨59464570285950090222489299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39643046857300060148326199 59464570285950090222489299)
    ·
      refine ⟨89196855428925135333733949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59464570285950090222489299 89196855428925135333733949)
      ·
        refine ⟨33448820785846925750150231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 89196855428925135333733949 33448820785846925750150231)
        ·
          refine ⟨50173231178770388625225347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33448820785846925750150231 50173231178770388625225347)
          ·
            refine ⟨75259846768155582937838021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50173231178770388625225347 75259846768155582937838021)
            ·
              refine ⟨14111221269029171800844629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 75259846768155582937838021 14111221269029171800844629)
              ·
                refine ⟨41341468561608901760287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 14111221269029171800844629 41341468561608901760287)
                ·
                  rfl

theorem cell22_1086915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 10].length) (baseStart_1086915 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1086915 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1086915 prefixEnd_1086915 := by exact prefixLift 1086915
  have htrace : WordTrace (prefixWord ++ tailWord_1086915) baseStart_1086915 baseEnd_1086915 := by
    simpa [prefixWord, tailWord_1086915, baseEnd_1086915] using wordTrace_append hprefix tailTrace_1086915
  have hstable : (prefixWord ++ tailWord_1086915).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1086915).length < 2 ^ (prefixWord ++ tailWord_1086915).sum := by decide
  have hdescent : baseEnd_1086915 < baseStart_1086915 := by decide
  rcases family_descends (prefixWord ++ tailWord_1086915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1086966 : List Nat := [5, 1, 1, 1, 2, 4, 2, 6]
def baseStart_1086966 : Nat := 118140960795 + 1086966 * 2 ^ 59
def prefixEnd_1086966 : Nat := 4983230072969 + 3 ^ 40 * 1086966 * 2
def baseEnd_1086966 : Nat := 41343408377414775868603

theorem tailTrace_1086966 : CollatzResearch.WordTrace tailWord_1086966 prefixEnd_1086966 41343408377414775868603 := by
  unfold tailWord_1086966
  simp only [CollatzResearch.WordTrace]
  refine ⟨2477806686257205991152047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 26429937986743530572288501 2477806686257205991152047)
  ·
    refine ⟨3716710029385808986728071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2477806686257205991152047 3716710029385808986728071)
    ·
      refine ⟨5575065044078713480092107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3716710029385808986728071 5575065044078713480092107)
      ·
        refine ⟨8362597566118070220138161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5575065044078713480092107 8362597566118070220138161)
        ·
          refine ⟨6271948174588552665103621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8362597566118070220138161 6271948174588552665103621)
          ·
            refine ⟨1175990282735353624706929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6271948174588552665103621 1175990282735353624706929)
            ·
              refine ⟨881992712051515218530197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1175990282735353624706929 881992712051515218530197)
              ·
                refine ⟨41343408377414775868603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 881992712051515218530197 41343408377414775868603)
                ·
                  rfl

theorem cell22_1086966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 4, 2, 6].length) (baseStart_1086966 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1086966 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1086966 prefixEnd_1086966 := by exact prefixLift 1086966
  have htrace : WordTrace (prefixWord ++ tailWord_1086966) baseStart_1086966 baseEnd_1086966 := by
    simpa [prefixWord, tailWord_1086966, baseEnd_1086966] using wordTrace_append hprefix tailTrace_1086966
  have hstable : (prefixWord ++ tailWord_1086966).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1086966).length < 2 ^ (prefixWord ++ tailWord_1086966).sum := by decide
  have hdescent : baseEnd_1086966 < baseStart_1086966 := by decide
  rcases family_descends (prefixWord ++ tailWord_1086966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1087086 : List Nat := [4, 1, 2, 2, 3, 1, 1, 1, 1, 6]
def baseStart_1087086 : Nat := 118140960795 + 1087086 * 2 ^ 59
def prefixEnd_1087086 : Nat := 4983230072969 + 3 ^ 40 * 1087086 * 2
def baseEnd_1087086 : Nat := 372131753849092669817059

theorem tailTrace_1087086 : CollatzResearch.WordTrace tailWord_1087086 prefixEnd_1087086 372131753849092669817059 := by
  unfold tailWord_1087086
  simp only [CollatzResearch.WordTrace]
  refine ⟨4956160467460069544100139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26432855826453704235200741 4956160467460069544100139)
  ·
    refine ⟨7434240701190104316150209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4956160467460069544100139 7434240701190104316150209)
    ·
      refine ⟨5575680525892578237112657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7434240701190104316150209 5575680525892578237112657)
      ·
        refine ⟨4181760394419433677834493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5575680525892578237112657 4181760394419433677834493)
        ·
          refine ⟨1568160147907287629187935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4181760394419433677834493 1568160147907287629187935)
          ·
            refine ⟨2352240221860931443781903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1568160147907287629187935 2352240221860931443781903)
            ·
              refine ⟨3528360332791397165672855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2352240221860931443781903 3528360332791397165672855)
              ·
                refine ⟨5292540499187095748509283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3528360332791397165672855 5292540499187095748509283)
                ·
                  refine ⟨7938810748780643622763925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5292540499187095748509283 7938810748780643622763925)
                  ·
                    refine ⟨372131753849092669817059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7938810748780643622763925 372131753849092669817059)
                    ·
                      rfl

theorem cell22_1087086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 1, 1, 1, 6].length) (baseStart_1087086 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1087086 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1087086 prefixEnd_1087086 := by exact prefixLift 1087086
  have htrace : WordTrace (prefixWord ++ tailWord_1087086) baseStart_1087086 baseEnd_1087086 := by
    simpa [prefixWord, tailWord_1087086, baseEnd_1087086] using wordTrace_append hprefix tailTrace_1087086
  have hstable : (prefixWord ++ tailWord_1087086).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1087086).length < 2 ^ (prefixWord ++ tailWord_1087086).sum := by decide
  have hdescent : baseEnd_1087086 < baseStart_1087086 := by decide
  rcases family_descends (prefixWord ++ tailWord_1087086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1087099 : List Nat := [1, 1, 1, 1, 1, 4, 3, 2, 5, 3]
def baseStart_1087099 : Nat := 118140960795 + 1087099 * 2 ^ 59
def prefixEnd_1087099 : Nat := 4983230072969 + 3 ^ 40 * 1087099 * 2
def baseEnd_1087099 : Nat := 372136204014764969242019

theorem tailTrace_1087099 : CollatzResearch.WordTrace tailWord_1087099 prefixEnd_1087099 372136204014764969242019 := by
  unfold tailWord_1087099
  simp only [CollatzResearch.WordTrace]
  refine ⟨39649757888633459573024351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26433171925755639715349567 39649757888633459573024351)
  ·
    refine ⟨59474636832950189359536527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39649757888633459573024351 59474636832950189359536527)
    ·
      refine ⟨89211955249425284039304791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59474636832950189359536527 89211955249425284039304791)
      ·
        refine ⟨133817932874137926058957187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89211955249425284039304791 133817932874137926058957187)
        ·
          refine ⟨200726899311206889088435781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 133817932874137926058957187 200726899311206889088435781)
          ·
            refine ⟨37636293620851291704081709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 200726899311206889088435781 37636293620851291704081709)
            ·
              refine ⟨14113610107819234389030641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37636293620851291704081709 14113610107819234389030641)
              ·
                refine ⟨10585207580864425791772981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14113610107819234389030641 10585207580864425791772981)
                ·
                  refine ⟨992363210706039917978717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 10585207580864425791772981 992363210706039917978717)
                  ·
                    refine ⟨372136204014764969242019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 992363210706039917978717 372136204014764969242019)
                    ·
                      rfl

theorem cell22_1087099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 2, 5, 3].length) (baseStart_1087099 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1087099 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1087099 prefixEnd_1087099 := by exact prefixLift 1087099
  have htrace : WordTrace (prefixWord ++ tailWord_1087099) baseStart_1087099 baseEnd_1087099 := by
    simpa [prefixWord, tailWord_1087099, baseEnd_1087099] using wordTrace_append hprefix tailTrace_1087099
  have hstable : (prefixWord ++ tailWord_1087099).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1087099).length < 2 ^ (prefixWord ++ tailWord_1087099).sum := by decide
  have hdescent : baseEnd_1087099 < baseStart_1087099 := by decide
  rcases family_descends (prefixWord ++ tailWord_1087099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1087116 : List Nat := [2, 2, 1, 2, 1, 1, 6, 1, 3, 3]
def baseStart_1087116 : Nat := 118140960795 + 1087116 * 2 ^ 59
def prefixEnd_1087116 : Nat := 4983230072969 + 3 ^ 40 * 1087116 * 2
def baseEnd_1087116 : Nat := 372142023462182591566967

theorem tailTrace_1087116 : CollatzResearch.WordTrace tailWord_1087116 prefixEnd_1087116 372142023462182591566967 := by
  unfold tailWord_1087116
  simp only [CollatzResearch.WordTrace]
  refine ⟨19825188964785935738196601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26433585286381247650928801 19825188964785935738196601)
  ·
    refine ⟨14868891723589451803647451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19825188964785935738196601 14868891723589451803647451)
    ·
      refine ⟨22303337585384177705471177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14868891723589451803647451 22303337585384177705471177)
      ·
        refine ⟨16727503189038133279103383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22303337585384177705471177 16727503189038133279103383)
        ·
          refine ⟨25091254783557199918655075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16727503189038133279103383 25091254783557199918655075)
          ·
            refine ⟨37636882175335799877982613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25091254783557199918655075 37636882175335799877982613)
            ·
              refine ⟨1764228851968865619280435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 37636882175335799877982613 1764228851968865619280435)
              ·
                refine ⟨2646343277953298428920653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1764228851968865619280435 2646343277953298428920653)
                ·
                  refine ⟨992378729232486910845245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2646343277953298428920653 992378729232486910845245)
                  ·
                    refine ⟨372142023462182591566967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 992378729232486910845245 372142023462182591566967)
                    ·
                      rfl

theorem cell22_1087116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 6, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 6, 1, 3, 3].length) (baseStart_1087116 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1087116 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1087116 prefixEnd_1087116 := by exact prefixLift 1087116
  have htrace : WordTrace (prefixWord ++ tailWord_1087116) baseStart_1087116 baseEnd_1087116 := by
    simpa [prefixWord, tailWord_1087116, baseEnd_1087116] using wordTrace_append hprefix tailTrace_1087116
  have hstable : (prefixWord ++ tailWord_1087116).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1087116).length < 2 ^ (prefixWord ++ tailWord_1087116).sum := by decide
  have hdescent : baseEnd_1087116 < baseStart_1087116 := by decide
  rcases family_descends (prefixWord ++ tailWord_1087116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1087135 : List Nat := [1, 1, 2, 7, 2, 1, 2, 6]
def baseStart_1087135 : Nat := 118140960795 + 1087135 * 2 ^ 59
def prefixEnd_1087135 : Nat := 4983230072969 + 3 ^ 40 * 1087135 * 2
def baseEnd_1087135 : Nat := 41349836394496986149101

theorem tailTrace_1087135 : CollatzResearch.WordTrace tailWord_1087135 prefixEnd_1087135 41349836394496986149101 := by
  unfold tailWord_1087135
  simp only [CollatzResearch.WordTrace]
  refine ⟨39651070916503037721334859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26434047277668691814223239 39651070916503037721334859)
  ·
    refine ⟨59476606374754556582002289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39651070916503037721334859 59476606374754556582002289)
    ·
      refine ⟨44607454781065917436501717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59476606374754556582002289 44607454781065917436501717)
      ·
        refine ⟨1045487221431232439918009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 44607454781065917436501717 1045487221431232439918009)
        ·
          refine ⟨784115416073424329938507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1045487221431232439918009 784115416073424329938507)
          ·
            refine ⟨1176173124110136494907761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 784115416073424329938507 1176173124110136494907761)
            ·
              refine ⟨882129843082602371180821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1176173124110136494907761 882129843082602371180821)
              ·
                refine ⟨41349836394496986149101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 882129843082602371180821 41349836394496986149101)
                ·
                  rfl

theorem cell22_1087135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 2, 1, 2, 6].length) (baseStart_1087135 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1087135 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1087135 prefixEnd_1087135 := by exact prefixLift 1087135
  have htrace : WordTrace (prefixWord ++ tailWord_1087135) baseStart_1087135 baseEnd_1087135 := by
    simpa [prefixWord, tailWord_1087135, baseEnd_1087135] using wordTrace_append hprefix tailTrace_1087135
  have hstable : (prefixWord ++ tailWord_1087135).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1087135).length < 2 ^ (prefixWord ++ tailWord_1087135).sum := by decide
  have hdescent : baseEnd_1087135 < baseStart_1087135 := by decide
  rcases family_descends (prefixWord ++ tailWord_1087135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1087180 : List Nat := [2, 2, 1, 5, 2, 2, 2, 1, 5]
def baseStart_1087180 : Nat := 118140960795 + 1087180 * 2 ^ 59
def prefixEnd_1087180 : Nat := 4983230072969 + 3 ^ 40 * 1087180 * 2
def baseEnd_1087180 : Nat := 124054643990035919322257

theorem tailTrace_1087180 : CollatzResearch.WordTrace tailWord_1087180 prefixEnd_1087180 124054643990035919322257 := by
  unfold tailWord_1087180
  simp only [CollatzResearch.WordTrace]
  refine ⟨19826356100670005203361497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26435141467560006937815329 19826356100670005203361497)
  ·
    refine ⟨14869767075502503902521123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19826356100670005203361497 14869767075502503902521123)
    ·
      refine ⟨22304650613253755853781685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14869767075502503902521123 22304650613253755853781685)
      ·
        refine ⟨2091060994992539611292033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 22304650613253755853781685 2091060994992539611292033)
        ·
          refine ⟨1568295746244404708469025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2091060994992539611292033 1568295746244404708469025)
          ·
            refine ⟨1176221809683303531351769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1568295746244404708469025 1176221809683303531351769)
            ·
              refine ⟨882166357262477648513827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1176221809683303531351769 882166357262477648513827)
              ·
                refine ⟨1323249535893716472770741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 882166357262477648513827 1323249535893716472770741)
                ·
                  refine ⟨124054643990035919322257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1323249535893716472770741 124054643990035919322257)
                  ·
                    rfl

theorem cell22_1087180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 2, 2, 1, 5].length) (baseStart_1087180 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1087180 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1087180 prefixEnd_1087180 := by exact prefixLift 1087180
  have htrace : WordTrace (prefixWord ++ tailWord_1087180) baseStart_1087180 baseEnd_1087180 := by
    simpa [prefixWord, tailWord_1087180, baseEnd_1087180] using wordTrace_append hprefix tailTrace_1087180
  have hstable : (prefixWord ++ tailWord_1087180).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1087180).length < 2 ^ (prefixWord ++ tailWord_1087180).sum := by decide
  have hdescent : baseEnd_1087180 < baseStart_1087180 := by decide
  rcases family_descends (prefixWord ++ tailWord_1087180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1087193 : List Nat := [1, 2, 1, 2, 3, 5, 1, 2, 1, 4]
def baseStart_1087193 : Nat := 118140960795 + 1087193 * 2 ^ 59
def prefixEnd_1087193 : Nat := 4983230072969 + 3 ^ 40 * 1087193 * 2
def baseEnd_1087193 : Nat := 372168382135780057391731

theorem tailTrace_1087193 : CollatzResearch.WordTrace tailWord_1087193 prefixEnd_1087193 372168382135780057391731 := by
  unfold tailWord_1087193
  simp only [CollatzResearch.WordTrace]
  refine ⟨39653186350292913626946233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26435457566861942417964155 39653186350292913626946233)
  ·
    refine ⟨29739889762719685220209675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39653186350292913626946233 29739889762719685220209675)
    ·
      refine ⟨44609834644079527830314513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29739889762719685220209675 44609834644079527830314513)
      ·
        refine ⟨33457375983059645872735885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44609834644079527830314513 33457375983059645872735885)
        ·
          refine ⟨12546515993647367202275957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33457375983059645872735885 12546515993647367202275957)
          ·
            refine ⟨1176235874404440675213371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 12546515993647367202275957 1176235874404440675213371)
            ·
              refine ⟨1764353811606661012820057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1176235874404440675213371 1764353811606661012820057)
              ·
                refine ⟨1323265358704995759615043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1764353811606661012820057 1323265358704995759615043)
                ·
                  refine ⟨1984898038057493639422565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1323265358704995759615043 1984898038057493639422565)
                  ·
                    refine ⟨372168382135780057391731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1984898038057493639422565 372168382135780057391731)
                    ·
                      rfl

theorem cell22_1087193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 5, 1, 2, 1, 4].length) (baseStart_1087193 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1087193 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1087193 prefixEnd_1087193 := by exact prefixLift 1087193
  have htrace : WordTrace (prefixWord ++ tailWord_1087193) baseStart_1087193 baseEnd_1087193 := by
    simpa [prefixWord, tailWord_1087193, baseEnd_1087193] using wordTrace_append hprefix tailTrace_1087193
  have hstable : (prefixWord ++ tailWord_1087193).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1087193).length < 2 ^ (prefixWord ++ tailWord_1087193).sum := by decide
  have hdescent : baseEnd_1087193 < baseStart_1087193 := by decide
  rcases family_descends (prefixWord ++ tailWord_1087193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1087236 : List Nat := [2, 3, 2, 2, 1, 2, 3, 7]
def baseStart_1087236 : Nat := 118140960795 + 1087236 * 2 ^ 59
def prefixEnd_1087236 : Nat := 4983230072969 + 3 ^ 40 * 1087236 * 2
def baseEnd_1087236 : Nat := 41353677990504697618511

theorem tailTrace_1087236 : CollatzResearch.WordTrace tailWord_1087236 prefixEnd_1087236 41353677990504697618511 := by
  unfold tailWord_1087236
  simp only [CollatzResearch.WordTrace]
  refine ⟨19827377344568565985380781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26436503126091421313841041 19827377344568565985380781)
  ·
    refine ⟨7435266504213212244517793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19827377344568565985380781 7435266504213212244517793)
    ·
      refine ⟨5576449878159909183388345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7435266504213212244517793 5576449878159909183388345)
      ·
        refine ⟨4182337408619931887541259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5576449878159909183388345 4182337408619931887541259)
        ·
          refine ⟨6273506112929897831311889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4182337408619931887541259 6273506112929897831311889)
          ·
            refine ⟨4705129584697423373483917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6273506112929897831311889 4705129584697423373483917)
            ·
              refine ⟨1764423594261533765056469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4705129584697423373483917 1764423594261533765056469)
              ·
                refine ⟨41353677990504697618511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1764423594261533765056469 41353677990504697618511)
                ·
                  rfl

theorem cell22_1087236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 3, 7].length) (baseStart_1087236 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1087236 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1087236 prefixEnd_1087236 := by exact prefixLift 1087236
  have htrace : WordTrace (prefixWord ++ tailWord_1087236) baseStart_1087236 baseEnd_1087236 := by
    simpa [prefixWord, tailWord_1087236, baseEnd_1087236] using wordTrace_append hprefix tailTrace_1087236
  have hstable : (prefixWord ++ tailWord_1087236).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1087236).length < 2 ^ (prefixWord ++ tailWord_1087236).sum := by decide
  have hdescent : baseEnd_1087236 < baseStart_1087236 := by decide
  rcases family_descends (prefixWord ++ tailWord_1087236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1087249 : List Nat := [1, 2, 2, 1, 1, 3, 1, 1, 4, 6]
def baseStart_1087249 : Nat := 118140960795 + 1087249 * 2 ^ 59
def prefixEnd_1087249 : Nat := 4983230072969 + 3 ^ 40 * 1087249 * 2
def baseEnd_1087249 : Nat := 372187552080214577991559

theorem tailTrace_1087249 : CollatzResearch.WordTrace tailWord_1087249 prefixEnd_1087249 372187552080214577991559 := by
  unfold tailWord_1087249
  simp only [CollatzResearch.WordTrace]
  refine ⟨39655228838090035190984801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26436819225393356793989867 39655228838090035190984801)
  ·
    refine ⟨29741421628567526393238601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39655228838090035190984801 29741421628567526393238601)
    ·
      refine ⟨22306066221425644794928951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29741421628567526393238601 22306066221425644794928951)
      ·
        refine ⟨33459099332138467192393427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22306066221425644794928951 33459099332138467192393427)
        ·
          refine ⟨50188648998207700788590141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33459099332138467192393427 50188648998207700788590141)
          ·
            refine ⟨18820743374327887795721303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50188648998207700788590141 18820743374327887795721303)
            ·
              refine ⟨28231115061491831693581955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18820743374327887795721303 28231115061491831693581955)
              ·
                refine ⟨42346672592237747540372933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28231115061491831693581955 42346672592237747540372933)
                ·
                  refine ⟨7940001111044577663819925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 42346672592237747540372933 7940001111044577663819925)
                  ·
                    refine ⟨372187552080214577991559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7940001111044577663819925 372187552080214577991559)
                    ·
                      rfl

theorem cell22_1087249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 6].length) (baseStart_1087249 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1087249 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1087249 prefixEnd_1087249 := by exact prefixLift 1087249
  have htrace : WordTrace (prefixWord ++ tailWord_1087249) baseStart_1087249 baseEnd_1087249 := by
    simpa [prefixWord, tailWord_1087249, baseEnd_1087249] using wordTrace_append hprefix tailTrace_1087249
  have hstable : (prefixWord ++ tailWord_1087249).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1087249).length < 2 ^ (prefixWord ++ tailWord_1087249).sum := by decide
  have hdescent : baseEnd_1087249 < baseStart_1087249 := by decide
  rcases family_descends (prefixWord ++ tailWord_1087249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1087279 : List Nat := [1, 1, 2, 1, 2, 1, 2, 2, 3, 7]
def baseStart_1087279 : Nat := 118140960795 + 1087279 * 2 ^ 59
def prefixEnd_1087279 : Nat := 4983230072969 + 3 ^ 40 * 1087279 * 2
def baseEnd_1087279 : Nat := 372197821693304499741467

theorem tailTrace_1087279 : CollatzResearch.WordTrace tailWord_1087279 prefixEnd_1087279 372197821693304499741467 := by
  unfold tailWord_1087279
  simp only [CollatzResearch.WordTrace]
  refine ⟨39656323027981350314576891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26437548685320900209717927 39656323027981350314576891)
  ·
    refine ⟨59484484541972025471865337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39656323027981350314576891 59484484541972025471865337)
    ·
      refine ⟨44613363406479019103899003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59484484541972025471865337 44613363406479019103899003)
      ·
        refine ⟨66920045109718528655848505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44613363406479019103899003 66920045109718528655848505)
        ·
          refine ⟨50190033832288896491886379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66920045109718528655848505 50190033832288896491886379)
          ·
            refine ⟨75285050748433344737829569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50190033832288896491886379 75285050748433344737829569)
            ·
              refine ⟨56463788061325008553372177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 75285050748433344737829569 56463788061325008553372177)
              ·
                refine ⟨42347841045993756415029133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 56463788061325008553372177 42347841045993756415029133)
                ·
                  refine ⟨15880440392247658655635925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 42347841045993756415029133 15880440392247658655635925)
                  ·
                    refine ⟨372197821693304499741467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 15880440392247658655635925 372197821693304499741467)
                    ·
                      rfl

theorem cell22_1087279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 2, 3, 7].length) (baseStart_1087279 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1087279 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1087279 prefixEnd_1087279 := by exact prefixLift 1087279
  have htrace : WordTrace (prefixWord ++ tailWord_1087279) baseStart_1087279 baseEnd_1087279 := by
    simpa [prefixWord, tailWord_1087279, baseEnd_1087279] using wordTrace_append hprefix tailTrace_1087279
  have hstable : (prefixWord ++ tailWord_1087279).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1087279).length < 2 ^ (prefixWord ++ tailWord_1087279).sum := by decide
  have hdescent : baseEnd_1087279 < baseStart_1087279 := by decide
  rcases family_descends (prefixWord ++ tailWord_1087279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1087281 : List Nat := [1, 2, 2, 3, 2, 3, 1, 1, 7]
def baseStart_1087281 : Nat := 118140960795 + 1087281 * 2 ^ 59
def prefixEnd_1087281 : Nat := 4983230072969 + 3 ^ 40 * 1087281 * 2
def baseEnd_1087281 : Nat := 124066168778059053730487

theorem tailTrace_1087281 : CollatzResearch.WordTrace tailWord_1087281 prefixEnd_1087281 124066168778059053730487 := by
  unfold tailWord_1087281
  simp only [CollatzResearch.WordTrace]
  refine ⟨39656395973974104656149697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26437597315982736437433131 39656395973974104656149697)
  ·
    refine ⟨29742296980480578492112273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39656395973974104656149697 29742296980480578492112273)
    ·
      refine ⟨22306722735360433869084205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29742296980480578492112273 22306722735360433869084205)
      ·
        refine ⟨8365021025760162700906577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22306722735360433869084205 8365021025760162700906577)
        ·
          refine ⟨6273765769320122025679933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8365021025760162700906577 6273765769320122025679933)
          ·
            refine ⟨2352662163495045759629975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6273765769320122025679933 2352662163495045759629975)
            ·
              refine ⟨3528993245242568639444963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2352662163495045759629975 3528993245242568639444963)
              ·
                refine ⟨5293489867863852959167445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3528993245242568639444963 5293489867863852959167445)
                ·
                  refine ⟨124066168778059053730487, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5293489867863852959167445 124066168778059053730487)
                  ·
                    rfl

theorem cell22_1087281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 1, 1, 7].length) (baseStart_1087281 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1087281 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1087281 prefixEnd_1087281 := by exact prefixLift 1087281
  have htrace : WordTrace (prefixWord ++ tailWord_1087281) baseStart_1087281 baseEnd_1087281 := by
    simpa [prefixWord, tailWord_1087281, baseEnd_1087281] using wordTrace_append hprefix tailTrace_1087281
  have hstable : (prefixWord ++ tailWord_1087281).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1087281).length < 2 ^ (prefixWord ++ tailWord_1087281).sum := by decide
  have hdescent : baseEnd_1087281 < baseStart_1087281 := by decide
  rcases family_descends (prefixWord ++ tailWord_1087281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1087285 : List Nat := [1, 3, 3, 1, 4, 1, 2, 1, 3, 3]
def baseStart_1087285 : Nat := 118140960795 + 1087285 * 2 ^ 59
def prefixEnd_1087285 : Nat := 4983230072969 + 3 ^ 40 * 1087285 * 2
def baseEnd_1087285 : Nat := 372199875615922484091449

theorem tailTrace_1087285 : CollatzResearch.WordTrace tailWord_1087285 prefixEnd_1087285 372199875615922484091449 := by
  unfold tailWord_1087285
  simp only [CollatzResearch.WordTrace]
  refine ⟨39656541865959613339295309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26437694577306408892863539 39656541865959613339295309)
  ·
    refine ⟨14871203199734855002235741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39656541865959613339295309 14871203199734855002235741)
    ·
      refine ⟨5576701199900570625838403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14871203199734855002235741 5576701199900570625838403)
      ·
        refine ⟨8365051799850855938757605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5576701199900570625838403 8365051799850855938757605)
        ·
          refine ⟨1568447212472035488517051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8365051799850855938757605 1568447212472035488517051)
          ·
            refine ⟨2352670818708053232775577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1568447212472035488517051 2352670818708053232775577)
            ·
              refine ⟨1764503114031039924581683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2352670818708053232775577 1764503114031039924581683)
              ·
                refine ⟨2646754671046559886872525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1764503114031039924581683 2646754671046559886872525)
                ·
                  refine ⟨992533001642459957577197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2646754671046559886872525 992533001642459957577197)
                  ·
                    refine ⟨372199875615922484091449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 992533001642459957577197 372199875615922484091449)
                    ·
                      rfl

theorem cell22_1087285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 2, 1, 3, 3].length) (baseStart_1087285 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1087285 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1087285 prefixEnd_1087285 := by exact prefixLift 1087285
  have htrace : WordTrace (prefixWord ++ tailWord_1087285) baseStart_1087285 baseEnd_1087285 := by
    simpa [prefixWord, tailWord_1087285, baseEnd_1087285] using wordTrace_append hprefix tailTrace_1087285
  have hstable : (prefixWord ++ tailWord_1087285).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1087285).length < 2 ^ (prefixWord ++ tailWord_1087285).sum := by decide
  have hdescent : baseEnd_1087285 < baseStart_1087285 := by decide
  rcases family_descends (prefixWord ++ tailWord_1087285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1087302 : List Nat := [6, 1, 1, 2, 1, 1, 2, 2, 3, 3]
def baseStart_1087302 : Nat := 118140960795 + 1087302 * 2 ^ 59
def prefixEnd_1087302 : Nat := 4983230072969 + 3 ^ 40 * 1087302 * 2
def baseEnd_1087302 : Nat := 372205695063340106416397

theorem tailTrace_1087302 : CollatzResearch.WordTrace tailWord_1087302 prefixEnd_1087302 372205695063340106416397 := by
  unfold tailWord_1087302
  simp only [CollatzResearch.WordTrace]
  refine ⟨1239286309590563288833255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 26438107937932016828442773 1239286309590563288833255)
  ·
    refine ⟨1858929464385844933249883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1239286309590563288833255 1858929464385844933249883)
    ·
      refine ⟨2788394196578767399874825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1858929464385844933249883 2788394196578767399874825)
      ·
        refine ⟨2091295647434075549906119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2788394196578767399874825 2091295647434075549906119)
        ·
          refine ⟨3136943471151113324859179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2091295647434075549906119 3136943471151113324859179)
          ·
            refine ⟨4705415206726669987288769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3136943471151113324859179 4705415206726669987288769)
            ·
              refine ⟨3529061405045002490466577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4705415206726669987288769 3529061405045002490466577)
              ·
                refine ⟨2646796053783751867849933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3529061405045002490466577 2646796053783751867849933)
                ·
                  refine ⟨992548520168906950443725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2646796053783751867849933 992548520168906950443725)
                  ·
                    refine ⟨372205695063340106416397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 992548520168906950443725 372205695063340106416397)
                    ·
                      rfl

theorem cell22_1087302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 2, 2, 3, 3].length) (baseStart_1087302 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1087302 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1087302 prefixEnd_1087302 := by exact prefixLift 1087302
  have htrace : WordTrace (prefixWord ++ tailWord_1087302) baseStart_1087302 baseEnd_1087302 := by
    simpa [prefixWord, tailWord_1087302, baseEnd_1087302] using wordTrace_append hprefix tailTrace_1087302
  have hstable : (prefixWord ++ tailWord_1087302).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1087302).length < 2 ^ (prefixWord ++ tailWord_1087302).sum := by decide
  have hdescent : baseEnd_1087302 < baseStart_1087302 := by decide
  rcases family_descends (prefixWord ++ tailWord_1087302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1087319 : List Nat := [1, 1, 3, 2, 6, 1, 1, 3, 1, 3]
def baseStart_1087319 : Nat := 118140960795 + 1087319 * 2 ^ 59
def prefixEnd_1087319 : Nat := 4983230072969 + 3 ^ 40 * 1087319 * 2
def baseEnd_1087319 : Nat := 372211514510757728741345

theorem tailTrace_1087319 : CollatzResearch.WordTrace tailWord_1087319 prefixEnd_1087319 372211514510757728741345 := by
  unfold tailWord_1087319
  simp only [CollatzResearch.WordTrace]
  refine ⟨39657781947836437146033011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26438521298557624764022007 39657781947836437146033011)
  ·
    refine ⟨59486672921754655719049517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39657781947836437146033011 59486672921754655719049517)
    ·
      refine ⟨22307502345657995894643569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59486672921754655719049517 22307502345657995894643569)
      ·
        refine ⟨16730626759243496920982677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22307502345657995894643569 16730626759243496920982677)
        ·
          refine ⟨784248129339538918171063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 16730626759243496920982677 784248129339538918171063)
          ·
            refine ⟨1176372194009308377256595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 784248129339538918171063 1176372194009308377256595)
            ·
              refine ⟨1764558291013962565884893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1176372194009308377256595 1764558291013962565884893)
              ·
                refine ⟨661709359130235962206835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1764558291013962565884893 661709359130235962206835)
                ·
                  refine ⟨992564038695353943310253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 661709359130235962206835 992564038695353943310253)
                  ·
                    refine ⟨372211514510757728741345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 992564038695353943310253 372211514510757728741345)
                    ·
                      rfl

theorem cell22_1087319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 6, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 6, 1, 1, 3, 1, 3].length) (baseStart_1087319 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1087319 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1087319 prefixEnd_1087319 := by exact prefixLift 1087319
  have htrace : WordTrace (prefixWord ++ tailWord_1087319) baseStart_1087319 baseEnd_1087319 := by
    simpa [prefixWord, tailWord_1087319, baseEnd_1087319] using wordTrace_append hprefix tailTrace_1087319
  have hstable : (prefixWord ++ tailWord_1087319).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1087319).length < 2 ^ (prefixWord ++ tailWord_1087319).sum := by decide
  have hdescent : baseEnd_1087319 < baseStart_1087319 := by decide
  rcases family_descends (prefixWord ++ tailWord_1087319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1087328 : List Nat := [2, 1, 1, 3, 3, 2, 2, 3, 1, 4]
def baseStart_1087328 : Nat := 118140960795 + 1087328 * 2 ^ 59
def prefixEnd_1087328 : Nat := 4983230072969 + 3 ^ 40 * 1087328 * 2
def baseEnd_1087328 : Nat := 372214595394684705266317

theorem tailTrace_1087328 : CollatzResearch.WordTrace tailWord_1087328 prefixEnd_1087328 372214595394684705266317 := by
  unfold tailWord_1087328
  simp only [CollatzResearch.WordTrace]
  refine ⟨19829055102401915841555319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26438740136535887788740425 19829055102401915841555319)
  ·
    refine ⟨29743582653602873762332979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19829055102401915841555319 29743582653602873762332979)
    ·
      refine ⟨44615373980404310643499469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29743582653602873762332979 44615373980404310643499469)
      ·
        refine ⟨16730765242651616491312301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44615373980404310643499469 16730765242651616491312301)
        ·
          refine ⟨6274036965994356184242113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16730765242651616491312301 6274036965994356184242113)
          ·
            refine ⟨4705527724495767138181585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6274036965994356184242113 4705527724495767138181585)
            ·
              refine ⟨3529145793371825353636189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4705527724495767138181585 3529145793371825353636189)
              ·
                refine ⟨1323429672514434507613571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3529145793371825353636189 1323429672514434507613571)
                ·
                  refine ⟨1985144508771651761420357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1323429672514434507613571 1985144508771651761420357)
                  ·
                    refine ⟨372214595394684705266317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1985144508771651761420357 372214595394684705266317)
                    ·
                      rfl

theorem cell22_1087328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 2, 3, 1, 4].length) (baseStart_1087328 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1087328 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1087328 prefixEnd_1087328 := by exact prefixLift 1087328
  have htrace : WordTrace (prefixWord ++ tailWord_1087328) baseStart_1087328 baseEnd_1087328 := by
    simpa [prefixWord, tailWord_1087328, baseEnd_1087328] using wordTrace_append hprefix tailTrace_1087328
  have hstable : (prefixWord ++ tailWord_1087328).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1087328).length < 2 ^ (prefixWord ++ tailWord_1087328).sum := by decide
  have hdescent : baseEnd_1087328 < baseStart_1087328 := by decide
  rcases family_descends (prefixWord ++ tailWord_1087328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1087394 : List Nat := [3, 3, 1, 2, 3, 2, 2, 2, 4]
def baseStart_1087394 : Nat := 118140960795 + 1087394 * 2 ^ 59
def prefixEnd_1087394 : Nat := 4983230072969 + 3 ^ 40 * 1087394 * 2
def baseEnd_1087394 : Nat := 124079062847827511038705

theorem tailTrace_1087394 : CollatzResearch.WordTrace tailWord_1087394 prefixEnd_1087394 124079062847827511038705 := by
  unfold tailWord_1087394
  simp only [CollatzResearch.WordTrace]
  refine ⟨9915129355641181238753309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26440344948376483303342157 9915129355641181238753309)
  ·
    refine ⟨3718173508365442964532491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9915129355641181238753309 3718173508365442964532491)
    ·
      refine ⟨5577260262548164446798737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3718173508365442964532491 5577260262548164446798737)
      ·
        refine ⟨4182945196911123335099053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5577260262548164446798737 4182945196911123335099053)
        ·
          refine ⟨1568604448841671250662145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4182945196911123335099053 1568604448841671250662145)
          ·
            refine ⟨1176453336631253437996609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1568604448841671250662145 1176453336631253437996609)
            ·
              refine ⟨882340002473440078497457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1176453336631253437996609 882340002473440078497457)
              ·
                refine ⟨661755001855080058873093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 882340002473440078497457 661755001855080058873093)
                ·
                  refine ⟨124079062847827511038705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 661755001855080058873093 124079062847827511038705)
                  ·
                    rfl

theorem cell22_1087394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 2, 2, 2, 4].length) (baseStart_1087394 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1087394 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1087394 prefixEnd_1087394 := by exact prefixLift 1087394
  have htrace : WordTrace (prefixWord ++ tailWord_1087394) baseStart_1087394 baseEnd_1087394 := by
    simpa [prefixWord, tailWord_1087394, baseEnd_1087394] using wordTrace_append hprefix tailTrace_1087394
  have hstable : (prefixWord ++ tailWord_1087394).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1087394).length < 2 ^ (prefixWord ++ tailWord_1087394).sum := by decide
  have hdescent : baseEnd_1087394 < baseStart_1087394 := by decide
  rcases family_descends (prefixWord ++ tailWord_1087394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1087431 : List Nat := [1, 1, 4, 1, 1, 2, 1, 1, 3, 7]
def baseStart_1087431 : Nat := 118140960795 + 1087431 * 2 ^ 59
def prefixEnd_1087431 : Nat := 4983230072969 + 3 ^ 40 * 1087431 * 2
def baseEnd_1087431 : Nat := 372249854399626769941001

theorem tailTrace_1087431 : CollatzResearch.WordTrace tailWord_1087431 prefixEnd_1087431 372249854399626769941001 := by
  unfold tailWord_1087431
  simp only [CollatzResearch.WordTrace]
  refine ⟨39661866923430680274110147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26441244615620453516073431 39661866923430680274110147)
  ·
    refine ⟨59492800385146020411165221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39661866923430680274110147 59492800385146020411165221)
    ·
      refine ⟨11154900072214878827093479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 59492800385146020411165221 11154900072214878827093479)
      ·
        refine ⟨16732350108322318240640219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11154900072214878827093479 16732350108322318240640219)
        ·
          refine ⟨25098525162483477360960329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16732350108322318240640219 25098525162483477360960329)
          ·
            refine ⟨18823893871862608020720247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25098525162483477360960329 18823893871862608020720247)
            ·
              refine ⟨28235840807793912031080371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18823893871862608020720247 28235840807793912031080371)
              ·
                refine ⟨42353761211690868046620557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28235840807793912031080371 42353761211690868046620557)
                ·
                  refine ⟨15882660454384075517482709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 42353761211690868046620557 15882660454384075517482709)
                  ·
                    refine ⟨372249854399626769941001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 15882660454384075517482709 372249854399626769941001)
                    ·
                      rfl

theorem cell22_1087431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 1, 3, 7].length) (baseStart_1087431 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1087431 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1087431 prefixEnd_1087431 := by exact prefixLift 1087431
  have htrace : WordTrace (prefixWord ++ tailWord_1087431) baseStart_1087431 baseEnd_1087431 := by
    simpa [prefixWord, tailWord_1087431, baseEnd_1087431] using wordTrace_append hprefix tailTrace_1087431
  have hstable : (prefixWord ++ tailWord_1087431).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1087431).length < 2 ^ (prefixWord ++ tailWord_1087431).sum := by decide
  have hdescent : baseEnd_1087431 < baseStart_1087431 := by decide
  rcases family_descends (prefixWord ++ tailWord_1087431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1087512 : List Nat := [2, 1, 2, 3, 2, 1, 5, 2, 4]
def baseStart_1087512 : Nat := 118140960795 + 1087512 * 2 ^ 59
def prefixEnd_1087512 : Nat := 4983230072969 + 3 ^ 40 * 1087512 * 2
def baseEnd_1087512 : Nat := 124092527451656519555251

theorem tailTrace_1087512 : CollatzResearch.WordTrace tailWord_1087512 prefixEnd_1087512 124092527451656519555251 := by
  unfold tailWord_1087512
  simp only [CollatzResearch.WordTrace]
  refine ⟨19832410618068615553904395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26443214157424820738539193 19832410618068615553904395)
  ·
    refine ⟨29748615927102923330856593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19832410618068615553904395 29748615927102923330856593)
    ·
      refine ⟨22311461945327192498142445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29748615927102923330856593 22311461945327192498142445)
      ·
        refine ⟨8366798229497697186803417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22311461945327192498142445 8366798229497697186803417)
        ·
          refine ⟨6275098672123272890102563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8366798229497697186803417 6275098672123272890102563)
          ·
            refine ⟨9412648008184909335153845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6275098672123272890102563 9412648008184909335153845)
            ·
              refine ⟨882435750767335250170673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9412648008184909335153845 882435750767335250170673)
              ·
                refine ⟨661826813075501437628005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 882435750767335250170673 661826813075501437628005)
                ·
                  refine ⟨124092527451656519555251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 661826813075501437628005 124092527451656519555251)
                  ·
                    rfl

theorem cell22_1087512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 5, 2, 4].length) (baseStart_1087512 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1087512 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1087512 prefixEnd_1087512 := by exact prefixLift 1087512
  have htrace : WordTrace (prefixWord ++ tailWord_1087512) baseStart_1087512 baseEnd_1087512 := by
    simpa [prefixWord, tailWord_1087512, baseEnd_1087512] using wordTrace_append hprefix tailTrace_1087512
  have hstable : (prefixWord ++ tailWord_1087512).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1087512).length < 2 ^ (prefixWord ++ tailWord_1087512).sum := by decide
  have hdescent : baseEnd_1087512 < baseStart_1087512 := by decide
  rcases family_descends (prefixWord ++ tailWord_1087512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1087523 : List Nat := [1, 1, 1, 4, 3, 1, 4, 7]
def baseStart_1087523 : Nat := 118140960795 + 1087523 * 2 ^ 59
def prefixEnd_1087523 : Nat := 4983230072969 + 3 ^ 40 * 1087523 * 2
def baseEnd_1087523 : Nat := 41364594208863244071191

theorem tailTrace_1087523 : CollatzResearch.WordTrace tailWord_1087523 prefixEnd_1087523 41364594208863244071191 := by
  unfold tailWord_1087523
  simp only [CollatzResearch.WordTrace]
  refine ⟨39665222439097379986459223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26443481626064919990972815 39665222439097379986459223)
  ·
    refine ⟨59497833658646069979688835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39665222439097379986459223 59497833658646069979688835)
    ·
      refine ⟨89246750487969104969533253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59497833658646069979688835 89246750487969104969533253)
      ·
        refine ⟨16733765716494207181787485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 89246750487969104969533253 16733765716494207181787485)
        ·
          refine ⟨6275162143685327693170307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16733765716494207181787485 6275162143685327693170307)
          ·
            refine ⟨9412743215527991539755461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6275162143685327693170307 9412743215527991539755461)
            ·
              refine ⟨1764889352911498413704149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9412743215527991539755461 1764889352911498413704149)
              ·
                refine ⟨41364594208863244071191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1764889352911498413704149 41364594208863244071191)
                ·
                  rfl

theorem cell22_1087523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 4, 7].length) (baseStart_1087523 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1087523 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1087523 prefixEnd_1087523 := by exact prefixLift 1087523
  have htrace : WordTrace (prefixWord ++ tailWord_1087523) baseStart_1087523 baseEnd_1087523 := by
    simpa [prefixWord, tailWord_1087523, baseEnd_1087523] using wordTrace_append hprefix tailTrace_1087523
  have hstable : (prefixWord ++ tailWord_1087523).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1087523).length < 2 ^ (prefixWord ++ tailWord_1087523).sum := by decide
  have hdescent : baseEnd_1087523 < baseStart_1087523 := by decide
  rcases family_descends (prefixWord ++ tailWord_1087523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1087542 : List Nat := [5, 1, 2, 1, 1, 1, 4, 1, 2, 4]
def baseStart_1087542 : Nat := 118140960795 + 1087542 * 2 ^ 59
def prefixEnd_1087542 : Nat := 4983230072969 + 3 ^ 40 * 1087542 * 2
def baseEnd_1087542 : Nat := 372287851968059480415661

theorem tailTrace_1087542 : CollatzResearch.WordTrace tailWord_1087542 prefixEnd_1087542 372287851968059480415661 := by
  unfold tailWord_1087542
  simp only [CollatzResearch.WordTrace]
  refine ⟨2479119714126784139462555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 26443943617352364154267253 2479119714126784139462555)
  ·
    refine ⟨3718679571190176209193833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2479119714126784139462555 3718679571190176209193833)
    ·
      refine ⟨2789009678392632156895375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3718679571190176209193833 2789009678392632156895375)
      ·
        refine ⟨4183514517588948235343063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2789009678392632156895375 4183514517588948235343063)
        ·
          refine ⟨6275271776383422353014595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4183514517588948235343063 6275271776383422353014595)
          ·
            refine ⟨9412907664575133529521893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6275271776383422353014595 9412907664575133529521893)
            ·
              refine ⟨1764920187107837536785355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9412907664575133529521893 1764920187107837536785355)
              ·
                refine ⟨2647380280661756305178033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1764920187107837536785355 2647380280661756305178033)
                ·
                  refine ⟨1985535210496317228883525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2647380280661756305178033 1985535210496317228883525)
                  ·
                    refine ⟨372287851968059480415661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1985535210496317228883525 372287851968059480415661)
                    ·
                      rfl

theorem cell22_1087542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 4, 1, 2, 4].length) (baseStart_1087542 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1087542 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1087542 prefixEnd_1087542 := by exact prefixLift 1087542
  have htrace : WordTrace (prefixWord ++ tailWord_1087542) baseStart_1087542 baseEnd_1087542 := by
    simpa [prefixWord, tailWord_1087542, baseEnd_1087542] using wordTrace_append hprefix tailTrace_1087542
  have hstable : (prefixWord ++ tailWord_1087542).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1087542).length < 2 ^ (prefixWord ++ tailWord_1087542).sum := by decide
  have hdescent : baseEnd_1087542 < baseStart_1087542 := by decide
  rcases family_descends (prefixWord ++ tailWord_1087542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1087574 : List Nat := [5, 2, 2, 1, 1, 3, 1, 7]
def baseStart_1087574 : Nat := 118140960795 + 1087574 * 2 ^ 59
def prefixEnd_1087574 : Nat := 4983230072969 + 3 ^ 40 * 1087574 * 2
def baseEnd_1087574 : Nat := 41366534024669118179507

theorem tailTrace_1087574 : CollatzResearch.WordTrace tailWord_1087574 prefixEnd_1087574 41366534024669118179507 := by
  unfold tailWord_1087574
  simp only [CollatzResearch.WordTrace]
  refine ⟨2479192660119538481035361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 26444721707941743797710517 2479192660119538481035361)
  ·
    refine ⟨1859394495089653860776521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2479192660119538481035361 1859394495089653860776521)
    ·
      refine ⟨1394545871317240395582391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1859394495089653860776521 1394545871317240395582391)
      ·
        refine ⟨2091818806975860593373587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1394545871317240395582391 2091818806975860593373587)
        ·
          refine ⟨3137728210463790890060381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2091818806975860593373587 3137728210463790890060381)
          ·
            refine ⟨1176648078923921583772643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3137728210463790890060381 1176648078923921583772643)
            ·
              refine ⟨1764972118385882375658965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1176648078923921583772643 1764972118385882375658965)
              ·
                refine ⟨41366534024669118179507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1764972118385882375658965 41366534024669118179507)
                ·
                  rfl

theorem cell22_1087574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 3, 1, 7].length) (baseStart_1087574 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1087574 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1087574 prefixEnd_1087574 := by exact prefixLift 1087574
  have htrace : WordTrace (prefixWord ++ tailWord_1087574) baseStart_1087574 baseEnd_1087574 := by
    simpa [prefixWord, tailWord_1087574, baseEnd_1087574] using wordTrace_append hprefix tailTrace_1087574
  have hstable : (prefixWord ++ tailWord_1087574).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1087574).length < 2 ^ (prefixWord ++ tailWord_1087574).sum := by decide
  have hdescent : baseEnd_1087574 < baseStart_1087574 := by decide
  rcases family_descends (prefixWord ++ tailWord_1087574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1087606 : List Nat := [5, 1, 1, 2, 1, 3, 2, 3, 1, 3]
def baseStart_1087606 : Nat := 118140960795 + 1087606 * 2 ^ 59
def prefixEnd_1087606 : Nat := 4983230072969 + 3 ^ 40 * 1087606 * 2
def baseEnd_1087606 : Nat := 372309760475984646815465

theorem tailTrace_1087606 : CollatzResearch.WordTrace tailWord_1087606 prefixEnd_1087606 372309760475984646815465 := by
  unfold tailWord_1087606
  simp only [CollatzResearch.WordTrace]
  refine ⟨2479265606112292822608167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 26445499798531123441153781 2479265606112292822608167)
  ·
    refine ⟨3718898409168439233912251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2479265606112292822608167 3718898409168439233912251)
    ·
      refine ⟨5578347613752658850868377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3718898409168439233912251 5578347613752658850868377)
      ·
        refine ⟨4183760710314494138151283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5578347613752658850868377 4183760710314494138151283)
        ·
          refine ⟨6275641065471741207226925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4183760710314494138151283 6275641065471741207226925)
          ·
            refine ⟨2353365399551902952710097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6275641065471741207226925 2353365399551902952710097)
            ·
              refine ⟨1765024049663927214532573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2353365399551902952710097 1765024049663927214532573)
              ·
                refine ⟨661884018623972705449715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1765024049663927214532573 661884018623972705449715)
                ·
                  refine ⟨992826027935959058174573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 661884018623972705449715 992826027935959058174573)
                  ·
                    refine ⟨372309760475984646815465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 992826027935959058174573 372309760475984646815465)
                    ·
                      rfl

theorem cell22_1087606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 2, 3, 1, 3].length) (baseStart_1087606 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1087606 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1087606 prefixEnd_1087606 := by exact prefixLift 1087606
  have htrace : WordTrace (prefixWord ++ tailWord_1087606) baseStart_1087606 baseEnd_1087606 := by
    simpa [prefixWord, tailWord_1087606, baseEnd_1087606] using wordTrace_append hprefix tailTrace_1087606
  have hstable : (prefixWord ++ tailWord_1087606).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1087606).length < 2 ^ (prefixWord ++ tailWord_1087606).sum := by decide
  have hdescent : baseEnd_1087606 < baseStart_1087606 := by decide
  rcases family_descends (prefixWord ++ tailWord_1087606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1087628 : List Nat := [2, 2, 1, 2, 1, 1, 1, 1, 2, 9]
def baseStart_1087628 : Nat := 118140960795 + 1087628 * 2 ^ 59
def prefixEnd_1087628 : Nat := 4983230072969 + 3 ^ 40 * 1087628 * 2
def baseEnd_1087628 : Nat := 372317291525583922765397

theorem tailTrace_1087628 : CollatzResearch.WordTrace tailWord_1087628 prefixEnd_1087628 372317291525583922765397 := by
  unfold tailWord_1087628
  simp only [CollatzResearch.WordTrace]
  refine ⟨19834526051858491459515769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26446034735811321946021025 19834526051858491459515769)
  ·
    refine ⟨14875894538893868594636827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19834526051858491459515769 14875894538893868594636827)
    ·
      refine ⟨22313841808340802891955241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14875894538893868594636827 22313841808340802891955241)
      ·
        refine ⟨16735381356255602168966431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22313841808340802891955241 16735381356255602168966431)
        ·
          refine ⟨25103072034383403253449647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16735381356255602168966431 25103072034383403253449647)
          ·
            refine ⟨37654608051575104880174471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25103072034383403253449647 37654608051575104880174471)
            ·
              refine ⟨56481912077362657320261707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37654608051575104880174471 56481912077362657320261707)
              ·
                refine ⟨84722868116043985980392561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56481912077362657320261707 84722868116043985980392561)
                ·
                  refine ⟨63542151087032989485294421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 84722868116043985980392561 63542151087032989485294421)
                  ·
                    refine ⟨372317291525583922765397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 63542151087032989485294421 372317291525583922765397)
                    ·
                      rfl

theorem cell22_1087628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 1, 2, 9].length) (baseStart_1087628 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1087628 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1087628 prefixEnd_1087628 := by exact prefixLift 1087628
  have htrace : WordTrace (prefixWord ++ tailWord_1087628) baseStart_1087628 baseEnd_1087628 := by
    simpa [prefixWord, tailWord_1087628, baseEnd_1087628] using wordTrace_append hprefix tailTrace_1087628
  have hstable : (prefixWord ++ tailWord_1087628).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1087628).length < 2 ^ (prefixWord ++ tailWord_1087628).sum := by decide
  have hdescent : baseEnd_1087628 < baseStart_1087628 := by decide
  rcases family_descends (prefixWord ++ tailWord_1087628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1087636 : List Nat := [2, 4, 2, 3, 1, 1, 3, 1, 5]
def baseStart_1087636 : Nat := 118140960795 + 1087636 * 2 ^ 59
def prefixEnd_1087636 : Nat := 4983230072969 + 3 ^ 40 * 1087636 * 2
def baseEnd_1087636 : Nat := 124106676696358189521791

theorem tailTrace_1087636 : CollatzResearch.WordTrace tailWord_1087636 prefixEnd_1087636 124106676696358189521791 := by
  unfold tailWord_1087636
  simp only [CollatzResearch.WordTrace]
  refine ⟨19834671943844000142661381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26446229258458666856881841 19834671943844000142661381)
  ·
    refine ⟨3719000989470750026749009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19834671943844000142661381 3719000989470750026749009)
    ·
      refine ⟨2789250742103062520061757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3719000989470750026749009 2789250742103062520061757)
      ·
        refine ⟨1045969028288648445023159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2789250742103062520061757 1045969028288648445023159)
        ·
          refine ⟨1568953542432972667534739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1045969028288648445023159 1568953542432972667534739)
          ·
            refine ⟨2353430313649459001302109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1568953542432972667534739 2353430313649459001302109)
            ·
              refine ⟨882536367618547125488291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2353430313649459001302109 882536367618547125488291)
              ·
                refine ⟨1323804551427820688232437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 882536367618547125488291 1323804551427820688232437)
                ·
                  refine ⟨124106676696358189521791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1323804551427820688232437 124106676696358189521791)
                  ·
                    rfl

theorem cell22_1087636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 3, 1, 5].length) (baseStart_1087636 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1087636 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1087636 prefixEnd_1087636 := by exact prefixLift 1087636
  have htrace : WordTrace (prefixWord ++ tailWord_1087636) baseStart_1087636 baseEnd_1087636 := by
    simpa [prefixWord, tailWord_1087636, baseEnd_1087636] using wordTrace_append hprefix tailTrace_1087636
  have hstable : (prefixWord ++ tailWord_1087636).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1087636).length < 2 ^ (prefixWord ++ tailWord_1087636).sum := by decide
  have hdescent : baseEnd_1087636 < baseStart_1087636 := by decide
  rcases family_descends (prefixWord ++ tailWord_1087636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1087643 : List Nat := [1, 1, 1, 1, 1, 1, 2, 5, 3, 6]
def baseStart_1087643 : Nat := 118140960795 + 1087643 * 2 ^ 59
def prefixEnd_1087643 : Nat := 4983230072969 + 3 ^ 40 * 1087643 * 2
def baseEnd_1087643 : Nat := 372322426332128883640351

theorem tailTrace_1087643 : CollatzResearch.WordTrace tailWord_1087643 prefixEnd_1087643 372322426332128883640351 := by
  unfold tailWord_1087643
  simp only [CollatzResearch.WordTrace]
  refine ⟨39669599198662640480827583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26446399465775093653885055 39669599198662640480827583)
  ·
    refine ⟨59504398797993960721241375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39669599198662640480827583 59504398797993960721241375)
    ·
      refine ⟨89256598196990941081862063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59504398797993960721241375 89256598196990941081862063)
      ·
        refine ⟨133884897295486411622793095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89256598196990941081862063 133884897295486411622793095)
        ·
          refine ⟨200827345943229617434189643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 133884897295486411622793095 200827345943229617434189643)
          ·
            refine ⟨301241018914844426151284465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 200827345943229617434189643 301241018914844426151284465)
            ·
              refine ⟨225930764186133319613463349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 301241018914844426151284465 225930764186133319613463349)
              ·
                refine ⟨21181009142449998713762189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 225930764186133319613463349 21181009142449998713762189)
                ·
                  refine ⟨7942878428418749517660821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21181009142449998713762189 7942878428418749517660821)
                  ·
                    refine ⟨372322426332128883640351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7942878428418749517660821 372322426332128883640351)
                    ·
                      rfl

theorem cell22_1087643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 5, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 5, 3, 6].length) (baseStart_1087643 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1087643 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1087643 prefixEnd_1087643 := by exact prefixLift 1087643
  have htrace : WordTrace (prefixWord ++ tailWord_1087643) baseStart_1087643 baseEnd_1087643 := by
    simpa [prefixWord, tailWord_1087643, baseEnd_1087643] using wordTrace_append hprefix tailTrace_1087643
  have hstable : (prefixWord ++ tailWord_1087643).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1087643).length < 2 ^ (prefixWord ++ tailWord_1087643).sum := by decide
  have hdescent : baseEnd_1087643 < baseStart_1087643 := by decide
  rcases family_descends (prefixWord ++ tailWord_1087643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1087681 : List Nat := [1, 2, 6, 1, 3, 1, 1, 1, 6]
def baseStart_1087681 : Nat := 118140960795 + 1087681 * 2 ^ 59
def prefixEnd_1087681 : Nat := 4983230072969 + 3 ^ 40 * 1087681 * 2
def baseEnd_1087681 : Nat := 124111811502903150396745

theorem tailTrace_1087681 : CollatzResearch.WordTrace tailWord_1087681 prefixEnd_1087681 124111811502903150396745 := by
  unfold tailWord_1087681
  simp only [CollatzResearch.WordTrace]
  refine ⟨39670985172524972970710897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26447323448349981980473931 39670985172524972970710897)
  ·
    refine ⟨29753238879393729728033173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39670985172524972970710897 29753238879393729728033173)
    ·
      refine ⟨1394683072471581081001555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 29753238879393729728033173 1394683072471581081001555)
      ·
        refine ⟨2092024608707371621502333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1394683072471581081001555 2092024608707371621502333)
        ·
          refine ⟨784509228265264358063375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2092024608707371621502333 784509228265264358063375)
          ·
            refine ⟨1176763842397896537095063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 784509228265264358063375 1176763842397896537095063)
            ·
              refine ⟨1765145763596844805642595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1176763842397896537095063 1765145763596844805642595)
              ·
                refine ⟨2647718645395267208463893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1765145763596844805642595 2647718645395267208463893)
                ·
                  refine ⟨124111811502903150396745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2647718645395267208463893 124111811502903150396745)
                  ·
                    rfl

theorem cell22_1087681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 3, 1, 1, 1, 6].length) (baseStart_1087681 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1087681 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1087681 prefixEnd_1087681 := by exact prefixLift 1087681
  have htrace : WordTrace (prefixWord ++ tailWord_1087681) baseStart_1087681 baseEnd_1087681 := by
    simpa [prefixWord, tailWord_1087681, baseEnd_1087681] using wordTrace_append hprefix tailTrace_1087681
  have hstable : (prefixWord ++ tailWord_1087681).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1087681).length < 2 ^ (prefixWord ++ tailWord_1087681).sum := by decide
  have hdescent : baseEnd_1087681 < baseStart_1087681 := by decide
  rcases family_descends (prefixWord ++ tailWord_1087681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1087724 : List Nat := [2, 2, 1, 1, 2, 3, 2, 5, 1, 3]
def baseStart_1087724 : Nat := 118140960795 + 1087724 * 2 ^ 59
def prefixEnd_1087724 : Nat := 4983230072969 + 3 ^ 40 * 1087724 * 2
def baseEnd_1087724 : Nat := 372350154287471672365103

theorem tailTrace_1087724 : CollatzResearch.WordTrace tailWord_1087724 prefixEnd_1087724 372350154287471672365103 := by
  unfold tailWord_1087724
  simp only [CollatzResearch.WordTrace]
  refine ⟨19836276755684595657263113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26448369007579460876350817 19836276755684595657263113)
  ·
    refine ⟨14877207566763446742947335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19836276755684595657263113 14877207566763446742947335)
    ·
      refine ⟨22315811350145170114421003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14877207566763446742947335 22315811350145170114421003)
      ·
        refine ⟨33473717025217755171631505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22315811350145170114421003 33473717025217755171631505)
        ·
          refine ⟨25105287768913316378723629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33473717025217755171631505 25105287768913316378723629)
          ·
            refine ⟨9414482913342493642021361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25105287768913316378723629 9414482913342493642021361)
            ·
              refine ⟨7060862185006870231516021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9414482913342493642021361 7060862185006870231516021)
              ·
                refine ⟨661955829844394084204627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7060862185006870231516021 661955829844394084204627)
                ·
                  refine ⟨992933744766591126306941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 661955829844394084204627 992933744766591126306941)
                  ·
                    refine ⟨372350154287471672365103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 992933744766591126306941 372350154287471672365103)
                    ·
                      rfl

theorem cell22_1087724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 2, 5, 1, 3].length) (baseStart_1087724 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1087724 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1087724 prefixEnd_1087724 := by exact prefixLift 1087724
  have htrace : WordTrace (prefixWord ++ tailWord_1087724) baseStart_1087724 baseEnd_1087724 := by
    simpa [prefixWord, tailWord_1087724, baseEnd_1087724] using wordTrace_append hprefix tailTrace_1087724
  have hstable : (prefixWord ++ tailWord_1087724).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1087724).length < 2 ^ (prefixWord ++ tailWord_1087724).sum := by decide
  have hdescent : baseEnd_1087724 < baseStart_1087724 := by decide
  rcases family_descends (prefixWord ++ tailWord_1087724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1087752 : List Nat := [2, 1, 3, 2, 3, 2, 1, 1, 2, 5]
def baseStart_1087752 : Nat := 118140960795 + 1087752 * 2 ^ 59
def prefixEnd_1087752 : Nat := 4983230072969 + 3 ^ 40 * 1087752 * 2
def baseEnd_1087752 : Nat := 372359739259688932665017

theorem tailTrace_1087752 : CollatzResearch.WordTrace tailWord_1087752 prefixEnd_1087752 372359739259688932665017 := by
  unfold tailWord_1087752
  simp only [CollatzResearch.WordTrace]
  refine ⟨19836787377633876048272755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26449049836845168064363673 19836787377633876048272755)
  ·
    refine ⟨29755181066450814072409133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19836787377633876048272755 29755181066450814072409133)
    ·
      refine ⟨11158192899919055277153425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29755181066450814072409133 11158192899919055277153425)
      ·
        refine ⟨8368644674939291457865069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11158192899919055277153425 8368644674939291457865069)
        ·
          refine ⟨3138241753102234296699401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8368644674939291457865069 3138241753102234296699401)
          ·
            refine ⟨2353681314826675722524551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3138241753102234296699401 2353681314826675722524551)
            ·
              refine ⟨3530521972240013583786827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2353681314826675722524551 3530521972240013583786827)
              ·
                refine ⟨5295782958360020375680241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3530521972240013583786827 5295782958360020375680241)
                ·
                  refine ⟨3971837218770015281760181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5295782958360020375680241 3971837218770015281760181)
                  ·
                    refine ⟨372359739259688932665017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3971837218770015281760181 372359739259688932665017)
                    ·
                      rfl

theorem cell22_1087752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 1, 1, 2, 5].length) (baseStart_1087752 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1087752 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1087752 prefixEnd_1087752 := by exact prefixLift 1087752
  have htrace : WordTrace (prefixWord ++ tailWord_1087752) baseStart_1087752 baseEnd_1087752 := by
    simpa [prefixWord, tailWord_1087752, baseEnd_1087752] using wordTrace_append hprefix tailTrace_1087752
  have hstable : (prefixWord ++ tailWord_1087752).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1087752).length < 2 ^ (prefixWord ++ tailWord_1087752).sum := by decide
  have hdescent : baseEnd_1087752 < baseStart_1087752 := by decide
  rcases family_descends (prefixWord ++ tailWord_1087752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1087765 : List Nat := [1, 3, 2, 1, 2, 1, 3, 1, 8]
def baseStart_1087765 : Nat := 118140960795 + 1087765 * 2 ^ 59
def prefixEnd_1087765 : Nat := 4983230072969 + 3 ^ 40 * 1087765 * 2
def baseEnd_1087765 : Nat := 124121396475120410696659

theorem tailTrace_1087765 : CollatzResearch.WordTrace tailWord_1087765 prefixEnd_1087765 124121396475120410696659 := by
  unfold tailWord_1087765
  simp only [CollatzResearch.WordTrace]
  refine ⟨39674048904220655316768749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26449365936147103544512499 39674048904220655316768749)
  ·
    refine ⟨14877768339082745743788281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39674048904220655316768749 14877768339082745743788281)
    ·
      refine ⟨11158326254312059307841211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14877768339082745743788281 11158326254312059307841211)
      ·
        refine ⟨16737489381468088961761817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11158326254312059307841211 16737489381468088961761817)
        ·
          refine ⟨12553117036101066721321363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16737489381468088961761817 12553117036101066721321363)
          ·
            refine ⟨18829675554151600081982045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12553117036101066721321363 18829675554151600081982045)
            ·
              refine ⟨7061128332806850030743267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18829675554151600081982045 7061128332806850030743267)
              ·
                refine ⟨10591692499210275046114901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7061128332806850030743267 10591692499210275046114901)
                ·
                  refine ⟨124121396475120410696659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 10591692499210275046114901 124121396475120410696659)
                  ·
                    rfl

theorem cell22_1087765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 3, 1, 8].length) (baseStart_1087765 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1087765 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1087765 prefixEnd_1087765 := by exact prefixLift 1087765
  have htrace : WordTrace (prefixWord ++ tailWord_1087765) baseStart_1087765 baseEnd_1087765 := by
    simpa [prefixWord, tailWord_1087765, baseEnd_1087765] using wordTrace_append hprefix tailTrace_1087765
  have hstable : (prefixWord ++ tailWord_1087765).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1087765).length < 2 ^ (prefixWord ++ tailWord_1087765).sum := by decide
  have hdescent : baseEnd_1087765 < baseStart_1087765 := by decide
  rcases family_descends (prefixWord ++ tailWord_1087765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1087767 : List Nat := [1, 1, 3, 4, 1, 2, 2, 1, 3, 4]
def baseStart_1087767 : Nat := 118140960795 + 1087767 * 2 ^ 59
def prefixEnd_1087767 : Nat := 4983230072969 + 3 ^ 40 * 1087767 * 2
def baseEnd_1087767 : Nat := 372364874066233893539971

theorem tailTrace_1087767 : CollatzResearch.WordTrace tailWord_1087767 prefixEnd_1087767 372364874066233893539971 := by
  unfold tailWord_1087767
  simp only [CollatzResearch.WordTrace]
  refine ⟨39674121850213409658341555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26449414566808939772227703 39674121850213409658341555)
  ·
    refine ⟨59511182775320114487512333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39674121850213409658341555 59511182775320114487512333)
    ·
      refine ⟨22316693540745042932817125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59511182775320114487512333 22316693540745042932817125)
      ·
        refine ⟨4184380038889695549903211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22316693540745042932817125 4184380038889695549903211)
        ·
          refine ⟨6276570058334543324854817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4184380038889695549903211 6276570058334543324854817)
          ·
            refine ⟨4707427543750907493641113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6276570058334543324854817 4707427543750907493641113)
            ·
              refine ⟨3530570657813180620230835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4707427543750907493641113 3530570657813180620230835)
              ·
                refine ⟨5295855986719770930346253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3530570657813180620230835 5295855986719770930346253)
                ·
                  refine ⟨1985945995019914098879845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5295855986719770930346253 1985945995019914098879845)
                  ·
                    refine ⟨372364874066233893539971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1985945995019914098879845 372364874066233893539971)
                    ·
                      rfl

theorem cell22_1087767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 2, 1, 3, 4].length) (baseStart_1087767 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1087767 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1087767 prefixEnd_1087767 := by exact prefixLift 1087767
  have htrace : WordTrace (prefixWord ++ tailWord_1087767) baseStart_1087767 baseEnd_1087767 := by
    simpa [prefixWord, tailWord_1087767, baseEnd_1087767] using wordTrace_append hprefix tailTrace_1087767
  have hstable : (prefixWord ++ tailWord_1087767).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1087767).length < 2 ^ (prefixWord ++ tailWord_1087767).sum := by decide
  have hdescent : baseEnd_1087767 < baseStart_1087767 := by decide
  rcases family_descends (prefixWord ++ tailWord_1087767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1087962 : List Nat := [3, 1, 1, 2, 3, 1, 11]
def baseStart_1087962 : Nat := 118140960795 + 1087962 * 2 ^ 59
def prefixEnd_1087962 : Nat := 4983230072969 + 3 ^ 40 * 1087962 * 2
def baseEnd_1087962 : Nat := 13793763946345125367199

theorem tailTrace_1087962 : CollatzResearch.WordTrace tailWord_1087962 prefixEnd_1087962 13793763946345125367199 := by
  unfold tailWord_1087962
  simp only [CollatzResearch.WordTrace]
  refine ⟨9920308521126739490422535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26454156056337971974460093 9920308521126739490422535)
  ·
    refine ⟨14880462781690109235633803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9920308521126739490422535 14880462781690109235633803)
    ·
      refine ⟨22320694172535163853450705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14880462781690109235633803 22320694172535163853450705)
      ·
        refine ⟨16740520629401372890088029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22320694172535163853450705 16740520629401372890088029)
        ·
          refine ⟨6277695236025514833783011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16740520629401372890088029 6277695236025514833783011)
          ·
            refine ⟨9416542854038272250674517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6277695236025514833783011 9416542854038272250674517)
            ·
              refine ⟨13793763946345125367199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 9416542854038272250674517 13793763946345125367199)
              ·
                rfl

theorem cell22_1087962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 11].length) (baseStart_1087962 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1087962 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1087962 prefixEnd_1087962 := by exact prefixLift 1087962
  have htrace : WordTrace (prefixWord ++ tailWord_1087962) baseStart_1087962 baseEnd_1087962 := by
    simpa [prefixWord, tailWord_1087962, baseEnd_1087962] using wordTrace_append hprefix tailTrace_1087962
  have hstable : (prefixWord ++ tailWord_1087962).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1087962).length < 2 ^ (prefixWord ++ tailWord_1087962).sum := by decide
  have hdescent : baseEnd_1087962 < baseStart_1087962 := by decide
  rcases family_descends (prefixWord ++ tailWord_1087962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1087994 : List Nat := [3, 1, 1, 1, 1, 2, 2, 3, 5, 3]
def baseStart_1087994 : Nat := 118140960795 + 1087994 * 2 ^ 59
def prefixEnd_1087994 : Nat := 4983230072969 + 3 ^ 40 * 1087994 * 2
def baseEnd_1087994 : Nat := 372442580805280968114275

theorem tailTrace_1087994 : CollatzResearch.WordTrace tailWord_1087994 prefixEnd_1087994 372442580805280968114275 := by
  unfold tailWord_1087994
  simp only [CollatzResearch.WordTrace]
  refine ⟨9920600305097756856713759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26454934146927351617903357 9920600305097756856713759)
  ·
    refine ⟨14880900457646635285070639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9920600305097756856713759 14880900457646635285070639)
    ·
      refine ⟨22321350686469952927605959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14880900457646635285070639 22321350686469952927605959)
      ·
        refine ⟨33482026029704929391408939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22321350686469952927605959 33482026029704929391408939)
        ·
          refine ⟨50223039044557394087113409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33482026029704929391408939 50223039044557394087113409)
          ·
            refine ⟨37667279283418045565335057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50223039044557394087113409 37667279283418045565335057)
            ·
              refine ⟨28250459462563534174001293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37667279283418045565335057 28250459462563534174001293)
              ·
                refine ⟨10593922298461325315250485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28250459462563534174001293 10593922298461325315250485)
                ·
                  refine ⟨993180215480749248304733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 10593922298461325315250485 993180215480749248304733)
                  ·
                    refine ⟨372442580805280968114275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 993180215480749248304733 372442580805280968114275)
                    ·
                      rfl

theorem cell22_1087994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 3, 5, 3].length) (baseStart_1087994 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1087994 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1087994 prefixEnd_1087994 := by exact prefixLift 1087994
  have htrace : WordTrace (prefixWord ++ tailWord_1087994) baseStart_1087994 baseEnd_1087994 := by
    simpa [prefixWord, tailWord_1087994, baseEnd_1087994] using wordTrace_append hprefix tailTrace_1087994
  have hstable : (prefixWord ++ tailWord_1087994).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1087994).length < 2 ^ (prefixWord ++ tailWord_1087994).sum := by decide
  have hdescent : baseEnd_1087994 < baseStart_1087994 := by decide
  rcases family_descends (prefixWord ++ tailWord_1087994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1088002 : List Nat := [3, 4, 1, 2, 3, 1, 1, 3, 4]
def baseStart_1088002 : Nat := 118140960795 + 1088002 * 2 ^ 59
def prefixEnd_1088002 : Nat := 4983230072969 + 3 ^ 40 * 1088002 * 2
def baseEnd_1088002 : Nat := 124148439789590537971417

theorem tailTrace_1088002 : CollatzResearch.WordTrace tailWord_1088002 prefixEnd_1088002 124148439789590537971417 := by
  unfold tailWord_1088002
  simp only [CollatzResearch.WordTrace]
  refine ⟨9920673251090511198286565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26455128669574696528764173 9920673251090511198286565)
  ·
    refine ⟨1860126234579470849678731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9920673251090511198286565 1860126234579470849678731)
    ·
      refine ⟨2790189351869206274518097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1860126234579470849678731 2790189351869206274518097)
      ·
        refine ⟨2092642013901904705888573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2790189351869206274518097 2092642013901904705888573)
        ·
          refine ⟨784740755213214264708215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2092642013901904705888573 784740755213214264708215)
          ·
            refine ⟨1177111132819821397062323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 784740755213214264708215 1177111132819821397062323)
            ·
              refine ⟨1765666699229732095593485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1177111132819821397062323 1765666699229732095593485)
              ·
                refine ⟨662125012211149535847557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1765666699229732095593485 662125012211149535847557)
                ·
                  refine ⟨124148439789590537971417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 662125012211149535847557 124148439789590537971417)
                  ·
                    rfl

theorem cell22_1088002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 3, 1, 1, 3, 4].length) (baseStart_1088002 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1088002 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1088002 prefixEnd_1088002 := by exact prefixLift 1088002
  have htrace : WordTrace (prefixWord ++ tailWord_1088002) baseStart_1088002 baseEnd_1088002 := by
    simpa [prefixWord, tailWord_1088002, baseEnd_1088002] using wordTrace_append hprefix tailTrace_1088002
  have hstable : (prefixWord ++ tailWord_1088002).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1088002).length < 2 ^ (prefixWord ++ tailWord_1088002).sum := by decide
  have hdescent : baseEnd_1088002 < baseStart_1088002 := by decide
  rcases family_descends (prefixWord ++ tailWord_1088002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1088013 : List Nat := [1, 7, 1, 1, 1, 3, 8]
def baseStart_1088013 : Nat := 118140960795 + 1088013 * 2 ^ 59
def prefixEnd_1088013 : Nat := 4983230072969 + 3 ^ 40 * 1088013 * 2
def baseEnd_1088013 : Nat := 13794410551613750069971

theorem tailTrace_1088013 : CollatzResearch.WordTrace tailWord_1088013 prefixEnd_1088013 13794410551613750069971 := by
  unfold tailWord_1088013
  simp only [CollatzResearch.WordTrace]
  refine ⟨39683094207322193671796693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26455396138214795781197795 39683094207322193671796693)
  ·
    refine ⟨930072520484113914182735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 39683094207322193671796693 930072520484113914182735)
    ·
      refine ⟨1395108780726170871274103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 930072520484113914182735 1395108780726170871274103)
      ·
        refine ⟨2092663171089256306911155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1395108780726170871274103 2092663171089256306911155)
        ·
          refine ⟨3138994756633884460366733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2092663171089256306911155 3138994756633884460366733)
          ·
            refine ⟨1177123033737706672637525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3138994756633884460366733 1177123033737706672637525)
            ·
              refine ⟨13794410551613750069971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1177123033737706672637525 13794410551613750069971)
              ·
                rfl

theorem cell22_1088013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 3, 8].length) (baseStart_1088013 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1088013 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1088013 prefixEnd_1088013 := by exact prefixLift 1088013
  have htrace : WordTrace (prefixWord ++ tailWord_1088013) baseStart_1088013 baseEnd_1088013 := by
    simpa [prefixWord, tailWord_1088013, baseEnd_1088013] using wordTrace_append hprefix tailTrace_1088013
  have hstable : (prefixWord ++ tailWord_1088013).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1088013).length < 2 ^ (prefixWord ++ tailWord_1088013).sum := by decide
  have hdescent : baseEnd_1088013 < baseStart_1088013 := by decide
  rcases family_descends (prefixWord ++ tailWord_1088013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1088024 : List Nat := [2, 1, 2, 3, 3, 1, 2, 1, 7]
def baseStart_1088024 : Nat := 118140960795 + 1088024 * 2 ^ 59
def prefixEnd_1088024 : Nat := 4983230072969 + 3 ^ 40 * 1088024 * 2
def baseEnd_1088024 : Nat := 124150950139456963288061

theorem tailTrace_1088024 : CollatzResearch.WordTrace tailWord_1088024 prefixEnd_1088024 124150950139456963288061 := by
  unfold tailWord_1088024
  simp only [CollatzResearch.WordTrace]
  refine ⟨19841747705141171275223563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26455663606854895033631417 19841747705141171275223563)
  ·
    refine ⟨29762621557711756912835345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19841747705141171275223563 29762621557711756912835345)
    ·
      refine ⟨22321966168283817684626509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29762621557711756912835345 22321966168283817684626509)
      ·
        refine ⟨8370737313106431631734941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22321966168283817684626509 8370737313106431631734941)
        ·
          refine ⟨3139026492414911861900603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8370737313106431631734941 3139026492414911861900603)
          ·
            refine ⟨4708539738622367792850905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3139026492414911861900603 4708539738622367792850905)
            ·
              refine ⟨3531404803966775844638179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4708539738622367792850905 3531404803966775844638179)
              ·
                refine ⟨5297107205950163766957269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3531404803966775844638179 5297107205950163766957269)
                ·
                  refine ⟨124150950139456963288061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5297107205950163766957269 124150950139456963288061)
                  ·
                    rfl

theorem cell22_1088024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 2, 1, 7].length) (baseStart_1088024 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1088024 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1088024 prefixEnd_1088024 := by exact prefixLift 1088024
  have htrace : WordTrace (prefixWord ++ tailWord_1088024) baseStart_1088024 baseEnd_1088024 := by
    simpa [prefixWord, tailWord_1088024, baseEnd_1088024] using wordTrace_append hprefix tailTrace_1088024
  have hstable : (prefixWord ++ tailWord_1088024).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1088024).length < 2 ^ (prefixWord ++ tailWord_1088024).sum := by decide
  have hdescent : baseEnd_1088024 < baseStart_1088024 := by decide
  rcases family_descends (prefixWord ++ tailWord_1088024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1088028 : List Nat := [2, 2, 3, 1, 2, 4, 1, 1, 3, 3]
def baseStart_1088028 : Nat := 118140960795 + 1088028 * 2 ^ 59
def prefixEnd_1088028 : Nat := 4983230072969 + 3 ^ 40 * 1088028 * 2
def baseEnd_1088028 : Nat := 372454219700116212764171

theorem tailTrace_1088028 : CollatzResearch.WordTrace tailWord_1088028 prefixEnd_1088028 372454219700116212764171 := by
  unfold tailWord_1088028
  simp only [CollatzResearch.WordTrace]
  refine ⟨19841820651133925616796369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26455760868178567489061825 19841820651133925616796369)
  ·
    refine ⟨14881365488350444212597277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19841820651133925616796369 14881365488350444212597277)
    ·
      refine ⟨5580512058131416579723979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14881365488350444212597277 5580512058131416579723979)
      ·
        refine ⟨8370768087197124869585969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5580512058131416579723979 8370768087197124869585969)
        ·
          refine ⟨6278076065397843652189477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8370768087197124869585969 6278076065397843652189477)
          ·
            refine ⟨1177139262262095684785527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6278076065397843652189477 1177139262262095684785527)
            ·
              refine ⟨1765708893393143527178291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1177139262262095684785527 1765708893393143527178291)
              ·
                refine ⟨2648563340089715290767437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1765708893393143527178291 2648563340089715290767437)
                ·
                  refine ⟨993211252533643234037789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2648563340089715290767437 993211252533643234037789)
                  ·
                    refine ⟨372454219700116212764171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 993211252533643234037789 372454219700116212764171)
                    ·
                      rfl

theorem cell22_1088028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 4, 1, 1, 3, 3].length) (baseStart_1088028 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1088028 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1088028 prefixEnd_1088028 := by exact prefixLift 1088028
  have htrace : WordTrace (prefixWord ++ tailWord_1088028) baseStart_1088028 baseEnd_1088028 := by
    simpa [prefixWord, tailWord_1088028, baseEnd_1088028] using wordTrace_append hprefix tailTrace_1088028
  have hstable : (prefixWord ++ tailWord_1088028).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1088028).length < 2 ^ (prefixWord ++ tailWord_1088028).sum := by decide
  have hdescent : baseEnd_1088028 < baseStart_1088028 := by decide
  rcases family_descends (prefixWord ++ tailWord_1088028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1088099 : List Nat := [1, 1, 1, 5, 1, 2, 2, 2, 1, 6]
def baseStart_1088099 : Nat := 118140960795 + 1088099 * 2 ^ 59
def prefixEnd_1088099 : Nat := 4983230072969 + 3 ^ 40 * 1088099 * 2
def baseEnd_1088099 : Nat := 372478524451095694238953

theorem tailTrace_1088099 : CollatzResearch.WordTrace tailWord_1088099 prefixEnd_1088099 372478524451095694238953 := by
  unfold tailWord_1088099
  simp only [CollatzResearch.WordTrace]
  refine ⟨39686230885010630359427351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26457487256673753572951567 39686230885010630359427351)
  ·
    refine ⟨59529346327515945539141027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39686230885010630359427351 59529346327515945539141027)
    ·
      refine ⟨89294019491273918308711541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59529346327515945539141027 89294019491273918308711541)
      ·
        refine ⟨8371314327306929841441707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 89294019491273918308711541 8371314327306929841441707)
        ·
          refine ⟨12556971490960394762162561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8371314327306929841441707 12556971490960394762162561)
          ·
            refine ⟨9417728618220296071621921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12556971490960394762162561 9417728618220296071621921)
            ·
              refine ⟨7063296463665222053716441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9417728618220296071621921 7063296463665222053716441)
              ·
                refine ⟨5297472347748916540287331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7063296463665222053716441 5297472347748916540287331)
                ·
                  refine ⟨7946208521623374810430997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5297472347748916540287331 7946208521623374810430997)
                  ·
                    refine ⟨372478524451095694238953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7946208521623374810430997 372478524451095694238953)
                    ·
                      rfl

theorem cell22_1088099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 2, 2, 1, 6].length) (baseStart_1088099 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1088099 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1088099 prefixEnd_1088099 := by exact prefixLift 1088099
  have htrace : WordTrace (prefixWord ++ tailWord_1088099) baseStart_1088099 baseEnd_1088099 := by
    simpa [prefixWord, tailWord_1088099, baseEnd_1088099] using wordTrace_append hprefix tailTrace_1088099
  have hstable : (prefixWord ++ tailWord_1088099).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1088099).length < 2 ^ (prefixWord ++ tailWord_1088099).sum := by decide
  have hdescent : baseEnd_1088099 < baseStart_1088099 := by decide
  rcases family_descends (prefixWord ++ tailWord_1088099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1088223 : List Nat := [1, 1, 2, 3, 2, 3, 3, 2, 1, 4]
def baseStart_1088223 : Nat := 118140960795 + 1088223 * 2 ^ 59
def prefixEnd_1088223 : Nat := 4983230072969 + 3 ^ 40 * 1088223 * 2
def baseEnd_1088223 : Nat := 372520972185200704138573

theorem tailTrace_1088223 : CollatzResearch.WordTrace tailWord_1088223 prefixEnd_1088223 372520972185200704138573 := by
  unfold tailWord_1088223
  simp only [CollatzResearch.WordTrace]
  refine ⟨39690753536561399536941323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26460502357707599691294215 39690753536561399536941323)
  ·
    refine ⟨59536130304842099305411985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39690753536561399536941323 59536130304842099305411985)
    ·
      refine ⟨44652097728631574479058989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59536130304842099305411985 44652097728631574479058989)
      ·
        refine ⟨16744536648236840429647121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44652097728631574479058989 16744536648236840429647121)
        ·
          refine ⟨12558402486177630322235341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16744536648236840429647121 12558402486177630322235341)
          ·
            refine ⟨4709400932316611370838253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12558402486177630322235341 4709400932316611370838253)
            ·
              refine ⟨1766025349618729264064345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4709400932316611370838253 1766025349618729264064345)
              ·
                refine ⟨1324519012214046948048259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1766025349618729264064345 1324519012214046948048259)
                ·
                  refine ⟨1986778518321070422072389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1324519012214046948048259 1986778518321070422072389)
                  ·
                    refine ⟨372520972185200704138573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1986778518321070422072389 372520972185200704138573)
                    ·
                      rfl

theorem cell22_1088223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 3, 2, 1, 4].length) (baseStart_1088223 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1088223 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1088223 prefixEnd_1088223 := by exact prefixLift 1088223
  have htrace : WordTrace (prefixWord ++ tailWord_1088223) baseStart_1088223 baseEnd_1088223 := by
    simpa [prefixWord, tailWord_1088223, baseEnd_1088223] using wordTrace_append hprefix tailTrace_1088223
  have hstable : (prefixWord ++ tailWord_1088223).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1088223).length < 2 ^ (prefixWord ++ tailWord_1088223).sum := by decide
  have hdescent : baseEnd_1088223 < baseStart_1088223 := by decide
  rcases family_descends (prefixWord ++ tailWord_1088223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1088285 : List Nat := [1, 4, 2, 4, 1, 1, 1, 1, 1, 6]
def baseStart_1088285 : Nat := 118140960795 + 1088285 * 2 ^ 59
def prefixEnd_1088285 : Nat := 4983230072969 + 3 ^ 40 * 1088285 * 2
def baseEnd_1088285 : Nat := 372542196052253209088383

theorem tailTrace_1088285 : CollatzResearch.WordTrace tailWord_1088285 prefixEnd_1088285 372542196052253209088383 := by
  unfold tailWord_1088285
  simp only [CollatzResearch.WordTrace]
  refine ⟨39693014862336784125698309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26462009908224522750465539 39693014862336784125698309)
  ·
    refine ⟨7442440286688147023568433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 39693014862336784125698309 7442440286688147023568433)
    ·
      refine ⟨5581830215016110267676325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7442440286688147023568433 5581830215016110267676325)
      ·
        refine ⟨1046593165315520675189311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5581830215016110267676325 1046593165315520675189311)
        ·
          refine ⟨1569889747973281012783967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1046593165315520675189311 1569889747973281012783967)
          ·
            refine ⟨2354834621959921519175951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1569889747973281012783967 2354834621959921519175951)
            ·
              refine ⟨3532251932939882278763927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2354834621959921519175951 3532251932939882278763927)
              ·
                refine ⟨5298377899409823418145891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3532251932939882278763927 5298377899409823418145891)
                ·
                  refine ⟨7947566849114735127218837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5298377899409823418145891 7947566849114735127218837)
                  ·
                    refine ⟨372542196052253209088383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7947566849114735127218837 372542196052253209088383)
                    ·
                      rfl

theorem cell22_1088285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 1, 1, 1, 6].length) (baseStart_1088285 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1088285 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1088285 prefixEnd_1088285 := by exact prefixLift 1088285
  have htrace : WordTrace (prefixWord ++ tailWord_1088285) baseStart_1088285 baseEnd_1088285 := by
    simpa [prefixWord, tailWord_1088285, baseEnd_1088285] using wordTrace_append hprefix tailTrace_1088285
  have hstable : (prefixWord ++ tailWord_1088285).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1088285).length < 2 ^ (prefixWord ++ tailWord_1088285).sum := by decide
  have hdescent : baseEnd_1088285 < baseStart_1088285 := by decide
  rcases family_descends (prefixWord ++ tailWord_1088285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1088311 : List Nat := [1, 1, 3, 1, 2, 1, 5, 1, 7]
def baseStart_1088311 : Nat := 118140960795 + 1088311 * 2 ^ 59
def prefixEnd_1088311 : Nat := 4983230072969 + 3 ^ 40 * 1088311 * 2
def baseEnd_1088311 : Nat := 124183698794532602646101

theorem tailTrace_1088311 : CollatzResearch.WordTrace tailWord_1088311 prefixEnd_1088311 124183698794532602646101 := by
  unfold tailWord_1088311
  simp only [CollatzResearch.WordTrace]
  refine ⟨39693963160242590566144787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26462642106828393710763191 39693963160242590566144787)
  ·
    refine ⟨59540944740363885849217181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39693963160242590566144787 59540944740363885849217181)
    ·
      refine ⟨22327854277636457193456443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59540944740363885849217181 22327854277636457193456443)
      ·
        refine ⟨33491781416454685790184665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22327854277636457193456443 33491781416454685790184665)
        ·
          refine ⟨25118836062341014342638499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33491781416454685790184665 25118836062341014342638499)
          ·
            refine ⟨37678254093511521513957749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25118836062341014342638499 37678254093511521513957749)
            ·
              refine ⟨3532336321266705141933539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 37678254093511521513957749 3532336321266705141933539)
              ·
                refine ⟨5298504481900057712900309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3532336321266705141933539 5298504481900057712900309)
                ·
                  refine ⟨124183698794532602646101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5298504481900057712900309 124183698794532602646101)
                  ·
                    rfl

theorem cell22_1088311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 5, 1, 7].length) (baseStart_1088311 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1088311 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1088311 prefixEnd_1088311 := by exact prefixLift 1088311
  have htrace : WordTrace (prefixWord ++ tailWord_1088311) baseStart_1088311 baseEnd_1088311 := by
    simpa [prefixWord, tailWord_1088311, baseEnd_1088311] using wordTrace_append hprefix tailTrace_1088311
  have hstable : (prefixWord ++ tailWord_1088311).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1088311).length < 2 ^ (prefixWord ++ tailWord_1088311).sum := by decide
  have hdescent : baseEnd_1088311 < baseStart_1088311 := by decide
  rcases family_descends (prefixWord ++ tailWord_1088311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1088366 : List Nat := [4, 1, 2, 3, 2, 1, 3, 2, 1, 3]
def baseStart_1088366 : Nat := 118140960795 + 1088366 * 2 ^ 59
def prefixEnd_1088366 : Nat := 4983230072969 + 3 ^ 40 * 1088366 * 2
def baseEnd_1088366 : Nat := 372569924007595997813135

theorem tailTrace_1088366 : CollatzResearch.WordTrace tailWord_1088366 prefixEnd_1088366 372569924007595997813135 := by
  unfold tailWord_1088366
  simp only [CollatzResearch.WordTrace]
  refine ⟨4961996146880416869924619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26463979450028889972931301 4961996146880416869924619)
  ·
    refine ⟨7442994220320625304886929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4961996146880416869924619 7442994220320625304886929)
    ·
      refine ⟨5582245665240468978665197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7442994220320625304886929 5582245665240468978665197)
      ·
        refine ⟨2093342124465175866999449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5582245665240468978665197 2093342124465175866999449)
        ·
          refine ⟨1570006593348881900249587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2093342124465175866999449 1570006593348881900249587)
          ·
            refine ⟨2355009890023322850374381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1570006593348881900249587 2355009890023322850374381)
            ·
              refine ⟨883128708758746068890393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2355009890023322850374381 883128708758746068890393)
              ·
                refine ⟨662346531569059551667795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 883128708758746068890393 662346531569059551667795)
                ·
                  refine ⟨993519797353589327501693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 662346531569059551667795 993519797353589327501693)
                  ·
                    refine ⟨372569924007595997813135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 993519797353589327501693 372569924007595997813135)
                    ·
                      rfl

theorem cell22_1088366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 3, 2, 1, 3].length) (baseStart_1088366 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1088366 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1088366 prefixEnd_1088366 := by exact prefixLift 1088366
  have htrace : WordTrace (prefixWord ++ tailWord_1088366) baseStart_1088366 baseEnd_1088366 := by
    simpa [prefixWord, tailWord_1088366, baseEnd_1088366] using wordTrace_append hprefix tailTrace_1088366
  have hstable : (prefixWord ++ tailWord_1088366).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1088366).length < 2 ^ (prefixWord ++ tailWord_1088366).sum := by decide
  have hdescent : baseEnd_1088366 < baseStart_1088366 := by decide
  rcases family_descends (prefixWord ++ tailWord_1088366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1088388 : List Nat := [2, 3, 2, 1, 1, 1, 1, 5, 1, 5]
def baseStart_1088388 : Nat := 118140960795 + 1088388 * 2 ^ 59
def prefixEnd_1088388 : Nat := 4983230072969 + 3 ^ 40 * 1088388 * 2
def baseEnd_1088388 : Nat := 372577455057195273763067

theorem tailTrace_1088388 : CollatzResearch.WordTrace tailWord_1088388 prefixEnd_1088388 372577455057195273763067 := by
  unfold tailWord_1088388
  simp only [CollatzResearch.WordTrace]
  refine ⟨19848385790481816358348909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26464514387309088477798545 19848385790481816358348909)
  ·
    refine ⟨7443144671430681134380841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19848385790481816358348909 7443144671430681134380841)
    ·
      refine ⟨5582358503573010850785631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7443144671430681134380841 5582358503573010850785631)
      ·
        refine ⟨8373537755359516276178447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5582358503573010850785631 8373537755359516276178447)
        ·
          refine ⟨12560306633039274414267671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8373537755359516276178447 12560306633039274414267671)
          ·
            refine ⟨18840459949558911621401507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12560306633039274414267671 18840459949558911621401507)
            ·
              refine ⟨28260689924338367432102261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18840459949558911621401507 28260689924338367432102261)
              ·
                refine ⟨2649439680406721946759587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 28260689924338367432102261 2649439680406721946759587)
                ·
                  refine ⟨3974159520610082920139381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2649439680406721946759587 3974159520610082920139381)
                  ·
                    refine ⟨372577455057195273763067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3974159520610082920139381 372577455057195273763067)
                    ·
                      rfl

theorem cell22_1088388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 5, 1, 5].length) (baseStart_1088388 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1088388 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1088388 prefixEnd_1088388 := by exact prefixLift 1088388
  have htrace : WordTrace (prefixWord ++ tailWord_1088388) baseStart_1088388 baseEnd_1088388 := by
    simpa [prefixWord, tailWord_1088388, baseEnd_1088388] using wordTrace_append hprefix tailTrace_1088388
  have hstable : (prefixWord ++ tailWord_1088388).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1088388).length < 2 ^ (prefixWord ++ tailWord_1088388).sum := by decide
  have hdescent : baseEnd_1088388 < baseStart_1088388 := by decide
  rcases family_descends (prefixWord ++ tailWord_1088388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1088392 : List Nat := [2, 1, 3, 3, 2, 3, 1, 2, 1, 4]
def baseStart_1088392 : Nat := 118140960795 + 1088392 * 2 ^ 59
def prefixEnd_1088392 : Nat := 4983230072969 + 3 ^ 40 * 1088392 * 2
def baseEnd_1088392 : Nat := 372578824338940596663055

theorem tailTrace_1088392 : CollatzResearch.WordTrace tailWord_1088392 prefixEnd_1088392 372578824338940596663055 := by
  unfold tailWord_1088392
  simp only [CollatzResearch.WordTrace]
  refine ⟨19848458736474570699921715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26464611648632760933228953 19848458736474570699921715)
  ·
    refine ⟨29772688104711856049882573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19848458736474570699921715 29772688104711856049882573)
    ·
      refine ⟨11164758039266946018705965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29772688104711856049882573 11164758039266946018705965)
      ·
        refine ⟨4186784264725104757014737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11164758039266946018705965 4186784264725104757014737)
        ·
          refine ⟨3140088198543828567761053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4186784264725104757014737 3140088198543828567761053)
          ·
            refine ⟨1177533074453935712910395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3140088198543828567761053 1177533074453935712910395)
            ·
              refine ⟨1766299611680903569365593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1177533074453935712910395 1766299611680903569365593)
              ·
                refine ⟨1324724708760677677024195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1766299611680903569365593 1324724708760677677024195)
                ·
                  refine ⟨1987087063141016515536293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1324724708760677677024195 1987087063141016515536293)
                  ·
                    refine ⟨372578824338940596663055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1987087063141016515536293 372578824338940596663055)
                    ·
                      rfl

theorem cell22_1088392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 3, 1, 2, 1, 4].length) (baseStart_1088392 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1088392 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1088392 prefixEnd_1088392 := by exact prefixLift 1088392
  have htrace : WordTrace (prefixWord ++ tailWord_1088392) baseStart_1088392 baseEnd_1088392 := by
    simpa [prefixWord, tailWord_1088392, baseEnd_1088392] using wordTrace_append hprefix tailTrace_1088392
  have hstable : (prefixWord ++ tailWord_1088392).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1088392).length < 2 ^ (prefixWord ++ tailWord_1088392).sum := by decide
  have hdescent : baseEnd_1088392 < baseStart_1088392 := by decide
  rcases family_descends (prefixWord ++ tailWord_1088392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1088418 : List Nat := [3, 3, 1, 2, 2, 11]
def baseStart_1088418 : Nat := 118140960795 + 1088418 * 2 ^ 59
def prefixEnd_1088418 : Nat := 4983230072969 + 3 ^ 40 * 1088418 * 2
def baseEnd_1088418 : Nat := 4599848452719570314975

theorem tailTrace_1088418 : CollatzResearch.WordTrace tailWord_1088418 prefixEnd_1088418 4599848452719570314975 := by
  unfold tailWord_1088418
  simp only [CollatzResearch.WordTrace]
  refine ⟨9924466442713736960072477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26465243847236631893526605 9924466442713736960072477)
  ·
    refine ⟨3721674916017651360027179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9924466442713736960072477 3721674916017651360027179)
    ·
      refine ⟨5582512374026477040040769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3721674916017651360027179 5582512374026477040040769)
      ·
        refine ⟨4186884280519857780030577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5582512374026477040040769 4186884280519857780030577)
        ·
          refine ⟨3140163210389893335022933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4186884280519857780030577 3140163210389893335022933)
          ·
            refine ⟨4599848452719570314975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 3140163210389893335022933 4599848452719570314975)
            ·
              rfl

theorem cell22_1088418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 11].length) (baseStart_1088418 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1088418 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1088418 prefixEnd_1088418 := by exact prefixLift 1088418
  have htrace : WordTrace (prefixWord ++ tailWord_1088418) baseStart_1088418 baseEnd_1088418 := by
    simpa [prefixWord, tailWord_1088418, baseEnd_1088418] using wordTrace_append hprefix tailTrace_1088418
  have hstable : (prefixWord ++ tailWord_1088418).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1088418).length < 2 ^ (prefixWord ++ tailWord_1088418).sum := by decide
  have hdescent : baseEnd_1088418 < baseStart_1088418 := by decide
  rcases family_descends (prefixWord ++ tailWord_1088418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1088497 : List Nat := [1, 2, 2, 2, 4, 2, 3, 1, 5]
def baseStart_1088497 : Nat := 118140960795 + 1088497 * 2 ^ 59
def prefixEnd_1088497 : Nat := 4983230072969 + 3 ^ 40 * 1088497 * 2
def baseEnd_1088497 : Nat := 124204922661585107595911

theorem tailTrace_1088497 : CollatzResearch.WordTrace tailWord_1088497 prefixEnd_1088497 124204922661585107595911 := by
  unfold tailWord_1088497
  simp only [CollatzResearch.WordTrace]
  refine ⟨39700747137568744332415745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26467164758379162888277163 39700747137568744332415745)
  ·
    refine ⟨29775560353176558249311809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39700747137568744332415745 29775560353176558249311809)
    ·
      refine ⟨22331670264882418686983857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29775560353176558249311809 22331670264882418686983857)
      ·
        refine ⟨16748752698661814015237893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22331670264882418686983857 16748752698661814015237893)
        ·
          refine ⟨3140391130999090127857105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16748752698661814015237893 3140391130999090127857105)
          ·
            refine ⟨2355293348249317595892829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3140391130999090127857105 2355293348249317595892829)
            ·
              refine ⟨883235005593494098459811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2355293348249317595892829 883235005593494098459811)
              ·
                refine ⟨1324852508390241147689717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 883235005593494098459811 1324852508390241147689717)
                ·
                  refine ⟨124204922661585107595911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1324852508390241147689717 124204922661585107595911)
                  ·
                    rfl

theorem cell22_1088497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 3, 1, 5].length) (baseStart_1088497 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1088497 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1088497 prefixEnd_1088497 := by exact prefixLift 1088497
  have htrace : WordTrace (prefixWord ++ tailWord_1088497) baseStart_1088497 baseEnd_1088497 := by
    simpa [prefixWord, tailWord_1088497, baseEnd_1088497] using wordTrace_append hprefix tailTrace_1088497
  have hstable : (prefixWord ++ tailWord_1088497).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1088497).length < 2 ^ (prefixWord ++ tailWord_1088497).sum := by decide
  have hdescent : baseEnd_1088497 < baseStart_1088497 := by decide
  rcases family_descends (prefixWord ++ tailWord_1088497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1088572 : List Nat := [2, 2, 2, 2, 2, 3, 2, 1, 2, 4]
def baseStart_1088572 : Nat := 118140960795 + 1088572 * 2 ^ 59
def prefixEnd_1088572 : Nat := 4983230072969 + 3 ^ 40 * 1088572 * 2
def baseEnd_1088572 : Nat := 372640442017480127162503

theorem tailTrace_1088572 : CollatzResearch.WordTrace tailWord_1088572 prefixEnd_1088572 372640442017480127162503 := by
  unfold tailWord_1088572
  simp only [CollatzResearch.WordTrace]
  refine ⟨19851741306148516070697985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26468988408198021427597313 19851741306148516070697985)
  ·
    refine ⟨14888805979611387053023489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19851741306148516070697985 14888805979611387053023489)
    ·
      refine ⟨11166604484708540289767617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14888805979611387053023489 11166604484708540289767617)
      ·
        refine ⟨8374953363531405217325713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11166604484708540289767617 8374953363531405217325713)
        ·
          refine ⟨6281215022648553912994285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8374953363531405217325713 6281215022648553912994285)
          ·
            refine ⟨2355455633493207717372857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6281215022648553912994285 2355455633493207717372857)
            ·
              refine ⟨1766591725119905788029643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2355455633493207717372857 1766591725119905788029643)
              ·
                refine ⟨2649887587679858682044465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1766591725119905788029643 2649887587679858682044465)
                ·
                  refine ⟨1987415690759894011533349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2649887587679858682044465 1987415690759894011533349)
                  ·
                    refine ⟨372640442017480127162503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1987415690759894011533349 372640442017480127162503)
                    ·
                      rfl

theorem cell22_1088572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 2, 1, 2, 4].length) (baseStart_1088572 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1088572 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1088572 prefixEnd_1088572 := by exact prefixLift 1088572
  have htrace : WordTrace (prefixWord ++ tailWord_1088572) baseStart_1088572 baseEnd_1088572 := by
    simpa [prefixWord, tailWord_1088572, baseEnd_1088572] using wordTrace_append hprefix tailTrace_1088572
  have hstable : (prefixWord ++ tailWord_1088572).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1088572).length < 2 ^ (prefixWord ++ tailWord_1088572).sum := by decide
  have hdescent : baseEnd_1088572 < baseStart_1088572 := by decide
  rcases family_descends (prefixWord ++ tailWord_1088572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1088585 : List Nat := [1, 2, 1, 1, 2, 2, 2, 1, 7, 3]
def baseStart_1088585 : Nat := 118140960795 + 1088585 * 2 ^ 59
def prefixEnd_1088585 : Nat := 4983230072969 + 3 ^ 40 * 1088585 * 2
def baseEnd_1088585 : Nat := 372644892183152426587463

theorem tailTrace_1088585 : CollatzResearch.WordTrace tailWord_1088585 prefixEnd_1088585 372644892183152426587463 := by
  unfold tailWord_1088585
  simp only [CollatzResearch.WordTrace]
  refine ⟨39703956761249935361619209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26469304507499956907746139 39703956761249935361619209)
  ·
    refine ⟨29777967570937451521214407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39703956761249935361619209 29777967570937451521214407)
    ·
      refine ⟨44666951356406177281821611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29777967570937451521214407 44666951356406177281821611)
      ·
        refine ⟨67000427034609265922732417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44666951356406177281821611 67000427034609265922732417)
        ·
          refine ⟨50250320275956949442049313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67000427034609265922732417 50250320275956949442049313)
          ·
            refine ⟨37687740206967712081536985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50250320275956949442049313 37687740206967712081536985)
            ·
              refine ⟨28265805155225784061152739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37687740206967712081536985 28265805155225784061152739)
              ·
                refine ⟨42398707732838676091729109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28265805155225784061152739 42398707732838676091729109)
                ·
                  refine ⟨993719712488406470899901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 42398707732838676091729109 993719712488406470899901)
                  ·
                    refine ⟨372644892183152426587463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 993719712488406470899901 372644892183152426587463)
                    ·
                      rfl

theorem cell22_1088585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 1, 7, 3].length) (baseStart_1088585 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1088585 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1088585 prefixEnd_1088585 := by exact prefixLift 1088585
  have htrace : WordTrace (prefixWord ++ tailWord_1088585) baseStart_1088585 baseEnd_1088585 := by
    simpa [prefixWord, tailWord_1088585, baseEnd_1088585] using wordTrace_append hprefix tailTrace_1088585
  have hstable : (prefixWord ++ tailWord_1088585).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1088585).length < 2 ^ (prefixWord ++ tailWord_1088585).sum := by decide
  have hdescent : baseEnd_1088585 < baseStart_1088585 := by decide
  rcases family_descends (prefixWord ++ tailWord_1088585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1088679 : List Nat := [1, 1, 6, 2, 1, 1, 1, 4, 1, 4]
def baseStart_1088679 : Nat := 118140960795 + 1088679 * 2 ^ 59
def prefixEnd_1088679 : Nat := 4983230072969 + 3 ^ 40 * 1088679 * 2
def baseEnd_1088679 : Nat := 372677070304167514737175

theorem tailTrace_1088679 : CollatzResearch.WordTrace tailWord_1088679 prefixEnd_1088679 372677070304167514737175 := by
  unfold tailWord_1088679
  simp only [CollatzResearch.WordTrace]
  refine ⟨39707385222909389415541091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26471590148606259610360727 39707385222909389415541091)
  ·
    refine ⟨59561077834364084123311637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39707385222909389415541091 59561077834364084123311637)
    ·
      refine ⟨2791925523485816443280233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 59561077834364084123311637 2791925523485816443280233)
      ·
        refine ⟨2093944142614362332460175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2791925523485816443280233 2093944142614362332460175)
        ·
          refine ⟨3140916213921543498690263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2093944142614362332460175 3140916213921543498690263)
          ·
            refine ⟨4711374320882315248035395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3140916213921543498690263 4711374320882315248035395)
            ·
              refine ⟨7067061481323472872053093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4711374320882315248035395 7067061481323472872053093)
              ·
                refine ⟨1325074027748151163509955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7067061481323472872053093 1325074027748151163509955)
                ·
                  refine ⟨1987611041622226745264933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1325074027748151163509955 1987611041622226745264933)
                  ·
                    refine ⟨372677070304167514737175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1987611041622226745264933 372677070304167514737175)
                    ·
                      rfl

theorem cell22_1088679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 1, 4, 1, 4].length) (baseStart_1088679 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1088679 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1088679 prefixEnd_1088679 := by exact prefixLift 1088679
  have htrace : WordTrace (prefixWord ++ tailWord_1088679) baseStart_1088679 baseEnd_1088679 := by
    simpa [prefixWord, tailWord_1088679, baseEnd_1088679] using wordTrace_append hprefix tailTrace_1088679
  have hstable : (prefixWord ++ tailWord_1088679).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1088679).length < 2 ^ (prefixWord ++ tailWord_1088679).sum := by decide
  have hdescent : baseEnd_1088679 < baseStart_1088679 := by decide
  rcases family_descends (prefixWord ++ tailWord_1088679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1088722 : List Nat := [3, 2, 2, 2, 1, 1, 4, 7]
def baseStart_1088722 : Nat := 118140960795 + 1088722 * 2 ^ 59
def prefixEnd_1088722 : Nat := 4983230072969 + 3 ^ 40 * 1088722 * 2
def baseEnd_1088722 : Nat := 41410198898103303990227

theorem tailTrace_1088722 : CollatzResearch.WordTrace tailWord_1088722 prefixEnd_1088722 41410198898103303990227 := by
  unfold tailWord_1088722
  simp only [CollatzResearch.WordTrace]
  refine ⟨9927238390438401939839105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26472635707835738506237613 9927238390438401939839105)
  ·
    refine ⟨7445428792828801454879329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9927238390438401939839105 7445428792828801454879329)
    ·
      refine ⟨5584071594621601091159497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7445428792828801454879329 5584071594621601091159497)
      ·
        refine ⟨4188053695966200818369623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5584071594621601091159497 4188053695966200818369623)
        ·
          refine ⟨6282080543949301227554435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4188053695966200818369623 6282080543949301227554435)
          ·
            refine ⟨9423120815923951841331653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6282080543949301227554435 9423120815923951841331653)
            ·
              refine ⟨1766835152985740970249685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9423120815923951841331653 1766835152985740970249685)
              ·
                refine ⟨41410198898103303990227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1766835152985740970249685 41410198898103303990227)
                ·
                  rfl

theorem cell22_1088722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 4, 7].length) (baseStart_1088722 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1088722 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1088722 prefixEnd_1088722 := by exact prefixLift 1088722
  have htrace : WordTrace (prefixWord ++ tailWord_1088722) baseStart_1088722 baseEnd_1088722 := by
    simpa [prefixWord, tailWord_1088722, baseEnd_1088722] using wordTrace_append hprefix tailTrace_1088722
  have hstable : (prefixWord ++ tailWord_1088722).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1088722).length < 2 ^ (prefixWord ++ tailWord_1088722).sum := by decide
  have hdescent : baseEnd_1088722 < baseStart_1088722 := by decide
  rcases family_descends (prefixWord ++ tailWord_1088722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1088756 : List Nat := [2, 6, 1, 2, 1, 10]
def baseStart_1088756 : Nat := 118140960795 + 1088756 * 2 ^ 59
def prefixEnd_1088756 : Nat := 4983230072969 + 3 ^ 40 * 1088756 * 2
def baseEnd_1088756 : Nat := 4601276900960061488419

theorem tailTrace_1088756 : CollatzResearch.WordTrace tailWord_1088756 prefixEnd_1088756 4601276900960061488419 := by
  unfold tailWord_1088756
  simp only [CollatzResearch.WordTrace]
  refine ⟨19855096821815215783047061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26473462429086954377396081 19855096821815215783047061)
  ·
    refine ⟨930707663522588239830331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 19855096821815215783047061 930707663522588239830331)
    ·
      refine ⟨1396061495283882359745497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 930707663522588239830331 1396061495283882359745497)
      ·
        refine ⟨1047046121462911769809123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1396061495283882359745497 1047046121462911769809123)
        ·
          refine ⟨1570569182194367654713685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1047046121462911769809123 1570569182194367654713685)
          ·
            refine ⟨4601276900960061488419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 1570569182194367654713685 4601276900960061488419)
            ·
              rfl

theorem cell22_1088756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 10].length) (baseStart_1088756 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1088756 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1088756 prefixEnd_1088756 := by exact prefixLift 1088756
  have htrace : WordTrace (prefixWord ++ tailWord_1088756) baseStart_1088756 baseEnd_1088756 := by
    simpa [prefixWord, tailWord_1088756, baseEnd_1088756] using wordTrace_append hprefix tailTrace_1088756
  have hstable : (prefixWord ++ tailWord_1088756).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1088756).length < 2 ^ (prefixWord ++ tailWord_1088756).sum := by decide
  have hdescent : baseEnd_1088756 < baseStart_1088756 := by decide
  rcases family_descends (prefixWord ++ tailWord_1088756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1088767 : List Nat := [1, 1, 2, 2, 1, 5, 1, 4, 5]
def baseStart_1088767 : Nat := 118140960795 + 1088767 * 2 ^ 59
def prefixEnd_1088767 : Nat := 4983230072969 + 3 ^ 40 * 1088767 * 2
def baseEnd_1088767 : Nat := 124235731500854872845635

theorem tailTrace_1088767 : CollatzResearch.WordTrace tailWord_1088767 prefixEnd_1088767 124235731500854872845635 := by
  unfold tailWord_1088767
  simp only [CollatzResearch.WordTrace]
  refine ⟨39710594846590580444744555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26473729897727053629829703 39710594846590580444744555)
  ·
    refine ⟨59565892269885870667116833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39710594846590580444744555 59565892269885870667116833)
    ·
      refine ⟨44674419202414403000337625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59565892269885870667116833 44674419202414403000337625)
      ·
        refine ⟨33505814401810802250253219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44674419202414403000337625 33505814401810802250253219)
        ·
          refine ⟨50258721602716203375379829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33505814401810802250253219 50258721602716203375379829)
          ·
            refine ⟨4711755150254644066441859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 50258721602716203375379829 4711755150254644066441859)
            ·
              refine ⟨7067632725381966099662789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4711755150254644066441859 7067632725381966099662789)
              ·
                refine ⟨1325181136009118643686773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7067632725381966099662789 1325181136009118643686773)
                ·
                  refine ⟨124235731500854872845635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1325181136009118643686773 124235731500854872845635)
                  ·
                    rfl

theorem cell22_1088767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 1, 4, 5].length) (baseStart_1088767 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1088767 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1088767 prefixEnd_1088767 := by exact prefixLift 1088767
  have htrace : WordTrace (prefixWord ++ tailWord_1088767) baseStart_1088767 baseEnd_1088767 := by
    simpa [prefixWord, tailWord_1088767, baseEnd_1088767] using wordTrace_append hprefix tailTrace_1088767
  have hstable : (prefixWord ++ tailWord_1088767).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1088767).length < 2 ^ (prefixWord ++ tailWord_1088767).sum := by decide
  have hdescent : baseEnd_1088767 < baseStart_1088767 := by decide
  rcases family_descends (prefixWord ++ tailWord_1088767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1088771 : List Nat := [1, 1, 1, 3, 2, 5, 1, 4, 1, 3]
def baseStart_1088771 : Nat := 118140960795 + 1088771 * 2 ^ 59
def prefixEnd_1088771 : Nat := 4983230072969 + 3 ^ 40 * 1088771 * 2
def baseEnd_1088771 : Nat := 372708563784309941436893

theorem tailTrace_1088771 : CollatzResearch.WordTrace tailWord_1088771 prefixEnd_1088771 372708563784309941436893 := by
  unfold tailWord_1088771
  simp only [CollatzResearch.WordTrace]
  refine ⟨39710740738576089127890167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26473827159050726085260111 39710740738576089127890167)
  ·
    refine ⟨59566111107864133691835251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39710740738576089127890167 59566111107864133691835251)
    ·
      refine ⟨89349166661796200537752877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59566111107864133691835251 89349166661796200537752877)
      ·
        refine ⟨33505937498173575201657329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 89349166661796200537752877 33505937498173575201657329)
        ·
          refine ⟨25129453123630181401242997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33505937498173575201657329 25129453123630181401242997)
          ·
            refine ⟨2355886230340329506366531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 25129453123630181401242997 2355886230340329506366531)
            ·
              refine ⟨3533829345510494259549797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2355886230340329506366531 3533829345510494259549797)
              ·
                refine ⟨662593002283217673665587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3533829345510494259549797 662593002283217673665587)
                ·
                  refine ⟨993889503424826510498381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 662593002283217673665587 993889503424826510498381)
                  ·
                    refine ⟨372708563784309941436893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 993889503424826510498381 372708563784309941436893)
                    ·
                      rfl

theorem cell22_1088771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 1, 4, 1, 3].length) (baseStart_1088771 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1088771 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1088771 prefixEnd_1088771 := by exact prefixLift 1088771
  have htrace : WordTrace (prefixWord ++ tailWord_1088771) baseStart_1088771 baseEnd_1088771 := by
    simpa [prefixWord, tailWord_1088771, baseEnd_1088771] using wordTrace_append hprefix tailTrace_1088771
  have hstable : (prefixWord ++ tailWord_1088771).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1088771).length < 2 ^ (prefixWord ++ tailWord_1088771).sum := by decide
  have hdescent : baseEnd_1088771 < baseStart_1088771 := by decide
  rcases family_descends (prefixWord ++ tailWord_1088771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1088782 : List Nat := [4, 1, 1, 2, 1, 3, 1, 1, 1, 7]
def baseStart_1088782 : Nat := 118140960795 + 1088782 * 2 ^ 59
def prefixEnd_1088782 : Nat := 4983230072969 + 3 ^ 40 * 1088782 * 2
def baseEnd_1088782 : Nat := 372712329309109579411859

theorem tailTrace_1088782 : CollatzResearch.WordTrace tailWord_1088782 prefixEnd_1088782 372712329309109579411859 := by
  unfold tailWord_1088782
  simp only [CollatzResearch.WordTrace]
  refine ⟨4963892742692029750817575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26474094627690825337693733 4963892742692029750817575)
  ·
    refine ⟨7445839114038044626226363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4963892742692029750817575 7445839114038044626226363)
    ·
      refine ⟨11168758671057066939339545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7445839114038044626226363 11168758671057066939339545)
      ·
        refine ⟨8376569003292800204504659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11168758671057066939339545 8376569003292800204504659)
        ·
          refine ⟨12564853504939200306756989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8376569003292800204504659 12564853504939200306756989)
          ·
            refine ⟨4711820064352200115033871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12564853504939200306756989 4711820064352200115033871)
            ·
              refine ⟨7067730096528300172550807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4711820064352200115033871 7067730096528300172550807)
              ·
                refine ⟨10601595144792450258826211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7067730096528300172550807 10601595144792450258826211)
                ·
                  refine ⟨15902392717188675388239317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10601595144792450258826211 15902392717188675388239317)
                  ·
                    refine ⟨372712329309109579411859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 15902392717188675388239317 372712329309109579411859)
                    ·
                      rfl

theorem cell22_1088782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 1, 1, 1, 7].length) (baseStart_1088782 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1088782 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1088782 prefixEnd_1088782 := by exact prefixLift 1088782
  have htrace : WordTrace (prefixWord ++ tailWord_1088782) baseStart_1088782 baseEnd_1088782 := by
    simpa [prefixWord, tailWord_1088782, baseEnd_1088782] using wordTrace_append hprefix tailTrace_1088782
  have hstable : (prefixWord ++ tailWord_1088782).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1088782).length < 2 ^ (prefixWord ++ tailWord_1088782).sum := by decide
  have hdescent : baseEnd_1088782 < baseStart_1088782 := by decide
  rcases family_descends (prefixWord ++ tailWord_1088782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1088844 : List Nat := [2, 2, 1, 3, 2, 2, 3, 1, 1, 5]
def baseStart_1088844 : Nat := 118140960795 + 1088844 * 2 ^ 59
def prefixEnd_1088844 : Nat := 4983230072969 + 3 ^ 40 * 1088844 * 2
def baseEnd_1088844 : Nat := 372733553176162084361669

theorem tailTrace_1088844 : CollatzResearch.WordTrace tailWord_1088844 prefixEnd_1088844 372733553176162084361669 := by
  unfold tailWord_1088844
  simp only [CollatzResearch.WordTrace]
  refine ⟨19856701633655811297648793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26475602178207748396865057 19856701633655811297648793)
  ·
    refine ⟨14892526225241858473236595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19856701633655811297648793 14892526225241858473236595)
    ·
      refine ⟨22338789337862787709854893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14892526225241858473236595 22338789337862787709854893)
      ·
        refine ⟨8377046001698545391195585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22338789337862787709854893 8377046001698545391195585)
        ·
          refine ⟨6282784501273909043396689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8377046001698545391195585 6282784501273909043396689)
          ·
            refine ⟨4712088375955431782547517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6282784501273909043396689 4712088375955431782547517)
            ·
              refine ⟨1767033140983286918455319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4712088375955431782547517 1767033140983286918455319)
              ·
                refine ⟨2650549711474930377682979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1767033140983286918455319 2650549711474930377682979)
                ·
                  refine ⟨3975824567212395566524469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2650549711474930377682979 3975824567212395566524469)
                  ·
                    refine ⟨372733553176162084361669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3975824567212395566524469 372733553176162084361669)
                    ·
                      rfl

theorem cell22_1088844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 3, 1, 1, 5].length) (baseStart_1088844 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1088844 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1088844 prefixEnd_1088844 := by exact prefixLift 1088844
  have htrace : WordTrace (prefixWord ++ tailWord_1088844) baseStart_1088844 baseEnd_1088844 := by
    simpa [prefixWord, tailWord_1088844, baseEnd_1088844] using wordTrace_append hprefix tailTrace_1088844
  have hstable : (prefixWord ++ tailWord_1088844).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1088844).length < 2 ^ (prefixWord ++ tailWord_1088844).sum := by decide
  have hdescent : baseEnd_1088844 < baseStart_1088844 := by decide
  rcases family_descends (prefixWord ++ tailWord_1088844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1088887 : List Nat := [1, 1, 3, 1, 1, 2, 4, 1, 2, 6]
def baseStart_1088887 : Nat := 118140960795 + 1088887 * 2 ^ 59
def prefixEnd_1088887 : Nat := 4983230072969 + 3 ^ 40 * 1088887 * 2
def baseEnd_1088887 : Nat := 372748272954924305536537

theorem tailTrace_1088887 : CollatzResearch.WordTrace tailWord_1088887 prefixEnd_1088887 372748272954924305536537 := by
  unfold tailWord_1088887
  simp only [CollatzResearch.WordTrace]
  refine ⟨39714971606155840939112915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26476647737437227292741943 39714971606155840939112915)
  ·
    refine ⟨59572457409233761408669373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39714971606155840939112915 59572457409233761408669373)
    ·
      refine ⟨22339671528462660528251015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59572457409233761408669373 22339671528462660528251015)
      ·
        refine ⟨33509507292693990792376523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22339671528462660528251015 33509507292693990792376523)
        ·
          refine ⟨50264260939040986188564785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33509507292693990792376523 50264260939040986188564785)
          ·
            refine ⟨37698195704280739641423589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50264260939040986188564785 37698195704280739641423589)
            ·
              refine ⟨7068411694552638682766923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 37698195704280739641423589 7068411694552638682766923)
              ·
                refine ⟨10602617541828958024150385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7068411694552638682766923 10602617541828958024150385)
                ·
                  refine ⟨7951963156371718518112789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10602617541828958024150385 7951963156371718518112789)
                  ·
                    refine ⟨372748272954924305536537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7951963156371718518112789 372748272954924305536537)
                    ·
                      rfl

theorem cell22_1088887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 4, 1, 2, 6].length) (baseStart_1088887 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1088887 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1088887 prefixEnd_1088887 := by exact prefixLift 1088887
  have htrace : WordTrace (prefixWord ++ tailWord_1088887) baseStart_1088887 baseEnd_1088887 := by
    simpa [prefixWord, tailWord_1088887, baseEnd_1088887] using wordTrace_append hprefix tailTrace_1088887
  have hstable : (prefixWord ++ tailWord_1088887).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1088887).length < 2 ^ (prefixWord ++ tailWord_1088887).sum := by decide
  have hdescent : baseEnd_1088887 < baseStart_1088887 := by decide
  rcases family_descends (prefixWord ++ tailWord_1088887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1088947 : List Nat := [1, 1, 1, 2, 3, 1, 1, 2, 10]
def baseStart_1088947 : Nat := 118140960795 + 1088947 * 2 ^ 59
def prefixEnd_1088947 : Nat := 4983230072969 + 3 ^ 40 * 1088947 * 2
def baseEnd_1088947 : Nat := 124256270727034716345451

theorem tailTrace_1088947 : CollatzResearch.WordTrace tailWord_1088947 prefixEnd_1088947 124256270727034716345451 := by
  unfold tailWord_1088947
  simp only [CollatzResearch.WordTrace]
  refine ⟨39717159985938471186297095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26478106657292314124198063 39717159985938471186297095)
  ·
    refine ⟨59575739978907706779445643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39717159985938471186297095 59575739978907706779445643)
    ·
      refine ⟨89363609968361560169168465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59575739978907706779445643 89363609968361560169168465)
      ·
        refine ⟨67022707476271170126876349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 89363609968361560169168465 67022707476271170126876349)
        ·
          refine ⟨25133515303601688797578631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 67022707476271170126876349 25133515303601688797578631)
          ·
            refine ⟨37700272955402533196367947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25133515303601688797578631 37700272955402533196367947)
            ·
              refine ⟨56550409433103799794551921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37700272955402533196367947 56550409433103799794551921)
              ·
                refine ⟨42412807074827849845913941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 56550409433103799794551921 42412807074827849845913941)
                ·
                  refine ⟨124256270727034716345451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 42412807074827849845913941 124256270727034716345451)
                  ·
                    rfl

theorem cell22_1088947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 2, 10].length) (baseStart_1088947 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1088947 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1088947 prefixEnd_1088947 := by exact prefixLift 1088947
  have htrace : WordTrace (prefixWord ++ tailWord_1088947) baseStart_1088947 baseEnd_1088947 := by
    simpa [prefixWord, tailWord_1088947, baseEnd_1088947] using wordTrace_append hprefix tailTrace_1088947
  have hstable : (prefixWord ++ tailWord_1088947).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1088947).length < 2 ^ (prefixWord ++ tailWord_1088947).sum := by decide
  have hdescent : baseEnd_1088947 < baseStart_1088947 := by decide
  rcases family_descends (prefixWord ++ tailWord_1088947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1089013 : List Nat := [1, 3, 5, 1, 1, 1, 3, 1, 1, 5]
def baseStart_1089013 : Nat := 118140960795 + 1089013 * 2 ^ 59
def prefixEnd_1089013 : Nat := 4983230072969 + 3 ^ 40 * 1089013 * 2
def baseEnd_1089013 : Nat := 372791405329901976886151

theorem tailTrace_1089013 : CollatzResearch.WordTrace tailWord_1089013 prefixEnd_1089013 372791405329901976886151 := by
  unfold tailWord_1089013
  simp only [CollatzResearch.WordTrace]
  refine ⟨39719567203699364458199693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26479711469132909638799795 39719567203699364458199693)
  ·
    refine ⟨14894837701387261671824885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39719567203699364458199693 14894837701387261671824885)
    ·
      refine ⟨1396391034505055781733583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 14894837701387261671824885 1396391034505055781733583)
      ·
        refine ⟨2094586551757583672600375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1396391034505055781733583 2094586551757583672600375)
        ·
          refine ⟨3141879827636375508900563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2094586551757583672600375 3141879827636375508900563)
          ·
            refine ⟨4712819741454563263350845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3141879827636375508900563 4712819741454563263350845)
            ·
              refine ⟨1767307403045461223756567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4712819741454563263350845 1767307403045461223756567)
              ·
                refine ⟨2650961104568191835634851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1767307403045461223756567 2650961104568191835634851)
                ·
                  refine ⟨3976441656852287753452277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2650961104568191835634851 3976441656852287753452277)
                  ·
                    refine ⟨372791405329901976886151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3976441656852287753452277 372791405329901976886151)
                    ·
                      rfl

theorem cell22_1089013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 3, 1, 1, 5].length) (baseStart_1089013 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1089013 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1089013 prefixEnd_1089013 := by exact prefixLift 1089013
  have htrace : WordTrace (prefixWord ++ tailWord_1089013) baseStart_1089013 baseEnd_1089013 := by
    simpa [prefixWord, tailWord_1089013, baseEnd_1089013] using wordTrace_append hprefix tailTrace_1089013
  have hstable : (prefixWord ++ tailWord_1089013).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1089013).length < 2 ^ (prefixWord ++ tailWord_1089013).sum := by decide
  have hdescent : baseEnd_1089013 < baseStart_1089013 := by decide
  rcases family_descends (prefixWord ++ tailWord_1089013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1089058 : List Nat := [3, 3, 1, 1, 1, 1, 5, 1, 3, 3]
def baseStart_1089058 : Nat := 118140960795 + 1089058 * 2 ^ 59
def prefixEnd_1089058 : Nat := 4983230072969 + 3 ^ 40 * 1089058 * 2
def baseEnd_1089058 : Nat := 372806809749536859511013

theorem tailTrace_1089058 : CollatzResearch.WordTrace tailWord_1089058 prefixEnd_1089058 372806809749536859511013 := by
  unfold tailWord_1089058
  simp only [CollatzResearch.WordTrace]
  refine ⟨9930302122134084285896957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26480805659024224762391885 9930302122134084285896957)
  ·
    refine ⟨3723863295800281607211359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9930302122134084285896957 3723863295800281607211359)
    ·
      refine ⟨5585794943700422410817039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3723863295800281607211359 5585794943700422410817039)
      ·
        refine ⟨8378692415550633616225559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5585794943700422410817039 8378692415550633616225559)
        ·
          refine ⟨12568038623325950424338339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8378692415550633616225559 12568038623325950424338339)
          ·
            refine ⟨18852057934988925636507509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12568038623325950424338339 18852057934988925636507509)
            ·
              refine ⟨1767380431405211778422579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 18852057934988925636507509 1767380431405211778422579)
              ·
                refine ⟨2651070647107817667633869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1767380431405211778422579 2651070647107817667633869)
                ·
                  refine ⟨994151492665431625362701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2651070647107817667633869 994151492665431625362701)
                  ·
                    refine ⟨372806809749536859511013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 994151492665431625362701 372806809749536859511013)
                    ·
                      rfl

theorem cell22_1089058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 5, 1, 3, 3].length) (baseStart_1089058 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1089058 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1089058 prefixEnd_1089058 := by exact prefixLift 1089058
  have htrace : WordTrace (prefixWord ++ tailWord_1089058) baseStart_1089058 baseEnd_1089058 := by
    simpa [prefixWord, tailWord_1089058, baseEnd_1089058] using wordTrace_append hprefix tailTrace_1089058
  have hstable : (prefixWord ++ tailWord_1089058).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1089058).length < 2 ^ (prefixWord ++ tailWord_1089058).sum := by decide
  have hdescent : baseEnd_1089058 < baseStart_1089058 := by decide
  rcases family_descends (prefixWord ++ tailWord_1089058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1089064 : List Nat := [2, 1, 5, 2, 3, 1, 2, 1, 2, 3]
def baseStart_1089064 : Nat := 118140960795 + 1089064 * 2 ^ 59
def prefixEnd_1089064 : Nat := 4983230072969 + 3 ^ 40 * 1089064 * 2
def baseEnd_1089064 : Nat := 372808863672154843860995

theorem tailTrace_1089064 : CollatzResearch.WordTrace tailWord_1089064 prefixEnd_1089064 372808863672154843860995 := by
  unfold tailWord_1089064
  simp only [CollatzResearch.WordTrace]
  refine ⟨19860713663257300084153123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26480951551009733445537497 19860713663257300084153123)
  ·
    refine ⟨29791070494885950126229685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19860713663257300084153123 29791070494885950126229685)
    ·
      refine ⟨2792912858895557824334033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 29791070494885950126229685 2792912858895557824334033)
      ·
        refine ⟨2094684644171668368250525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2792912858895557824334033 2094684644171668368250525)
        ·
          refine ⟨785506741564375638093947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2094684644171668368250525 785506741564375638093947)
          ·
            refine ⟨1178260112346563457140921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 785506741564375638093947 1178260112346563457140921)
            ·
              refine ⟨883695084259922592855691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1178260112346563457140921 883695084259922592855691)
              ·
                refine ⟨1325542626389883889283537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 883695084259922592855691 1325542626389883889283537)
                ·
                  refine ⟨994156969792412916962653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1325542626389883889283537 994156969792412916962653)
                  ·
                    refine ⟨372808863672154843860995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 994156969792412916962653 372808863672154843860995)
                    ·
                      rfl

theorem cell22_1089064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 3, 1, 2, 1, 2, 3].length) (baseStart_1089064 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1089064 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1089064 prefixEnd_1089064 := by exact prefixLift 1089064
  have htrace : WordTrace (prefixWord ++ tailWord_1089064) baseStart_1089064 baseEnd_1089064 := by
    simpa [prefixWord, tailWord_1089064, baseEnd_1089064] using wordTrace_append hprefix tailTrace_1089064
  have hstable : (prefixWord ++ tailWord_1089064).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1089064).length < 2 ^ (prefixWord ++ tailWord_1089064).sum := by decide
  have hdescent : baseEnd_1089064 < baseStart_1089064 := by decide
  rcases family_descends (prefixWord ++ tailWord_1089064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1089133 : List Nat := [1, 5, 1, 1, 4, 1, 1, 2, 6]
def baseStart_1089133 : Nat := 118140960795 + 1089133 * 2 ^ 59
def prefixEnd_1089133 : Nat := 4983230072969 + 3 ^ 40 * 1089133 * 2
def baseEnd_1089133 : Nat := 124277494594087221295261

theorem tailTrace_1089133 : CollatzResearch.WordTrace tailWord_1089133 prefixEnd_1089133 124277494594087221295261 := by
  unfold tailWord_1089133
  simp only [CollatzResearch.WordTrace]
  refine ⟨39723943963264624952568053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26482629308843083301712035 39723943963264624952568053)
  ·
    refine ⟨3724119746556058589303255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 39723943963264624952568053 3724119746556058589303255)
    ·
      refine ⟨5586179619834087883954883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3724119746556058589303255 5586179619834087883954883)
      ·
        refine ⟨8379269429751131825932325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5586179619834087883954883 8379269429751131825932325)
        ·
          refine ⟨1571113018078337217362311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8379269429751131825932325 1571113018078337217362311)
          ·
            refine ⟨2356669527117505826043467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1571113018078337217362311 2356669527117505826043467)
            ·
              refine ⟨3535004290676258739065201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2356669527117505826043467 3535004290676258739065201)
              ·
                refine ⟨2651253218007194054298901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3535004290676258739065201 2651253218007194054298901)
                ·
                  refine ⟨124277494594087221295261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2651253218007194054298901 124277494594087221295261)
                  ·
                    rfl

theorem cell22_1089133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 1, 2, 6].length) (baseStart_1089133 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1089133 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1089133 prefixEnd_1089133 := by exact prefixLift 1089133
  have htrace : WordTrace (prefixWord ++ tailWord_1089133) baseStart_1089133 baseEnd_1089133 := by
    simpa [prefixWord, tailWord_1089133, baseEnd_1089133] using wordTrace_append hprefix tailTrace_1089133
  have hstable : (prefixWord ++ tailWord_1089133).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1089133).length < 2 ^ (prefixWord ++ tailWord_1089133).sum := by decide
  have hdescent : baseEnd_1089133 < baseStart_1089133 := by decide
  rcases family_descends (prefixWord ++ tailWord_1089133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1089146 : List Nat := [3, 1, 1, 1, 1, 1, 1, 7, 2, 4]
def baseStart_1089146 : Nat := 118140960795 + 1089146 * 2 ^ 59
def prefixEnd_1089146 : Nat := 4983230072969 + 3 ^ 40 * 1089146 * 2
def baseEnd_1089146 : Nat := 372836933947933963310743

theorem tailTrace_1089146 : CollatzResearch.WordTrace tailWord_1089146 prefixEnd_1089146 372836933947933963310743 := by
  unfold tailWord_1089146
  simp only [CollatzResearch.WordTrace]
  refine ⟨9931104528054382043197823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26482945408145018781860861 9931104528054382043197823)
  ·
    refine ⟨14896656792081573064796735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9931104528054382043197823 14896656792081573064796735)
    ·
      refine ⟨22344985188122359597195103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14896656792081573064796735 22344985188122359597195103)
      ·
        refine ⟨33517477782183539395792655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22344985188122359597195103 33517477782183539395792655)
        ·
          refine ⟨50276216673275309093688983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33517477782183539395792655 50276216673275309093688983)
          ·
            refine ⟨75414325009912963640533475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50276216673275309093688983 75414325009912963640533475)
            ·
              refine ⟨113121487514869445460800213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75414325009912963640533475 113121487514869445460800213)
              ·
                refine ⟨2651284863629752627987505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 113121487514869445460800213 2651284863629752627987505)
                ·
                  refine ⟨1988463647722314470990629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2651284863629752627987505 1988463647722314470990629)
                  ·
                    refine ⟨372836933947933963310743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1988463647722314470990629 372836933947933963310743)
                    ·
                      rfl

theorem cell22_1089146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 7, 2, 4].length) (baseStart_1089146 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1089146 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1089146 prefixEnd_1089146 := by exact prefixLift 1089146
  have htrace : WordTrace (prefixWord ++ tailWord_1089146) baseStart_1089146 baseEnd_1089146 := by
    simpa [prefixWord, tailWord_1089146, baseEnd_1089146] using wordTrace_append hprefix tailTrace_1089146
  have hstable : (prefixWord ++ tailWord_1089146).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1089146).length < 2 ^ (prefixWord ++ tailWord_1089146).sum := by decide
  have hdescent : baseEnd_1089146 < baseStart_1089146 := by decide
  rcases family_descends (prefixWord ++ tailWord_1089146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1089253 : List Nat := [1, 3, 1, 4, 1, 1, 3, 1, 3, 4]
def baseStart_1089253 : Nat := 118140960795 + 1089253 * 2 ^ 59
def prefixEnd_1089253 : Nat := 4983230072969 + 3 ^ 40 * 1089253 * 2
def baseEnd_1089253 : Nat := 372873562234621350885415

theorem tailTrace_1089253 : CollatzResearch.WordTrace tailWord_1089253 prefixEnd_1089253 372873562234621350885415 := by
  unfold tailWord_1089253
  simp only [CollatzResearch.WordTrace]
  refine ⟨39728320722829885446936413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26485547148553256964624275 39728320722829885446936413)
  ·
    refine ⟨14898120271061207042601155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39728320722829885446936413 14898120271061207042601155)
    ·
      refine ⟨22347180406591810563901733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14898120271061207042601155 22347180406591810563901733)
      ·
        refine ⟨4190096326235964480731575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22347180406591810563901733 4190096326235964480731575)
        ·
          refine ⟨6285144489353946721097363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4190096326235964480731575 6285144489353946721097363)
          ·
            refine ⟨9427716734030920081646045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6285144489353946721097363 9427716734030920081646045)
            ·
              refine ⟨3535393775261595030617267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9427716734030920081646045 3535393775261595030617267)
              ·
                refine ⟨5303090662892392545925901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3535393775261595030617267 5303090662892392545925901)
                ·
                  refine ⟨1988658998584647204722213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5303090662892392545925901 1988658998584647204722213)
                  ·
                    refine ⟨372873562234621350885415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1988658998584647204722213 372873562234621350885415)
                    ·
                      rfl

theorem cell22_1089253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 3, 1, 3, 4].length) (baseStart_1089253 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1089253 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1089253 prefixEnd_1089253 := by exact prefixLift 1089253
  have htrace : WordTrace (prefixWord ++ tailWord_1089253) baseStart_1089253 baseEnd_1089253 := by
    simpa [prefixWord, tailWord_1089253, baseEnd_1089253] using wordTrace_append hprefix tailTrace_1089253
  have hstable : (prefixWord ++ tailWord_1089253).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1089253).length < 2 ^ (prefixWord ++ tailWord_1089253).sum := by decide
  have hdescent : baseEnd_1089253 < baseStart_1089253 := by decide
  rcases family_descends (prefixWord ++ tailWord_1089253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1089278 : List Nat := [4, 2, 2, 1, 4, 1, 2, 2, 1, 3]
def baseStart_1089278 : Nat := 118140960795 + 1089278 * 2 ^ 59
def prefixEnd_1089278 : Nat := 4983230072969 + 3 ^ 40 * 1089278 * 2
def baseEnd_1089278 : Nat := 372882120245529619010339

theorem tailTrace_1089278 : CollatzResearch.WordTrace tailWord_1089278 prefixEnd_1089278 372882120245529619010339 := by
  unfold tailWord_1089278
  simp only [CollatzResearch.WordTrace]
  refine ⟨4966154068467414339574561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26486155031826209811064325 4966154068467414339574561)
  ·
    refine ⟨3724615551350560754680921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4966154068467414339574561 3724615551350560754680921)
    ·
      refine ⟨2793461663512920566010691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3724615551350560754680921 2793461663512920566010691)
      ·
        refine ⟨4190192495269380849016037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2793461663512920566010691 4190192495269380849016037)
        ·
          refine ⟨785661092863008909190507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4190192495269380849016037 785661092863008909190507)
          ·
            refine ⟨1178491639294513363785761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 785661092863008909190507 1178491639294513363785761)
            ·
              refine ⟨883868729470885022839321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1178491639294513363785761 883868729470885022839321)
              ·
                refine ⟨662901547103163767129491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 883868729470885022839321 662901547103163767129491)
                ·
                  refine ⟨994352320654745650694237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 662901547103163767129491 994352320654745650694237)
                  ·
                    refine ⟨372882120245529619010339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 994352320654745650694237 372882120245529619010339)
                    ·
                      rfl

theorem cell22_1089278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 4, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 4, 1, 2, 2, 1, 3].length) (baseStart_1089278 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1089278 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1089278 prefixEnd_1089278 := by exact prefixLift 1089278
  have htrace : WordTrace (prefixWord ++ tailWord_1089278) baseStart_1089278 baseEnd_1089278 := by
    simpa [prefixWord, tailWord_1089278, baseEnd_1089278] using wordTrace_append hprefix tailTrace_1089278
  have hstable : (prefixWord ++ tailWord_1089278).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1089278).length < 2 ^ (prefixWord ++ tailWord_1089278).sum := by decide
  have hdescent : baseEnd_1089278 < baseStart_1089278 := by decide
  rcases family_descends (prefixWord ++ tailWord_1089278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1089283 : List Nat := [1, 1, 1, 3, 2, 2, 2, 3, 4, 3]
def baseStart_1089283 : Nat := 118140960795 + 1089283 * 2 ^ 59
def prefixEnd_1089283 : Nat := 4983230072969 + 3 ^ 40 * 1089283 * 2
def baseEnd_1089283 : Nat := 372883831847711272635323

theorem tailTrace_1089283 : CollatzResearch.WordTrace tailWord_1089283 prefixEnd_1089283 372883831847711272635323 := by
  unfold tailWord_1089283
  simp only [CollatzResearch.WordTrace]
  refine ⟨39729414912721200570528503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26486276608480800380352335 39729414912721200570528503)
  ·
    refine ⟨59594122369081800855792755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39729414912721200570528503 59594122369081800855792755)
    ·
      refine ⟨89391183553622701283689133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59594122369081800855792755 89391183553622701283689133)
      ·
        refine ⟨33521693832608512981383425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 89391183553622701283689133 33521693832608512981383425)
        ·
          refine ⟨25141270374456384736037569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33521693832608512981383425 25141270374456384736037569)
          ·
            refine ⟨18855952780842288552028177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25141270374456384736037569 18855952780842288552028177)
            ·
              refine ⟨14141964585631716414021133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18855952780842288552028177 14141964585631716414021133)
              ·
                refine ⟨5303236719611893655257925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14141964585631716414021133 5303236719611893655257925)
                ·
                  refine ⟨994356884927230060360861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5303236719611893655257925 994356884927230060360861)
                  ·
                    refine ⟨372883831847711272635323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 994356884927230060360861 372883831847711272635323)
                    ·
                      rfl

theorem cell22_1089283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 3, 4, 3].length) (baseStart_1089283 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1089283 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1089283 prefixEnd_1089283 := by exact prefixLift 1089283
  have htrace : WordTrace (prefixWord ++ tailWord_1089283) baseStart_1089283 baseEnd_1089283 := by
    simpa [prefixWord, tailWord_1089283, baseEnd_1089283] using wordTrace_append hprefix tailTrace_1089283
  have hstable : (prefixWord ++ tailWord_1089283).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1089283).length < 2 ^ (prefixWord ++ tailWord_1089283).sum := by decide
  have hdescent : baseEnd_1089283 < baseStart_1089283 := by decide
  rcases family_descends (prefixWord ++ tailWord_1089283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1089334 : List Nat := [5, 1, 2, 2, 1, 1, 3, 2, 2, 3]
def baseStart_1089334 : Nat := 118140960795 + 1089334 * 2 ^ 59
def prefixEnd_1089334 : Nat := 4983230072969 + 3 ^ 40 * 1089334 * 2
def baseEnd_1089334 : Nat := 372901290189964139610167

theorem tailTrace_1089334 : CollatzResearch.WordTrace tailWord_1089334 prefixEnd_1089334 372901290189964139610167 := by
  unfold tailWord_1089334
  simp only [CollatzResearch.WordTrace]
  refine ⟨2483204689721027267539691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 26487516690357624187090037 2483204689721027267539691)
  ·
    refine ⟨3724807034581540901309537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2483204689721027267539691 3724807034581540901309537)
    ·
      refine ⟨2793605275936155675982153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3724807034581540901309537 2793605275936155675982153)
      ·
        refine ⟨2095203956952116756986615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2793605275936155675982153 2095203956952116756986615)
        ·
          refine ⟨3142805935428175135479923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2095203956952116756986615 3142805935428175135479923)
          ·
            refine ⟨4714208903142262703219885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3142805935428175135479923 4714208903142262703219885)
            ·
              refine ⟨1767828338678348513707457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4714208903142262703219885 1767828338678348513707457)
              ·
                refine ⟨1325871254008761385280593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1767828338678348513707457 1325871254008761385280593)
                ·
                  refine ⟨994403440506571038960445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1325871254008761385280593 994403440506571038960445)
                  ·
                    refine ⟨372901290189964139610167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 994403440506571038960445 372901290189964139610167)
                    ·
                      rfl

theorem cell22_1089334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 3, 2, 2, 3].length) (baseStart_1089334 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1089334 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1089334 prefixEnd_1089334 := by exact prefixLift 1089334
  have htrace : WordTrace (prefixWord ++ tailWord_1089334) baseStart_1089334 baseEnd_1089334 := by
    simpa [prefixWord, tailWord_1089334, baseEnd_1089334] using wordTrace_append hprefix tailTrace_1089334
  have hstable : (prefixWord ++ tailWord_1089334).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1089334).length < 2 ^ (prefixWord ++ tailWord_1089334).sum := by decide
  have hdescent : baseEnd_1089334 < baseStart_1089334 := by decide
  rcases family_descends (prefixWord ++ tailWord_1089334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1089433 : List Nat := [1, 2, 1, 2, 1, 3, 2, 3, 1, 6]
def baseStart_1089433 : Nat := 118140960795 + 1089433 * 2 ^ 59
def prefixEnd_1089433 : Nat := 4983230072969 + 3 ^ 40 * 1089433 * 2
def baseEnd_1089433 : Nat := 372935179913160881384863

theorem tailTrace_1089433 : CollatzResearch.WordTrace tailWord_1089433 prefixEnd_1089433 372935179913160881384863 := by
  unfold tailWord_1089433
  simp only [CollatzResearch.WordTrace]
  refine ⟨39734885862177776188488953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26489923908118517458992635 39734885862177776188488953)
  ·
    refine ⟨29801164396633332141366715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39734885862177776188488953 29801164396633332141366715)
    ·
      refine ⟨44701746594949998212050073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29801164396633332141366715 44701746594949998212050073)
      ·
        refine ⟨33526309946212498659037555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44701746594949998212050073 33526309946212498659037555)
        ·
          refine ⟨50289464919318747988556333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33526309946212498659037555 50289464919318747988556333)
          ·
            refine ⟨18858549344744530495708625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50289464919318747988556333 18858549344744530495708625)
            ·
              refine ⟨14143912008558397871781469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18858549344744530495708625 14143912008558397871781469)
              ·
                refine ⟨5303967003209399201918051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14143912008558397871781469 5303967003209399201918051)
                ·
                  refine ⟨7955950504814098802877077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5303967003209399201918051 7955950504814098802877077)
                  ·
                    refine ⟨372935179913160881384863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7955950504814098802877077 372935179913160881384863)
                    ·
                      rfl

theorem cell22_1089433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 3, 1, 6].length) (baseStart_1089433 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1089433 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1089433 prefixEnd_1089433 := by exact prefixLift 1089433
  have htrace : WordTrace (prefixWord ++ tailWord_1089433) baseStart_1089433 baseEnd_1089433 := by
    simpa [prefixWord, tailWord_1089433, baseEnd_1089433] using wordTrace_append hprefix tailTrace_1089433
  have hstable : (prefixWord ++ tailWord_1089433).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1089433).length < 2 ^ (prefixWord ++ tailWord_1089433).sum := by decide
  have hdescent : baseEnd_1089433 < baseStart_1089433 := by decide
  rcases family_descends (prefixWord ++ tailWord_1089433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1089439 : List Nat := [1, 1, 2, 5, 3, 1, 3, 1, 1, 4]
def baseStart_1089439 : Nat := 118140960795 + 1089439 * 2 ^ 59
def prefixEnd_1089439 : Nat := 4983230072969 + 3 ^ 40 * 1089439 * 2
def baseEnd_1089439 : Nat := 372937233835778865734845

theorem tailTrace_1089439 : CollatzResearch.WordTrace tailWord_1089439 prefixEnd_1089439 372937233835778865734845 := by
  unfold tailWord_1089439
  simp only [CollatzResearch.WordTrace]
  refine ⟨39735104700156039213207371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26490069800104026142138247 39735104700156039213207371)
  ·
    refine ⟨59602657050234058819811057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39735104700156039213207371 59602657050234058819811057)
    ·
      refine ⟨44701992787675544114858293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59602657050234058819811057 44701992787675544114858293)
      ·
        refine ⟨4190811823844582260767965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 44701992787675544114858293 4190811823844582260767965)
        ·
          refine ⟨1571554433941718347787987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4190811823844582260767965 1571554433941718347787987)
          ·
            refine ⟨2357331650912577521681981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1571554433941718347787987 2357331650912577521681981)
            ·
              refine ⟨883999369092216570630743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2357331650912577521681981 883999369092216570630743)
              ·
                refine ⟨1325999053638324855946115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 883999369092216570630743 1325999053638324855946115)
                ·
                  refine ⟨1988998580457487283919173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1325999053638324855946115 1988998580457487283919173)
                  ·
                    refine ⟨372937233835778865734845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1988998580457487283919173 372937233835778865734845)
                    ·
                      rfl

theorem cell22_1089439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 3, 1, 1, 4].length) (baseStart_1089439 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1089439 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1089439 prefixEnd_1089439 := by exact prefixLift 1089439
  have htrace : WordTrace (prefixWord ++ tailWord_1089439) baseStart_1089439 baseEnd_1089439 := by
    simpa [prefixWord, tailWord_1089439, baseEnd_1089439] using wordTrace_append hprefix tailTrace_1089439
  have hstable : (prefixWord ++ tailWord_1089439).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1089439).length < 2 ^ (prefixWord ++ tailWord_1089439).sum := by decide
  have hdescent : baseEnd_1089439 < baseStart_1089439 := by decide
  rcases family_descends (prefixWord ++ tailWord_1089439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1089463 : List Nat := [1, 1, 3, 1, 3, 1, 1, 2, 2, 7]
def baseStart_1089463 : Nat := 118140960795 + 1089463 * 2 ^ 59
def prefixEnd_1089463 : Nat := 4983230072969 + 3 ^ 40 * 1089463 * 2
def baseEnd_1089463 : Nat := 372945449526250803134771

theorem tailTrace_1089463 : CollatzResearch.WordTrace tailWord_1089463 prefixEnd_1089463 372945449526250803134771 := by
  unfold tailWord_1089463
  simp only [CollatzResearch.WordTrace]
  refine ⟨39735980052069091312081043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26490653368046060874720695 39735980052069091312081043)
  ·
    refine ⟨59603970078103636968121565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39735980052069091312081043 59603970078103636968121565)
    ·
      refine ⟨22351488779288863863045587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59603970078103636968121565 22351488779288863863045587)
      ·
        refine ⟨33527233168933295794568381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22351488779288863863045587 33527233168933295794568381)
        ·
          refine ⟨12572712438349985922963143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33527233168933295794568381 12572712438349985922963143)
          ·
            refine ⟨18859068657524978884444715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12572712438349985922963143 18859068657524978884444715)
            ·
              refine ⟨28288602986287468326667073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18859068657524978884444715 28288602986287468326667073)
              ·
                refine ⟨21216452239715601245000305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28288602986287468326667073 21216452239715601245000305)
                ·
                  refine ⟨15912339179786700933750229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21216452239715601245000305 15912339179786700933750229)
                  ·
                    refine ⟨372945449526250803134771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 15912339179786700933750229 372945449526250803134771)
                    ·
                      rfl

theorem cell22_1089463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 2, 2, 7].length) (baseStart_1089463 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1089463 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1089463 prefixEnd_1089463 := by exact prefixLift 1089463
  have htrace : WordTrace (prefixWord ++ tailWord_1089463) baseStart_1089463 baseEnd_1089463 := by
    simpa [prefixWord, tailWord_1089463, baseEnd_1089463] using wordTrace_append hprefix tailTrace_1089463
  have hstable : (prefixWord ++ tailWord_1089463).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1089463).length < 2 ^ (prefixWord ++ tailWord_1089463).sum := by decide
  have hdescent : baseEnd_1089463 < baseStart_1089463 := by decide
  rcases family_descends (prefixWord ++ tailWord_1089463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1089514 : List Nat := [3, 1, 3, 1, 2, 1, 1, 6, 1, 3]
def baseStart_1089514 : Nat := 118140960795 + 1089514 * 2 ^ 59
def prefixEnd_1089514 : Nat := 4983230072969 + 3 ^ 40 * 1089514 * 2
def baseEnd_1089514 : Nat := 372962907868503670109615

theorem tailTrace_1089514 : CollatzResearch.WordTrace tailWord_1089514 prefixEnd_1089514 372962907868503670109615 := by
  unfold tailWord_1089514
  simp only [CollatzResearch.WordTrace]
  refine ⟨9934460043721081755546899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26491893449922884681458397 9934460043721081755546899)
  ·
    refine ⟨14901690065581622633320349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9934460043721081755546899 14901690065581622633320349)
    ·
      refine ⟨5588133774593108487495131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14901690065581622633320349 5588133774593108487495131)
      ·
        refine ⟨8382200661889662731242697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5588133774593108487495131 8382200661889662731242697)
        ·
          refine ⟨6286650496417247048432023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8382200661889662731242697 6286650496417247048432023)
          ·
            refine ⟨9429975744625870572648035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6286650496417247048432023 9429975744625870572648035)
            ·
              refine ⟨14144963616938805858972053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9429975744625870572648035 14144963616938805858972053)
              ·
                refine ⟨663045169544006524639315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 14144963616938805858972053 663045169544006524639315)
                ·
                  refine ⟨994567754316009786958973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 663045169544006524639315 994567754316009786958973)
                  ·
                    refine ⟨372962907868503670109615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 994567754316009786958973 372962907868503670109615)
                    ·
                      rfl

theorem cell22_1089514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 6, 1, 3].length) (baseStart_1089514 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1089514 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1089514 prefixEnd_1089514 := by exact prefixLift 1089514
  have htrace : WordTrace (prefixWord ++ tailWord_1089514) baseStart_1089514 baseEnd_1089514 := by
    simpa [prefixWord, tailWord_1089514, baseEnd_1089514] using wordTrace_append hprefix tailTrace_1089514
  have hstable : (prefixWord ++ tailWord_1089514).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1089514).length < 2 ^ (prefixWord ++ tailWord_1089514).sum := by decide
  have hdescent : baseEnd_1089514 < baseStart_1089514 := by decide
  rcases family_descends (prefixWord ++ tailWord_1089514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1089600 : List Nat := [2, 1, 1, 2, 2, 4, 2, 8]
def baseStart_1089600 : Nat := 118140960795 + 1089600 * 2 ^ 59
def prefixEnd_1089600 : Nat := 4983230072969 + 3 ^ 40 * 1089600 * 2
def baseEnd_1089600 : Nat := 41443594158447568051039

theorem tailTrace_1089600 : CollatzResearch.WordTrace tailWord_1089600 prefixEnd_1089600 41443594158447568051039 := by
  unfold tailWord_1089600
  simp only [CollatzResearch.WordTrace]
  refine ⟨19870488426286381854909127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26493984568381842473212169 19870488426286381854909127)
  ·
    refine ⟨29805732639429572782363691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19870488426286381854909127 29805732639429572782363691)
    ·
      refine ⟨44708598959144359173545537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29805732639429572782363691 44708598959144359173545537)
      ·
        refine ⟨33531449219358269380159153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44708598959144359173545537 33531449219358269380159153)
        ·
          refine ⟨25148586914518702035119365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33531449219358269380159153 25148586914518702035119365)
          ·
            refine ⟨4715360046472256631584881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25148586914518702035119365 4715360046472256631584881)
            ·
              refine ⟨3536520034854192473688661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4715360046472256631584881 3536520034854192473688661)
              ·
                refine ⟨41443594158447568051039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3536520034854192473688661 41443594158447568051039)
                ·
                  rfl

theorem cell22_1089600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 2, 8].length) (baseStart_1089600 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1089600 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1089600 prefixEnd_1089600 := by exact prefixLift 1089600
  have htrace : WordTrace (prefixWord ++ tailWord_1089600) baseStart_1089600 baseEnd_1089600 := by
    simpa [prefixWord, tailWord_1089600, baseEnd_1089600] using wordTrace_append hprefix tailTrace_1089600
  have hstable : (prefixWord ++ tailWord_1089600).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1089600).length < 2 ^ (prefixWord ++ tailWord_1089600).sum := by decide
  have hdescent : baseEnd_1089600 < baseStart_1089600 := by decide
  rcases family_descends (prefixWord ++ tailWord_1089600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1089606 : List Nat := [6, 1, 1, 1, 1, 1, 2, 5, 4]
def baseStart_1089606 : Nat := 118140960795 + 1089606 * 2 ^ 59
def prefixEnd_1089606 : Nat := 4983230072969 + 3 ^ 40 * 1089606 * 2
def baseEnd_1089606 : Nat := 124331467116215365603111

theorem tailTrace_1089606 : CollatzResearch.WordTrace tailWord_1089606 prefixEnd_1089606 124331467116215365603111 := by
  unfold tailWord_1089606
  simp only [CollatzResearch.WordTrace]
  refine ⟨1241912365329719585454271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 26494130460367351156357781 1241912365329719585454271)
  ·
    refine ⟨1862868547994579378181407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1241912365329719585454271 1862868547994579378181407)
    ·
      refine ⟨2794302821991869067272111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1862868547994579378181407 2794302821991869067272111)
      ·
        refine ⟨4191454232987803600908167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2794302821991869067272111 4191454232987803600908167)
        ·
          refine ⟨6287181349481705401362251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4191454232987803600908167 6287181349481705401362251)
          ·
            refine ⟨9430772024222558102043377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6287181349481705401362251 9430772024222558102043377)
            ·
              refine ⟨7073079018166918576532533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9430772024222558102043377 7073079018166918576532533)
              ·
                refine ⟨663101157953148616549925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7073079018166918576532533 663101157953148616549925)
                ·
                  refine ⟨124331467116215365603111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 663101157953148616549925 124331467116215365603111)
                  ·
                    rfl

theorem cell22_1089606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 2, 5, 4].length) (baseStart_1089606 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1089606 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1089606 prefixEnd_1089606 := by exact prefixLift 1089606
  have htrace : WordTrace (prefixWord ++ tailWord_1089606) baseStart_1089606 baseEnd_1089606 := by
    simpa [prefixWord, tailWord_1089606, baseEnd_1089606] using wordTrace_append hprefix tailTrace_1089606
  have hstable : (prefixWord ++ tailWord_1089606).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1089606).length < 2 ^ (prefixWord ++ tailWord_1089606).sum := by decide
  have hdescent : baseEnd_1089606 < baseStart_1089606 := by decide
  rcases family_descends (prefixWord ++ tailWord_1089606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1089717 : List Nat := [1, 3, 3, 4, 2, 1, 1, 3, 1, 3]
def baseStart_1089717 : Nat := 118140960795 + 1089717 * 2 ^ 59
def prefixEnd_1089717 : Nat := 4983230072969 + 3 ^ 40 * 1089717 * 2
def baseEnd_1089717 : Nat := 373032398917078807283993

theorem tailTrace_1089717 : CollatzResearch.WordTrace tailWord_1089717 prefixEnd_1089717 373032398917078807283993 := by
  unfold tailWord_1089717
  simp only [CollatzResearch.WordTrace]
  refine ⟨39745244193148892691827405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26496829462099261794551603 39745244193148892691827405)
  ·
    refine ⟨14904466572430834759435277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39745244193148892691827405 14904466572430834759435277)
    ·
      refine ⟨5589174964661563034788229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14904466572430834759435277 5589174964661563034788229)
      ·
        refine ⟨1047970305874043069022793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5589174964661563034788229 1047970305874043069022793)
        ·
          refine ⟨785977729405532301767095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1047970305874043069022793 785977729405532301767095)
          ·
            refine ⟨1178966594108298452650643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 785977729405532301767095 1178966594108298452650643)
            ·
              refine ⟨1768449891162447678975965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1178966594108298452650643 1768449891162447678975965)
              ·
                refine ⟨663168709185917879615987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1768449891162447678975965 663168709185917879615987)
                ·
                  refine ⟨994753063778876819423981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 663168709185917879615987 994753063778876819423981)
                  ·
                    refine ⟨373032398917078807283993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 994753063778876819423981 373032398917078807283993)
                    ·
                      rfl

theorem cell22_1089717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 2, 1, 1, 3, 1, 3].length) (baseStart_1089717 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1089717 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1089717 prefixEnd_1089717 := by exact prefixLift 1089717
  have htrace : WordTrace (prefixWord ++ tailWord_1089717) baseStart_1089717 baseEnd_1089717 := by
    simpa [prefixWord, tailWord_1089717, baseEnd_1089717] using wordTrace_append hprefix tailTrace_1089717
  have hstable : (prefixWord ++ tailWord_1089717).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1089717).length < 2 ^ (prefixWord ++ tailWord_1089717).sum := by decide
  have hdescent : baseEnd_1089717 < baseStart_1089717 := by decide
  rcases family_descends (prefixWord ++ tailWord_1089717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1089722 : List Nat := [3, 1, 1, 1, 2, 2, 2, 4, 1, 5]
def baseStart_1089722 : Nat := 118140960795 + 1089722 * 2 ^ 59
def prefixEnd_1089722 : Nat := 4983230072969 + 3 ^ 40 * 1089722 * 2
def baseEnd_1089722 : Nat := 373034110519260460908977

theorem tailTrace_1089722 : CollatzResearch.WordTrace tailWord_1089722 prefixEnd_1089722 373034110519260460908977 := by
  unfold tailWord_1089722
  simp only [CollatzResearch.WordTrace]
  refine ⟨9936356639532694636439855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26496951038753852363839613 9936356639532694636439855)
  ·
    refine ⟨14904534959299041954659783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9936356639532694636439855 14904534959299041954659783)
    ·
      refine ⟨22356802438948562931989675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14904534959299041954659783 22356802438948562931989675)
      ·
        refine ⟨33535203658422844397984513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22356802438948562931989675 33535203658422844397984513)
        ·
          refine ⟨25151402743817133298488385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33535203658422844397984513 25151402743817133298488385)
          ·
            refine ⟨18863552057862849973866289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25151402743817133298488385 18863552057862849973866289)
            ·
              refine ⟨14147664043397137480399717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18863552057862849973866289 14147664043397137480399717)
              ·
                refine ⟨2652687008136963277574947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14147664043397137480399717 2652687008136963277574947)
                ·
                  refine ⟨3979030512205444916362421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2652687008136963277574947 3979030512205444916362421)
                  ·
                    refine ⟨373034110519260460908977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3979030512205444916362421 373034110519260460908977)
                    ·
                      rfl

theorem cell22_1089722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 4, 1, 5].length) (baseStart_1089722 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1089722 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1089722 prefixEnd_1089722 := by exact prefixLift 1089722
  have htrace : WordTrace (prefixWord ++ tailWord_1089722) baseStart_1089722 baseEnd_1089722 := by
    simpa [prefixWord, tailWord_1089722, baseEnd_1089722] using wordTrace_append hprefix tailTrace_1089722
  have hstable : (prefixWord ++ tailWord_1089722).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1089722).length < 2 ^ (prefixWord ++ tailWord_1089722).sum := by decide
  have hdescent : baseEnd_1089722 < baseStart_1089722 := by decide
  rcases family_descends (prefixWord ++ tailWord_1089722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1089739 : List Nat := [1, 1, 1, 1, 3, 2, 4, 4, 2, 3]
def baseStart_1089739 : Nat := 118140960795 + 1089739 * 2 ^ 59
def prefixEnd_1089739 : Nat := 4983230072969 + 3 ^ 40 * 1089739 * 2
def baseEnd_1089739 : Nat := 373039929966678083233925

theorem tailTrace_1089739 : CollatzResearch.WordTrace tailWord_1089739 prefixEnd_1089739 373039929966678083233925 := by
  unfold tailWord_1089739
  simp only [CollatzResearch.WordTrace]
  refine ⟨39746046599069190449128271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26497364399379460299418847 39746046599069190449128271)
  ·
    refine ⟨59619069898603785673692407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39746046599069190449128271 59619069898603785673692407)
    ·
      refine ⟨89428604847905678510538611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59619069898603785673692407 89428604847905678510538611)
      ·
        refine ⟨134142907271858517765807917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89428604847905678510538611 134142907271858517765807917)
        ·
          refine ⟨50303590226946944162177969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 134142907271858517765807917 50303590226946944162177969)
          ·
            refine ⟨37727692670210208121633477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50303590226946944162177969 37727692670210208121633477)
            ·
              refine ⟨7073942375664414022806277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 37727692670210208121633477 7073942375664414022806277)
              ·
                refine ⟨1326364195437077629276177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7073942375664414022806277 1326364195437077629276177)
                ·
                  refine ⟨994773146577808221957133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1326364195437077629276177 994773146577808221957133)
                  ·
                    refine ⟨373039929966678083233925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 994773146577808221957133 373039929966678083233925)
                    ·
                      rfl

theorem cell22_1089739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 4, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 4, 4, 2, 3].length) (baseStart_1089739 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1089739 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1089739 prefixEnd_1089739 := by exact prefixLift 1089739
  have htrace : WordTrace (prefixWord ++ tailWord_1089739) baseStart_1089739 baseEnd_1089739 := by
    simpa [prefixWord, tailWord_1089739, baseEnd_1089739] using wordTrace_append hprefix tailTrace_1089739
  have hstable : (prefixWord ++ tailWord_1089739).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1089739).length < 2 ^ (prefixWord ++ tailWord_1089739).sum := by decide
  have hdescent : baseEnd_1089739 < baseStart_1089739 := by decide
  rcases family_descends (prefixWord ++ tailWord_1089739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1089752 : List Nat := [2, 1, 2, 2, 4, 1, 1, 9]
def baseStart_1089752 : Nat := 118140960795 + 1089752 * 2 ^ 59
def prefixEnd_1089752 : Nat := 4983230072969 + 3 ^ 40 * 1089752 * 2
def baseEnd_1089752 : Nat := 41449375570261153628765

theorem tailTrace_1089752 : CollatzResearch.WordTrace tailWord_1089752 prefixEnd_1089752 41449375570261153628765 := by
  unfold tailWord_1089752
  simp only [CollatzResearch.WordTrace]
  refine ⟨19873260374011046834675755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26497680498681395779567673 19873260374011046834675755)
  ·
    refine ⟨29809890561016570252013633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19873260374011046834675755 29809890561016570252013633)
    ·
      refine ⟨22357417920762427689010225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29809890561016570252013633 22357417920762427689010225)
      ·
        refine ⟨16768063440571820766757669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22357417920762427689010225 16768063440571820766757669)
        ·
          refine ⟨3144011895107216393767063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16768063440571820766757669 3144011895107216393767063)
          ·
            refine ⟨4716017842660824590650595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3144011895107216393767063 4716017842660824590650595)
            ·
              refine ⟨7074026763991236885975893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4716017842660824590650595 7074026763991236885975893)
              ·
                refine ⟨41449375570261153628765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 7074026763991236885975893 41449375570261153628765)
                ·
                  rfl

theorem cell22_1089752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 1, 9].length) (baseStart_1089752 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1089752 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1089752 prefixEnd_1089752 := by exact prefixLift 1089752
  have htrace : WordTrace (prefixWord ++ tailWord_1089752) baseStart_1089752 baseEnd_1089752 := by
    simpa [prefixWord, tailWord_1089752, baseEnd_1089752] using wordTrace_append hprefix tailTrace_1089752
  have hstable : (prefixWord ++ tailWord_1089752).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1089752).length < 2 ^ (prefixWord ++ tailWord_1089752).sum := by decide
  have hdescent : baseEnd_1089752 < baseStart_1089752 := by decide
  rcases family_descends (prefixWord ++ tailWord_1089752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1089893 : List Nat := [1, 3, 1, 3, 1, 5, 1, 3, 4]
def baseStart_1089893 : Nat := 118140960795 + 1089893 * 2 ^ 59
def prefixEnd_1089893 : Nat := 4983230072969 + 3 ^ 40 * 1089893 * 2
def baseEnd_1089893 : Nat := 124364215771291004961151

theorem tailTrace_1089893 : CollatzResearch.WordTrace tailWord_1089893 prefixEnd_1089893 124364215771291004961151 := by
  unfold tailWord_1089893
  simp only [CollatzResearch.WordTrace]
  refine ⟨39751663440511274750234333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26501108960340849833489555 39751663440511274750234333)
  ·
    refine ⟨14906873790191728031337875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39751663440511274750234333 14906873790191728031337875)
    ·
      refine ⟨22360310685287592047006813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14906873790191728031337875 22360310685287592047006813)
      ·
        refine ⟨8385116506982847017627555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22360310685287592047006813 8385116506982847017627555)
        ·
          refine ⟨12577674760474270526441333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8385116506982847017627555 12577674760474270526441333)
          ·
            refine ⟨1179157008794462861853875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 12577674760474270526441333 1179157008794462861853875)
            ·
              refine ⟨1768735513191694292780813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1179157008794462861853875 1768735513191694292780813)
              ·
                refine ⟨663275817446885359792805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1768735513191694292780813 663275817446885359792805)
                ·
                  refine ⟨124364215771291004961151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 663275817446885359792805 124364215771291004961151)
                  ·
                    rfl

theorem cell22_1089893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 5, 1, 3, 4].length) (baseStart_1089893 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1089893 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1089893 prefixEnd_1089893 := by exact prefixLift 1089893
  have htrace : WordTrace (prefixWord ++ tailWord_1089893) baseStart_1089893 baseEnd_1089893 := by
    simpa [prefixWord, tailWord_1089893, baseEnd_1089893] using wordTrace_append hprefix tailTrace_1089893
  have hstable : (prefixWord ++ tailWord_1089893).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1089893).length < 2 ^ (prefixWord ++ tailWord_1089893).sum := by decide
  have hdescent : baseEnd_1089893 < baseStart_1089893 := by decide
  rcases family_descends (prefixWord ++ tailWord_1089893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1089904 : List Nat := [2, 1, 1, 1, 4, 5, 8]
def baseStart_1089904 : Nat := 118140960795 + 1089904 * 2 ^ 59
def prefixEnd_1089904 : Nat := 4983230072969 + 3 ^ 40 * 1089904 * 2
def baseEnd_1089904 : Nat := 13818385660691579735497

theorem tailTrace_1089904 : CollatzResearch.WordTrace tailWord_1089904 prefixEnd_1089904 13818385660691579735497 := by
  unfold tailWord_1089904
  simp only [CollatzResearch.WordTrace]
  refine ⟨19876032321735711814442383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26501376428980949085923177 19876032321735711814442383)
  ·
    refine ⟨29814048482603567721663575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19876032321735711814442383 29814048482603567721663575)
    ·
      refine ⟨44721072723905351582495363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29814048482603567721663575 44721072723905351582495363)
      ·
        refine ⟨67081609085858027373743045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44721072723905351582495363 67081609085858027373743045)
        ·
          refine ⟨12577801703598380132576821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 67081609085858027373743045 12577801703598380132576821)
          ·
            refine ⟨1179168909712348137429077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 12577801703598380132576821 1179168909712348137429077)
            ·
              refine ⟨13818385660691579735497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1179168909712348137429077 13818385660691579735497)
              ·
                rfl

theorem cell22_1089904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 5, 8].length) (baseStart_1089904 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1089904 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1089904 prefixEnd_1089904 := by exact prefixLift 1089904
  have htrace : WordTrace (prefixWord ++ tailWord_1089904) baseStart_1089904 baseEnd_1089904 := by
    simpa [prefixWord, tailWord_1089904, baseEnd_1089904] using wordTrace_append hprefix tailTrace_1089904
  have hstable : (prefixWord ++ tailWord_1089904).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1089904).length < 2 ^ (prefixWord ++ tailWord_1089904).sum := by decide
  have hdescent : baseEnd_1089904 < baseStart_1089904 := by decide
  rcases family_descends (prefixWord ++ tailWord_1089904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1089906 : List Nat := [3, 2, 1, 2, 1, 4, 1, 2, 2, 4]
def baseStart_1089906 : Nat := 118140960795 + 1089906 * 2 ^ 59
def prefixEnd_1089906 : Nat := 4983230072969 + 3 ^ 40 * 1089906 * 2
def baseEnd_1089906 : Nat := 373097097479545314308413

theorem tailTrace_1089906 : CollatzResearch.WordTrace tailWord_1089906 prefixEnd_1089906 373097097479545314308413 := by
  unfold tailWord_1089906
  simp only [CollatzResearch.WordTrace]
  refine ⟨9938034397366044492614393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26501425059642785313638381 9938034397366044492614393)
  ·
    refine ⟨7453525798024533369460795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9938034397366044492614393 7453525798024533369460795)
    ·
      refine ⟨11180288697036800054191193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7453525798024533369460795 11180288697036800054191193)
      ·
        refine ⟨8385216522777600040643395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11180288697036800054191193 8385216522777600040643395)
        ·
          refine ⟨12577824784166400060965093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8385216522777600040643395 12577824784166400060965093)
          ·
            refine ⟨2358342147031200011430955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12577824784166400060965093 2358342147031200011430955)
            ·
              refine ⟨3537513220546800017146433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2358342147031200011430955 3537513220546800017146433)
              ·
                refine ⟨2653134915410100012859825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3537513220546800017146433 2653134915410100012859825)
                ·
                  refine ⟨1989851186557575009644869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2653134915410100012859825 1989851186557575009644869)
                  ·
                    refine ⟨373097097479545314308413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1989851186557575009644869 373097097479545314308413)
                    ·
                      rfl

theorem cell22_1089906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 1, 2, 2, 4].length) (baseStart_1089906 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1089906 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1089906 prefixEnd_1089906 := by exact prefixLift 1089906
  have htrace : WordTrace (prefixWord ++ tailWord_1089906) baseStart_1089906 baseEnd_1089906 := by
    simpa [prefixWord, tailWord_1089906, baseEnd_1089906] using wordTrace_append hprefix tailTrace_1089906
  have hstable : (prefixWord ++ tailWord_1089906).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1089906).length < 2 ^ (prefixWord ++ tailWord_1089906).sum := by decide
  have hdescent : baseEnd_1089906 < baseStart_1089906 := by decide
  rcases family_descends (prefixWord ++ tailWord_1089906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1089910 : List Nat := [5, 1, 1, 4, 1, 2, 1, 1, 6]
def baseStart_1089910 : Nat := 118140960795 + 1089910 * 2 ^ 59
def prefixEnd_1089910 : Nat := 4983230072969 + 3 ^ 40 * 1089910 * 2
def baseEnd_1089910 : Nat := 124366155587096879069467

theorem tailTrace_1089910 : CollatzResearch.WordTrace tailWord_1089910 prefixEnd_1089910 124366155587096879069467 := by
  unfold tailWord_1089910
  simp only [CollatzResearch.WordTrace]
  refine ⟨2484517717590605415850199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 26501522320966457769068789 2484517717590605415850199)
  ·
    refine ⟨3726776576385908123775299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2484517717590605415850199 3726776576385908123775299)
    ·
      refine ⟨5590164864578862185662949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3726776576385908123775299 5590164864578862185662949)
      ·
        refine ⟨1048155912108536659811803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5590164864578862185662949 1048155912108536659811803)
        ·
          refine ⟨1572233868162804989717705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1048155912108536659811803 1572233868162804989717705)
          ·
            refine ⟨1179175401122103742288279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1572233868162804989717705 1179175401122103742288279)
            ·
              refine ⟨1768763101683155613432419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1179175401122103742288279 1768763101683155613432419)
              ·
                refine ⟨2653144652524733420148629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1768763101683155613432419 2653144652524733420148629)
                ·
                  refine ⟨124366155587096879069467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2653144652524733420148629 124366155587096879069467)
                  ·
                    rfl

theorem cell22_1089910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 2, 1, 1, 6].length) (baseStart_1089910 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1089910 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1089910 prefixEnd_1089910 := by exact prefixLift 1089910
  have htrace : WordTrace (prefixWord ++ tailWord_1089910) baseStart_1089910 baseEnd_1089910 := by
    simpa [prefixWord, tailWord_1089910, baseEnd_1089910] using wordTrace_append hprefix tailTrace_1089910
  have hstable : (prefixWord ++ tailWord_1089910).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1089910).length < 2 ^ (prefixWord ++ tailWord_1089910).sum := by decide
  have hdescent : baseEnd_1089910 < baseStart_1089910 := by decide
  rcases family_descends (prefixWord ++ tailWord_1089910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1089921 : List Nat := [1, 2, 4, 3, 1, 2, 2, 7]
def baseStart_1089921 : Nat := 118140960795 + 1089921 * 2 ^ 59
def prefixEnd_1089921 : Nat := 4983230072969 + 3 ^ 40 * 1089921 * 2
def baseEnd_1089921 : Nat := 41455803587343363909263

theorem tailTrace_1089921 : CollatzResearch.WordTrace tailWord_1089921 prefixEnd_1089921 41455803587343363909263 := by
  unfold tailWord_1089921
  simp only [CollatzResearch.WordTrace]
  refine ⟨39752684684409835532253617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26501789789606557021502411 39752684684409835532253617)
  ·
    refine ⟨29814513513307376649190213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39752684684409835532253617 29814513513307376649190213)
    ·
      refine ⟨5590221283745133121723165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29814513513307376649190213 5590221283745133121723165)
      ·
        refine ⟨2096332981404424920646187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5590221283745133121723165 2096332981404424920646187)
        ·
          refine ⟨3144499472106637380969281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2096332981404424920646187 3144499472106637380969281)
          ·
            refine ⟨2358374604079978035726961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3144499472106637380969281 2358374604079978035726961)
            ·
              refine ⟨1768780953059983526795221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2358374604079978035726961 1768780953059983526795221)
              ·
                refine ⟨41455803587343363909263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1768780953059983526795221 41455803587343363909263)
                ·
                  rfl

theorem cell22_1089921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 2, 7].length) (baseStart_1089921 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1089921 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1089921 prefixEnd_1089921 := by exact prefixLift 1089921
  have htrace : WordTrace (prefixWord ++ tailWord_1089921) baseStart_1089921 baseEnd_1089921 := by
    simpa [prefixWord, tailWord_1089921, baseEnd_1089921] using wordTrace_append hprefix tailTrace_1089921
  have hstable : (prefixWord ++ tailWord_1089921).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1089921).length < 2 ^ (prefixWord ++ tailWord_1089921).sum := by decide
  have hdescent : baseEnd_1089921 < baseStart_1089921 := by decide
  rcases family_descends (prefixWord ++ tailWord_1089921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1089942 : List Nat := [5, 3, 1, 2, 1, 1, 1, 2, 1, 5]
def baseStart_1089942 : Nat := 118140960795 + 1089942 * 2 ^ 59
def prefixEnd_1089942 : Nat := 4983230072969 + 3 ^ 40 * 1089942 * 2
def baseEnd_1089942 : Nat := 373109421015253220408303

theorem tailTrace_1089942 : CollatzResearch.WordTrace tailWord_1089942 prefixEnd_1089942 373109421015253220408303 := by
  unfold tailWord_1089942
  simp only [CollatzResearch.WordTrace]
  refine ⟨2484590663583359757423005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 26502300411555837412512053 2484590663583359757423005)
  ·
    refine ⟨931721498843759909033627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2484590663583359757423005 931721498843759909033627)
    ·
      refine ⟨1397582248265639863550441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 931721498843759909033627 1397582248265639863550441)
      ·
        refine ⟨1048186686199229897662831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1397582248265639863550441 1048186686199229897662831)
        ·
          refine ⟨1572280029298844846494247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1048186686199229897662831 1572280029298844846494247)
          ·
            refine ⟨2358420043948267269741371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1572280029298844846494247 2358420043948267269741371)
            ·
              refine ⟨3537630065922400904612057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2358420043948267269741371 3537630065922400904612057)
              ·
                refine ⟨2653222549441800678459043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3537630065922400904612057 2653222549441800678459043)
                ·
                  refine ⟨3979833824162701017688565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2653222549441800678459043 3979833824162701017688565)
                  ·
                    refine ⟨373109421015253220408303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3979833824162701017688565 373109421015253220408303)
                    ·
                      rfl

theorem cell22_1089942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 1, 2, 1, 5].length) (baseStart_1089942 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1089942 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1089942 prefixEnd_1089942 := by exact prefixLift 1089942
  have htrace : WordTrace (prefixWord ++ tailWord_1089942) baseStart_1089942 baseEnd_1089942 := by
    simpa [prefixWord, tailWord_1089942, baseEnd_1089942] using wordTrace_append hprefix tailTrace_1089942
  have hstable : (prefixWord ++ tailWord_1089942).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1089942).length < 2 ^ (prefixWord ++ tailWord_1089942).sum := by decide
  have hdescent : baseEnd_1089942 < baseStart_1089942 := by decide
  rcases family_descends (prefixWord ++ tailWord_1089942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1089964 : List Nat := [2, 2, 1, 1, 1, 1, 3, 4, 2, 5]
def baseStart_1089964 : Nat := 118140960795 + 1089964 * 2 ^ 59
def prefixEnd_1089964 : Nat := 4983230072969 + 3 ^ 40 * 1089964 * 2
def baseEnd_1089964 : Nat := 373116952064852496358235

theorem tailTrace_1089964 : CollatzResearch.WordTrace tailWord_1089964 prefixEnd_1089964 373116952064852496358235 := by
  unfold tailWord_1089964
  simp only [CollatzResearch.WordTrace]
  refine ⟨19877126511627026938034473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26502835348836035917379297 19877126511627026938034473)
  ·
    refine ⟨14907844883720270203525855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19877126511627026938034473 14907844883720270203525855)
    ·
      refine ⟨22361767325580405305288783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14907844883720270203525855 22361767325580405305288783)
      ·
        refine ⟨33542650988370607957933175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22361767325580405305288783 33542650988370607957933175)
        ·
          refine ⟨50313976482555911936899763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33542650988370607957933175 50313976482555911936899763)
          ·
            refine ⟨75470964723833867905349645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50313976482555911936899763 75470964723833867905349645)
            ·
              refine ⟨28301611771437700464506117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 75470964723833867905349645 28301611771437700464506117)
              ·
                refine ⟨5306552207144568837094897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28301611771437700464506117 5306552207144568837094897)
                ·
                  refine ⟨3979914155358426627821173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5306552207144568837094897 3979914155358426627821173)
                  ·
                    refine ⟨373116952064852496358235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3979914155358426627821173 373116952064852496358235)
                    ·
                      rfl

theorem cell22_1089964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 5].length) (baseStart_1089964 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1089964 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1089964 prefixEnd_1089964 := by exact prefixLift 1089964
  have htrace : WordTrace (prefixWord ++ tailWord_1089964) baseStart_1089964 baseEnd_1089964 := by
    simpa [prefixWord, tailWord_1089964, baseEnd_1089964] using wordTrace_append hprefix tailTrace_1089964
  have hstable : (prefixWord ++ tailWord_1089964).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1089964).length < 2 ^ (prefixWord ++ tailWord_1089964).sum := by decide
  have hdescent : baseEnd_1089964 < baseStart_1089964 := by decide
  rcases family_descends (prefixWord ++ tailWord_1089964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1089972 : List Nat := [2, 5, 2, 2, 2, 1, 1, 7]
def baseStart_1089972 : Nat := 118140960795 + 1089972 * 2 ^ 59
def prefixEnd_1089972 : Nat := 4983230072969 + 3 ^ 40 * 1089972 * 2
def baseEnd_1089972 : Nat := 41457743403149238017579

theorem tailTrace_1089972 : CollatzResearch.WordTrace tailWord_1089972 prefixEnd_1089972 41457743403149238017579 := by
  unfold tailWord_1089972
  simp only [CollatzResearch.WordTrace]
  refine ⟨19877272403612535621180085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26503029871483380828240113 19877272403612535621180085)
  ·
    refine ⟨1863494287838675214485633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 19877272403612535621180085 1863494287838675214485633)
    ·
      refine ⟨1397620715879006410864225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1863494287838675214485633 1397620715879006410864225)
      ·
        refine ⟨1048215536909254808148169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1397620715879006410864225 1048215536909254808148169)
        ·
          refine ⟨786161652681941106111127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1048215536909254808148169 786161652681941106111127)
          ·
            refine ⟨1179242479022911659166691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 786161652681941106111127 1179242479022911659166691)
            ·
              refine ⟨1768863718534367488750037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1179242479022911659166691 1768863718534367488750037)
              ·
                refine ⟨41457743403149238017579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1768863718534367488750037 41457743403149238017579)
                ·
                  rfl

theorem cell22_1089972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 2, 1, 1, 7].length) (baseStart_1089972 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1089972 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1089972 prefixEnd_1089972 := by exact prefixLift 1089972
  have htrace : WordTrace (prefixWord ++ tailWord_1089972) baseStart_1089972 baseEnd_1089972 := by
    simpa [prefixWord, tailWord_1089972, baseEnd_1089972] using wordTrace_append hprefix tailTrace_1089972
  have hstable : (prefixWord ++ tailWord_1089972).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1089972).length < 2 ^ (prefixWord ++ tailWord_1089972).sum := by decide
  have hdescent : baseEnd_1089972 < baseStart_1089972 := by decide
  rcases family_descends (prefixWord ++ tailWord_1089972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1089981 : List Nat := [1, 4, 1, 2, 2, 3, 1, 1, 2, 5]
def baseStart_1089981 : Nat := 118140960795 + 1089981 * 2 ^ 59
def prefixEnd_1089981 : Nat := 4983230072969 + 3 ^ 40 * 1089981 * 2
def baseEnd_1089981 : Nat := 373122771512270118683183

theorem tailTrace_1089981 : CollatzResearch.WordTrace tailWord_1089981 prefixEnd_1089981 373122771512270118683183 := by
  unfold tailWord_1089981
  simp only [CollatzResearch.WordTrace]
  refine ⟨39754873064192465779437797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26503248709461643852958531 39754873064192465779437797)
  ·
    refine ⟨7454038699536087333644587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 39754873064192465779437797 7454038699536087333644587)
    ·
      refine ⟨11181058049304131000466881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7454038699536087333644587 11181058049304131000466881)
      ·
        refine ⟨8385793536978098250350161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11181058049304131000466881 8385793536978098250350161)
        ·
          refine ⟨6289345152733573687762621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8385793536978098250350161 6289345152733573687762621)
          ·
            refine ⟨2358504432275090132910983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6289345152733573687762621 2358504432275090132910983)
            ·
              refine ⟨3537756648412635199366475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2358504432275090132910983 3537756648412635199366475)
              ·
                refine ⟨5306634972618952799049713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3537756648412635199366475 5306634972618952799049713)
                ·
                  refine ⟨3979976229464214599287285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5306634972618952799049713 3979976229464214599287285)
                  ·
                    refine ⟨373122771512270118683183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3979976229464214599287285 373122771512270118683183)
                    ·
                      rfl

theorem cell22_1089981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 1, 1, 2, 5].length) (baseStart_1089981 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1089981 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1089981 prefixEnd_1089981 := by exact prefixLift 1089981
  have htrace : WordTrace (prefixWord ++ tailWord_1089981) baseStart_1089981 baseEnd_1089981 := by
    simpa [prefixWord, tailWord_1089981, baseEnd_1089981] using wordTrace_append hprefix tailTrace_1089981
  have hstable : (prefixWord ++ tailWord_1089981).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1089981).length < 2 ^ (prefixWord ++ tailWord_1089981).sum := by decide
  have hdescent : baseEnd_1089981 < baseStart_1089981 := by decide
  rcases family_descends (prefixWord ++ tailWord_1089981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1090013 : List Nat := [1, 4, 3, 1, 1, 1, 3, 3, 1, 4]
def baseStart_1090013 : Nat := 118140960795 + 1090013 * 2 ^ 59
def prefixEnd_1090013 : Nat := 4983230072969 + 3 ^ 40 * 1090013 * 2
def baseEnd_1090013 : Nat := 373133725766232701883085

theorem tailTrace_1090013 : CollatzResearch.WordTrace tailWord_1090013 prefixEnd_1090013 373133725766232701883085 := by
  unfold tailWord_1090013
  simp only [CollatzResearch.WordTrace]
  refine ⟨39756040200076535244602693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26504026800051023496401795 39756040200076535244602693)
  ·
    refine ⟨7454257537514350358363005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 39756040200076535244602693 7454257537514350358363005)
    ·
      refine ⟨2795346576567881384386127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7454257537514350358363005 2795346576567881384386127)
      ·
        refine ⟨4193019864851822076579191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2795346576567881384386127 4193019864851822076579191)
        ·
          refine ⟨6289529797277733114868787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4193019864851822076579191 6289529797277733114868787)
          ·
            refine ⟨9434294695916599672303181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6289529797277733114868787 9434294695916599672303181)
            ·
              refine ⟨3537860510968724877113693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9434294695916599672303181 3537860510968724877113693)
              ·
                refine ⟨1326697691613271828917635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3537860510968724877113693 1326697691613271828917635)
                ·
                  refine ⟨1990046537419907743376453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1326697691613271828917635 1990046537419907743376453)
                  ·
                    refine ⟨373133725766232701883085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1990046537419907743376453 373133725766232701883085)
                    ·
                      rfl

theorem cell22_1090013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 3, 3, 1, 4].length) (baseStart_1090013 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1090013 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1090013 prefixEnd_1090013 := by exact prefixLift 1090013
  have htrace : WordTrace (prefixWord ++ tailWord_1090013) baseStart_1090013 baseEnd_1090013 := by
    simpa [prefixWord, tailWord_1090013, baseEnd_1090013] using wordTrace_append hprefix tailTrace_1090013
  have hstable : (prefixWord ++ tailWord_1090013).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1090013).length < 2 ^ (prefixWord ++ tailWord_1090013).sum := by decide
  have hdescent : baseEnd_1090013 < baseStart_1090013 := by decide
  rcases family_descends (prefixWord ++ tailWord_1090013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1090094 : List Nat := [4, 1, 3, 1, 3, 2, 2, 1, 2, 3]
def baseStart_1090094 : Nat := 118140960795 + 1090094 * 2 ^ 59
def prefixEnd_1090094 : Nat := 4983230072969 + 3 ^ 40 * 1090094 * 2
def baseEnd_1090094 : Nat := 373161453721575490607837

theorem tailTrace_1090094 : CollatzResearch.WordTrace tailWord_1090094 prefixEnd_1090094 373161453721575490607837 := by
  unfold tailWord_1090094
  simp only [CollatzResearch.WordTrace]
  refine ⟨4969874314097885759787667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26505996341855390718867557 4969874314097885759787667)
  ·
    refine ⟨7454811471146828639681501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4969874314097885759787667 7454811471146828639681501)
    ·
      refine ⟨2795554301680060739880563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7454811471146828639681501 2795554301680060739880563)
      ·
        refine ⟨4193331452520091109820845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2795554301680060739880563 4193331452520091109820845)
        ·
          refine ⟨1572499294695034166182817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4193331452520091109820845 1572499294695034166182817)
          ·
            refine ⟨1179374471021275624637113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1572499294695034166182817 1179374471021275624637113)
            ·
              refine ⟨884530853265956718477835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1179374471021275624637113 884530853265956718477835)
              ·
                refine ⟨1326796279898935077716753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 884530853265956718477835 1326796279898935077716753)
                ·
                  refine ⟨995097209924201308287565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1326796279898935077716753 995097209924201308287565)
                  ·
                    refine ⟨373161453721575490607837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 995097209924201308287565 373161453721575490607837)
                    ·
                      rfl

theorem cell22_1090094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 2, 2, 1, 2, 3].length) (baseStart_1090094 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1090094 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1090094 prefixEnd_1090094 := by exact prefixLift 1090094
  have htrace : WordTrace (prefixWord ++ tailWord_1090094) baseStart_1090094 baseEnd_1090094 := by
    simpa [prefixWord, tailWord_1090094, baseEnd_1090094] using wordTrace_append hprefix tailTrace_1090094
  have hstable : (prefixWord ++ tailWord_1090094).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1090094).length < 2 ^ (prefixWord ++ tailWord_1090094).sum := by decide
  have hdescent : baseEnd_1090094 < baseStart_1090094 := by decide
  rcases family_descends (prefixWord ++ tailWord_1090094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1090180 : List Nat := [2, 3, 2, 1, 3, 1, 1, 5, 4]
def baseStart_1090180 : Nat := 118140960795 + 1090180 * 2 ^ 59
def prefixEnd_1090180 : Nat := 4983230072969 + 3 ^ 40 * 1090180 * 2
def baseEnd_1090180 : Nat := 124396964426366644319191

theorem tailTrace_1090180 : CollatzResearch.WordTrace tailWord_1090180 prefixEnd_1090180 124396964426366644319191 := by
  unfold tailWord_1090180
  simp only [CollatzResearch.WordTrace]
  refine ⟨19881065595235761382965997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26508087460314348510621329 19881065595235761382965997)
  ·
    refine ⟨7455399598213410518612249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19881065595235761382965997 7455399598213410518612249)
    ·
      refine ⟨5591549698660057888959187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7455399598213410518612249 5591549698660057888959187)
      ·
        refine ⟨8387324547990086833438781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5591549698660057888959187 8387324547990086833438781)
        ·
          refine ⟨3145246705496282562539543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8387324547990086833438781 3145246705496282562539543)
          ·
            refine ⟨4717870058244423843809315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3145246705496282562539543 4717870058244423843809315)
            ·
              refine ⟨7076805087366635765713973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4717870058244423843809315 7076805087366635765713973)
              ·
                refine ⟨663450476940622103035685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7076805087366635765713973 663450476940622103035685)
                ·
                  refine ⟨124396964426366644319191, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 663450476940622103035685 124396964426366644319191)
                  ·
                    rfl

theorem cell22_1090180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 1, 5, 4].length) (baseStart_1090180 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1090180 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1090180 prefixEnd_1090180 := by exact prefixLift 1090180
  have htrace : WordTrace (prefixWord ++ tailWord_1090180) baseStart_1090180 baseEnd_1090180 := by
    simpa [prefixWord, tailWord_1090180, baseEnd_1090180] using wordTrace_append hprefix tailTrace_1090180
  have hstable : (prefixWord ++ tailWord_1090180).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1090180).length < 2 ^ (prefixWord ++ tailWord_1090180).sum := by decide
  have hdescent : baseEnd_1090180 < baseStart_1090180 := by decide
  rcases family_descends (prefixWord ++ tailWord_1090180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1090212 : List Nat := [2, 3, 1, 2, 2, 1, 5, 1, 2, 3]
def baseStart_1090212 : Nat := 118140960795 + 1090212 * 2 ^ 59
def prefixEnd_1090212 : Nat := 4983230072969 + 3 ^ 40 * 1090212 * 2
def baseEnd_1090212 : Nat := 373201847533062516157475

theorem tailTrace_1090212 : CollatzResearch.WordTrace tailWord_1090212 prefixEnd_1090212 373201847533062516157475 := by
  unfold tailWord_1090212
  simp only [CollatzResearch.WordTrace]
  refine ⟨19881649163177796115548445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26508865550903728154064593 19881649163177796115548445)
  ·
    refine ⟨7455618436191673543330667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19881649163177796115548445 7455618436191673543330667)
    ·
      refine ⟨11183427654287510314996001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7455618436191673543330667 11183427654287510314996001)
      ·
        refine ⟨8387570740715632736247001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11183427654287510314996001 8387570740715632736247001)
        ·
          refine ⟨6290678055536724552185251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8387570740715632736247001 6290678055536724552185251)
          ·
            refine ⟨9436017083305086828277877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6290678055536724552185251 9436017083305086828277877)
            ·
              refine ⟨884626601559851890151051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9436017083305086828277877 884626601559851890151051)
              ·
                refine ⟨1326939902339777835226577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 884626601559851890151051 1326939902339777835226577)
                ·
                  refine ⟨995204926754833376419933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1326939902339777835226577 995204926754833376419933)
                  ·
                    refine ⟨373201847533062516157475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 995204926754833376419933 373201847533062516157475)
                    ·
                      rfl

theorem cell22_1090212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 5, 1, 2, 3].length) (baseStart_1090212 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1090212 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1090212 prefixEnd_1090212 := by exact prefixLift 1090212
  have htrace : WordTrace (prefixWord ++ tailWord_1090212) baseStart_1090212 baseEnd_1090212 := by
    simpa [prefixWord, tailWord_1090212, baseEnd_1090212] using wordTrace_append hprefix tailTrace_1090212
  have hstable : (prefixWord ++ tailWord_1090212).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1090212).length < 2 ^ (prefixWord ++ tailWord_1090212).sum := by decide
  have hdescent : baseEnd_1090212 < baseStart_1090212 := by decide
  rcases family_descends (prefixWord ++ tailWord_1090212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1090225 : List Nat := [1, 2, 2, 6, 1, 1, 1, 8]
def baseStart_1090225 : Nat := 118140960795 + 1090225 * 2 ^ 59
def prefixEnd_1090225 : Nat := 4983230072969 + 3 ^ 40 * 1090225 * 2
def baseEnd_1090225 : Nat := 41467366410970535064715

theorem tailTrace_1090225 : CollatzResearch.WordTrace tailWord_1090225 prefixEnd_1090225 41467366410970535064715 := by
  unfold tailWord_1090225
  simp only [CollatzResearch.WordTrace]
  refine ⟨39763772475308495451320129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26509181650205663634213419 39763772475308495451320129)
  ·
    refine ⟨29822829356481371588490097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39763772475308495451320129 29822829356481371588490097)
    ·
      refine ⟨22367122017361028691367573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29822829356481371588490097 22367122017361028691367573)
      ·
        refine ⟨1048458844563798219907855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 22367122017361028691367573 1048458844563798219907855)
        ·
          refine ⟨1572688266845697329861783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1048458844563798219907855 1572688266845697329861783)
          ·
            refine ⟨2359032400268545994792675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1572688266845697329861783 2359032400268545994792675)
            ·
              refine ⟨3538548600402818992189013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2359032400268545994792675 3538548600402818992189013)
              ·
                refine ⟨41467366410970535064715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3538548600402818992189013 41467366410970535064715)
                ·
                  rfl

theorem cell22_1090225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 1, 8].length) (baseStart_1090225 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1090225 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1090225 prefixEnd_1090225 := by exact prefixLift 1090225
  have htrace : WordTrace (prefixWord ++ tailWord_1090225) baseStart_1090225 baseEnd_1090225 := by
    simpa [prefixWord, tailWord_1090225, baseEnd_1090225] using wordTrace_append hprefix tailTrace_1090225
  have hstable : (prefixWord ++ tailWord_1090225).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1090225).length < 2 ^ (prefixWord ++ tailWord_1090225).sum := by decide
  have hdescent : baseEnd_1090225 < baseStart_1090225 := by decide
  rcases family_descends (prefixWord ++ tailWord_1090225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1090328 : List Nat := [2, 1, 2, 3, 1, 1, 1, 4, 1, 6]
def baseStart_1090328 : Nat := 118140960795 + 1090328 * 2 ^ 59
def prefixEnd_1090328 : Nat := 4983230072969 + 3 ^ 40 * 1090328 * 2
def baseEnd_1090328 : Nat := 373241556703676880257119

theorem tailTrace_1090328 : CollatzResearch.WordTrace tailWord_1090328 prefixEnd_1090328 373241556703676880257119 := by
  unfold tailWord_1090328
  simp only [CollatzResearch.WordTrace]
  refine ⟨19883764596967672021159819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26511686129290229361546425 19883764596967672021159819)
  ·
    refine ⟨29825646895451508031739729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19883764596967672021159819 29825646895451508031739729)
    ·
      refine ⟨22369235171588631023804797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29825646895451508031739729 22369235171588631023804797)
      ·
        refine ⟨8388463189345736633926799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22369235171588631023804797 8388463189345736633926799)
        ·
          refine ⟨12582694784018604950890199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8388463189345736633926799 12582694784018604950890199)
          ·
            refine ⟨18874042176027907426335299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12582694784018604950890199 18874042176027907426335299)
            ·
              refine ⟨28311063264041861139502949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18874042176027907426335299 28311063264041861139502949)
              ·
                refine ⟨5308324362007848963656803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28311063264041861139502949 5308324362007848963656803)
                ·
                  refine ⟨7962486543011773445485205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5308324362007848963656803 7962486543011773445485205)
                  ·
                    refine ⟨373241556703676880257119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7962486543011773445485205 373241556703676880257119)
                    ·
                      rfl

theorem cell22_1090328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 4, 1, 6].length) (baseStart_1090328 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1090328 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1090328 prefixEnd_1090328 := by exact prefixLift 1090328
  have htrace : WordTrace (prefixWord ++ tailWord_1090328) baseStart_1090328 baseEnd_1090328 := by
    simpa [prefixWord, tailWord_1090328, baseEnd_1090328] using wordTrace_append hprefix tailTrace_1090328
  have hstable : (prefixWord ++ tailWord_1090328).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1090328).length < 2 ^ (prefixWord ++ tailWord_1090328).sum := by decide
  have hdescent : baseEnd_1090328 < baseStart_1090328 := by decide
  rcases family_descends (prefixWord ++ tailWord_1090328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1090330 : List Nat := [3, 1, 1, 3, 2, 1, 4, 1, 1, 5]
def baseStart_1090330 : Nat := 118140960795 + 1090330 * 2 ^ 59
def prefixEnd_1090330 : Nat := 4983230072969 + 3 ^ 40 * 1090330 * 2
def baseEnd_1090330 : Nat := 373242241344549541707113

theorem tailTrace_1090330 : CollatzResearch.WordTrace tailWord_1090330 prefixEnd_1090330 373242241344549541707113 := by
  unfold tailWord_1090330
  simp only [CollatzResearch.WordTrace]
  refine ⟨9941900534982024595973111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26511734759952065589261629 9941900534982024595973111)
  ·
    refine ⟨14912850802473036893959667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9941900534982024595973111 14912850802473036893959667)
    ·
      refine ⟨22369276203709555340939501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14912850802473036893959667 22369276203709555340939501)
      ·
        refine ⟨8388478576391083252852313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22369276203709555340939501 8388478576391083252852313)
        ·
          refine ⟨6291358932293312439639235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8388478576391083252852313 6291358932293312439639235)
          ·
            refine ⟨9437038398439968659458853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6291358932293312439639235 9437038398439968659458853)
            ·
              refine ⟨1769444699707494123648535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9437038398439968659458853 1769444699707494123648535)
              ·
                refine ⟨2654167049561241185472803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1769444699707494123648535 2654167049561241185472803)
                ·
                  refine ⟨3981250574341861778209205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2654167049561241185472803 3981250574341861778209205)
                  ·
                    refine ⟨373242241344549541707113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3981250574341861778209205 373242241344549541707113)
                    ·
                      rfl

theorem cell22_1090330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 4, 1, 1, 5].length) (baseStart_1090330 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1090330 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1090330 prefixEnd_1090330 := by exact prefixLift 1090330
  have htrace : WordTrace (prefixWord ++ tailWord_1090330) baseStart_1090330 baseEnd_1090330 := by
    simpa [prefixWord, tailWord_1090330, baseEnd_1090330] using wordTrace_append hprefix tailTrace_1090330
  have hstable : (prefixWord ++ tailWord_1090330).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1090330).length < 2 ^ (prefixWord ++ tailWord_1090330).sum := by decide
  have hdescent : baseEnd_1090330 < baseStart_1090330 := by decide
  rcases family_descends (prefixWord ++ tailWord_1090330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1090373 : List Nat := [1, 3, 1, 1, 1, 2, 2, 3, 2, 6]
def baseStart_1090373 : Nat := 118140960795 + 1090373 * 2 ^ 59
def prefixEnd_1090373 : Nat := 4983230072969 + 3 ^ 40 * 1090373 * 2
def baseEnd_1090373 : Nat := 373256961123311762881981

theorem tailTrace_1090373 : CollatzResearch.WordTrace tailWord_1090373 prefixEnd_1090373 373256961123311762881981 := by
  unfold tailWord_1090373
  simp only [CollatzResearch.WordTrace]
  refine ⟨39769170478772316727707773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26512780319181544485138515 39769170478772316727707773)
  ·
    refine ⟨14913438929539618772890415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39769170478772316727707773 14913438929539618772890415)
    ·
      refine ⟨22370158394309428159335623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14913438929539618772890415 22370158394309428159335623)
      ·
        refine ⟨33555237591464142239003435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22370158394309428159335623 33555237591464142239003435)
        ·
          refine ⟨50332856387196213358505153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33555237591464142239003435 50332856387196213358505153)
          ·
            refine ⟨37749642290397160018878865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50332856387196213358505153 37749642290397160018878865)
            ·
              refine ⟨28312231717797870014159149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37749642290397160018878865 28312231717797870014159149)
              ·
                refine ⟨10617086894174201255309681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28312231717797870014159149 10617086894174201255309681)
                ·
                  refine ⟨7962815170630650941482261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10617086894174201255309681 7962815170630650941482261)
                  ·
                    refine ⟨373256961123311762881981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7962815170630650941482261 373256961123311762881981)
                    ·
                      rfl

theorem cell22_1090373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 3, 2, 6].length) (baseStart_1090373 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1090373 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1090373 prefixEnd_1090373 := by exact prefixLift 1090373
  have htrace : WordTrace (prefixWord ++ tailWord_1090373) baseStart_1090373 baseEnd_1090373 := by
    simpa [prefixWord, tailWord_1090373, baseEnd_1090373] using wordTrace_append hprefix tailTrace_1090373
  have hstable : (prefixWord ++ tailWord_1090373).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1090373).length < 2 ^ (prefixWord ++ tailWord_1090373).sum := by decide
  have hdescent : baseEnd_1090373 < baseStart_1090373 := by decide
  rcases family_descends (prefixWord ++ tailWord_1090373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1090381 : List Nat := [1, 6, 1, 2, 3, 1, 1, 1, 1, 5]
def baseStart_1090381 : Nat := 118140960795 + 1090381 * 2 ^ 59
def prefixEnd_1090381 : Nat := 4983230072969 + 3 ^ 40 * 1090381 * 2
def baseEnd_1090381 : Nat := 373259699686802408681957

theorem tailTrace_1090381 : CollatzResearch.WordTrace tailWord_1090381 prefixEnd_1090381 373259699686802408681957 := by
  unfold tailWord_1090381
  simp only [CollatzResearch.WordTrace]
  refine ⟨39769462262743334093998997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26512974841828889395999331 39769462262743334093998997)
  ·
    refine ⟨1864193543566093785656203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 39769462262743334093998997 1864193543566093785656203)
    ·
      refine ⟨2796290315349140678484305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1864193543566093785656203 2796290315349140678484305)
      ·
        refine ⟨2097217736511855508863229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2796290315349140678484305 2097217736511855508863229)
        ·
          refine ⟨786456651191945815823711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2097217736511855508863229 786456651191945815823711)
          ·
            refine ⟨1179684976787918723735567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 786456651191945815823711 1179684976787918723735567)
            ·
              refine ⟨1769527465181878085603351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1179684976787918723735567 1769527465181878085603351)
              ·
                refine ⟨2654291197772817128405027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1769527465181878085603351 2654291197772817128405027)
                ·
                  refine ⟨3981436796659225692607541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2654291197772817128405027 3981436796659225692607541)
                  ·
                    refine ⟨373259699686802408681957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3981436796659225692607541 373259699686802408681957)
                    ·
                      rfl

theorem cell22_1090381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 3, 1, 1, 1, 1, 5].length) (baseStart_1090381 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1090381 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1090381 prefixEnd_1090381 := by exact prefixLift 1090381
  have htrace : WordTrace (prefixWord ++ tailWord_1090381) baseStart_1090381 baseEnd_1090381 := by
    simpa [prefixWord, tailWord_1090381, baseEnd_1090381] using wordTrace_append hprefix tailTrace_1090381
  have hstable : (prefixWord ++ tailWord_1090381).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1090381).length < 2 ^ (prefixWord ++ tailWord_1090381).sum := by decide
  have hdescent : baseEnd_1090381 < baseStart_1090381 := by decide
  rcases family_descends (prefixWord ++ tailWord_1090381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1090422 : List Nat := [5, 1, 1, 3, 1, 1, 2, 1, 7]
def baseStart_1090422 : Nat := 118140960795 + 1090422 * 2 ^ 59
def prefixEnd_1090422 : Nat := 4983230072969 + 3 ^ 40 * 1090422 * 2
def baseEnd_1090422 : Nat := 124424578274897322802277

theorem tailTrace_1090422 : CollatzResearch.WordTrace tailWord_1090422 prefixEnd_1090422 124424578274897322802277 := by
  unfold tailWord_1090422
  simp only [CollatzResearch.WordTrace]
  refine ⟨2485684853474674881015095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 26513971770396532064161013 2485684853474674881015095)
  ·
    refine ⟨3728527280212012321522643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2485684853474674881015095 3728527280212012321522643)
    ·
      refine ⟨5592790920318018482283965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3728527280212012321522643 5592790920318018482283965)
      ·
        refine ⟨2097296595119256930856487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5592790920318018482283965 2097296595119256930856487)
        ·
          refine ⟨3145944892678885396284731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2097296595119256930856487 3145944892678885396284731)
          ·
            refine ⟨4718917339018328094427097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3145944892678885396284731 4718917339018328094427097)
            ·
              refine ⟨3539188004263746070820323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4718917339018328094427097 3539188004263746070820323)
              ·
                refine ⟨5308782006395619106230485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3539188004263746070820323 5308782006395619106230485)
                ·
                  refine ⟨124424578274897322802277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5308782006395619106230485 124424578274897322802277)
                  ·
                    rfl

theorem cell22_1090422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 2, 1, 7].length) (baseStart_1090422 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1090422 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1090422 prefixEnd_1090422 := by exact prefixLift 1090422
  have htrace : WordTrace (prefixWord ++ tailWord_1090422) baseStart_1090422 baseEnd_1090422 := by
    simpa [prefixWord, tailWord_1090422, baseEnd_1090422] using wordTrace_append hprefix tailTrace_1090422
  have hstable : (prefixWord ++ tailWord_1090422).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1090422).length < 2 ^ (prefixWord ++ tailWord_1090422).sum := by decide
  have hdescent : baseEnd_1090422 < baseStart_1090422 := by decide
  rcases family_descends (prefixWord ++ tailWord_1090422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1090435 : List Nat := [1, 1, 1, 3, 4, 1, 2, 2, 3, 4]
def baseStart_1090435 : Nat := 118140960795 + 1090435 * 2 ^ 59
def prefixEnd_1090435 : Nat := 4983230072969 + 3 ^ 40 * 1090435 * 2
def baseEnd_1090435 : Nat := 373278184990364267831791

theorem tailTrace_1090435 : CollatzResearch.WordTrace tailWord_1090435 prefixEnd_1090435 373278184990364267831791 := by
  unfold tailWord_1090435
  simp only [CollatzResearch.WordTrace]
  refine ⟨39771431804547701316464759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26514287869698467544309839 39771431804547701316464759)
  ·
    refine ⟨59657147706821551974697139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39771431804547701316464759 59657147706821551974697139)
    ·
      refine ⟨89485721560232327962045709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59657147706821551974697139 89485721560232327962045709)
      ·
        refine ⟨33557145585087122985767141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 89485721560232327962045709 33557145585087122985767141)
        ·
          refine ⟨6291964797203835559831339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 33557145585087122985767141 6291964797203835559831339)
          ·
            refine ⟨9437947195805753339747009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6291964797203835559831339 9437947195805753339747009)
            ·
              refine ⟨7078460396854315004810257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9437947195805753339747009 7078460396854315004810257)
              ·
                refine ⟨5308845297640736253607693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7078460396854315004810257 5308845297640736253607693)
                ·
                  refine ⟨1990816986615276095102885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5308845297640736253607693 1990816986615276095102885)
                  ·
                    refine ⟨373278184990364267831791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1990816986615276095102885 373278184990364267831791)
                    ·
                      rfl

theorem cell22_1090435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 2, 2, 3, 4].length) (baseStart_1090435 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1090435 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1090435 prefixEnd_1090435 := by exact prefixLift 1090435
  have htrace : WordTrace (prefixWord ++ tailWord_1090435) baseStart_1090435 baseEnd_1090435 := by
    simpa [prefixWord, tailWord_1090435, baseEnd_1090435] using wordTrace_append hprefix tailTrace_1090435
  have hstable : (prefixWord ++ tailWord_1090435).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1090435).length < 2 ^ (prefixWord ++ tailWord_1090435).sum := by decide
  have hdescent : baseEnd_1090435 < baseStart_1090435 := by decide
  rcases family_descends (prefixWord ++ tailWord_1090435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1090439 : List Nat := [1, 1, 4, 2, 3, 3, 2, 1, 5]
def baseStart_1090439 : Nat := 118140960795 + 1090439 * 2 ^ 59
def prefixEnd_1090439 : Nat := 4983230072969 + 3 ^ 40 * 1090439 * 2
def baseEnd_1090439 : Nat := 124426518090703196910593

theorem tailTrace_1090439 : CollatzResearch.WordTrace tailWord_1090439 prefixEnd_1090439 124426518090703196910593 := by
  unfold tailWord_1090439
  simp only [CollatzResearch.WordTrace]
  refine ⟨39771577696533209999610371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26514385131022139999740247 39771577696533209999610371)
  ·
    refine ⟨59657366544799814999415557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39771577696533209999610371 59657366544799814999415557)
    ·
      refine ⟨11185756227149965312390417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 59657366544799814999415557 11185756227149965312390417)
      ·
        refine ⟨8389317170362473984292813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11185756227149965312390417 8389317170362473984292813)
        ·
          refine ⟨3145993938885927744109805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8389317170362473984292813 3145993938885927744109805)
          ·
            refine ⟨1179747727082222904041177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3145993938885927744109805 1179747727082222904041177)
            ·
              refine ⟨884810795311667178030883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1179747727082222904041177 884810795311667178030883)
              ·
                refine ⟨1327216192967500767046325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 884810795311667178030883 1327216192967500767046325)
                ·
                  refine ⟨124426518090703196910593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1327216192967500767046325 124426518090703196910593)
                  ·
                    rfl

theorem cell22_1090439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 3, 2, 1, 5].length) (baseStart_1090439 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1090439 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1090439 prefixEnd_1090439 := by exact prefixLift 1090439
  have htrace : WordTrace (prefixWord ++ tailWord_1090439) baseStart_1090439 baseEnd_1090439 := by
    simpa [prefixWord, tailWord_1090439, baseEnd_1090439] using wordTrace_append hprefix tailTrace_1090439
  have hstable : (prefixWord ++ tailWord_1090439).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1090439).length < 2 ^ (prefixWord ++ tailWord_1090439).sum := by decide
  have hdescent : baseEnd_1090439 < baseStart_1090439 := by decide
  rcases family_descends (prefixWord ++ tailWord_1090439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1090452 : List Nat := [2, 4, 2, 1, 1, 1, 3, 1, 3, 4]
def baseStart_1090452 : Nat := 118140960795 + 1090452 * 2 ^ 59
def prefixEnd_1090452 : Nat := 4983230072969 + 3 ^ 40 * 1090452 * 2
def baseEnd_1090452 : Nat := 373284004437781890156739

theorem tailTrace_1090452 : CollatzResearch.WordTrace tailWord_1090452 prefixEnd_1090452 373284004437781890156739 := by
  unfold tailWord_1090452
  simp only [CollatzResearch.WordTrace]
  refine ⟨19886025922743056609916805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26514701230324075479889073 19886025922743056609916805)
  ·
    refine ⟨3728629860514323114359401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19886025922743056609916805 3728629860514323114359401)
    ·
      refine ⟨2796472395385742335769551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3728629860514323114359401 2796472395385742335769551)
      ·
        refine ⟨4194708593078613503654327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2796472395385742335769551 4194708593078613503654327)
        ·
          refine ⟨6292062889617920255481491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4194708593078613503654327 6292062889617920255481491)
          ·
            refine ⟨9438094334426880383222237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6292062889617920255481491 9438094334426880383222237)
            ·
              refine ⟨3539285375410080143708339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9438094334426880383222237 3539285375410080143708339)
              ·
                refine ⟨5308928063115120215562509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3539285375410080143708339 5308928063115120215562509)
                ·
                  refine ⟨1990848023668170080835941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5308928063115120215562509 1990848023668170080835941)
                  ·
                    refine ⟨373284004437781890156739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1990848023668170080835941 373284004437781890156739)
                    ·
                      rfl

theorem cell22_1090452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 3, 1, 3, 4].length) (baseStart_1090452 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1090452 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1090452 prefixEnd_1090452 := by exact prefixLift 1090452
  have htrace : WordTrace (prefixWord ++ tailWord_1090452) baseStart_1090452 baseEnd_1090452 := by
    simpa [prefixWord, tailWord_1090452, baseEnd_1090452] using wordTrace_append hprefix tailTrace_1090452
  have hstable : (prefixWord ++ tailWord_1090452).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1090452).length < 2 ^ (prefixWord ++ tailWord_1090452).sum := by decide
  have hdescent : baseEnd_1090452 < baseStart_1090452 := by decide
  rcases family_descends (prefixWord ++ tailWord_1090452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1090477 : List Nat := [1, 5, 2, 3, 2, 1, 2, 2, 1, 3]
def baseStart_1090477 : Nat := 118140960795 + 1090477 * 2 ^ 59
def prefixEnd_1090477 : Nat := 4983230072969 + 3 ^ 40 * 1090477 * 2
def baseEnd_1090477 : Nat := 373292562448690158281663

theorem tailTrace_1090477 : CollatzResearch.WordTrace tailWord_1090477 prefixEnd_1090477 373292562448690158281663 := by
  unfold tailWord_1090477
  simp only [CollatzResearch.WordTrace]
  refine ⟨39772963670395542489493685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26515309113597028326329123 39772963670395542489493685)
  ·
    refine ⟨3728715344099582108390033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 39772963670395542489493685 3728715344099582108390033)
    ·
      refine ⟨2796536508074686581292525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3728715344099582108390033 2796536508074686581292525)
      ·
        refine ⟨1048701190528007467984697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2796536508074686581292525 1048701190528007467984697)
        ·
          refine ⟨786525892896005600988523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1048701190528007467984697 786525892896005600988523)
          ·
            refine ⟨1179788839344008401482785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 786525892896005600988523 1179788839344008401482785)
            ·
              refine ⟨884841629508006301112089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1179788839344008401482785 884841629508006301112089)
              ·
                refine ⟨663631222131004725834067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 884841629508006301112089 663631222131004725834067)
                ·
                  refine ⟨995446833196507088751101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 663631222131004725834067 995446833196507088751101)
                  ·
                    refine ⟨373292562448690158281663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 995446833196507088751101 373292562448690158281663)
                    ·
                      rfl

theorem cell22_1090477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 2, 1, 2, 2, 1, 3].length) (baseStart_1090477 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1090477 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1090477 prefixEnd_1090477 := by exact prefixLift 1090477
  have htrace : WordTrace (prefixWord ++ tailWord_1090477) baseStart_1090477 baseEnd_1090477 := by
    simpa [prefixWord, tailWord_1090477, baseEnd_1090477] using wordTrace_append hprefix tailTrace_1090477
  have hstable : (prefixWord ++ tailWord_1090477).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1090477).length < 2 ^ (prefixWord ++ tailWord_1090477).sum := by decide
  have hdescent : baseEnd_1090477 < baseStart_1090477 := by decide
  rcases family_descends (prefixWord ++ tailWord_1090477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1090514 : List Nat := [3, 2, 2, 3, 1, 1, 3, 1, 2, 4]
def baseStart_1090514 : Nat := 118140960795 + 1090514 * 2 ^ 59
def prefixEnd_1090514 : Nat := 4983230072969 + 3 ^ 40 * 1090514 * 2
def baseEnd_1090514 : Nat := 373305228304834395106549

theorem tailTrace_1090514 : CollatzResearch.WordTrace tailWord_1090514 prefixEnd_1090514 373305228304834395106549 := by
  unfold tailWord_1090514
  simp only [CollatzResearch.WordTrace]
  refine ⟨9943578292815374452147649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26516208780840998539060397 9943578292815374452147649)
  ·
    refine ⟨7457683719611530839110737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9943578292815374452147649 7457683719611530839110737)
    ·
      refine ⟨5593262789708648129333053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7457683719611530839110737 5593262789708648129333053)
      ·
        refine ⟨2097473546140743048499895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5593262789708648129333053 2097473546140743048499895)
        ·
          refine ⟨3146210319211114572749843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2097473546140743048499895 3146210319211114572749843)
          ·
            refine ⟨4719315478816671859124765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3146210319211114572749843 4719315478816671859124765)
            ·
              refine ⟨1769743304556251947171787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4719315478816671859124765 1769743304556251947171787)
              ·
                refine ⟨2654614956834377920757681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1769743304556251947171787 2654614956834377920757681)
                ·
                  refine ⟨1990961217625783440568261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2654614956834377920757681 1990961217625783440568261)
                  ·
                    refine ⟨373305228304834395106549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1990961217625783440568261 373305228304834395106549)
                    ·
                      rfl

theorem cell22_1090514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 3, 1, 2, 4].length) (baseStart_1090514 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1090514 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1090514 prefixEnd_1090514 := by exact prefixLift 1090514
  have htrace : WordTrace (prefixWord ++ tailWord_1090514) baseStart_1090514 baseEnd_1090514 := by
    simpa [prefixWord, tailWord_1090514, baseEnd_1090514] using wordTrace_append hprefix tailTrace_1090514
  have hstable : (prefixWord ++ tailWord_1090514).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1090514).length < 2 ^ (prefixWord ++ tailWord_1090514).sum := by decide
  have hdescent : baseEnd_1090514 < baseStart_1090514 := by decide
  rcases family_descends (prefixWord ++ tailWord_1090514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1090533 : List Nat := [1, 3, 1, 6, 1, 2, 1, 2, 2, 3]
def baseStart_1090533 : Nat := 118140960795 + 1090533 * 2 ^ 59
def prefixEnd_1090533 : Nat := 4983230072969 + 3 ^ 40 * 1090533 * 2
def baseEnd_1090533 : Nat := 373311732393124678881491

theorem tailTrace_1090533 : CollatzResearch.WordTrace tailWord_1090533 prefixEnd_1090533 373311732393124678881491 := by
  unfold tailWord_1090533
  simp only [CollatzResearch.WordTrace]
  refine ⟨39775006158192664053532253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26516670772128442702354835 39775006158192664053532253)
  ·
    refine ⟨14915627309322249020074595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39775006158192664053532253 14915627309322249020074595)
    ·
      refine ⟨22373440963983373530111893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14915627309322249020074595 22373440963983373530111893)
      ·
        refine ⟨1048755045186720634223995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 22373440963983373530111893 1048755045186720634223995)
        ·
          refine ⟨1573132567780080951335993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1048755045186720634223995 1573132567780080951335993)
          ·
            refine ⟨1179849425835060713501995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1573132567780080951335993 1179849425835060713501995)
            ·
              refine ⟨1769774138752591070252993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1179849425835060713501995 1769774138752591070252993)
              ·
                refine ⟨1327330604064443302689745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1769774138752591070252993 1327330604064443302689745)
                ·
                  refine ⟨995497953048332477017309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1327330604064443302689745 995497953048332477017309)
                  ·
                    refine ⟨373311732393124678881491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 995497953048332477017309 373311732393124678881491)
                    ·
                      rfl

theorem cell22_1090533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 2, 1, 2, 2, 3].length) (baseStart_1090533 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1090533 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1090533 prefixEnd_1090533 := by exact prefixLift 1090533
  have htrace : WordTrace (prefixWord ++ tailWord_1090533) baseStart_1090533 baseEnd_1090533 := by
    simpa [prefixWord, tailWord_1090533, baseEnd_1090533] using wordTrace_append hprefix tailTrace_1090533
  have hstable : (prefixWord ++ tailWord_1090533).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1090533).length < 2 ^ (prefixWord ++ tailWord_1090533).sum := by decide
  have hdescent : baseEnd_1090533 < baseStart_1090533 := by decide
  rcases family_descends (prefixWord ++ tailWord_1090533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1090585 : List Nat := [1, 2, 1, 2, 1, 1, 4, 2, 8]
def baseStart_1090585 : Nat := 118140960795 + 1090585 * 2 ^ 59
def prefixEnd_1090585 : Nat := 4983230072969 + 3 ^ 40 * 1090585 * 2
def baseEnd_1090585 : Nat := 124443177685271292193777

theorem tailTrace_1090585 : CollatzResearch.WordTrace tailWord_1090585 prefixEnd_1090585 124443177685271292193777 := by
  unfold tailWord_1090585
  simp only [CollatzResearch.WordTrace]
  refine ⟨39776902754004276934425209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26517935169336184622950139 39776902754004276934425209)
  ·
    refine ⟨29832677065503207700818907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39776902754004276934425209 29832677065503207700818907)
    ·
      refine ⟨44749015598254811551228361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29832677065503207700818907 44749015598254811551228361)
      ·
        refine ⟨33561761698691108663421271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44749015598254811551228361 33561761698691108663421271)
        ·
          refine ⟨50342642548036662995131907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33561761698691108663421271 50342642548036662995131907)
          ·
            refine ⟨75513963822054994492697861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50342642548036662995131907 75513963822054994492697861)
            ·
              refine ⟨14158868216635311467380849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 75513963822054994492697861 14158868216635311467380849)
              ·
                refine ⟨10619151162476483600535637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14158868216635311467380849 10619151162476483600535637)
                ·
                  refine ⟨124443177685271292193777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 10619151162476483600535637 124443177685271292193777)
                  ·
                    rfl

theorem cell22_1090585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 2, 8].length) (baseStart_1090585 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1090585 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1090585 prefixEnd_1090585 := by exact prefixLift 1090585
  have htrace : WordTrace (prefixWord ++ tailWord_1090585) baseStart_1090585 baseEnd_1090585 := by
    simpa [prefixWord, tailWord_1090585, baseEnd_1090585] using wordTrace_append hprefix tailTrace_1090585
  have hstable : (prefixWord ++ tailWord_1090585).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1090585).length < 2 ^ (prefixWord ++ tailWord_1090585).sum := by decide
  have hdescent : baseEnd_1090585 < baseStart_1090585 := by decide
  rcases family_descends (prefixWord ++ tailWord_1090585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1090621 : List Nat := [1, 4, 1, 3, 1, 4, 1, 2, 1, 4]
def baseStart_1090621 : Nat := 118140960795 + 1090621 * 2 ^ 59
def prefixEnd_1090621 : Nat := 4983230072969 + 3 ^ 40 * 1090621 * 2
def baseEnd_1090621 : Nat := 373341856591521782681221

theorem tailTrace_1090621 : CollatzResearch.WordTrace tailWord_1090621 prefixEnd_1090621 373341856591521782681221 := by
  unfold tailWord_1090621
  simp only [CollatzResearch.WordTrace]
  refine ⟨39778215781873855082735717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26518810521249236721823811 39778215781873855082735717)
  ·
    refine ⟨7458415459101347828012947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 39778215781873855082735717 7458415459101347828012947)
    ·
      refine ⟨11187623188652021742019421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7458415459101347828012947 11187623188652021742019421)
      ·
        refine ⟨4195358695744508153257283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11187623188652021742019421 4195358695744508153257283)
        ·
          refine ⟨6293038043616762229885925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4195358695744508153257283 6293038043616762229885925)
          ·
            refine ⟨1179944633178142918103611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6293038043616762229885925 1179944633178142918103611)
            ·
              refine ⟨1769916949767214377155417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1179944633178142918103611 1769916949767214377155417)
              ·
                refine ⟨1327437712325410782866563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1769916949767214377155417 1327437712325410782866563)
                ·
                  refine ⟨1991156568488116174299845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1327437712325410782866563 1991156568488116174299845)
                  ·
                    refine ⟨373341856591521782681221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1991156568488116174299845 373341856591521782681221)
                    ·
                      rfl

theorem cell22_1090621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 4, 1, 2, 1, 4].length) (baseStart_1090621 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1090621 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1090621 prefixEnd_1090621 := by exact prefixLift 1090621
  have htrace : WordTrace (prefixWord ++ tailWord_1090621) baseStart_1090621 baseEnd_1090621 := by
    simpa [prefixWord, tailWord_1090621, baseEnd_1090621] using wordTrace_append hprefix tailTrace_1090621
  have hstable : (prefixWord ++ tailWord_1090621).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1090621).length < 2 ^ (prefixWord ++ tailWord_1090621).sum := by decide
  have hdescent : baseEnd_1090621 < baseStart_1090621 := by decide
  rcases family_descends (prefixWord ++ tailWord_1090621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1090653 : List Nat := [1, 4, 4, 1, 2, 1, 1, 4, 4]
def baseStart_1090653 : Nat := 118140960795 + 1090653 * 2 ^ 59
def prefixEnd_1090653 : Nat := 4983230072969 + 3 ^ 40 * 1090653 * 2
def baseEnd_1090653 : Nat := 124450936948494788627041

theorem tailTrace_1090653 : CollatzResearch.WordTrace tailWord_1090653 prefixEnd_1090653 124450936948494788627041 := by
  unfold tailWord_1090653
  simp only [CollatzResearch.WordTrace]
  refine ⟨39779382917757924547900613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26519588611838616365267075 39779382917757924547900613)
  ·
    refine ⟨7458634297079610852731365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 39779382917757924547900613 7458634297079610852731365)
    ·
      refine ⟨1398493930702427034887131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7458634297079610852731365 1398493930702427034887131)
      ·
        refine ⟨2097740896053640552330697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1398493930702427034887131 2097740896053640552330697)
        ·
          refine ⟨1573305672040230414248023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2097740896053640552330697 1573305672040230414248023)
          ·
            refine ⟨2359958508060345621372035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1573305672040230414248023 2359958508060345621372035)
            ·
              refine ⟨3539937762090518432058053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2359958508060345621372035 3539937762090518432058053)
              ·
                refine ⟨663738330391972206010885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3539937762090518432058053 663738330391972206010885)
                ·
                  refine ⟨124450936948494788627041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 663738330391972206010885 124450936948494788627041)
                  ·
                    rfl

theorem cell22_1090653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 1, 4, 4].length) (baseStart_1090653 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1090653 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1090653 prefixEnd_1090653 := by exact prefixLift 1090653
  have htrace : WordTrace (prefixWord ++ tailWord_1090653) baseStart_1090653 baseEnd_1090653 := by
    simpa [prefixWord, tailWord_1090653, baseEnd_1090653] using wordTrace_append hprefix tailTrace_1090653
  have hstable : (prefixWord ++ tailWord_1090653).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1090653).length < 2 ^ (prefixWord ++ tailWord_1090653).sum := by decide
  have hdescent : baseEnd_1090653 < baseStart_1090653 := by decide
  rcases family_descends (prefixWord ++ tailWord_1090653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1090679 : List Nat := [1, 1, 3, 1, 1, 4, 3, 2, 3, 3]
def baseStart_1090679 : Nat := 118140960795 + 1090679 * 2 ^ 59
def prefixEnd_1090679 : Nat := 4983230072969 + 3 ^ 40 * 1090679 * 2
def baseEnd_1090679 : Nat := 373361711176828964731043

theorem tailTrace_1090679 : CollatzResearch.WordTrace tailWord_1090679 prefixEnd_1090679 373361711176828964731043 := by
  unfold tailWord_1090679
  simp only [CollatzResearch.WordTrace]
  refine ⟨39780331215663730988347091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26520220810442487325564727 39780331215663730988347091)
  ·
    refine ⟨59670496823495596482520637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39780331215663730988347091 59670496823495596482520637)
    ·
      refine ⟨22376436308810848680945239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59670496823495596482520637 22376436308810848680945239)
      ·
        refine ⟨33564654463216273021417859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22376436308810848680945239 33564654463216273021417859)
        ·
          refine ⟨50346981694824409532126789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33564654463216273021417859 50346981694824409532126789)
          ·
            refine ⟨9440059067779576787273773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 50346981694824409532126789 9440059067779576787273773)
            ·
              refine ⟨3540022150417341295227665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9440059067779576787273773 3540022150417341295227665)
              ·
                refine ⟨2655016612813005971420749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3540022150417341295227665 2655016612813005971420749)
                ·
                  refine ⟨995631229804877239282781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2655016612813005971420749 995631229804877239282781)
                  ·
                    refine ⟨373361711176828964731043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 995631229804877239282781 373361711176828964731043)
                    ·
                      rfl

theorem cell22_1090679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 3, 2, 3, 3].length) (baseStart_1090679 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1090679 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1090679 prefixEnd_1090679 := by exact prefixLift 1090679
  have htrace : WordTrace (prefixWord ++ tailWord_1090679) baseStart_1090679 baseEnd_1090679 := by
    simpa [prefixWord, tailWord_1090679, baseEnd_1090679] using wordTrace_append hprefix tailTrace_1090679
  have hstable : (prefixWord ++ tailWord_1090679).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1090679).length < 2 ^ (prefixWord ++ tailWord_1090679).sum := by decide
  have hdescent : baseEnd_1090679 < baseStart_1090679 := by decide
  rcases family_descends (prefixWord ++ tailWord_1090679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1090707 : List Nat := [1, 1, 1, 2, 1, 2, 5, 2, 2, 5]
def baseStart_1090707 : Nat := 118140960795 + 1090707 * 2 ^ 59
def prefixEnd_1090707 : Nat := 4983230072969 + 3 ^ 40 * 1090707 * 2
def baseEnd_1090707 : Nat := 373371296149046225030957

theorem tailTrace_1090707 : CollatzResearch.WordTrace tailWord_1090707 prefixEnd_1090707 373371296149046225030957 := by
  unfold tailWord_1090707
  simp only [CollatzResearch.WordTrace]
  refine ⟨39781352459562291770366375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26520901639708194513577583 39781352459562291770366375)
  ·
    refine ⟨59672028689343437655549563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39781352459562291770366375 59672028689343437655549563)
    ·
      refine ⟨89508043034015156483324345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59672028689343437655549563 89508043034015156483324345)
      ·
        refine ⟨67131032275511367362493259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 89508043034015156483324345 67131032275511367362493259)
        ·
          refine ⟨100696548413267051043739889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67131032275511367362493259 100696548413267051043739889)
          ·
            refine ⟨75522411309950288282804917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 100696548413267051043739889 75522411309950288282804917)
            ·
              refine ⟨7080226060307839526512961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 75522411309950288282804917 7080226060307839526512961)
              ·
                refine ⟨5310169545230879644884721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7080226060307839526512961 5310169545230879644884721)
                ·
                  refine ⟨3982627158923159733663541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5310169545230879644884721 3982627158923159733663541)
                  ·
                    refine ⟨373371296149046225030957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3982627158923159733663541 373371296149046225030957)
                    ·
                      rfl

theorem cell22_1090707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 5, 2, 2, 5].length) (baseStart_1090707 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1090707 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1090707 prefixEnd_1090707 := by exact prefixLift 1090707
  have htrace : WordTrace (prefixWord ++ tailWord_1090707) baseStart_1090707 baseEnd_1090707 := by
    simpa [prefixWord, tailWord_1090707, baseEnd_1090707] using wordTrace_append hprefix tailTrace_1090707
  have hstable : (prefixWord ++ tailWord_1090707).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1090707).length < 2 ^ (prefixWord ++ tailWord_1090707).sum := by decide
  have hdescent : baseEnd_1090707 < baseStart_1090707 := by decide
  rcases family_descends (prefixWord ++ tailWord_1090707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1090724 : List Nat := [2, 3, 1, 2, 3, 1, 2, 1, 2, 5]
def baseStart_1090724 : Nat := 118140960795 + 1090724 * 2 ^ 59
def prefixEnd_1090724 : Nat := 4983230072969 + 3 ^ 40 * 1090724 * 2
def baseEnd_1090724 : Nat := 373377115596463847355905

theorem tailTrace_1090724 : CollatzResearch.WordTrace tailWord_1090724 prefixEnd_1090724 373377115596463847355905 := by
  unfold tailWord_1090724
  simp only [CollatzResearch.WordTrace]
  refine ⟨19890986250250351836867613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26521315000333802449156817 19890986250250351836867613)
  ·
    refine ⟨7459119843843881938825355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19890986250250351836867613 7459119843843881938825355)
    ·
      refine ⟨11188679765765822908238033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7459119843843881938825355 11188679765765822908238033)
      ·
        refine ⟨8391509824324367181178525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11188679765765822908238033 8391509824324367181178525)
        ·
          refine ⟨3146816184121637692941947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8391509824324367181178525 3146816184121637692941947)
          ·
            refine ⟨4720224276182456539412921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3146816184121637692941947 4720224276182456539412921)
            ·
              refine ⟨3540168207136842404559691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4720224276182456539412921 3540168207136842404559691)
              ·
                refine ⟨5310252310705263606839537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3540168207136842404559691 5310252310705263606839537)
                ·
                  refine ⟨3982689233028947705129653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5310252310705263606839537 3982689233028947705129653)
                  ·
                    refine ⟨373377115596463847355905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3982689233028947705129653 373377115596463847355905)
                    ·
                      rfl

theorem cell22_1090724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 2, 1, 2, 5].length) (baseStart_1090724 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1090724 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1090724 prefixEnd_1090724 := by exact prefixLift 1090724
  have htrace : WordTrace (prefixWord ++ tailWord_1090724) baseStart_1090724 baseEnd_1090724 := by
    simpa [prefixWord, tailWord_1090724, baseEnd_1090724] using wordTrace_append hprefix tailTrace_1090724
  have hstable : (prefixWord ++ tailWord_1090724).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1090724).length < 2 ^ (prefixWord ++ tailWord_1090724).sum := by decide
  have hdescent : baseEnd_1090724 < baseStart_1090724 := by decide
  rcases family_descends (prefixWord ++ tailWord_1090724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1090739 : List Nat := [1, 1, 1, 2, 3, 2, 3, 4, 1, 4]
def baseStart_1090739 : Nat := 118140960795 + 1090739 * 2 ^ 59
def prefixEnd_1090739 : Nat := 4983230072969 + 3 ^ 40 * 1090739 * 2
def baseEnd_1090739 : Nat := 373382250403008808230859

theorem tailTrace_1090739 : CollatzResearch.WordTrace tailWord_1090739 prefixEnd_1090739 373382250403008808230859 := by
  unfold tailWord_1090739
  simp only [CollatzResearch.WordTrace]
  refine ⟨39782519595446361235531271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26521679730297574157020847 39782519595446361235531271)
  ·
    refine ⟨59673779393169541853296907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39782519595446361235531271 59673779393169541853296907)
    ·
      refine ⟨89510669089754312779945361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59673779393169541853296907 89510669089754312779945361)
      ·
        refine ⟨67133001817315734584959021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 89510669089754312779945361 67133001817315734584959021)
        ·
          refine ⟨25174875681493400469359633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 67133001817315734584959021 25174875681493400469359633)
          ·
            refine ⟨18881156761120050352019725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25174875681493400469359633 18881156761120050352019725)
            ·
              refine ⟨7080433785420018882007397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18881156761120050352019725 7080433785420018882007397)
              ·
                refine ⟨1327581334766253540376387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7080433785420018882007397 1327581334766253540376387)
                ·
                  refine ⟨1991372002149380310564581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1327581334766253540376387 1991372002149380310564581)
                  ·
                    refine ⟨373382250403008808230859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1991372002149380310564581 373382250403008808230859)
                    ·
                      rfl

theorem cell22_1090739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 3, 4, 1, 4].length) (baseStart_1090739 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1090739 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1090739 prefixEnd_1090739 := by exact prefixLift 1090739
  have htrace : WordTrace (prefixWord ++ tailWord_1090739) baseStart_1090739 baseEnd_1090739 := by
    simpa [prefixWord, tailWord_1090739, baseEnd_1090739] using wordTrace_append hprefix tailTrace_1090739
  have hstable : (prefixWord ++ tailWord_1090739).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1090739).length < 2 ^ (prefixWord ++ tailWord_1090739).sum := by decide
  have hdescent : baseEnd_1090739 < baseStart_1090739 := by decide
  rcases family_descends (prefixWord ++ tailWord_1090739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1090767 : List Nat := [1, 1, 2, 1, 1, 3, 2, 2, 3, 6]
def baseStart_1090767 : Nat := 118140960795 + 1090767 * 2 ^ 59
def prefixEnd_1090767 : Nat := 4983230072969 + 3 ^ 40 * 1090767 * 2
def baseEnd_1090767 : Nat := 373391835375226068530773

theorem tailTrace_1090767 : CollatzResearch.WordTrace tailWord_1090767 prefixEnd_1090767 373391835375226068530773 := by
  unfold tailWord_1090767
  simp only [CollatzResearch.WordTrace]
  refine ⟨39783540839344922017550555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26522360559563281345033703 39783540839344922017550555)
  ·
    refine ⟨59675311259017383026325833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39783540839344922017550555 59675311259017383026325833)
    ·
      refine ⟨44756483444263037269744375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59675311259017383026325833 44756483444263037269744375)
      ·
        refine ⟨67134725166394555904616563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44756483444263037269744375 67134725166394555904616563)
        ·
          refine ⟨100702087749591833856924845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67134725166394555904616563 100702087749591833856924845)
          ·
            refine ⟨37763282906096937696346817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 100702087749591833856924845 37763282906096937696346817)
            ·
              refine ⟨28322462179572703272260113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37763282906096937696346817 28322462179572703272260113)
              ·
                refine ⟨21241846634679527454195085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28322462179572703272260113 21241846634679527454195085)
                ·
                  refine ⟨7965692488004822795323157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21241846634679527454195085 7965692488004822795323157)
                  ·
                    refine ⟨373391835375226068530773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7965692488004822795323157 373391835375226068530773)
                    ·
                      rfl

theorem cell22_1090767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 2, 3, 6].length) (baseStart_1090767 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1090767 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1090767 prefixEnd_1090767 := by exact prefixLift 1090767
  have htrace : WordTrace (prefixWord ++ tailWord_1090767) baseStart_1090767 baseEnd_1090767 := by
    simpa [prefixWord, tailWord_1090767, baseEnd_1090767] using wordTrace_append hprefix tailTrace_1090767
  have hstable : (prefixWord ++ tailWord_1090767).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1090767).length < 2 ^ (prefixWord ++ tailWord_1090767).sum := by decide
  have hdescent : baseEnd_1090767 < baseStart_1090767 := by decide
  rcases family_descends (prefixWord ++ tailWord_1090767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1090848 : List Nat := [2, 1, 1, 5, 3, 1, 1, 2, 3, 3]
def baseStart_1090848 : Nat := 118140960795 + 1090848 * 2 ^ 59
def prefixEnd_1090848 : Nat := 4983230072969 + 3 ^ 40 * 1090848 * 2
def baseEnd_1090848 : Nat := 373419563330568857255525

theorem tailTrace_1090848 : CollatzResearch.WordTrace tailWord_1090848 prefixEnd_1090848 373419563330568857255525 := by
  unfold tailWord_1090848
  simp only [CollatzResearch.WordTrace]
  refine ⟨19893247576025736425624599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26524330101367648567499465 19893247576025736425624599)
  ·
    refine ⟨29839871364038604638436899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19893247576025736425624599 29839871364038604638436899)
    ·
      refine ⟨44759807046057906957655349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29839871364038604638436899 44759807046057906957655349)
      ·
        refine ⟨4196231910567928777280189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 44759807046057906957655349 4196231910567928777280189)
        ·
          refine ⟨1573586966462973291480071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4196231910567928777280189 1573586966462973291480071)
          ·
            refine ⟨2360380449694459937220107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1573586966462973291480071 2360380449694459937220107)
            ·
              refine ⟨3540570674541689905830161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2360380449694459937220107 3540570674541689905830161)
              ·
                refine ⟨2655428005906267429372621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3540570674541689905830161 2655428005906267429372621)
                ·
                  refine ⟨995785502214850286014733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2655428005906267429372621 995785502214850286014733)
                  ·
                    refine ⟨373419563330568857255525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 995785502214850286014733 373419563330568857255525)
                    ·
                      rfl

theorem cell22_1090848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 1, 2, 3, 3].length) (baseStart_1090848 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1090848 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1090848 prefixEnd_1090848 := by exact prefixLift 1090848
  have htrace : WordTrace (prefixWord ++ tailWord_1090848) baseStart_1090848 baseEnd_1090848 := by
    simpa [prefixWord, tailWord_1090848, baseEnd_1090848] using wordTrace_append hprefix tailTrace_1090848
  have hstable : (prefixWord ++ tailWord_1090848).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1090848).length < 2 ^ (prefixWord ++ tailWord_1090848).sum := by decide
  have hdescent : baseEnd_1090848 < baseStart_1090848 := by decide
  rcases family_descends (prefixWord ++ tailWord_1090848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1090865 : List Nat := [1, 2, 2, 3, 3, 2, 2, 3, 1, 3]
def baseStart_1090865 : Nat := 118140960795 + 1090865 * 2 ^ 59
def prefixEnd_1090865 : Nat := 4983230072969 + 3 ^ 40 * 1090865 * 2
def baseEnd_1090865 : Nat := 373425382777986479580473

theorem tailTrace_1090865 : CollatzResearch.WordTrace tailWord_1090865 prefixEnd_1090865 373425382777986479580473 := by
  unfold tailWord_1090865
  simp only [CollatzResearch.WordTrace]
  refine ⟨39787115192989884754618049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26524743461993256503078699 39787115192989884754618049)
  ·
    refine ⟨29840336394742413565963537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39787115192989884754618049 29840336394742413565963537)
    ·
      refine ⟨22380252296056810174472653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29840336394742413565963537 22380252296056810174472653)
      ·
        refine ⟨8392594611021303815427245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22380252296056810174472653 8392594611021303815427245)
        ·
          refine ⟨3147222979132988930785217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8392594611021303815427245 3147222979132988930785217)
          ·
            refine ⟨2360417234349741698088913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3147222979132988930785217 2360417234349741698088913)
            ·
              refine ⟨1770312925762306273566685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2360417234349741698088913 1770312925762306273566685)
              ·
                refine ⟨663867347160864852587507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1770312925762306273566685 663867347160864852587507)
                ·
                  refine ⟨995801020741297278881261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 663867347160864852587507 995801020741297278881261)
                  ·
                    refine ⟨373425382777986479580473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 995801020741297278881261 373425382777986479580473)
                    ·
                      rfl

theorem cell22_1090865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 2, 3, 1, 3].length) (baseStart_1090865 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1090865 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1090865 prefixEnd_1090865 := by exact prefixLift 1090865
  have htrace : WordTrace (prefixWord ++ tailWord_1090865) baseStart_1090865 baseEnd_1090865 := by
    simpa [prefixWord, tailWord_1090865, baseEnd_1090865] using wordTrace_append hprefix tailTrace_1090865
  have hstable : (prefixWord ++ tailWord_1090865).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1090865).length < 2 ^ (prefixWord ++ tailWord_1090865).sum := by decide
  have hdescent : baseEnd_1090865 < baseStart_1090865 := by decide
  rcases family_descends (prefixWord ++ tailWord_1090865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1090889 : List Nat := [1, 2, 1, 1, 2, 3, 3, 3, 6]
def baseStart_1090889 : Nat := 118140960795 + 1090889 * 2 ^ 59
def prefixEnd_1090889 : Nat := 4983230072969 + 3 ^ 40 * 1090889 * 2
def baseEnd_1090889 : Nat := 124477866156152805660133

theorem tailTrace_1090889 : CollatzResearch.WordTrace tailWord_1090889 prefixEnd_1090889 124477866156152805660133 := by
  unfold tailWord_1090889
  simp only [CollatzResearch.WordTrace]
  refine ⟨39787990544902936853491721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26525327029935291235661147 39787990544902936853491721)
  ·
    refine ⟨29840992908677202640118791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39787990544902936853491721 29840992908677202640118791)
    ·
      refine ⟨44761489363015803960178187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29840992908677202640118791 44761489363015803960178187)
      ·
        refine ⟨67142234044523705940267281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44761489363015803960178187 67142234044523705940267281)
        ·
          refine ⟨50356675533392779455200461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67142234044523705940267281 50356675533392779455200461)
          ·
            refine ⟨18883753325022292295700173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50356675533392779455200461 18883753325022292295700173)
            ·
              refine ⟨7081407496883359610887565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18883753325022292295700173 7081407496883359610887565)
              ·
                refine ⟨2655527811331259854082837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7081407496883359610887565 2655527811331259854082837)
                ·
                  refine ⟨124477866156152805660133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2655527811331259854082837 124477866156152805660133)
                  ·
                    rfl

theorem cell22_1090889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 3, 3, 6].length) (baseStart_1090889 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1090889 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1090889 prefixEnd_1090889 := by exact prefixLift 1090889
  have htrace : WordTrace (prefixWord ++ tailWord_1090889) baseStart_1090889 baseEnd_1090889 := by
    simpa [prefixWord, tailWord_1090889, baseEnd_1090889] using wordTrace_append hprefix tailTrace_1090889
  have hstable : (prefixWord ++ tailWord_1090889).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1090889).length < 2 ^ (prefixWord ++ tailWord_1090889).sum := by decide
  have hdescent : baseEnd_1090889 < baseStart_1090889 := by decide
  rcases family_descends (prefixWord ++ tailWord_1090889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1090951 : List Nat := [1, 1, 4, 2, 2, 3, 2, 7]
def baseStart_1090951 : Nat := 118140960795 + 1090951 * 2 ^ 59
def prefixEnd_1090951 : Nat := 4983230072969 + 3 ^ 40 * 1090951 * 2
def baseEnd_1090951 : Nat := 41494980259501213547801

theorem tailTrace_1090951 : CollatzResearch.WordTrace tailWord_1090951 prefixEnd_1090951 41494980259501213547801 := by
  unfold tailWord_1090951
  simp only [CollatzResearch.WordTrace]
  refine ⟨39790251870678321442248707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26526834580452214294832471 39790251870678321442248707)
  ·
    refine ⟨59685377806017482163373061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39790251870678321442248707 59685377806017482163373061)
    ·
      refine ⟨11191008338628277905632449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 59685377806017482163373061 11191008338628277905632449)
      ·
        refine ⟨8393256253971208429224337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11191008338628277905632449 8393256253971208429224337)
        ·
          refine ⟨6294942190478406321918253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8393256253971208429224337 6294942190478406321918253)
          ·
            refine ⟨2360603321429402370719345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6294942190478406321918253 2360603321429402370719345)
            ·
              refine ⟨1770452491072051778039509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2360603321429402370719345 1770452491072051778039509)
              ·
                refine ⟨41494980259501213547801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1770452491072051778039509 41494980259501213547801)
                ·
                  rfl

theorem cell22_1090951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 2, 7].length) (baseStart_1090951 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1090951 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1090951 prefixEnd_1090951 := by exact prefixLift 1090951
  have htrace : WordTrace (prefixWord ++ tailWord_1090951) baseStart_1090951 baseEnd_1090951 := by
    simpa [prefixWord, tailWord_1090951, baseEnd_1090951] using wordTrace_append hprefix tailTrace_1090951
  have hstable : (prefixWord ++ tailWord_1090951).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1090951).length < 2 ^ (prefixWord ++ tailWord_1090951).sum := by decide
  have hdescent : baseEnd_1090951 < baseStart_1090951 := by decide
  rcases family_descends (prefixWord ++ tailWord_1090951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1091058 : List Nat := [3, 2, 1, 4, 1, 1, 1, 3, 6]
def baseStart_1091058 : Nat := 118140960795 + 1091058 * 2 ^ 59
def prefixEnd_1091058 : Nat := 4983230072969 + 3 ^ 40 * 1091058 * 2
def baseEnd_1091058 : Nat := 124497150207399436501627

theorem tailTrace_1091058 : CollatzResearch.WordTrace tailWord_1091058 prefixEnd_1091058 124497150207399436501627 := by
  unfold tailWord_1091058
  simp only [CollatzResearch.WordTrace]
  refine ⟨9948538620322669679098457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26529436320860452477595885 9948538620322669679098457)
  ·
    refine ⟨7461403965242002259323843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9948538620322669679098457 7461403965242002259323843)
    ·
      refine ⟨11192105947863003388985765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7461403965242002259323843 11192105947863003388985765)
      ·
        refine ⟨2098519865224313135434831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11192105947863003388985765 2098519865224313135434831)
        ·
          refine ⟨3147779797836469703152247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2098519865224313135434831 3147779797836469703152247)
          ·
            refine ⟨4721669696754704554728371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3147779797836469703152247 4721669696754704554728371)
            ·
              refine ⟨7082504545132056832092557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4721669696754704554728371 7082504545132056832092557)
              ·
                refine ⟨2655939204424521312034709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7082504545132056832092557 2655939204424521312034709)
                ·
                  refine ⟨124497150207399436501627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2655939204424521312034709 124497150207399436501627)
                  ·
                    rfl

theorem cell22_1091058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 1, 3, 6].length) (baseStart_1091058 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1091058 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1091058 prefixEnd_1091058 := by exact prefixLift 1091058
  have htrace : WordTrace (prefixWord ++ tailWord_1091058) baseStart_1091058 baseEnd_1091058 := by
    simpa [prefixWord, tailWord_1091058, baseEnd_1091058] using wordTrace_append hprefix tailTrace_1091058
  have hstable : (prefixWord ++ tailWord_1091058).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1091058).length < 2 ^ (prefixWord ++ tailWord_1091058).sum := by decide
  have hdescent : baseEnd_1091058 < baseStart_1091058 := by decide
  rcases family_descends (prefixWord ++ tailWord_1091058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1091071 : List Nat := [1, 1, 2, 2, 1, 2, 2, 1, 6, 4]
def baseStart_1091071 : Nat := 118140960795 + 1091071 * 2 ^ 59
def prefixEnd_1091071 : Nat := 4983230072969 + 3 ^ 40 * 1091071 * 2
def baseEnd_1091071 : Nat := 373495900787870608929841

theorem tailTrace_1091071 : CollatzResearch.WordTrace tailWord_1091071 prefixEnd_1091071 373495900787870608929841 := by
  unfold tailWord_1091071
  simp only [CollatzResearch.WordTrace]
  refine ⟨39794628630243581936617067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26529752420162387957744711 39794628630243581936617067)
  ·
    refine ⟨59691942945365372904925601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39794628630243581936617067 59691942945365372904925601)
    ·
      refine ⟨44768957209024029678694201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59691942945365372904925601 44768957209024029678694201)
      ·
        refine ⟨33576717906768022259020651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44768957209024029678694201 33576717906768022259020651)
        ·
          refine ⟨50365076860152033388530977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33576717906768022259020651 50365076860152033388530977)
          ·
            refine ⟨37773807645114025041398233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50365076860152033388530977 37773807645114025041398233)
            ·
              refine ⟨28330355733835518781048675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37773807645114025041398233 28330355733835518781048675)
              ·
                refine ⟨42495533600753278171573013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28330355733835518781048675 42495533600753278171573013)
                ·
                  refine ⟨1991978137535309914292485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 42495533600753278171573013 1991978137535309914292485)
                  ·
                    refine ⟨373495900787870608929841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1991978137535309914292485 373495900787870608929841)
                    ·
                      rfl

theorem cell22_1091071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 1, 6, 4].length) (baseStart_1091071 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1091071 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1091071 prefixEnd_1091071 := by exact prefixLift 1091071
  have htrace : WordTrace (prefixWord ++ tailWord_1091071) baseStart_1091071 baseEnd_1091071 := by
    simpa [prefixWord, tailWord_1091071, baseEnd_1091071] using wordTrace_append hprefix tailTrace_1091071
  have hstable : (prefixWord ++ tailWord_1091071).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1091071).length < 2 ^ (prefixWord ++ tailWord_1091071).sum := by decide
  have hdescent : baseEnd_1091071 < baseStart_1091071 := by decide
  rcases family_descends (prefixWord ++ tailWord_1091071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1091193 : List Nat := [1, 2, 1, 3, 3, 1, 3, 2, 6]
def baseStart_1091193 : Nat := 118140960795 + 1091193 * 2 ^ 59
def prefixEnd_1091193 : Nat := 4983230072969 + 3 ^ 40 * 1091193 * 2
def baseEnd_1091193 : Nat := 124512554627034319126489

theorem tailTrace_1091193 : CollatzResearch.WordTrace tailWord_1091193 prefixEnd_1091193 124512554627034319126489 := by
  unfold tailWord_1091193
  simp only [CollatzResearch.WordTrace]
  refine ⟨39799078335801596772558233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26532718890534397848372155 39799078335801596772558233)
  ·
    refine ⟨29849308751851197579418675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39799078335801596772558233 29849308751851197579418675)
    ·
      refine ⟨44773963127776796369128013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29849308751851197579418675 44773963127776796369128013)
      ·
        refine ⟨16790236172916298638423005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44773963127776796369128013 16790236172916298638423005)
        ·
          refine ⟨6296338564843611989408627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16790236172916298638423005 6296338564843611989408627)
          ·
            refine ⟨9444507847265417984112941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6296338564843611989408627 9444507847265417984112941)
            ·
              refine ⟨3541690442724531744042353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9444507847265417984112941 3541690442724531744042353)
              ·
                refine ⟨2656267832043398808031765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3541690442724531744042353 2656267832043398808031765)
                ·
                  refine ⟨124512554627034319126489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2656267832043398808031765 124512554627034319126489)
                  ·
                    rfl

theorem cell22_1091193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 3, 2, 6].length) (baseStart_1091193 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1091193 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1091193 prefixEnd_1091193 := by exact prefixLift 1091193
  have htrace : WordTrace (prefixWord ++ tailWord_1091193) baseStart_1091193 baseEnd_1091193 := by
    simpa [prefixWord, tailWord_1091193, baseEnd_1091193] using wordTrace_append hprefix tailTrace_1091193
  have hstable : (prefixWord ++ tailWord_1091193).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1091193).length < 2 ^ (prefixWord ++ tailWord_1091193).sum := by decide
  have hdescent : baseEnd_1091193 < baseStart_1091193 := by decide
  rcases family_descends (prefixWord ++ tailWord_1091193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1091225 : List Nat := [1, 2, 1, 2, 1, 2, 2, 6, 2, 3]
def baseStart_1091225 : Nat := 118140960795 + 1091225 * 2 ^ 59
def prefixEnd_1091225 : Nat := 4983230072969 + 3 ^ 40 * 1091225 * 2
def baseEnd_1091225 : Nat := 373548618135065540579369

theorem tailTrace_1091225 : CollatzResearch.WordTrace tailWord_1091225 prefixEnd_1091225 373548618135065540579369 := by
  unfold tailWord_1091225
  simp only [CollatzResearch.WordTrace]
  refine ⟨39800245471685666237723129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26533496981123777491815419 39800245471685666237723129)
  ·
    refine ⟨29850184103764249678292347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39800245471685666237723129 29850184103764249678292347)
    ·
      refine ⟨44775276155646374517438521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29850184103764249678292347 44775276155646374517438521)
      ·
        refine ⟨33581457116734780888078891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44775276155646374517438521 33581457116734780888078891)
        ·
          refine ⟨50372185675102171332118337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33581457116734780888078891 50372185675102171332118337)
          ·
            refine ⟨37779139256326628499088753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50372185675102171332118337 37779139256326628499088753)
            ·
              refine ⟨28334354442244971374316565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37779139256326628499088753 28334354442244971374316565)
              ·
                refine ⟨1328172864480233033171089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 28334354442244971374316565 1328172864480233033171089)
                ·
                  refine ⟨996129648360174774878317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1328172864480233033171089 996129648360174774878317)
                  ·
                    refine ⟨373548618135065540579369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 996129648360174774878317 373548618135065540579369)
                    ·
                      rfl

theorem cell22_1091225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 6, 2, 3].length) (baseStart_1091225 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1091225 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1091225 prefixEnd_1091225 := by exact prefixLift 1091225
  have htrace : WordTrace (prefixWord ++ tailWord_1091225) baseStart_1091225 baseEnd_1091225 := by
    simpa [prefixWord, tailWord_1091225, baseEnd_1091225] using wordTrace_append hprefix tailTrace_1091225
  have hstable : (prefixWord ++ tailWord_1091225).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1091225).length < 2 ^ (prefixWord ++ tailWord_1091225).sum := by decide
  have hdescent : baseEnd_1091225 < baseStart_1091225 := by decide
  rcases family_descends (prefixWord ++ tailWord_1091225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1091255 : List Nat := [1, 1, 3, 1, 5, 1, 4, 6]
def baseStart_1091255 : Nat := 118140960795 + 1091255 * 2 ^ 59
def prefixEnd_1091255 : Nat := 4983230072969 + 3 ^ 40 * 1091255 * 2
def baseEnd_1091255 : Nat := 41506543083128384703253

theorem tailTrace_1091255 : CollatzResearch.WordTrace tailWord_1091255 prefixEnd_1091255 41506543083128384703253 := by
  unfold tailWord_1091255
  simp only [CollatzResearch.WordTrace]
  refine ⟨39801339661576981361315219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26534226441051320907543479 39801339661576981361315219)
  ·
    refine ⟨59702009492365472041972829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39801339661576981361315219 59702009492365472041972829)
    ·
      refine ⟨22388253559637052015739811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59702009492365472041972829 22388253559637052015739811)
      ·
        refine ⟨33582380339455578023609717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22388253559637052015739811 33582380339455578023609717)
        ·
          refine ⟨3148348156823960439713411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 33582380339455578023609717 3148348156823960439713411)
          ·
            refine ⟨4722522235235940659570117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3148348156823960439713411 4722522235235940659570117)
            ·
              refine ⟨885472919106738873669397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4722522235235940659570117 885472919106738873669397)
              ·
                refine ⟨41506543083128384703253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 885472919106738873669397 41506543083128384703253)
                ·
                  rfl

theorem cell22_1091255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 4, 6].length) (baseStart_1091255 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1091255 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1091255 prefixEnd_1091255 := by exact prefixLift 1091255
  have htrace : WordTrace (prefixWord ++ tailWord_1091255) baseStart_1091255 baseEnd_1091255 := by
    simpa [prefixWord, tailWord_1091255, baseEnd_1091255] using wordTrace_append hprefix tailTrace_1091255
  have hstable : (prefixWord ++ tailWord_1091255).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1091255).length < 2 ^ (prefixWord ++ tailWord_1091255).sum := by decide
  have hdescent : baseEnd_1091255 < baseStart_1091255 := by decide
  rcases family_descends (prefixWord ++ tailWord_1091255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1091293 : List Nat := [1, 4, 3, 3, 1, 2, 2, 1, 2, 3]
def baseStart_1091293 : Nat := 118140960795 + 1091293 * 2 ^ 59
def prefixEnd_1091293 : Nat := 4983230072969 + 3 ^ 40 * 1091293 * 2
def baseEnd_1091293 : Nat := 373571895924736029879161

theorem tailTrace_1091293 : CollatzResearch.WordTrace tailWord_1091293 prefixEnd_1091293 373571895924736029879161 := by
  unfold tailWord_1091293
  simp only [CollatzResearch.WordTrace]
  refine ⟨39802725635439313851198533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26535150423626209234132355 39802725635439313851198533)
  ·
    refine ⟨7463011056644871347099725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 39802725635439313851198533 7463011056644871347099725)
    ·
      refine ⟨2798629146241826755162397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7463011056644871347099725 2798629146241826755162397)
      ·
        refine ⟨1049485929840685033185899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2798629146241826755162397 1049485929840685033185899)
        ·
          refine ⟨1574228894761027549778849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1049485929840685033185899 1574228894761027549778849)
          ·
            refine ⟨1180671671070770662334137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1574228894761027549778849 1180671671070770662334137)
            ·
              refine ⟨885503753303077996750603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1180671671070770662334137 885503753303077996750603)
              ·
                refine ⟨1328255629954616995125905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 885503753303077996750603 1328255629954616995125905)
                ·
                  refine ⟨996191722465962746344429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1328255629954616995125905 996191722465962746344429)
                  ·
                    refine ⟨373571895924736029879161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 996191722465962746344429 373571895924736029879161)
                    ·
                      rfl

theorem cell22_1091293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 2, 2, 1, 2, 3].length) (baseStart_1091293 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1091293 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1091293 prefixEnd_1091293 := by exact prefixLift 1091293
  have htrace : WordTrace (prefixWord ++ tailWord_1091293) baseStart_1091293 baseEnd_1091293 := by
    simpa [prefixWord, tailWord_1091293, baseEnd_1091293] using wordTrace_append hprefix tailTrace_1091293
  have hstable : (prefixWord ++ tailWord_1091293).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1091293).length < 2 ^ (prefixWord ++ tailWord_1091293).sum := by decide
  have hdescent : baseEnd_1091293 < baseStart_1091293 := by decide
  rcases family_descends (prefixWord ++ tailWord_1091293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1091300 : List Nat := [2, 3, 1, 1, 1, 3, 3, 3, 5]
def baseStart_1091300 : Nat := 118140960795 + 1091300 * 2 ^ 59
def prefixEnd_1091300 : Nat := 4983230072969 + 3 ^ 40 * 1091300 * 2
def baseEnd_1091300 : Nat := 124524764055930114984713

theorem tailTrace_1091300 : CollatzResearch.WordTrace tailWord_1091300 prefixEnd_1091300 124524764055930114984713 := by
  unfold tailWord_1091300
  simp only [CollatzResearch.WordTrace]
  refine ⟨19901490473206977023351677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26535320630942636031135569 19901490473206977023351677)
  ·
    refine ⟨7463058927452616383756879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19901490473206977023351677 7463058927452616383756879)
    ·
      refine ⟨11194588391178924575635319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7463058927452616383756879 11194588391178924575635319)
      ·
        refine ⟨16791882586768386863452979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11194588391178924575635319 16791882586768386863452979)
        ·
          refine ⟨25187823880152580295179469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16791882586768386863452979 25187823880152580295179469)
          ·
            refine ⟨9445433955057217610692301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25187823880152580295179469 9445433955057217610692301)
            ·
              refine ⟨3542037733146456604009613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9445433955057217610692301 3542037733146456604009613)
              ·
                refine ⟨1328264149929921226503605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3542037733146456604009613 1328264149929921226503605)
                ·
                  refine ⟨124524764055930114984713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1328264149929921226503605 124524764055930114984713)
                  ·
                    rfl

theorem cell22_1091300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 3, 3, 5].length) (baseStart_1091300 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1091300 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1091300 prefixEnd_1091300 := by exact prefixLift 1091300
  have htrace : WordTrace (prefixWord ++ tailWord_1091300) baseStart_1091300 baseEnd_1091300 := by
    simpa [prefixWord, tailWord_1091300, baseEnd_1091300] using wordTrace_append hprefix tailTrace_1091300
  have hstable : (prefixWord ++ tailWord_1091300).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1091300).length < 2 ^ (prefixWord ++ tailWord_1091300).sum := by decide
  have hdescent : baseEnd_1091300 < baseStart_1091300 := by decide
  rcases family_descends (prefixWord ++ tailWord_1091300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1091328 : List Nat := [2, 1, 1, 2, 1, 1, 2, 4, 8]
def baseStart_1091328 : Nat := 118140960795 + 1091328 * 2 ^ 59
def prefixEnd_1091328 : Nat := 4983230072969 + 3 ^ 40 * 1091328 * 2
def baseEnd_1091328 : Nat := 124527959046669201751351

theorem tailTrace_1091328 : CollatzResearch.WordTrace tailWord_1091328 prefixEnd_1091328 124527959046669201751351 := by
  unfold tailWord_1091328
  simp only [CollatzResearch.WordTrace]
  refine ⟨19902001095156257414361319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26536001460208343219148425 19902001095156257414361319)
  ·
    refine ⟨29853001642734386121541979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19902001095156257414361319 29853001642734386121541979)
    ·
      refine ⟨44779502464101579182312969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29853001642734386121541979 44779502464101579182312969)
      ·
        refine ⟨33584626848076184386734727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44779502464101579182312969 33584626848076184386734727)
        ·
          refine ⟨50376940272114276580102091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33584626848076184386734727 50376940272114276580102091)
          ·
            refine ⟨75565410408171414870153137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50376940272114276580102091 75565410408171414870153137)
            ·
              refine ⟨56674057806128561152614853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 75565410408171414870153137 56674057806128561152614853)
              ·
                refine ⟨10626385838649105216115285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 56674057806128561152614853 10626385838649105216115285)
                ·
                  refine ⟨124527959046669201751351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 10626385838649105216115285 124527959046669201751351)
                  ·
                    rfl

theorem cell22_1091328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 4, 8].length) (baseStart_1091328 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1091328 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1091328 prefixEnd_1091328 := by exact prefixLift 1091328
  have htrace : WordTrace (prefixWord ++ tailWord_1091328) baseStart_1091328 baseEnd_1091328 := by
    simpa [prefixWord, tailWord_1091328, baseEnd_1091328] using wordTrace_append hprefix tailTrace_1091328
  have hstable : (prefixWord ++ tailWord_1091328).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1091328).length < 2 ^ (prefixWord ++ tailWord_1091328).sum := by decide
  have hdescent : baseEnd_1091328 < baseStart_1091328 := by decide
  rcases family_descends (prefixWord ++ tailWord_1091328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1091379 : List Nat := [1, 1, 1, 2, 7, 1, 2, 3, 4]
def baseStart_1091379 : Nat := 118140960795 + 1091379 * 2 ^ 59
def prefixEnd_1091379 : Nat := 4983230072969 + 3 ^ 40 * 1091379 * 2
def baseEnd_1091379 : Nat := 124533778494086824076299

theorem tailTrace_1091379 : CollatzResearch.WordTrace tailWord_1091379 prefixEnd_1091379 124533778494086824076299 := by
  unfold tailWord_1091379
  simp only [CollatzResearch.WordTrace]
  refine ⟨39805862313127750538829191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26537241542085167025886127 39805862313127750538829191)
  ·
    refine ⟨59708793469691625808243787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39805862313127750538829191 59708793469691625808243787)
    ·
      refine ⟨89563190204537438712365681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59708793469691625808243787 89563190204537438712365681)
      ·
        refine ⟨67172392653403079034274261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 89563190204537438712365681 67172392653403079034274261)
        ·
          refine ⟨1574352952814134664865803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 67172392653403079034274261 1574352952814134664865803)
          ·
            refine ⟨2361529429221201997298705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1574352952814134664865803 2361529429221201997298705)
            ·
              refine ⟨1771147071915901497974029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2361529429221201997298705 1771147071915901497974029)
              ·
                refine ⟨664180151968463061740261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1771147071915901497974029 664180151968463061740261)
                ·
                  refine ⟨124533778494086824076299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 664180151968463061740261 124533778494086824076299)
                  ·
                    rfl

theorem cell22_1091379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 2, 3, 4].length) (baseStart_1091379 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1091379 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1091379 prefixEnd_1091379 := by exact prefixLift 1091379
  have htrace : WordTrace (prefixWord ++ tailWord_1091379) baseStart_1091379 baseEnd_1091379 := by
    simpa [prefixWord, tailWord_1091379, baseEnd_1091379] using wordTrace_append hprefix tailTrace_1091379
  have hstable : (prefixWord ++ tailWord_1091379).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1091379).length < 2 ^ (prefixWord ++ tailWord_1091379).sum := by decide
  have hdescent : baseEnd_1091379 < baseStart_1091379 := by decide
  rcases family_descends (prefixWord ++ tailWord_1091379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1091381 : List Nat := [1, 3, 3, 1, 4, 2, 2, 1, 1, 4]
def baseStart_1091381 : Nat := 118140960795 + 1091381 * 2 ^ 59
def prefixEnd_1091381 : Nat := 4983230072969 + 3 ^ 40 * 1091381 * 2
def baseEnd_1091381 : Nat := 373602020123133133678891

theorem tailTrace_1091381 : CollatzResearch.WordTrace tailWord_1091381 prefixEnd_1091381 373602020123133133678891 := by
  unfold tailWord_1091381
  simp only [CollatzResearch.WordTrace]
  refine ⟨39805935259120504880401997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26537290172747003253601331 39805935259120504880401997)
  ·
    refine ⟨14927225722170189330150749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39805935259120504880401997 14927225722170189330150749)
    ·
      refine ⟨5597709645813820998806531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14927225722170189330150749 5597709645813820998806531)
      ·
        refine ⟨8396564468720731498209797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5597709645813820998806531 8396564468720731498209797)
        ·
          refine ⟨1574355837885137155914337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8396564468720731498209797 1574355837885137155914337)
          ·
            refine ⟨1180766878413852866935753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1574355837885137155914337 1180766878413852866935753)
            ·
              refine ⟨885575158810389650201815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1180766878413852866935753 885575158810389650201815)
              ·
                refine ⟨1328362738215584475302723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 885575158810389650201815 1328362738215584475302723)
                ·
                  refine ⟨1992544107323376712954085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1328362738215584475302723 1992544107323376712954085)
                  ·
                    refine ⟨373602020123133133678891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1992544107323376712954085 373602020123133133678891)
                    ·
                      rfl

theorem cell22_1091381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 2, 2, 1, 1, 4].length) (baseStart_1091381 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1091381 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1091381 prefixEnd_1091381 := by exact prefixLift 1091381
  have htrace : WordTrace (prefixWord ++ tailWord_1091381) baseStart_1091381 baseEnd_1091381 := by
    simpa [prefixWord, tailWord_1091381, baseEnd_1091381] using wordTrace_append hprefix tailTrace_1091381
  have hstable : (prefixWord ++ tailWord_1091381).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1091381).length < 2 ^ (prefixWord ++ tailWord_1091381).sum := by decide
  have hdescent : baseEnd_1091381 < baseStart_1091381 := by decide
  rcases family_descends (prefixWord ++ tailWord_1091381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1091450 : List Nat := [3, 1, 1, 1, 1, 1, 4, 1, 4, 5]
def baseStart_1091450 : Nat := 118140960795 + 1091450 * 2 ^ 59
def prefixEnd_1091450 : Nat := 4983230072969 + 3 ^ 40 * 1091450 * 2
def baseEnd_1091450 : Nat := 373625640233239953703679

theorem tailTrace_1091450 : CollatzResearch.WordTrace tailWord_1091450 prefixEnd_1091450 373625640233239953703679 := by
  unfold tailWord_1091450
  simp only [CollatzResearch.WordTrace]
  refine ⟨9952112973967632416165951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26538967930580353109775869 9952112973967632416165951)
  ·
    refine ⟨14928169460951448624248927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9952112973967632416165951 14928169460951448624248927)
    ·
      refine ⟨22392254191427172936373391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14928169460951448624248927 22392254191427172936373391)
      ·
        refine ⟨33588381287140759404560087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22392254191427172936373391 33588381287140759404560087)
        ·
          refine ⟨50382571930711139106840131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33588381287140759404560087 50382571930711139106840131)
          ·
            refine ⟨75573857896066708660260197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50382571930711139106840131 75573857896066708660260197)
            ·
              refine ⟨14170098355512507873798787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 75573857896066708660260197 14170098355512507873798787)
              ·
                refine ⟨21255147533268761810698181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14170098355512507873798787 21255147533268761810698181)
                ·
                  refine ⟨3985340162487892839505909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21255147533268761810698181 3985340162487892839505909)
                  ·
                    refine ⟨373625640233239953703679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3985340162487892839505909 373625640233239953703679)
                    ·
                      rfl

theorem cell22_1091450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 1, 4, 5].length) (baseStart_1091450 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1091450 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1091450 prefixEnd_1091450 := by exact prefixLift 1091450
  have htrace : WordTrace (prefixWord ++ tailWord_1091450) baseStart_1091450 baseEnd_1091450 := by
    simpa [prefixWord, tailWord_1091450, baseEnd_1091450] using wordTrace_append hprefix tailTrace_1091450
  have hstable : (prefixWord ++ tailWord_1091450).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1091450).length < 2 ^ (prefixWord ++ tailWord_1091450).sum := by decide
  have hdescent : baseEnd_1091450 < baseStart_1091450 := by decide
  rcases family_descends (prefixWord ++ tailWord_1091450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1091456 : List Nat := [2, 1, 1, 2, 1, 2, 7, 2, 1, 3]
def baseStart_1091456 : Nat := 118140960795 + 1091456 * 2 ^ 59
def prefixEnd_1091456 : Nat := 4983230072969 + 3 ^ 40 * 1091456 * 2
def baseEnd_1091456 : Nat := 373627694155857938053661

theorem tailTrace_1091456 : CollatzResearch.WordTrace tailWord_1091456 prefixEnd_1091456 373627694155857938053661 := by
  unfold tailWord_1091456
  simp only [CollatzResearch.WordTrace]
  refine ⟨19904335366924396344691111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26539113822565861792921481 19904335366924396344691111)
  ·
    refine ⟨29856503050386594517036667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19904335366924396344691111 29856503050386594517036667)
    ·
      refine ⟨44784754575579891775555001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29856503050386594517036667 44784754575579891775555001)
      ·
        refine ⟨33588565931684918831666251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44784754575579891775555001 33588565931684918831666251)
        ·
          refine ⟨50382848897527378247499377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33588565931684918831666251 50382848897527378247499377)
          ·
            refine ⟨37787136673145533685624533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50382848897527378247499377 37787136673145533685624533)
            ·
              refine ⟨885636015776848445756825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 37787136673145533685624533 885636015776848445756825)
              ·
                refine ⟨664227011832636334317619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 885636015776848445756825 664227011832636334317619)
                ·
                  refine ⟨996340517748954501476429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 664227011832636334317619 996340517748954501476429)
                  ·
                    refine ⟨373627694155857938053661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 996340517748954501476429 373627694155857938053661)
                    ·
                      rfl

theorem cell22_1091456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 7, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 7, 2, 1, 3].length) (baseStart_1091456 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1091456 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1091456 prefixEnd_1091456 := by exact prefixLift 1091456
  have htrace : WordTrace (prefixWord ++ tailWord_1091456) baseStart_1091456 baseEnd_1091456 := by
    simpa [prefixWord, tailWord_1091456, baseEnd_1091456] using wordTrace_append hprefix tailTrace_1091456
  have hstable : (prefixWord ++ tailWord_1091456).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1091456).length < 2 ^ (prefixWord ++ tailWord_1091456).sum := by decide
  have hdescent : baseEnd_1091456 < baseStart_1091456 := by decide
  rcases family_descends (prefixWord ++ tailWord_1091456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
