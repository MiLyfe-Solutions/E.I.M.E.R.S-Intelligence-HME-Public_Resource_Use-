import V185TrunkScan23Chunk0900

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_5332273 : List Nat := [1, 2, 2, 3, 3, 1, 2, 2, 2, 3, 2]
def baseStart_5332273 : Nat := 118140960795 + 5332273 * 2 ^ 59
def prefixEnd_5332273 : Nat := 4983230072969 + 3 ^ 40 * 5332273 * 2
def baseEnd_5332273 : Nat := 2738019029991921191064829

theorem tailTrace_5332273 : CollatzResearch.WordTrace tailWord_5332273 prefixEnd_5332273 2738019029991921191064829 := by
  unfold tailWord_5332273
  simp only [CollatzResearch.WordTrace]
  refine ⟨194483973811093075570593473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129655982540728717047062315 194483973811093075570593473)
  ·
    refine ⟨145862980358319806677945105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 194483973811093075570593473 145862980358319806677945105)
    ·
      refine ⟨109397235268739855008458829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 145862980358319806677945105 109397235268739855008458829)
      ·
        refine ⟨41023963225777445628172061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 109397235268739855008458829 41023963225777445628172061)
        ·
          refine ⟨15383986209666542110564523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41023963225777445628172061 15383986209666542110564523)
          ·
            refine ⟨23075979314499813165846785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15383986209666542110564523 23075979314499813165846785)
            ·
              refine ⟨17306984485874859874385089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23075979314499813165846785 17306984485874859874385089)
              ·
                refine ⟨12980238364406144905788817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17306984485874859874385089 12980238364406144905788817)
                ·
                  refine ⟨9735178773304608679341613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12980238364406144905788817 9735178773304608679341613)
                  ·
                    refine ⟨3650692039989228254753105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9735178773304608679341613 3650692039989228254753105)
                    ·
                      refine ⟨2738019029991921191064829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3650692039989228254753105 2738019029991921191064829)
                      ·
                        rfl

theorem cell23_5332273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 2, 2, 2, 3, 2].length) (baseStart_5332273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5332273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5332273 prefixEnd_5332273 := by exact prefixLift 5332273
  have htrace : WordTrace (prefixWord ++ tailWord_5332273) baseStart_5332273 baseEnd_5332273 := by
    simpa [prefixWord, tailWord_5332273, baseEnd_5332273] using wordTrace_append hprefix tailTrace_5332273
  have hstable : (prefixWord ++ tailWord_5332273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5332273).length < 2 ^ (prefixWord ++ tailWord_5332273).sum := by decide
  have hdescent : baseEnd_5332273 < baseStart_5332273 := by decide
  rcases family_descends (prefixWord ++ tailWord_5332273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5332286 : List Nat := [4, 2, 1, 2, 1, 1, 1, 1, 5, 1, 4]
def baseStart_5332286 : Nat := 118140960795 + 5332286 * 2 ^ 59
def prefixEnd_5332286 : Nat := 4983230072969 + 3 ^ 40 * 5332286 * 2
def baseEnd_5332286 : Nat := 2738025705240429640202269

theorem tailTrace_5332286 : CollatzResearch.WordTrace tailWord_5332286 prefixEnd_5332286 2738025705240429640202269 := by
  unfold tailWord_5332286
  simp only [CollatzResearch.WordTrace]
  refine ⟨24310555995005747348852089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 129656298640030652527211141 24310555995005747348852089)
  ·
    refine ⟨18232916996254310511639067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24310555995005747348852089 18232916996254310511639067)
    ·
      refine ⟨27349375494381465767458601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18232916996254310511639067 27349375494381465767458601)
      ·
        refine ⟨20512031620786099325593951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27349375494381465767458601 20512031620786099325593951)
        ·
          refine ⟨30768047431179148988390927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20512031620786099325593951 30768047431179148988390927)
          ·
            refine ⟨46152071146768723482586391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30768047431179148988390927 46152071146768723482586391)
            ·
              refine ⟨69228106720153085223879587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46152071146768723482586391 69228106720153085223879587)
              ·
                refine ⟨103842160080229627835819381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 69228106720153085223879587 103842160080229627835819381)
                ·
                  refine ⟨9735202507521527609608067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 103842160080229627835819381 9735202507521527609608067)
                  ·
                    refine ⟨14602803761282291414412101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9735202507521527609608067 14602803761282291414412101)
                    ·
                      refine ⟨2738025705240429640202269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14602803761282291414412101 2738025705240429640202269)
                      ·
                        rfl

theorem cell23_5332286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 1, 5, 1, 4].length) (baseStart_5332286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5332286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5332286 prefixEnd_5332286 := by exact prefixLift 5332286
  have htrace : WordTrace (prefixWord ++ tailWord_5332286) baseStart_5332286 baseEnd_5332286 := by
    simpa [prefixWord, tailWord_5332286, baseEnd_5332286] using wordTrace_append hprefix tailTrace_5332286
  have hstable : (prefixWord ++ tailWord_5332286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5332286).length < 2 ^ (prefixWord ++ tailWord_5332286).sum := by decide
  have hdescent : baseEnd_5332286 < baseStart_5332286 := by decide
  rcases family_descends (prefixWord ++ tailWord_5332286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5332317 : List Nat := [1, 4, 5, 1, 1, 1, 1, 3, 1, 5]
def baseStart_5332317 : Nat := 118140960795 + 5332317 * 2 ^ 59
def prefixEnd_5332317 : Nat := 4983230072969 + 3 ^ 40 * 5332317 * 2
def baseEnd_5332317 : Nat := 912680541046906339638209

theorem tailTrace_5332317 : CollatzResearch.WordTrace tailWord_5332317 prefixEnd_5332317 912680541046906339638209 := by
  unfold tailWord_5332317
  simp only [CollatzResearch.WordTrace]
  refine ⟨194485578622933671085195205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129657052415289114056796803 194485578622933671085195205)
  ·
    refine ⟨36466045991800063328474101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 194485578622933671085195205 36466045991800063328474101)
    ·
      refine ⟨3418691811731255937044447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 36466045991800063328474101 3418691811731255937044447)
      ·
        refine ⟨5128037717596883905566671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3418691811731255937044447 5128037717596883905566671)
        ·
          refine ⟨7692056576395325858350007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5128037717596883905566671 7692056576395325858350007)
          ·
            refine ⟨11538084864592988787525011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7692056576395325858350007 11538084864592988787525011)
            ·
              refine ⟨17307127296889483181287517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11538084864592988787525011 17307127296889483181287517)
              ·
                refine ⟨6490172736333556192982819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17307127296889483181287517 6490172736333556192982819)
                ·
                  refine ⟨9735259104500334289474229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6490172736333556192982819 9735259104500334289474229)
                  ·
                    refine ⟨912680541046906339638209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9735259104500334289474229 912680541046906339638209)
                    ·
                      rfl

theorem cell23_5332317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 1, 3, 1, 5].length) (baseStart_5332317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5332317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5332317 prefixEnd_5332317 := by exact prefixLift 5332317
  have htrace : WordTrace (prefixWord ++ tailWord_5332317) baseStart_5332317 baseEnd_5332317 := by
    simpa [prefixWord, tailWord_5332317, baseEnd_5332317] using wordTrace_append hprefix tailTrace_5332317
  have hstable : (prefixWord ++ tailWord_5332317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5332317).length < 2 ^ (prefixWord ++ tailWord_5332317).sum := by decide
  have hdescent : baseEnd_5332317 < baseStart_5332317 := by decide
  rcases family_descends (prefixWord ++ tailWord_5332317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5332320 : List Nat := [2, 1, 1, 3, 4, 3, 2, 1, 1, 1, 4]
def baseStart_5332320 : Nat := 118140960795 + 5332320 * 2 ^ 59
def prefixEnd_5332320 : Nat := 4983230072969 + 3 ^ 40 * 5332320 * 2
def baseEnd_5332320 : Nat := 2738043163582682507177113

theorem tailTrace_5332320 : CollatzResearch.WordTrace tailWord_5332320 prefixEnd_5332320 2738043163582682507177113 := by
  unfold tailWord_5332320
  simp only [CollatzResearch.WordTrace]
  refine ⟨97242844020961401298777207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129657125361281868398369609 97242844020961401298777207)
  ·
    refine ⟨145864266031442101948165811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97242844020961401298777207 145864266031442101948165811)
    ·
      refine ⟨218796399047163152922248717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145864266031442101948165811 218796399047163152922248717)
      ·
        refine ⟨82048649642686182345843269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 218796399047163152922248717 82048649642686182345843269)
        ·
          refine ⟨15384121808003659189845613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 82048649642686182345843269 15384121808003659189845613)
          ·
            refine ⟨5769045678001372196192105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15384121808003659189845613 5769045678001372196192105)
            ·
              refine ⟨4326784258501029147144079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5769045678001372196192105 4326784258501029147144079)
              ·
                refine ⟨6490176387751543720716119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4326784258501029147144079 6490176387751543720716119)
                ·
                  refine ⟨9735264581627315581074179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6490176387751543720716119 9735264581627315581074179)
                  ·
                    refine ⟨14602896872440973371611269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9735264581627315581074179 14602896872440973371611269)
                    ·
                      refine ⟨2738043163582682507177113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14602896872440973371611269 2738043163582682507177113)
                      ·
                        rfl

theorem cell23_5332320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 3, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 3, 2, 1, 1, 1, 4].length) (baseStart_5332320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5332320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5332320 prefixEnd_5332320 := by exact prefixLift 5332320
  have htrace : WordTrace (prefixWord ++ tailWord_5332320) baseStart_5332320 baseEnd_5332320 := by
    simpa [prefixWord, tailWord_5332320, baseEnd_5332320] using wordTrace_append hprefix tailTrace_5332320
  have hstable : (prefixWord ++ tailWord_5332320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5332320).length < 2 ^ (prefixWord ++ tailWord_5332320).sum := by decide
  have hdescent : baseEnd_5332320 < baseStart_5332320 := by decide
  rcases family_descends (prefixWord ++ tailWord_5332320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5332323 : List Nat := [1, 1, 1, 5, 2, 3, 1, 3, 1, 2, 3]
def baseStart_5332323 : Nat := 118140960795 + 5332323 * 2 ^ 59
def prefixEnd_5332323 : Nat := 4983230072969 + 3 ^ 40 * 5332323 * 2
def baseEnd_5332323 : Nat := 2738044704024645995439599

theorem tailTrace_5332323 : CollatzResearch.WordTrace tailWord_5332323 prefixEnd_5332323 2738044704024645995439599 := by
  unfold tailWord_5332323
  simp only [CollatzResearch.WordTrace]
  refine ⟨194485797460911934109913623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129657198307274622739942415 194485797460911934109913623)
  ·
    refine ⟨291728696191367901164870435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194485797460911934109913623 291728696191367901164870435)
    ·
      refine ⟨437593044287051851747305653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 291728696191367901164870435 437593044287051851747305653)
      ·
        refine ⟨41024347901911111101309905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 437593044287051851747305653 41024347901911111101309905)
        ·
          refine ⟨30768260926433333325982429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41024347901911111101309905 30768260926433333325982429)
          ·
            refine ⟨11538097847412499997243411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30768260926433333325982429 11538097847412499997243411)
            ·
              refine ⟨17307146771118749995865117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11538097847412499997243411 17307146771118749995865117)
              ·
                refine ⟨6490180039169531248449419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17307146771118749995865117 6490180039169531248449419)
                ·
                  refine ⟨9735270058754296872674129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6490180039169531248449419 9735270058754296872674129)
                  ·
                    refine ⟨7301452544065722654505597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9735270058754296872674129 7301452544065722654505597)
                    ·
                      refine ⟨2738044704024645995439599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7301452544065722654505597 2738044704024645995439599)
                      ·
                        rfl

theorem cell23_5332323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 1, 3, 1, 2, 3].length) (baseStart_5332323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5332323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5332323 prefixEnd_5332323 := by exact prefixLift 5332323
  have htrace : WordTrace (prefixWord ++ tailWord_5332323) baseStart_5332323 baseEnd_5332323 := by
    simpa [prefixWord, tailWord_5332323, baseEnd_5332323] using wordTrace_append hprefix tailTrace_5332323
  have hstable : (prefixWord ++ tailWord_5332323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5332323).length < 2 ^ (prefixWord ++ tailWord_5332323).sum := by decide
  have hdescent : baseEnd_5332323 < baseStart_5332323 := by decide
  rcases family_descends (prefixWord ++ tailWord_5332323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5332350 : List Nat := [4, 2, 3, 2, 1, 1, 1, 1, 1, 1, 6]
def baseStart_5332350 : Nat := 118140960795 + 5332350 * 2 ^ 59
def prefixEnd_5332350 : Nat := 4983230072969 + 3 ^ 40 * 5332350 * 2
def baseEnd_5332350 : Nat := 2738058568002317389801975

theorem tailTrace_5332350 : CollatzResearch.WordTrace tailWord_5332350 prefixEnd_5332350 2738058568002317389801975 := by
  unfold tailWord_5332350
  simp only [CollatzResearch.WordTrace]
  refine ⟨24310847778976764715143313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 129657854821209411814097669 24310847778976764715143313)
  ·
    refine ⟨18233135834232573536357485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24310847778976764715143313 18233135834232573536357485)
    ·
      refine ⟨6837425937837215076134057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18233135834232573536357485 6837425937837215076134057)
      ·
        refine ⟨5128069453377911307100543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6837425937837215076134057 5128069453377911307100543)
        ·
          refine ⟨7692104180066866960650815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5128069453377911307100543 7692104180066866960650815)
          ·
            refine ⟨11538156270100300440976223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7692104180066866960650815 11538156270100300440976223)
            ·
              refine ⟨17307234405150450661464335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11538156270100300440976223 17307234405150450661464335)
              ·
                refine ⟨25960851607725675992196503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17307234405150450661464335 25960851607725675992196503)
                ·
                  refine ⟨38941277411588513988294755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25960851607725675992196503 38941277411588513988294755)
                  ·
                    refine ⟨58411916117382770982442133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 38941277411588513988294755 58411916117382770982442133)
                    ·
                      refine ⟨2738058568002317389801975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 58411916117382770982442133 2738058568002317389801975)
                      ·
                        rfl

theorem cell23_5332350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 1, 1, 1, 1, 6].length) (baseStart_5332350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5332350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5332350 prefixEnd_5332350 := by exact prefixLift 5332350
  have htrace : WordTrace (prefixWord ++ tailWord_5332350) baseStart_5332350 baseEnd_5332350 := by
    simpa [prefixWord, tailWord_5332350, baseEnd_5332350] using wordTrace_append hprefix tailTrace_5332350
  have hstable : (prefixWord ++ tailWord_5332350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5332350).length < 2 ^ (prefixWord ++ tailWord_5332350).sum := by decide
  have hdescent : baseEnd_5332350 < baseStart_5332350 := by decide
  rcases family_descends (prefixWord ++ tailWord_5332350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5332379 : List Nat := [1, 1, 1, 1, 1, 1, 2, 1, 8, 1, 5]
def baseStart_5332379 : Nat := 118140960795 + 5332379 * 2 ^ 59
def prefixEnd_5332379 : Nat := 4983230072969 + 3 ^ 40 * 5332379 * 2
def baseEnd_5332379 : Nat := 2738073458941297776339341

theorem tailTrace_5332379 : CollatzResearch.WordTrace tailWord_5332379 prefixEnd_5332379 2738073458941297776339341 := by
  unfold tailWord_5332379
  simp only [CollatzResearch.WordTrace]
  refine ⟨194487839948709055673952191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129658559965806037115968127 194487839948709055673952191)
  ·
    refine ⟨291731759923063583510928287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194487839948709055673952191 291731759923063583510928287)
    ·
      refine ⟨437597639884595375266392431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 291731759923063583510928287 437597639884595375266392431)
      ·
        refine ⟨656396459826893062899588647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 437597639884595375266392431 656396459826893062899588647)
        ·
          refine ⟨984594689740339594349382971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 656396459826893062899588647 984594689740339594349382971)
          ·
            refine ⟨1476892034610509391524074457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 984594689740339594349382971 1476892034610509391524074457)
            ·
              refine ⟨1107669025957882043643055843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1476892034610509391524074457 1107669025957882043643055843)
              ·
                refine ⟨1661503538936823065464583765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1107669025957882043643055843 1661503538936823065464583765)
                ·
                  refine ⟨19470744596915895298413091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 1661503538936823065464583765 19470744596915895298413091)
                  ·
                    refine ⟨29206116895373842947619637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19470744596915895298413091 29206116895373842947619637)
                    ·
                      refine ⟨2738073458941297776339341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29206116895373842947619637 2738073458941297776339341)
                      ·
                        rfl

theorem cell23_5332379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 8, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 8, 1, 5].length) (baseStart_5332379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5332379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5332379 prefixEnd_5332379 := by exact prefixLift 5332379
  have htrace : WordTrace (prefixWord ++ tailWord_5332379) baseStart_5332379 baseEnd_5332379 := by
    simpa [prefixWord, tailWord_5332379, baseEnd_5332379] using wordTrace_append hprefix tailTrace_5332379
  have hstable : (prefixWord ++ tailWord_5332379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5332379).length < 2 ^ (prefixWord ++ tailWord_5332379).sum := by decide
  have hdescent : baseEnd_5332379 < baseStart_5332379 := by decide
  rcases family_descends (prefixWord ++ tailWord_5332379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5332389 : List Nat := [1, 3, 1, 2, 1, 1, 2, 1, 2, 3, 6]
def baseStart_5332389 : Nat := 118140960795 + 5332389 * 2 ^ 59
def prefixEnd_5332389 : Nat := 4983230072969 + 3 ^ 40 * 5332389 * 2
def baseEnd_5332389 : Nat := 2738078593747842737214295

theorem tailTrace_5332389 : CollatzResearch.WordTrace tailWord_5332389 prefixEnd_5332389 2738078593747842737214295 := by
  unfold tailWord_5332389
  simp only [CollatzResearch.WordTrace]
  refine ⟨194488204678672827381816221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129658803119115218254544147 194488204678672827381816221)
  ·
    refine ⟨72933076754502310268181083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 194488204678672827381816221 72933076754502310268181083)
    ·
      refine ⟨109399615131753465402271625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72933076754502310268181083 109399615131753465402271625)
      ·
        refine ⟨82049711348815099051703719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 109399615131753465402271625 82049711348815099051703719)
        ·
          refine ⟨123074567023222648577555579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82049711348815099051703719 123074567023222648577555579)
          ·
            refine ⟨184611850534833972866333369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 123074567023222648577555579 184611850534833972866333369)
            ·
              refine ⟨138458887901125479649750027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 184611850534833972866333369 138458887901125479649750027)
              ·
                refine ⟨207688331851688219474625041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 138458887901125479649750027 207688331851688219474625041)
                ·
                  refine ⟨155766248888766164605968781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 207688331851688219474625041 155766248888766164605968781)
                  ·
                    refine ⟨58412343333287311727238293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 155766248888766164605968781 58412343333287311727238293)
                    ·
                      refine ⟨2738078593747842737214295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 58412343333287311727238293 2738078593747842737214295)
                      ·
                        rfl

theorem cell23_5332389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 1, 2, 3, 6].length) (baseStart_5332389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5332389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5332389 prefixEnd_5332389 := by exact prefixLift 5332389
  have htrace : WordTrace (prefixWord ++ tailWord_5332389) baseStart_5332389 baseEnd_5332389 := by
    simpa [prefixWord, tailWord_5332389, baseEnd_5332389] using wordTrace_append hprefix tailTrace_5332389
  have hstable : (prefixWord ++ tailWord_5332389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5332389).length < 2 ^ (prefixWord ++ tailWord_5332389).sum := by decide
  have hdescent : baseEnd_5332389 < baseStart_5332389 := by decide
  rcases family_descends (prefixWord ++ tailWord_5332389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5332456 : List Nat := [2, 1, 4, 1, 1, 2, 1, 3, 1, 2, 5]
def baseStart_5332456 : Nat := 118140960795 + 5332456 * 2 ^ 59
def prefixEnd_5332456 : Nat := 4983230072969 + 3 ^ 40 * 5332456 * 2
def baseEnd_5332456 : Nat := 2738112996951693975076487

theorem tailTrace_5332456 : CollatzResearch.WordTrace tailWord_5332456 prefixEnd_5332456 2738112996951693975076487 := by
  unfold tailWord_5332456
  simp only [CollatzResearch.WordTrace]
  refine ⟨97245324184715048912252611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129660432246286731883003481 97245324184715048912252611)
  ·
    refine ⟨145867986277072573368378917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97245324184715048912252611 145867986277072573368378917)
    ·
      refine ⟨27350247426951107506571047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 145867986277072573368378917 27350247426951107506571047)
      ·
        refine ⟨41025371140426661259856571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27350247426951107506571047 41025371140426661259856571)
        ·
          refine ⟨61538056710639991889784857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41025371140426661259856571 61538056710639991889784857)
          ·
            refine ⟨46153542532979993917338643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61538056710639991889784857 46153542532979993917338643)
            ·
              refine ⟨69230313799469990876007965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46153542532979993917338643 69230313799469990876007965)
              ·
                refine ⟨25961367674801246578502987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 69230313799469990876007965 25961367674801246578502987)
                ·
                  refine ⟨38942051512201869867754481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25961367674801246578502987 38942051512201869867754481)
                  ·
                    refine ⟨29206538634151402400815861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 38942051512201869867754481 29206538634151402400815861)
                    ·
                      refine ⟨2738112996951693975076487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29206538634151402400815861 2738112996951693975076487)
                      ·
                        rfl

theorem cell23_5332456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 3, 1, 2, 5].length) (baseStart_5332456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5332456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5332456 prefixEnd_5332456 := by exact prefixLift 5332456
  have htrace : WordTrace (prefixWord ++ tailWord_5332456) baseStart_5332456 baseEnd_5332456 := by
    simpa [prefixWord, tailWord_5332456, baseEnd_5332456] using wordTrace_append hprefix tailTrace_5332456
  have hstable : (prefixWord ++ tailWord_5332456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5332456).length < 2 ^ (prefixWord ++ tailWord_5332456).sum := by decide
  have hdescent : baseEnd_5332456 < baseStart_5332456 := by decide
  rcases family_descends (prefixWord ++ tailWord_5332456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5332560 : List Nat := [2, 1, 1, 1, 1, 3, 5, 2, 2, 3, 2]
def baseStart_5332560 : Nat := 118140960795 + 5332560 * 2 ^ 59
def prefixEnd_5332560 : Nat := 4983230072969 + 3 ^ 40 * 5332560 * 2
def baseEnd_5332560 : Nat := 2738166398939761568176009

theorem tailTrace_5332560 : CollatzResearch.WordTrace tailWord_5332560 prefixEnd_5332560 2738166398939761568176009 := by
  unfold tailWord_5332560
  simp only [CollatzResearch.WordTrace]
  refine ⟨97247220780526661793145567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129662961040702215724194089 97247220780526661793145567)
  ·
    refine ⟨145870831170789992689718351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97247220780526661793145567 145870831170789992689718351)
    ·
      refine ⟨218806246756184989034577527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145870831170789992689718351 218806246756184989034577527)
      ·
        refine ⟨328209370134277483551866291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 218806246756184989034577527 328209370134277483551866291)
        ·
          refine ⟨492314055201416225327799437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 328209370134277483551866291 492314055201416225327799437)
          ·
            refine ⟨184617770700531084497924789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 492314055201416225327799437 184617770700531084497924789)
            ·
              refine ⟨17307916003174789171680449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 184617770700531084497924789 17307916003174789171680449)
              ·
                refine ⟨12980937002381091878760337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17307916003174789171680449 12980937002381091878760337)
                ·
                  refine ⟨9735702751785818909070253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12980937002381091878760337 9735702751785818909070253)
                  ·
                    refine ⟨3650888531919682090901345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9735702751785818909070253 3650888531919682090901345)
                    ·
                      refine ⟨2738166398939761568176009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3650888531919682090901345 2738166398939761568176009)
                      ·
                        rfl

theorem cell23_5332560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 5, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 5, 2, 2, 3, 2].length) (baseStart_5332560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5332560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5332560 prefixEnd_5332560 := by exact prefixLift 5332560
  have htrace : WordTrace (prefixWord ++ tailWord_5332560) baseStart_5332560 baseEnd_5332560 := by
    simpa [prefixWord, tailWord_5332560, baseEnd_5332560] using wordTrace_append hprefix tailTrace_5332560
  have hstable : (prefixWord ++ tailWord_5332560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5332560).length < 2 ^ (prefixWord ++ tailWord_5332560).sum := by decide
  have hdescent : baseEnd_5332560 < baseStart_5332560 := by decide
  rcases family_descends (prefixWord ++ tailWord_5332560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5332567 : List Nat := [1, 1, 3, 2, 2, 5, 1, 1, 3, 1, 3]
def baseStart_5332567 : Nat := 118140960795 + 5332567 * 2 ^ 59
def prefixEnd_5332567 : Nat := 4983230072969 + 3 ^ 40 * 5332567 * 2
def baseEnd_5332567 : Nat := 2738169993304343040788477

theorem tailTrace_5332567 : CollatzResearch.WordTrace tailWord_5332567 prefixEnd_5332567 2738169993304343040788477 := by
  unfold tailWord_5332567
  simp only [CollatzResearch.WordTrace]
  refine ⟨194494696872027963781795955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129663131248018642521197303 194494696872027963781795955)
  ·
    refine ⟨291742045308041945672693933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194494696872027963781795955 291742045308041945672693933)
    ·
      refine ⟨109403266990515729627260225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 291742045308041945672693933 109403266990515729627260225)
      ·
        refine ⟨82052450242886797220445169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 109403266990515729627260225 82052450242886797220445169)
        ·
          refine ⟨61539337682165097915333877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82052450242886797220445169 61539337682165097915333877)
          ·
            refine ⟨5769312907702977929562551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 61539337682165097915333877 5769312907702977929562551)
            ·
              refine ⟨8653969361554466894343827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5769312907702977929562551 8653969361554466894343827)
              ·
                refine ⟨12980954042331700341515741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8653969361554466894343827 12980954042331700341515741)
                ·
                  refine ⟨4867857765874387628068403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12980954042331700341515741 4867857765874387628068403)
                  ·
                    refine ⟨7301786648811581442102605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4867857765874387628068403 7301786648811581442102605)
                    ·
                      refine ⟨2738169993304343040788477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7301786648811581442102605 2738169993304343040788477)
                      ·
                        rfl

theorem cell23_5332567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 5, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 5, 1, 1, 3, 1, 3].length) (baseStart_5332567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5332567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5332567 prefixEnd_5332567 := by exact prefixLift 5332567
  have htrace : WordTrace (prefixWord ++ tailWord_5332567) baseStart_5332567 baseEnd_5332567 := by
    simpa [prefixWord, tailWord_5332567, baseEnd_5332567] using wordTrace_append hprefix tailTrace_5332567
  have hstable : (prefixWord ++ tailWord_5332567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5332567).length < 2 ^ (prefixWord ++ tailWord_5332567).sum := by decide
  have hdescent : baseEnd_5332567 < baseStart_5332567 := by decide
  rcases family_descends (prefixWord ++ tailWord_5332567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5332603 : List Nat := [1, 1, 1, 1, 1, 4, 5, 2, 1, 2, 4]
def baseStart_5332603 : Nat := 118140960795 + 5332603 * 2 ^ 59
def prefixEnd_5332603 : Nat := 4983230072969 + 3 ^ 40 * 5332603 * 2
def baseEnd_5332603 : Nat := 2738188478607904899938311

theorem tailTrace_5332603 : CollatzResearch.WordTrace tailWord_5332603 prefixEnd_5332603 2738188478607904899938311 := by
  unfold tailWord_5332603
  simp only [CollatzResearch.WordTrace]
  refine ⟨194496009899897541930106463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129664006599931694620070975 194496009899897541930106463)
  ·
    refine ⟨291744014849846312895159695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194496009899897541930106463 291744014849846312895159695)
    ·
      refine ⟨437616022274769469342739543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 291744014849846312895159695 437616022274769469342739543)
      ·
        refine ⟨656424033412154204014109315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 437616022274769469342739543 656424033412154204014109315)
        ·
          refine ⟨984636050118231306021163973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 656424033412154204014109315 984636050118231306021163973)
          ·
            refine ⟨184619259397168369878968245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 984636050118231306021163973 184619259397168369878968245)
            ·
              refine ⟨17308055568484534676153273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 184619259397168369878968245 17308055568484534676153273)
              ·
                refine ⟨12981041676363401007114955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17308055568484534676153273 12981041676363401007114955)
                ·
                  refine ⟨19471562514545101510672433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12981041676363401007114955 19471562514545101510672433)
                  ·
                    refine ⟨14603671885908826133004325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19471562514545101510672433 14603671885908826133004325)
                    ·
                      refine ⟨2738188478607904899938311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14603671885908826133004325 2738188478607904899938311)
                      ·
                        rfl

theorem cell23_5332603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 5, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 5, 2, 1, 2, 4].length) (baseStart_5332603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5332603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5332603 prefixEnd_5332603 := by exact prefixLift 5332603
  have htrace : WordTrace (prefixWord ++ tailWord_5332603) baseStart_5332603 baseEnd_5332603 := by
    simpa [prefixWord, tailWord_5332603, baseEnd_5332603] using wordTrace_append hprefix tailTrace_5332603
  have hstable : (prefixWord ++ tailWord_5332603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5332603).length < 2 ^ (prefixWord ++ tailWord_5332603).sum := by decide
  have hdescent : baseEnd_5332603 < baseStart_5332603 := by decide
  rcases family_descends (prefixWord ++ tailWord_5332603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5332640 : List Nat := [2, 1, 1, 4, 3, 1, 1, 3, 1, 3, 3]
def baseStart_5332640 : Nat := 118140960795 + 5332640 * 2 ^ 59
def prefixEnd_5332640 : Nat := 4983230072969 + 3 ^ 40 * 5332640 * 2
def baseEnd_5332640 : Nat := 2738207477392121255175641

theorem tailTrace_5332640 : CollatzResearch.WordTrace tailWord_5332640 prefixEnd_5332640 2738207477392121255175641 := by
  unfold tailWord_5332640
  simp only [CollatzResearch.WordTrace]
  refine ⟨97248679700381748624601687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129664906267175664832802249 97248679700381748624601687)
  ·
    refine ⟨145873019550572622936902531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97248679700381748624601687 145873019550572622936902531)
    ·
      refine ⟨218809529325858934405353797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145873019550572622936902531 218809529325858934405353797)
      ·
        refine ⟨41026786748598550201003837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 218809529325858934405353797 41026786748598550201003837)
        ·
          refine ⟨15385045030724456325376439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41026786748598550201003837 15385045030724456325376439)
          ·
            refine ⟨23077567546086684488064659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15385045030724456325376439 23077567546086684488064659)
            ·
              refine ⟨34616351319130026732096989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23077567546086684488064659 34616351319130026732096989)
              ·
                refine ⟨12981131744673760024536371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34616351319130026732096989 12981131744673760024536371)
                ·
                  refine ⟨19471697617010640036804557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12981131744673760024536371 19471697617010640036804557)
                  ·
                    refine ⟨7301886606378990013801709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19471697617010640036804557 7301886606378990013801709)
                    ·
                      refine ⟨2738207477392121255175641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7301886606378990013801709 2738207477392121255175641)
                      ·
                        rfl

theorem cell23_5332640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 1, 3, 1, 3, 3].length) (baseStart_5332640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5332640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5332640 prefixEnd_5332640 := by exact prefixLift 5332640
  have htrace : WordTrace (prefixWord ++ tailWord_5332640) baseStart_5332640 baseEnd_5332640 := by
    simpa [prefixWord, tailWord_5332640, baseEnd_5332640] using wordTrace_append hprefix tailTrace_5332640
  have hstable : (prefixWord ++ tailWord_5332640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5332640).length < 2 ^ (prefixWord ++ tailWord_5332640).sum := by decide
  have hdescent : baseEnd_5332640 < baseStart_5332640 := by decide
  rcases family_descends (prefixWord ++ tailWord_5332640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5332661 : List Nat := [1, 3, 3, 3, 2, 2, 2, 1, 1, 2, 3]
def baseStart_5332661 : Nat := 118140960795 + 5332661 * 2 ^ 59
def prefixEnd_5332661 : Nat := 4983230072969 + 3 ^ 40 * 5332661 * 2
def baseEnd_5332661 : Nat := 2738218260485865673013045

theorem tailTrace_5332661 : CollatzResearch.WordTrace tailWord_5332661 prefixEnd_5332661 2738218260485865673013045 := by
  unfold tailWord_5332661
  simp only [CollatzResearch.WordTrace]
  refine ⟨194498125333687417835717837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129665416889124945223811891 194498125333687417835717837)
  ·
    refine ⟨72936797000132781688394189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 194498125333687417835717837 72936797000132781688394189)
    ·
      refine ⟨27351298875049793133147821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72936797000132781688394189 27351298875049793133147821)
      ·
        refine ⟨10256737078143672424930433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27351298875049793133147821 10256737078143672424930433)
        ·
          refine ⟨7692552808607754318697825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10256737078143672424930433 7692552808607754318697825)
          ·
            refine ⟨5769414606455815739023369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7692552808607754318697825 5769414606455815739023369)
            ·
              refine ⟨4327060954841861804267527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5769414606455815739023369 4327060954841861804267527)
              ·
                refine ⟨6490591432262792706401291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4327060954841861804267527 6490591432262792706401291)
                ·
                  refine ⟨9735887148394189059601937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6490591432262792706401291 9735887148394189059601937)
                  ·
                    refine ⟨7301915361295641794701453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9735887148394189059601937 7301915361295641794701453)
                    ·
                      refine ⟨2738218260485865673013045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7301915361295641794701453 2738218260485865673013045)
                      ·
                        rfl

theorem cell23_5332661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 2, 2, 1, 1, 2, 3].length) (baseStart_5332661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5332661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5332661 prefixEnd_5332661 := by exact prefixLift 5332661
  have htrace : WordTrace (prefixWord ++ tailWord_5332661) baseStart_5332661 baseEnd_5332661 := by
    simpa [prefixWord, tailWord_5332661, baseEnd_5332661] using wordTrace_append hprefix tailTrace_5332661
  have hstable : (prefixWord ++ tailWord_5332661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5332661).length < 2 ^ (prefixWord ++ tailWord_5332661).sum := by decide
  have hdescent : baseEnd_5332661 < baseStart_5332661 := by decide
  rcases family_descends (prefixWord ++ tailWord_5332661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5332683 : List Nat := [1, 1, 1, 1, 3, 2, 1, 3, 1, 6, 3]
def baseStart_5332683 : Nat := 118140960795 + 5332683 * 2 ^ 59
def prefixEnd_5332683 : Nat := 4983230072969 + 3 ^ 40 * 5332683 * 2
def baseEnd_5332683 : Nat := 2738229557060264586937943

theorem tailTrace_5332683 : CollatzResearch.WordTrace tailWord_5332683 prefixEnd_5332683 2738229557060264586937943 := by
  unfold tailWord_5332683
  simp only [CollatzResearch.WordTrace]
  refine ⟨194498927739607715593018703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129665951826405143728679135 194498927739607715593018703)
  ·
    refine ⟨291748391609411573389528055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194498927739607715593018703 291748391609411573389528055)
    ·
      refine ⟨437622587414117360084292083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 291748391609411573389528055 437622587414117360084292083)
      ·
        refine ⟨656433881121176040126438125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 437622587414117360084292083 656433881121176040126438125)
        ·
          refine ⟨246162705420441015047414297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 656433881121176040126438125 246162705420441015047414297)
          ·
            refine ⟨184622029065330761285560723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 246162705420441015047414297 184622029065330761285560723)
            ·
              refine ⟨276933043597996141928341085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 184622029065330761285560723 276933043597996141928341085)
              ·
                refine ⟨103849891349248553223127907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 276933043597996141928341085 103849891349248553223127907)
                ·
                  refine ⟨155774837023872829834691861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 103849891349248553223127907 155774837023872829834691861)
                  ·
                    refine ⟨7301945485494038898501181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 155774837023872829834691861 7301945485494038898501181)
                    ·
                      refine ⟨2738229557060264586937943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7301945485494038898501181 2738229557060264586937943)
                      ·
                        rfl

theorem cell23_5332683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 3, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 3, 1, 6, 3].length) (baseStart_5332683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5332683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5332683 prefixEnd_5332683 := by exact prefixLift 5332683
  have htrace : WordTrace (prefixWord ++ tailWord_5332683) baseStart_5332683 baseEnd_5332683 := by
    simpa [prefixWord, tailWord_5332683, baseEnd_5332683] using wordTrace_append hprefix tailTrace_5332683
  have hstable : (prefixWord ++ tailWord_5332683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5332683).length < 2 ^ (prefixWord ++ tailWord_5332683).sum := by decide
  have hdescent : baseEnd_5332683 < baseStart_5332683 := by decide
  rcases family_descends (prefixWord ++ tailWord_5332683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5332690 : List Nat := [3, 2, 2, 2, 2, 1, 2, 1, 2, 6]
def baseStart_5332690 : Nat := 118140960795 + 5332690 * 2 ^ 59
def prefixEnd_5332690 : Nat := 4983230072969 + 3 ^ 40 * 5332690 * 2
def baseEnd_5332690 : Nat := 912744383808282019850137

theorem tailTrace_5332690 : CollatzResearch.WordTrace tailWord_5332690 prefixEnd_5332690 912744383808282019850137 := by
  unfold tailWord_5332690
  simp only [CollatzResearch.WordTrace]
  refine ⟨48624795762645588947130881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129666122033721570525682349 48624795762645588947130881)
  ·
    refine ⟨36468596821984191710348161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48624795762645588947130881 36468596821984191710348161)
    ·
      refine ⟨27351447616488143782761121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36468596821984191710348161 27351447616488143782761121)
      ·
        refine ⟨20513585712366107837070841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27351447616488143782761121 20513585712366107837070841)
        ·
          refine ⟨15385189284274580877803131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20513585712366107837070841 15385189284274580877803131)
          ·
            refine ⟨23077783926411871316704697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15385189284274580877803131 23077783926411871316704697)
            ·
              refine ⟨17308337944808903487528523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23077783926411871316704697 17308337944808903487528523)
              ·
                refine ⟨25962506917213355231292785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17308337944808903487528523 25962506917213355231292785)
                ·
                  refine ⟨19471880187910016423469589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25962506917213355231292785 19471880187910016423469589)
                  ·
                    refine ⟨912744383808282019850137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19471880187910016423469589 912744383808282019850137)
                    ·
                      rfl

theorem cell23_5332690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 2, 1, 2, 6].length) (baseStart_5332690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5332690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5332690 prefixEnd_5332690 := by exact prefixLift 5332690
  have htrace : WordTrace (prefixWord ++ tailWord_5332690) baseStart_5332690 baseEnd_5332690 := by
    simpa [prefixWord, tailWord_5332690, baseEnd_5332690] using wordTrace_append hprefix tailTrace_5332690
  have hstable : (prefixWord ++ tailWord_5332690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5332690).length < 2 ^ (prefixWord ++ tailWord_5332690).sum := by decide
  have hdescent : baseEnd_5332690 < baseStart_5332690 := by decide
  rcases family_descends (prefixWord ++ tailWord_5332690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5332697 : List Nat := [1, 2, 1, 2, 3, 3, 3, 1, 1, 4, 2]
def baseStart_5332697 : Nat := 118140960795 + 5332697 * 2 ^ 59
def prefixEnd_5332697 : Nat := 4983230072969 + 3 ^ 40 * 5332697 * 2
def baseEnd_5332697 : Nat := 2738236745789427532162879

theorem tailTrace_5332697 : CollatzResearch.WordTrace tailWord_5332697 prefixEnd_5332697 2738236745789427532162879 := by
  unfold tailWord_5332697
  simp only [CollatzResearch.WordTrace]
  refine ⟨194499438361556995984028345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129666292241037997322685563 194499438361556995984028345)
  ·
    refine ⟨145874578771167746988021259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 194499438361556995984028345 145874578771167746988021259)
    ·
      refine ⟨218811868156751620482031889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145874578771167746988021259 218811868156751620482031889)
      ·
        refine ⟨164108901117563715361523917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 218811868156751620482031889 164108901117563715361523917)
        ·
          refine ⟨61540837919086393260571469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 164108901117563715361523917 61540837919086393260571469)
          ·
            refine ⟨23077814219657397472714301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 61540837919086393260571469 23077814219657397472714301)
            ·
              refine ⟨8654180332371524052267863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23077814219657397472714301 8654180332371524052267863)
              ·
                refine ⟨12981270498557286078401795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8654180332371524052267863 12981270498557286078401795)
                ·
                  refine ⟨19471905747835929117602693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12981270498557286078401795 19471905747835929117602693)
                  ·
                    refine ⟨3650982327719236709550505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19471905747835929117602693 3650982327719236709550505)
                    ·
                      refine ⟨2738236745789427532162879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3650982327719236709550505 2738236745789427532162879)
                      ·
                        rfl

theorem cell23_5332697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 3, 1, 1, 4, 2].length) (baseStart_5332697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5332697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5332697 prefixEnd_5332697 := by exact prefixLift 5332697
  have htrace : WordTrace (prefixWord ++ tailWord_5332697) baseStart_5332697 baseEnd_5332697 := by
    simpa [prefixWord, tailWord_5332697, baseEnd_5332697] using wordTrace_append hprefix tailTrace_5332697
  have hstable : (prefixWord ++ tailWord_5332697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5332697).length < 2 ^ (prefixWord ++ tailWord_5332697).sum := by decide
  have hdescent : baseEnd_5332697 < baseStart_5332697 := by decide
  rcases family_descends (prefixWord ++ tailWord_5332697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5332703 : List Nat := [1, 1, 2, 3, 2, 2, 1, 4, 7]
def baseStart_5332703 : Nat := 118140960795 + 5332703 * 2 ^ 59
def prefixEnd_5332703 : Nat := 4983230072969 + 3 ^ 40 * 5332703 * 2
def baseEnd_5332703 : Nat := 304248869630372723187539

theorem tailTrace_5332703 : CollatzResearch.WordTrace tailWord_5332703 prefixEnd_5332703 304248869630372723187539 := by
  unfold tailWord_5332703
  simp only [CollatzResearch.WordTrace]
  refine ⟨194499657199535259008746763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129666438133023506005831175 194499657199535259008746763)
  ·
    refine ⟨291749485799302888513120145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194499657199535259008746763 291749485799302888513120145)
    ·
      refine ⟨218812114349477166384840109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 291749485799302888513120145 218812114349477166384840109)
      ·
        refine ⟨82054542881053937394315041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 218812114349477166384840109 82054542881053937394315041)
        ·
          refine ⟨61540907160790453045736281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82054542881053937394315041 61540907160790453045736281)
          ·
            refine ⟨46155680370592839784302211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61540907160790453045736281 46155680370592839784302211)
            ·
              refine ⟨69233520555889259676453317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46155680370592839784302211 69233520555889259676453317)
              ·
                refine ⟨12981285104229236189334997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 69233520555889259676453317 12981285104229236189334997)
                ·
                  refine ⟨304248869630372723187539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12981285104229236189334997 304248869630372723187539)
                  ·
                    rfl

theorem cell23_5332703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 4, 7].length) (baseStart_5332703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5332703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5332703 prefixEnd_5332703 := by exact prefixLift 5332703
  have htrace : WordTrace (prefixWord ++ tailWord_5332703) baseStart_5332703 baseEnd_5332703 := by
    simpa [prefixWord, tailWord_5332703, baseEnd_5332703] using wordTrace_append hprefix tailTrace_5332703
  have hstable : (prefixWord ++ tailWord_5332703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5332703).length < 2 ^ (prefixWord ++ tailWord_5332703).sum := by decide
  have hdescent : baseEnd_5332703 < baseStart_5332703 := by decide
  rcases family_descends (prefixWord ++ tailWord_5332703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5332720 : List Nat := [2, 1, 1, 1, 3, 1, 2, 7, 5]
def baseStart_5332720 : Nat := 118140960795 + 5332720 * 2 ^ 59
def prefixEnd_5332720 : Nat := 4983230072969 + 3 ^ 40 * 5332720 * 2
def baseEnd_5332720 : Nat := 304249839538275660241697

theorem tailTrace_5332720 : CollatzResearch.WordTrace tailWord_5332720 prefixEnd_5332720 304249839538275660241697 := by
  unfold tailWord_5332720
  simp only [CollatzResearch.WordTrace]
  refine ⟨97250138620236835456057807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129666851493649113941410409 97250138620236835456057807)
  ·
    refine ⟨145875207930355253184086711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97250138620236835456057807 145875207930355253184086711)
    ·
      refine ⟨218812811895532879776130067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145875207930355253184086711 218812811895532879776130067)
      ·
        refine ⟨328219217843299319664195101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 218812811895532879776130067 328219217843299319664195101)
        ·
          refine ⟨123082206691237244874073163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 328219217843299319664195101 123082206691237244874073163)
          ·
            refine ⟨184623310036855867311109745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 123082206691237244874073163 184623310036855867311109745)
            ·
              refine ⟨138467482527641900483332309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 184623310036855867311109745 138467482527641900483332309)
              ·
                refine ⟨3245331621741607042578101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 138467482527641900483332309 3245331621741607042578101)
                ·
                  refine ⟨304249839538275660241697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3245331621741607042578101 304249839538275660241697)
                  ·
                    rfl

theorem cell23_5332720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 7, 5].length) (baseStart_5332720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5332720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5332720 prefixEnd_5332720 := by exact prefixLift 5332720
  have htrace : WordTrace (prefixWord ++ tailWord_5332720) baseStart_5332720 baseEnd_5332720 := by
    simpa [prefixWord, tailWord_5332720, baseEnd_5332720] using wordTrace_append hprefix tailTrace_5332720
  have hstable : (prefixWord ++ tailWord_5332720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5332720).length < 2 ^ (prefixWord ++ tailWord_5332720).sum := by decide
  have hdescent : baseEnd_5332720 < baseStart_5332720 := by decide
  rcases family_descends (prefixWord ++ tailWord_5332720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5332733 : List Nat := [1, 4, 1, 1, 1, 1, 2, 2, 3, 7]
def baseStart_5332733 : Nat := 118140960795 + 5332733 * 2 ^ 59
def prefixEnd_5332733 : Nat := 4983230072969 + 3 ^ 40 * 5332733 * 2
def baseEnd_5332733 : Nat := 912751743697663130437571

theorem tailTrace_5332733 : CollatzResearch.WordTrace tailWord_5332733 prefixEnd_5332733 912751743697663130437571 := by
  unfold tailWord_5332733
  simp only [CollatzResearch.WordTrace]
  refine ⟨194500751389426574132338853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129667167592951049421559235 194500751389426574132338853)
  ·
    refine ⟨36468890885517482649813535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 194500751389426574132338853 36468890885517482649813535)
    ·
      refine ⟨54703336328276223974720303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36468890885517482649813535 54703336328276223974720303)
      ·
        refine ⟨82055004492414335962080455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54703336328276223974720303 82055004492414335962080455)
        ·
          refine ⟨123082506738621503943120683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82055004492414335962080455 123082506738621503943120683)
          ·
            refine ⟨184623760107932255914681025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 123082506738621503943120683 184623760107932255914681025)
            ·
              refine ⟨138467820080949191936010769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 184623760107932255914681025 138467820080949191936010769)
              ·
                refine ⟨103850865060711893952008077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 138467820080949191936010769 103850865060711893952008077)
                ·
                  refine ⟨38944074397766960232003029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 103850865060711893952008077 38944074397766960232003029)
                  ·
                    refine ⟨912751743697663130437571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 38944074397766960232003029 912751743697663130437571)
                    ·
                      rfl

theorem cell23_5332733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 2, 3, 7].length) (baseStart_5332733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5332733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5332733 prefixEnd_5332733 := by exact prefixLift 5332733
  have htrace : WordTrace (prefixWord ++ tailWord_5332733) baseStart_5332733 baseEnd_5332733 := by
    simpa [prefixWord, tailWord_5332733, baseEnd_5332733] using wordTrace_append hprefix tailTrace_5332733
  have hstable : (prefixWord ++ tailWord_5332733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5332733).length < 2 ^ (prefixWord ++ tailWord_5332733).sum := by decide
  have hdescent : baseEnd_5332733 < baseStart_5332733 := by decide
  rcases family_descends (prefixWord ++ tailWord_5332733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5332742 : List Nat := [6, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3]
def baseStart_5332742 : Nat := 118140960795 + 5332742 * 2 ^ 59
def prefixEnd_5332742 : Nat := 4983230072969 + 3 ^ 40 * 5332742 * 2
def baseEnd_5332742 : Nat := 2738259852418879856100173

theorem tailTrace_5332742 : CollatzResearch.WordTrace tailWord_5332742 prefixEnd_5332742 2738259852418879856100173 := by
  unfold tailWord_5332742
  simp only [CollatzResearch.WordTrace]
  refine ⟨6078158738949811520919265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 129667386430929312446277653 6078158738949811520919265)
  ·
    refine ⟨4558619054212358640689449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6078158738949811520919265 4558619054212358640689449)
    ·
      refine ⟨3418964290659268980517087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4558619054212358640689449 3418964290659268980517087)
      ·
        refine ⟨5128446435988903470775631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3418964290659268980517087 5128446435988903470775631)
        ·
          refine ⟨7692669653983355206163447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5128446435988903470775631 7692669653983355206163447)
          ·
            refine ⟨11539004480975032809245171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7692669653983355206163447 11539004480975032809245171)
            ·
              refine ⟨17308506721462549213867757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11539004480975032809245171 17308506721462549213867757)
              ·
                refine ⟨6490690020548455955200409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17308506721462549213867757 6490690020548455955200409)
                ·
                  refine ⟨4868017515411341966400307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6490690020548455955200409 4868017515411341966400307)
                  ·
                    refine ⟨7302026273117012949600461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4868017515411341966400307 7302026273117012949600461)
                    ·
                      refine ⟨2738259852418879856100173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7302026273117012949600461 2738259852418879856100173)
                      ·
                        rfl

theorem cell23_5332742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3].length) (baseStart_5332742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5332742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5332742 prefixEnd_5332742 := by exact prefixLift 5332742
  have htrace : WordTrace (prefixWord ++ tailWord_5332742) baseStart_5332742 baseEnd_5332742 := by
    simpa [prefixWord, tailWord_5332742, baseEnd_5332742] using wordTrace_append hprefix tailTrace_5332742
  have hstable : (prefixWord ++ tailWord_5332742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5332742).length < 2 ^ (prefixWord ++ tailWord_5332742).sum := by decide
  have hdescent : baseEnd_5332742 < baseStart_5332742 := by decide
  rcases family_descends (prefixWord ++ tailWord_5332742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5332783 : List Nat := [1, 1, 2, 1, 2, 1, 2, 3, 1, 3, 6]
def baseStart_5332783 : Nat := 118140960795 + 5332783 * 2 ^ 59
def prefixEnd_5332783 : Nat := 4983230072969 + 3 ^ 40 * 5332783 * 2
def baseEnd_5332783 : Nat := 2738280905125714195687483

theorem tailTrace_5332783 : CollatzResearch.WordTrace tailWord_5332783 prefixEnd_5332783 2738280905125714195687483 := by
  unfold tailWord_5332783
  simp only [CollatzResearch.WordTrace]
  refine ⟨194502575039245432671659003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129668383359496955114439335 194502575039245432671659003)
  ·
    refine ⟨291753862558868149007488505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194502575039245432671659003 291753862558868149007488505)
    ·
      refine ⟨218815396919151111755616379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 291753862558868149007488505 218815396919151111755616379)
      ·
        refine ⟨328223095378726667633424569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 218815396919151111755616379 328223095378726667633424569)
        ·
          refine ⟨246167321534045000725068427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 328223095378726667633424569 246167321534045000725068427)
          ·
            refine ⟨369250982301067501087602641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 246167321534045000725068427 369250982301067501087602641)
            ·
              refine ⟨276938236725800625815701981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 369250982301067501087602641 276938236725800625815701981)
              ·
                refine ⟨103851838772175234680888243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 276938236725800625815701981 103851838772175234680888243)
                ·
                  refine ⟨155777758158262852021332365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 103851838772175234680888243 155777758158262852021332365)
                  ·
                    refine ⟨58416659309348569507999637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 155777758158262852021332365 58416659309348569507999637)
                    ·
                      refine ⟨2738280905125714195687483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 58416659309348569507999637 2738280905125714195687483)
                      ·
                        rfl

theorem cell23_5332783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 3, 1, 3, 6].length) (baseStart_5332783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5332783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5332783 prefixEnd_5332783 := by exact prefixLift 5332783
  have htrace : WordTrace (prefixWord ++ tailWord_5332783) baseStart_5332783 baseEnd_5332783 := by
    simpa [prefixWord, tailWord_5332783, baseEnd_5332783] using wordTrace_append hprefix tailTrace_5332783
  have hstable : (prefixWord ++ tailWord_5332783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5332783).length < 2 ^ (prefixWord ++ tailWord_5332783).sum := by decide
  have hdescent : baseEnd_5332783 < baseStart_5332783 := by decide
  rcases family_descends (prefixWord ++ tailWord_5332783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5332810 : List Nat := [3, 1, 2, 1, 1, 1, 3, 5, 6]
def baseStart_5332810 : Nat := 118140960795 + 5332810 * 2 ^ 59
def prefixEnd_5332810 : Nat := 4983230072969 + 3 ^ 40 * 5332810 * 2
def baseEnd_5332810 : Nat := 304254974344820621116651

theorem tailTrace_5332810 : CollatzResearch.WordTrace tailWord_5332810 prefixEnd_5332810 304254974344820621116651 := by
  unfold tailWord_5332810
  simp only [CollatzResearch.WordTrace]
  refine ⟨48625889952536904070722971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129669039873431744188594589 48625889952536904070722971)
  ·
    refine ⟨72938834928805356106084457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48625889952536904070722971 72938834928805356106084457)
    ·
      refine ⟨54704126196604017079563343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72938834928805356106084457 54704126196604017079563343)
      ·
        refine ⟨82056189294906025619345015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54704126196604017079563343 82056189294906025619345015)
        ·
          refine ⟨123084283942359038429017523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82056189294906025619345015 123084283942359038429017523)
          ·
            refine ⟨184626425913538557643526285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 123084283942359038429017523 184626425913538557643526285)
            ·
              refine ⟨69234909717576959116322357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 184626425913538557643526285 69234909717576959116322357)
              ·
                refine ⟨6490772786022839917155221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 69234909717576959116322357 6490772786022839917155221)
                ·
                  refine ⟨304254974344820621116651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6490772786022839917155221 304254974344820621116651)
                  ·
                    rfl

theorem cell23_5332810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 5, 6].length) (baseStart_5332810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5332810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5332810 prefixEnd_5332810 := by exact prefixLift 5332810
  have htrace : WordTrace (prefixWord ++ tailWord_5332810) baseStart_5332810 baseEnd_5332810 := by
    simpa [prefixWord, tailWord_5332810, baseEnd_5332810] using wordTrace_append hprefix tailTrace_5332810
  have hstable : (prefixWord ++ tailWord_5332810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5332810).length < 2 ^ (prefixWord ++ tailWord_5332810).sum := by decide
  have hdescent : baseEnd_5332810 < baseStart_5332810 := by decide
  rcases family_descends (prefixWord ++ tailWord_5332810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5332837 : List Nat := [1, 3, 1, 3, 1, 1, 1, 1, 7, 1, 3]
def baseStart_5332837 : Nat := 118140960795 + 5332837 * 2 ^ 59
def prefixEnd_5332837 : Nat := 4983230072969 + 3 ^ 40 * 5332837 * 2
def baseEnd_5332837 : Nat := 2738308633081056984412235

theorem tailTrace_5332837 : CollatzResearch.WordTrace tailWord_5332837 prefixEnd_5332837 2738308633081056984412235 := by
  unfold tailWord_5332837
  simp only [CollatzResearch.WordTrace]
  refine ⟨194504544581049799894124765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129669696387366533262749843 194504544581049799894124765)
  ·
    refine ⟨72939204217893674960296787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 194504544581049799894124765 72939204217893674960296787)
    ·
      refine ⟨109408806326840512440445181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72939204217893674960296787 109408806326840512440445181)
      ·
        refine ⟨41028302372565192165166943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 109408806326840512440445181 41028302372565192165166943)
        ·
          refine ⟨61542453558847788247750415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41028302372565192165166943 61542453558847788247750415)
          ·
            refine ⟨92313680338271682371625623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61542453558847788247750415 92313680338271682371625623)
            ·
              refine ⟨138470520507407523557438435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 92313680338271682371625623 138470520507407523557438435)
              ·
                refine ⟨207705780761111285336157653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 138470520507407523557438435 207705780761111285336157653)
                ·
                  refine ⟨4868104236588545750066195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 207705780761111285336157653 4868104236588545750066195)
                  ·
                    refine ⟨7302156354882818625099293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4868104236588545750066195 7302156354882818625099293)
                    ·
                      refine ⟨2738308633081056984412235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7302156354882818625099293 2738308633081056984412235)
                      ·
                        rfl

theorem cell23_5332837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 1, 7, 1, 3].length) (baseStart_5332837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5332837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5332837 prefixEnd_5332837 := by exact prefixLift 5332837
  have htrace : WordTrace (prefixWord ++ tailWord_5332837) baseStart_5332837 baseEnd_5332837 := by
    simpa [prefixWord, tailWord_5332837, baseEnd_5332837] using wordTrace_append hprefix tailTrace_5332837
  have hstable : (prefixWord ++ tailWord_5332837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5332837).length < 2 ^ (prefixWord ++ tailWord_5332837).sum := by decide
  have hdescent : baseEnd_5332837 < baseStart_5332837 := by decide
  rcases family_descends (prefixWord ++ tailWord_5332837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5332887 : List Nat := [1, 1, 3, 3, 1, 3, 1, 2, 4, 4]
def baseStart_5332887 : Nat := 118140960795 + 5332887 * 2 ^ 59
def prefixEnd_5332887 : Nat := 4983230072969 + 3 ^ 40 * 5332887 * 2
def baseEnd_5332887 : Nat := 912778102371260596262335

theorem tailTrace_5332887 : CollatzResearch.WordTrace tailWord_5332887 prefixEnd_5332887 912778102371260596262335 := by
  unfold tailWord_5332887
  simp only [CollatzResearch.WordTrace]
  refine ⟨194506368230868658433444915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129670912153912438955629943 194506368230868658433444915)
  ·
    refine ⟨291759552346302987650167373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194506368230868658433444915 291759552346302987650167373)
    ·
      refine ⟨109409832129863620368812765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 291759552346302987650167373 109409832129863620368812765)
      ·
        refine ⟨41028687048698857638304787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 109409832129863620368812765 41028687048698857638304787)
        ·
          refine ⟨61543030573048286457457181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41028687048698857638304787 61543030573048286457457181)
          ·
            refine ⟨23078636464893107421546443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 61543030573048286457457181 23078636464893107421546443)
            ·
              refine ⟨34617954697339661132319665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23078636464893107421546443 34617954697339661132319665)
              ·
                refine ⟨25963466023004745849239749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34617954697339661132319665 25963466023004745849239749)
                ·
                  refine ⟨4868149879313389846732453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25963466023004745849239749 4868149879313389846732453)
                  ·
                    refine ⟨912778102371260596262335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4868149879313389846732453 912778102371260596262335)
                    ·
                      rfl

theorem cell23_5332887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 1, 2, 4, 4].length) (baseStart_5332887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5332887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5332887 prefixEnd_5332887 := by exact prefixLift 5332887
  have htrace : WordTrace (prefixWord ++ tailWord_5332887) baseStart_5332887 baseEnd_5332887 := by
    simpa [prefixWord, tailWord_5332887, baseEnd_5332887] using wordTrace_append hprefix tailTrace_5332887
  have hstable : (prefixWord ++ tailWord_5332887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5332887).length < 2 ^ (prefixWord ++ tailWord_5332887).sum := by decide
  have hdescent : baseEnd_5332887 < baseStart_5332887 := by decide
  rcases family_descends (prefixWord ++ tailWord_5332887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5332900 : List Nat := [2, 3, 1, 2, 1, 3, 11]
def baseStart_5332900 : Nat := 118140960795 + 5332900 * 2 ^ 59
def prefixEnd_5332900 : Nat := 4983230072969 + 3 ^ 40 * 5332900 * 2
def baseEnd_5332900 : Nat := 33806678794596175776845

theorem tailTrace_5332900 : CollatzResearch.WordTrace tailWord_5332900 prefixEnd_5332900 33806678794596175776845 := by
  unfold tailWord_5332900
  simp only [CollatzResearch.WordTrace]
  refine ⟨97253421189910780826834077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129671228253214374435778769 97253421189910780826834077)
  ·
    refine ⟨36470032946216542810062779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 97253421189910780826834077 36470032946216542810062779)
    ·
      refine ⟨54705049419324814215094169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36470032946216542810062779 54705049419324814215094169)
      ·
        refine ⟨41028787064493610661320627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54705049419324814215094169 41028787064493610661320627)
        ·
          refine ⟨61543180596740415991980941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41028787064493610661320627 61543180596740415991980941)
          ·
            refine ⟨23078692723777655996992853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 61543180596740415991980941 23078692723777655996992853)
            ·
              refine ⟨33806678794596175776845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 23078692723777655996992853 33806678794596175776845)
              ·
                rfl

theorem cell23_5332900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 11].length) (baseStart_5332900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5332900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5332900 prefixEnd_5332900 := by exact prefixLift 5332900
  have htrace : WordTrace (prefixWord ++ tailWord_5332900) baseStart_5332900 baseEnd_5332900 := by
    simpa [prefixWord, tailWord_5332900, baseEnd_5332900] using wordTrace_append hprefix tailTrace_5332900
  have hstable : (prefixWord ++ tailWord_5332900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5332900).length < 2 ^ (prefixWord ++ tailWord_5332900).sum := by decide
  have hdescent : baseEnd_5332900 < baseStart_5332900 := by decide
  rcases family_descends (prefixWord ++ tailWord_5332900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5332917 : List Nat := [1, 3, 3, 2, 1, 3, 2, 8]
def baseStart_5332917 : Nat := 118140960795 + 5332917 * 2 ^ 59
def prefixEnd_5332917 : Nat := 4983230072969 + 3 ^ 40 * 5332917 * 2
def baseEnd_5332917 : Nat := 101420359686422839681921

theorem tailTrace_5332917 : CollatzResearch.WordTrace tailWord_5332917 prefixEnd_5332917 101420359686422839681921 := by
  unfold tailWord_5332917
  simp only [CollatzResearch.WordTrace]
  refine ⟨194507462420759973557037005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129671641613839982371358003 194507462420759973557037005)
  ·
    refine ⟨72940298407784990083888877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 194507462420759973557037005 72940298407784990083888877)
    ·
      refine ⟨27352611902919371281458329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72940298407784990083888877 27352611902919371281458329)
      ·
        refine ⟨20514458927189528461093747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27352611902919371281458329 20514458927189528461093747)
        ·
          refine ⟨30771688390784292691640621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20514458927189528461093747 30771688390784292691640621)
          ·
            refine ⟨11539383146544109759365233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30771688390784292691640621 11539383146544109759365233)
            ·
              refine ⟨8654537359908082319523925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11539383146544109759365233 8654537359908082319523925)
              ·
                refine ⟨101420359686422839681921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8654537359908082319523925 101420359686422839681921)
                ·
                  rfl

theorem cell23_5332917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 2, 8].length) (baseStart_5332917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5332917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5332917 prefixEnd_5332917 := by exact prefixLift 5332917
  have htrace : WordTrace (prefixWord ++ tailWord_5332917) baseStart_5332917 baseEnd_5332917 := by
    simpa [prefixWord, tailWord_5332917, baseEnd_5332917] using wordTrace_append hprefix tailTrace_5332917
  have hstable : (prefixWord ++ tailWord_5332917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5332917).length < 2 ^ (prefixWord ++ tailWord_5332917).sum := by decide
  have hdescent : baseEnd_5332917 < baseStart_5332917 := by decide
  rcases family_descends (prefixWord ++ tailWord_5332917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5332920 : List Nat := [2, 1, 2, 1, 2, 3, 1, 1, 2, 2, 6]
def baseStart_5332920 : Nat := 118140960795 + 5332920 * 2 ^ 59
def prefixEnd_5332920 : Nat := 4983230072969 + 3 ^ 40 * 5332920 * 2
def baseEnd_5332920 : Nat := 2738351251975380159674353

theorem tailTrace_5332920 : CollatzResearch.WordTrace tailWord_5332920 prefixEnd_5332920 2738351251975380159674353 := by
  unfold tailWord_5332920
  simp only [CollatzResearch.WordTrace]
  refine ⟨97253785919874552534698107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129671714559832736712930809 97253785919874552534698107)
  ·
    refine ⟨145880678879811828802047161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97253785919874552534698107 145880678879811828802047161)
    ·
      refine ⟨109410509159858871601535371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 145880678879811828802047161 109410509159858871601535371)
      ·
        refine ⟨164115763739788307402303057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109410509159858871601535371 164115763739788307402303057)
        ·
          refine ⟨123086822804841230551727293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 164115763739788307402303057 123086822804841230551727293)
          ·
            refine ⟨46157558551815461456897735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 123086822804841230551727293 46157558551815461456897735)
            ·
              refine ⟨69236337827723192185346603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46157558551815461456897735 69236337827723192185346603)
              ·
                refine ⟨103854506741584788278019905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 69236337827723192185346603 103854506741584788278019905)
                ·
                  refine ⟨77890880056188591208514929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 103854506741584788278019905 77890880056188591208514929)
                  ·
                    refine ⟨58418160042141443406386197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 77890880056188591208514929 58418160042141443406386197)
                    ·
                      refine ⟨2738351251975380159674353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 58418160042141443406386197 2738351251975380159674353)
                      ·
                        rfl

theorem cell23_5332920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 1, 2, 2, 6].length) (baseStart_5332920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5332920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5332920 prefixEnd_5332920 := by exact prefixLift 5332920
  have htrace : WordTrace (prefixWord ++ tailWord_5332920) baseStart_5332920 baseEnd_5332920 := by
    simpa [prefixWord, tailWord_5332920, baseEnd_5332920] using wordTrace_append hprefix tailTrace_5332920
  have hstable : (prefixWord ++ tailWord_5332920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5332920).length < 2 ^ (prefixWord ++ tailWord_5332920).sum := by decide
  have hdescent : baseEnd_5332920 < baseStart_5332920 := by decide
  rcases family_descends (prefixWord ++ tailWord_5332920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5332927 : List Nat := [1, 1, 2, 2, 2, 1, 4, 3, 1, 3, 3]
def baseStart_5332927 : Nat := 118140960795 + 5332927 * 2 ^ 59
def prefixEnd_5332927 : Nat := 4983230072969 + 3 ^ 40 * 5332927 * 2
def baseEnd_5332927 : Nat := 2738354846339961632286821

theorem tailTrace_5332927 : CollatzResearch.WordTrace tailWord_5332927 prefixEnd_5332927 2738354846339961632286821 := by
  unfold tailWord_5332927
  simp only [CollatzResearch.WordTrace]
  refine ⟨194507827150723745264901035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129671884767149163509934023 194507827150723745264901035)
  ·
    refine ⟨291761740726085617897351553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194507827150723745264901035 291761740726085617897351553)
    ·
      refine ⟨218821305544564213423013665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 291761740726085617897351553 218821305544564213423013665)
      ·
        refine ⟨164115979158423160067260249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 218821305544564213423013665 164115979158423160067260249)
        ·
          refine ⟨123086984368817370050445187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 164115979158423160067260249 123086984368817370050445187)
          ·
            refine ⟨184630476553226055075667781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 123086984368817370050445187 184630476553226055075667781)
            ·
              refine ⟨34618214353729885326687709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 184630476553226055075667781 34618214353729885326687709)
              ·
                refine ⟨12981830382648706997507891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34618214353729885326687709 12981830382648706997507891)
                ·
                  refine ⟨19472745573973060496261837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12981830382648706997507891 19472745573973060496261837)
                  ·
                    refine ⟨7302279590239897686098189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19472745573973060496261837 7302279590239897686098189)
                    ·
                      refine ⟨2738354846339961632286821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7302279590239897686098189 2738354846339961632286821)
                      ·
                        rfl

theorem cell23_5332927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 4, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 4, 3, 1, 3, 3].length) (baseStart_5332927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5332927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5332927 prefixEnd_5332927 := by exact prefixLift 5332927
  have htrace : WordTrace (prefixWord ++ tailWord_5332927) baseStart_5332927 baseEnd_5332927 := by
    simpa [prefixWord, tailWord_5332927, baseEnd_5332927] using wordTrace_append hprefix tailTrace_5332927
  have hstable : (prefixWord ++ tailWord_5332927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5332927).length < 2 ^ (prefixWord ++ tailWord_5332927).sum := by decide
  have hdescent : baseEnd_5332927 < baseStart_5332927 := by decide
  rcases family_descends (prefixWord ++ tailWord_5332927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5332937 : List Nat := [1, 2, 1, 1, 2, 1, 2, 2, 2, 7, 2]
def baseStart_5332937 : Nat := 118140960795 + 5332937 * 2 ^ 59
def prefixEnd_5332937 : Nat := 4983230072969 + 3 ^ 40 * 5332937 * 2
def baseEnd_5332937 : Nat := 2738359981146506593161775

theorem tailTrace_5332937 : CollatzResearch.WordTrace tailWord_5332937 prefixEnd_5332937 2738359981146506593161775 := by
  unfold tailWord_5332937
  simp only [CollatzResearch.WordTrace]
  refine ⟨194508191880687516972765065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129672127920458344648510043 194508191880687516972765065)
  ·
    refine ⟨145881143910515637729573799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 194508191880687516972765065 145881143910515637729573799)
    ·
      refine ⟨218821715865773456594360699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145881143910515637729573799 218821715865773456594360699)
      ·
        refine ⟨328232573798660184891541049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 218821715865773456594360699 328232573798660184891541049)
        ·
          refine ⟨246174430348995138668655787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 328232573798660184891541049 246174430348995138668655787)
          ·
            refine ⟨369261645523492708002983681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 246174430348995138668655787 369261645523492708002983681)
            ·
              refine ⟨276946234142619531002237761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 369261645523492708002983681 276946234142619531002237761)
              ·
                refine ⟨207709675606964648251678321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 276946234142619531002237761 207709675606964648251678321)
                ·
                  refine ⟨155782256705223486188758741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 207709675606964648251678321 155782256705223486188758741)
                  ·
                    refine ⟨3651146641528675457549033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 155782256705223486188758741 3651146641528675457549033)
                    ·
                      refine ⟨2738359981146506593161775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3651146641528675457549033 2738359981146506593161775)
                      ·
                        rfl

theorem cell23_5332937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 2, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 2, 2, 7, 2].length) (baseStart_5332937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5332937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5332937 prefixEnd_5332937 := by exact prefixLift 5332937
  have htrace : WordTrace (prefixWord ++ tailWord_5332937) baseStart_5332937 baseEnd_5332937 := by
    simpa [prefixWord, tailWord_5332937, baseEnd_5332937] using wordTrace_append hprefix tailTrace_5332937
  have hstable : (prefixWord ++ tailWord_5332937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5332937).length < 2 ^ (prefixWord ++ tailWord_5332937).sum := by decide
  have hdescent : baseEnd_5332937 < baseStart_5332937 := by decide
  rcases family_descends (prefixWord ++ tailWord_5332937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5332956 : List Nat := [2, 2, 6, 1, 2, 1, 2, 2, 1, 1, 3]
def baseStart_5332956 : Nat := 118140960795 + 5332956 * 2 ^ 59
def prefixEnd_5332956 : Nat := 4983230072969 + 3 ^ 40 * 5332956 * 2
def baseEnd_5332956 : Nat := 2738369737278942018824189

theorem tailTrace_5332956 : CollatzResearch.WordTrace tailWord_5332956 prefixEnd_5332956 2738369737278942018824189 := by
  unfold tailWord_5332956
  simp only [CollatzResearch.WordTrace]
  refine ⟨97254442433809341608853361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129672589911745788811804481 97254442433809341608853361)
  ·
    refine ⟨72940831825357006206640021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97254442433809341608853361 72940831825357006206640021)
    ·
      refine ⟨3419101491813609665936251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 72940831825357006206640021 3419101491813609665936251)
      ·
        refine ⟨5128652237720414498904377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3419101491813609665936251 5128652237720414498904377)
        ·
          refine ⟨3846489178290310874178283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5128652237720414498904377 3846489178290310874178283)
          ·
            refine ⟨5769733767435466311267425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3846489178290310874178283 5769733767435466311267425)
            ·
              refine ⟨4327300325576599733450569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5769733767435466311267425 4327300325576599733450569)
              ·
                refine ⟨3245475244182449800087927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4327300325576599733450569 3245475244182449800087927)
                ·
                  refine ⟨4868212866273674700131891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3245475244182449800087927 4868212866273674700131891)
                  ·
                    refine ⟨7302319299410512050197837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4868212866273674700131891 7302319299410512050197837)
                    ·
                      refine ⟨2738369737278942018824189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7302319299410512050197837 2738369737278942018824189)
                      ·
                        rfl

theorem cell23_5332956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 2, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 2, 1, 2, 2, 1, 1, 3].length) (baseStart_5332956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5332956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5332956 prefixEnd_5332956 := by exact prefixLift 5332956
  have htrace : WordTrace (prefixWord ++ tailWord_5332956) baseStart_5332956 baseEnd_5332956 := by
    simpa [prefixWord, tailWord_5332956, baseEnd_5332956] using wordTrace_append hprefix tailTrace_5332956
  have hstable : (prefixWord ++ tailWord_5332956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5332956).length < 2 ^ (prefixWord ++ tailWord_5332956).sum := by decide
  have hdescent : baseEnd_5332956 < baseStart_5332956 := by decide
  rcases family_descends (prefixWord ++ tailWord_5332956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5332960 : List Nat := [2, 1, 1, 3, 1, 1, 1, 2, 3, 8]
def baseStart_5332960 : Nat := 118140960795 + 5332960 * 2 ^ 59
def prefixEnd_5332960 : Nat := 4983230072969 + 3 ^ 40 * 5332960 * 2
def baseEnd_5332960 : Nat := 912790597067186667724723

theorem tailTrace_5332960 : CollatzResearch.WordTrace tailWord_5332960 prefixEnd_5332960 912790597067186667724723 := by
  unfold tailWord_5332960
  simp only [CollatzResearch.WordTrace]
  refine ⟨97254515379802095950426167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129672687173069461267234889 97254515379802095950426167)
  ·
    refine ⟨145881773069703143925639251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97254515379802095950426167 145881773069703143925639251)
    ·
      refine ⟨218822659604554715888458877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145881773069703143925639251 218822659604554715888458877)
      ·
        refine ⟨82058497351708018458172079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 218822659604554715888458877 82058497351708018458172079)
        ·
          refine ⟨123087746027562027687258119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82058497351708018458172079 123087746027562027687258119)
          ·
            refine ⟨184631619041343041530887179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 123087746027562027687258119 184631619041343041530887179)
            ·
              refine ⟨276947428562014562296330769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 184631619041343041530887179 276947428562014562296330769)
              ·
                refine ⟨207710571421510921722248077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 276947428562014562296330769 207710571421510921722248077)
                ·
                  refine ⟨77891464283066595645843029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 207710571421510921722248077 77891464283066595645843029)
                  ·
                    refine ⟨912790597067186667724723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 77891464283066595645843029 912790597067186667724723)
                    ·
                      rfl

theorem cell23_5332960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 2, 3, 8].length) (baseStart_5332960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5332960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5332960 prefixEnd_5332960 := by exact prefixLift 5332960
  have htrace : WordTrace (prefixWord ++ tailWord_5332960) baseStart_5332960 baseEnd_5332960 := by
    simpa [prefixWord, tailWord_5332960, baseEnd_5332960] using wordTrace_append hprefix tailTrace_5332960
  have hstable : (prefixWord ++ tailWord_5332960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5332960).length < 2 ^ (prefixWord ++ tailWord_5332960).sum := by decide
  have hdescent : baseEnd_5332960 < baseStart_5332960 := by decide
  rcases family_descends (prefixWord ++ tailWord_5332960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5332962 : List Nat := [3, 3, 3, 1, 2, 1, 1, 4, 1, 2, 2]
def baseStart_5332962 : Nat := 118140960795 + 5332962 * 2 ^ 59
def prefixEnd_5332962 : Nat := 4983230072969 + 3 ^ 40 * 5332962 * 2
def baseEnd_5332962 : Nat := 2738372818162868995349161

theorem tailTrace_5332962 : CollatzResearch.WordTrace tailWord_5332962 prefixEnd_5332962 2738372818162868995349161 := by
  unfold tailWord_5332962
  simp only [CollatzResearch.WordTrace]
  refine ⟨48627275926399236560606285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129672735803731297494950093 48627275926399236560606285)
  ·
    refine ⟨18235228472399713710227357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48627275926399236560606285 18235228472399713710227357)
    ·
      refine ⟨6838210677149892641335259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18235228472399713710227357 6838210677149892641335259)
      ·
        refine ⟨10257316015724838962002889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6838210677149892641335259 10257316015724838962002889)
        ·
          refine ⟨7692987011793629221502167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10257316015724838962002889 7692987011793629221502167)
          ·
            refine ⟨11539480517690443832253251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7692987011793629221502167 11539480517690443832253251)
            ·
              refine ⟨17309220776535665748379877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11539480517690443832253251 17309220776535665748379877)
              ·
                refine ⟨3245478895600437327821227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17309220776535665748379877 3245478895600437327821227)
                ·
                  refine ⟨4868218343400655991731841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3245478895600437327821227 4868218343400655991731841)
                  ·
                    refine ⟨3651163757550491993798881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4868218343400655991731841 3651163757550491993798881)
                    ·
                      refine ⟨2738372818162868995349161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3651163757550491993798881 2738372818162868995349161)
                      ·
                        rfl

theorem cell23_5332962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 1, 4, 1, 2, 2].length) (baseStart_5332962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5332962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5332962 prefixEnd_5332962 := by exact prefixLift 5332962
  have htrace : WordTrace (prefixWord ++ tailWord_5332962) baseStart_5332962 baseEnd_5332962 := by
    simpa [prefixWord, tailWord_5332962, baseEnd_5332962] using wordTrace_append hprefix tailTrace_5332962
  have hstable : (prefixWord ++ tailWord_5332962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5332962).length < 2 ^ (prefixWord ++ tailWord_5332962).sum := by decide
  have hdescent : baseEnd_5332962 < baseStart_5332962 := by decide
  rcases family_descends (prefixWord ++ tailWord_5332962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5332984 : List Nat := [2, 1, 2, 1, 1, 3, 3, 3, 1, 4, 2]
def baseStart_5332984 : Nat := 118140960795 + 5332984 * 2 ^ 59
def prefixEnd_5332984 : Nat := 4983230072969 + 3 ^ 40 * 5332984 * 2
def baseEnd_5332984 : Nat := 2738384114737267909274059

theorem tailTrace_5332984 : CollatzResearch.WordTrace tailWord_5332984 prefixEnd_5332984 2738384114737267909274059 := by
  unfold tailWord_5332984
  simp only [CollatzResearch.WordTrace]
  refine ⟨97254953055758621999863003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129673270741011495999817337 97254953055758621999863003)
  ·
    refine ⟨145882429583637932999794505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97254953055758621999863003 145882429583637932999794505)
    ·
      refine ⟨109411822187728449749845879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 145882429583637932999794505 109411822187728449749845879)
      ·
        refine ⟨164117733281592674624768819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109411822187728449749845879 164117733281592674624768819)
        ·
          refine ⟨246176599922389011937153229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 164117733281592674624768819 246176599922389011937153229)
          ·
            refine ⟨92316224970895879476432461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 246176599922389011937153229 92316224970895879476432461)
            ·
              refine ⟨34618584364085954803662173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 92316224970895879476432461 34618584364085954803662173)
              ·
                refine ⟨12981969136532233051373315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34618584364085954803662173 12981969136532233051373315)
                ·
                  refine ⟨19472953704798349577059973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12981969136532233051373315 19472953704798349577059973)
                  ·
                    refine ⟨3651178819649690545698745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19472953704798349577059973 3651178819649690545698745)
                    ·
                      refine ⟨2738384114737267909274059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3651178819649690545698745 2738384114737267909274059)
                      ·
                        rfl

theorem cell23_5332984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 3, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 3, 3, 1, 4, 2].length) (baseStart_5332984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5332984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5332984 prefixEnd_5332984 := by exact prefixLift 5332984
  have htrace : WordTrace (prefixWord ++ tailWord_5332984) baseStart_5332984 baseEnd_5332984 := by
    simpa [prefixWord, tailWord_5332984, baseEnd_5332984] using wordTrace_append hprefix tailTrace_5332984
  have hstable : (prefixWord ++ tailWord_5332984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5332984).length < 2 ^ (prefixWord ++ tailWord_5332984).sum := by decide
  have hdescent : baseEnd_5332984 < baseStart_5332984 := by decide
  rcases family_descends (prefixWord ++ tailWord_5332984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5333012 : List Nat := [2, 4, 3, 2, 1, 2, 1, 2, 2, 1, 3]
def baseStart_5333012 : Nat := 118140960795 + 5333012 * 2 ^ 59
def prefixEnd_5333012 : Nat := 4983230072969 + 3 ^ 40 * 5333012 * 2
def baseEnd_5333012 : Nat := 2738398492195593799723931

theorem tailTrace_5333012 : CollatzResearch.WordTrace tailWord_5333012 prefixEnd_5333012 2738398492195593799723931 := by
  unfold tailWord_5333012
  simp only [CollatzResearch.WordTrace]
  refine ⟨97255463677707902390872645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129673951570277203187830193 97255463677707902390872645)
  ·
    refine ⟨18235399439570231698288621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 97255463677707902390872645 18235399439570231698288621)
    ·
      refine ⟨6838274789838836886858233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18235399439570231698288621 6838274789838836886858233)
      ·
        refine ⟨5128706092379127665143675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6838274789838836886858233 5128706092379127665143675)
        ·
          refine ⟨7693059138568691497715513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5128706092379127665143675 7693059138568691497715513)
          ·
            refine ⟨5769794353926518623286635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7693059138568691497715513 5769794353926518623286635)
            ·
              refine ⟨8654691530889777934929953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5769794353926518623286635 8654691530889777934929953)
              ·
                refine ⟨6491018648167333451197465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8654691530889777934929953 6491018648167333451197465)
                ·
                  refine ⟨4868263986125500088398099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6491018648167333451197465 4868263986125500088398099)
                  ·
                    refine ⟨7302395979188250132597149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4868263986125500088398099 7302395979188250132597149)
                    ·
                      refine ⟨2738398492195593799723931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7302395979188250132597149 2738398492195593799723931)
                      ·
                        rfl

theorem cell23_5333012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 2, 1, 2, 2, 1, 3].length) (baseStart_5333012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5333012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5333012 prefixEnd_5333012 := by exact prefixLift 5333012
  have htrace : WordTrace (prefixWord ++ tailWord_5333012) baseStart_5333012 baseEnd_5333012 := by
    simpa [prefixWord, tailWord_5333012, baseEnd_5333012] using wordTrace_append hprefix tailTrace_5333012
  have hstable : (prefixWord ++ tailWord_5333012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5333012).length < 2 ^ (prefixWord ++ tailWord_5333012).sum := by decide
  have hdescent : baseEnd_5333012 < baseStart_5333012 := by decide
  rcases family_descends (prefixWord ++ tailWord_5333012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5333018 : List Nat := [3, 1, 1, 3, 1, 3, 3, 2, 2, 2, 2]
def baseStart_5333018 : Nat := 118140960795 + 5333018 * 2 ^ 59
def prefixEnd_5333018 : Nat := 4983230072969 + 3 ^ 40 * 5333018 * 2
def baseEnd_5333018 : Nat := 2738401573079520776248903

theorem tailTrace_5333018 : CollatzResearch.WordTrace tailWord_5333018 prefixEnd_5333018 2738401573079520776248903 := by
  unfold tailWord_5333018
  simp only [CollatzResearch.WordTrace]
  refine ⟨48627786548348516951615927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129674097462262711870975805 48627786548348516951615927)
  ·
    refine ⟨72941679822522775427423891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48627786548348516951615927 72941679822522775427423891)
    ·
      refine ⟨109412519733784163141135837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72941679822522775427423891 109412519733784163141135837)
      ·
        refine ⟨41029694900169061177925939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 109412519733784163141135837 41029694900169061177925939)
        ·
          refine ⟨61544542350253591766888909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41029694900169061177925939 61544542350253591766888909)
          ·
            refine ⟨23079203381345096912583341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 61544542350253591766888909 23079203381345096912583341)
            ·
              refine ⟨8654701268004411342218753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23079203381345096912583341 8654701268004411342218753)
              ·
                refine ⟨6491025951003308506664065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8654701268004411342218753 6491025951003308506664065)
                ·
                  refine ⟨4868269463252481379998049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6491025951003308506664065 4868269463252481379998049)
                  ·
                    refine ⟨3651202097439361034998537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4868269463252481379998049 3651202097439361034998537)
                    ·
                      refine ⟨2738401573079520776248903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3651202097439361034998537 2738401573079520776248903)
                      ·
                        rfl

theorem cell23_5333018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 3, 2, 2, 2, 2].length) (baseStart_5333018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5333018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5333018 prefixEnd_5333018 := by exact prefixLift 5333018
  have htrace : WordTrace (prefixWord ++ tailWord_5333018) baseStart_5333018 baseEnd_5333018 := by
    simpa [prefixWord, tailWord_5333018, baseEnd_5333018] using wordTrace_append hprefix tailTrace_5333018
  have hstable : (prefixWord ++ tailWord_5333018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5333018).length < 2 ^ (prefixWord ++ tailWord_5333018).sum := by decide
  have hdescent : baseEnd_5333018 < baseStart_5333018 := by decide
  rcases family_descends (prefixWord ++ tailWord_5333018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5333086 : List Nat := [4, 4, 1, 1, 2, 2, 2, 1, 2, 2, 2]
def baseStart_5333086 : Nat := 118140960795 + 5333086 * 2 ^ 59
def prefixEnd_5333086 : Nat := 4983230072969 + 3 ^ 40 * 5333086 * 2
def baseEnd_5333086 : Nat := 2738436489764026510198591

theorem tailTrace_5333086 : CollatzResearch.WordTrace tailWord_5333086 prefixEnd_5333086 2738436489764026510198591 := by
  unfold tailWord_5333086
  simp only [CollatzResearch.WordTrace]
  refine ⟨24314203294643464427492389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 129675750904765143613292741 24314203294643464427492389)
  ·
    refine ⟨4558913117745649580154823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24314203294643464427492389 4558913117745649580154823)
    ·
      refine ⟨6838369676618474370232235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4558913117745649580154823 6838369676618474370232235)
      ·
        refine ⟨10257554514927711555348353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6838369676618474370232235 10257554514927711555348353)
        ·
          refine ⟨7693165886195783666511265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10257554514927711555348353 7693165886195783666511265)
          ·
            refine ⟨5769874414646837749883449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7693165886195783666511265 5769874414646837749883449)
            ·
              refine ⟨4327405810985128312412587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5769874414646837749883449 4327405810985128312412587)
              ·
                refine ⟨6491108716477692468618881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4327405810985128312412587 6491108716477692468618881)
                ·
                  refine ⟨4868331537358269351464161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6491108716477692468618881 4868331537358269351464161)
                  ·
                    refine ⟨3651248653018702013598121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4868331537358269351464161 3651248653018702013598121)
                    ·
                      refine ⟨2738436489764026510198591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3651248653018702013598121 2738436489764026510198591)
                      ·
                        rfl

theorem cell23_5333086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 2, 2, 1, 2, 2, 2].length) (baseStart_5333086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5333086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5333086 prefixEnd_5333086 := by exact prefixLift 5333086
  have htrace : WordTrace (prefixWord ++ tailWord_5333086) baseStart_5333086 baseEnd_5333086 := by
    simpa [prefixWord, tailWord_5333086, baseEnd_5333086] using wordTrace_append hprefix tailTrace_5333086
  have hstable : (prefixWord ++ tailWord_5333086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5333086).length < 2 ^ (prefixWord ++ tailWord_5333086).sum := by decide
  have hdescent : baseEnd_5333086 < baseStart_5333086 := by decide
  rcases family_descends (prefixWord ++ tailWord_5333086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5333087 : List Nat := [1, 1, 2, 3, 1, 1, 2, 2, 2, 4, 4]
def baseStart_5333087 : Nat := 118140960795 + 5333087 * 2 ^ 59
def prefixEnd_5333087 : Nat := 4983230072969 + 3 ^ 40 * 5333087 * 2
def baseEnd_5333087 : Nat := 2738437003244681006286085

theorem tailTrace_5333087 : CollatzResearch.WordTrace tailWord_5333087 prefixEnd_5333087 2738437003244681006286085 := by
  unfold tailWord_5333087
  simp only [CollatzResearch.WordTrace]
  refine ⟨194513662830144092590725515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129675775220096061727150343 194513662830144092590725515)
  ·
    refine ⟨291770494245216138886088273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194513662830144092590725515 291770494245216138886088273)
    ·
      refine ⟨218827870683912104164566205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 291770494245216138886088273 218827870683912104164566205)
      ·
        refine ⟨82060451506467039061712327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 218827870683912104164566205 82060451506467039061712327)
        ·
          refine ⟨123090677259700558592568491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82060451506467039061712327 123090677259700558592568491)
          ·
            refine ⟨184636015889550837888852737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 123090677259700558592568491 184636015889550837888852737)
            ·
              refine ⟨138477011917163128416639553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 184636015889550837888852737 138477011917163128416639553)
              ·
                refine ⟨103857758937872346312479665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 138477011917163128416639553 103857758937872346312479665)
                ·
                  refine ⟨77893319203404259734359749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 103857758937872346312479665 77893319203404259734359749)
                  ·
                    refine ⟨14604997350638298700192453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 77893319203404259734359749 14604997350638298700192453)
                    ·
                      refine ⟨2738437003244681006286085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14604997350638298700192453 2738437003244681006286085)
                      ·
                        rfl

theorem cell23_5333087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 2, 2, 4, 4].length) (baseStart_5333087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5333087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5333087 prefixEnd_5333087 := by exact prefixLift 5333087
  have htrace : WordTrace (prefixWord ++ tailWord_5333087) baseStart_5333087 baseEnd_5333087 := by
    simpa [prefixWord, tailWord_5333087, baseEnd_5333087] using wordTrace_append hprefix tailTrace_5333087
  have hstable : (prefixWord ++ tailWord_5333087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5333087).length < 2 ^ (prefixWord ++ tailWord_5333087).sum := by decide
  have hdescent : baseEnd_5333087 < baseStart_5333087 := by decide
  rcases family_descends (prefixWord ++ tailWord_5333087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5333111 : List Nat := [1, 1, 3, 1, 1, 6, 2, 1, 2, 2, 3]
def baseStart_5333111 : Nat := 118140960795 + 5333111 * 2 ^ 59
def prefixEnd_5333111 : Nat := 4983230072969 + 3 ^ 40 * 5333111 * 2
def baseEnd_5333111 : Nat := 2738449326780388912385975

theorem tailTrace_5333111 : CollatzResearch.WordTrace tailWord_5333111 prefixEnd_5333111 2738449326780388912385975 := by
  unfold tailWord_5333111
  simp only [CollatzResearch.WordTrace]
  refine ⟨194514538182057144689599187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129676358788038096459732791 194514538182057144689599187)
  ·
    refine ⟨291771807273085717034398781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194514538182057144689599187 291771807273085717034398781)
    ·
      refine ⟨109414427727407143887899543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 291771807273085717034398781 109414427727407143887899543)
      ·
        refine ⟨164121641591110715831849315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109414427727407143887899543 164121641591110715831849315)
        ·
          refine ⟨246182462386666073747773973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 164121641591110715831849315 246182462386666073747773973)
          ·
            refine ⟨11539802924374972206926905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 246182462386666073747773973 11539802924374972206926905)
            ·
              refine ⟨8654852193281229155195179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11539802924374972206926905 8654852193281229155195179)
              ·
                refine ⟨12982278289921843732792769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8654852193281229155195179 12982278289921843732792769)
                ·
                  refine ⟨9736708717441382799594577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12982278289921843732792769 9736708717441382799594577)
                  ·
                    refine ⟨7302531538081037099695933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9736708717441382799594577 7302531538081037099695933)
                    ·
                      refine ⟨2738449326780388912385975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7302531538081037099695933 2738449326780388912385975)
                      ·
                        rfl

theorem cell23_5333111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 2, 1, 2, 2, 3].length) (baseStart_5333111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5333111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5333111 prefixEnd_5333111 := by exact prefixLift 5333111
  have htrace : WordTrace (prefixWord ++ tailWord_5333111) baseStart_5333111 baseEnd_5333111 := by
    simpa [prefixWord, tailWord_5333111, baseEnd_5333111] using wordTrace_append hprefix tailTrace_5333111
  have hstable : (prefixWord ++ tailWord_5333111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5333111).length < 2 ^ (prefixWord ++ tailWord_5333111).sum := by decide
  have hdescent : baseEnd_5333111 < baseStart_5333111 := by decide
  rcases family_descends (prefixWord ++ tailWord_5333111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5333137 : List Nat := [1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 5]
def baseStart_5333137 : Nat := 118140960795 + 5333137 * 2 ^ 59
def prefixEnd_5333137 : Nat := 4983230072969 + 3 ^ 40 * 5333137 * 2
def baseEnd_5333137 : Nat := 2738462677277405810660855

theorem tailTrace_5333137 : CollatzResearch.WordTrace tailWord_5333137 prefixEnd_5333137 2738462677277405810660855 := by
  unfold tailWord_5333137
  simp only [CollatzResearch.WordTrace]
  refine ⟨194515486479962951130045665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129676990986641967420030443 194515486479962951130045665)
  ·
    refine ⟨145886614859972213347534249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 194515486479962951130045665 145886614859972213347534249)
    ·
      refine ⟨109414961144979160010650687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 145886614859972213347534249 109414961144979160010650687)
      ·
        refine ⟨164122441717468740015976031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109414961144979160010650687 164122441717468740015976031)
        ·
          refine ⟨246183662576203110023964047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 164122441717468740015976031 246183662576203110023964047)
          ·
            refine ⟨369275493864304665035946071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 246183662576203110023964047 369275493864304665035946071)
            ·
              refine ⟨553913240796456997553919107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 369275493864304665035946071 553913240796456997553919107)
              ·
                refine ⟨830869861194685496330878661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 553913240796456997553919107 830869861194685496330878661)
                ·
                  refine ⟨155788098974003530562039749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 830869861194685496330878661 155788098974003530562039749)
                  ·
                    refine ⟨29210268557625661980382453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 155788098974003530562039749 29210268557625661980382453)
                    ·
                      refine ⟨2738462677277405810660855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29210268557625661980382453 2738462677277405810660855)
                      ·
                        rfl

theorem cell23_5333137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 5].length) (baseStart_5333137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5333137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5333137 prefixEnd_5333137 := by exact prefixLift 5333137
  have htrace : WordTrace (prefixWord ++ tailWord_5333137) baseStart_5333137 baseEnd_5333137 := by
    simpa [prefixWord, tailWord_5333137, baseEnd_5333137] using wordTrace_append hprefix tailTrace_5333137
  have hstable : (prefixWord ++ tailWord_5333137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5333137).length < 2 ^ (prefixWord ++ tailWord_5333137).sum := by decide
  have hdescent : baseEnd_5333137 < baseStart_5333137 := by decide
  rcases family_descends (prefixWord ++ tailWord_5333137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5333141 : List Nat := [1, 3, 2, 1, 1, 1, 4, 3, 3, 1, 3]
def baseStart_5333141 : Nat := 118140960795 + 5333141 * 2 ^ 59
def prefixEnd_5333141 : Nat := 4983230072969 + 3 ^ 40 * 5333141 * 2
def baseEnd_5333141 : Nat := 2738464731200023795010837

theorem tailTrace_5333141 : CollatzResearch.WordTrace tailWord_5333141 prefixEnd_5333141 2738464731200023795010837 := by
  unfold tailWord_5333141
  simp only [CollatzResearch.WordTrace]
  refine ⟨194515632371948459813191277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129677088247965639875460851 194515632371948459813191277)
  ·
    refine ⟨72943362139480672429946729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 194515632371948459813191277 72943362139480672429946729)
    ·
      refine ⟨54707521604610504322460047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72943362139480672429946729 54707521604610504322460047)
      ·
        refine ⟨82061282406915756483690071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54707521604610504322460047 82061282406915756483690071)
        ·
          refine ⟨123091923610373634725535107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82061282406915756483690071 123091923610373634725535107)
          ·
            refine ⟨184637885415560452088302661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 123091923610373634725535107 184637885415560452088302661)
            ·
              refine ⟨34619603515417584766556749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 184637885415560452088302661 34619603515417584766556749)
              ·
                refine ⟨12982351318281594287458781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34619603515417584766556749 12982351318281594287458781)
                ·
                  refine ⟨4868381744355597857797043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12982351318281594287458781 4868381744355597857797043)
                  ·
                    refine ⟨7302572616533396786695565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4868381744355597857797043 7302572616533396786695565)
                    ·
                      refine ⟨2738464731200023795010837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7302572616533396786695565 2738464731200023795010837)
                      ·
                        rfl

theorem cell23_5333141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 4, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 4, 3, 3, 1, 3].length) (baseStart_5333141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5333141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5333141 prefixEnd_5333141 := by exact prefixLift 5333141
  have htrace : WordTrace (prefixWord ++ tailWord_5333141) baseStart_5333141 baseEnd_5333141 := by
    simpa [prefixWord, tailWord_5333141, baseEnd_5333141] using wordTrace_append hprefix tailTrace_5333141
  have hstable : (prefixWord ++ tailWord_5333141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5333141).length < 2 ^ (prefixWord ++ tailWord_5333141).sum := by decide
  have hdescent : baseEnd_5333141 < baseStart_5333141 := by decide
  rcases family_descends (prefixWord ++ tailWord_5333141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5333162 : List Nat := [3, 1, 5, 1, 3, 1, 1, 1, 2, 2, 3]
def baseStart_5333162 : Nat := 118140960795 + 5333162 * 2 ^ 59
def prefixEnd_5333162 : Nat := 4983230072969 + 3 ^ 40 * 5333162 * 2
def baseEnd_5333162 : Nat := 2738475514293768212848241

theorem tailTrace_5333162 : CollatzResearch.WordTrace tailWord_5333162 prefixEnd_5333162 2738475514293768212848241 := by
  unfold tailWord_5333162
  simp only [CollatzResearch.WordTrace]
  refine ⟨48629099576218095099926435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129677598869914920266470493 48629099576218095099926435)
  ·
    refine ⟨72943649364327142649889653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48629099576218095099926435 72943649364327142649889653)
    ·
      refine ⟨6838467127905669623427155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 72943649364327142649889653 6838467127905669623427155)
      ·
        refine ⟨10257700691858504435140733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6838467127905669623427155 10257700691858504435140733)
        ·
          refine ⟨3846637759446939163177775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10257700691858504435140733 3846637759446939163177775)
          ·
            refine ⟨5769956639170408744766663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3846637759446939163177775 5769956639170408744766663)
            ·
              refine ⟨8654934958755613117149995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5769956639170408744766663 8654934958755613117149995)
              ·
                refine ⟨12982402438133419675724993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8654934958755613117149995 12982402438133419675724993)
                ·
                  refine ⟨9736801828600064756793745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12982402438133419675724993 9736801828600064756793745)
                  ·
                    refine ⟨7302601371450048567595309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9736801828600064756793745 7302601371450048567595309)
                    ·
                      refine ⟨2738475514293768212848241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7302601371450048567595309 2738475514293768212848241)
                      ·
                        rfl

theorem cell23_5333162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 3, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 3, 1, 1, 1, 2, 2, 3].length) (baseStart_5333162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5333162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5333162 prefixEnd_5333162 := by exact prefixLift 5333162
  have htrace : WordTrace (prefixWord ++ tailWord_5333162) baseStart_5333162 baseEnd_5333162 := by
    simpa [prefixWord, tailWord_5333162, baseEnd_5333162] using wordTrace_append hprefix tailTrace_5333162
  have hstable : (prefixWord ++ tailWord_5333162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5333162).length < 2 ^ (prefixWord ++ tailWord_5333162).sum := by decide
  have hdescent : baseEnd_5333162 < baseStart_5333162 := by decide
  rcases family_descends (prefixWord ++ tailWord_5333162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5333175 : List Nat := [1, 1, 3, 1, 4, 3, 2, 3, 1, 1, 3]
def baseStart_5333175 : Nat := 118140960795 + 5333175 * 2 ^ 59
def prefixEnd_5333175 : Nat := 4983230072969 + 3 ^ 40 * 5333175 * 2
def baseEnd_5333175 : Nat := 2738482189542276661985681

theorem tailTrace_5333175 : CollatzResearch.WordTrace tailWord_5333175 prefixEnd_5333175 2738482189542276661985681 := by
  unfold tailWord_5333175
  simp only [CollatzResearch.WordTrace]
  refine ⟨194516872453825283619928979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129677914969216855746619319 194516872453825283619928979)
  ·
    refine ⟨291775308680737925429893469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194516872453825283619928979 291775308680737925429893469)
    ·
      refine ⟨109415740755276722036210051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 291775308680737925429893469 109415740755276722036210051)
      ·
        refine ⟨164123611132915083054315077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109415740755276722036210051 164123611132915083054315077)
        ·
          refine ⟨30773177087421578072684077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 164123611132915083054315077 30773177087421578072684077)
          ·
            refine ⟨11539941407783091777256529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30773177087421578072684077 11539941407783091777256529)
            ·
              refine ⟨8654956055837318832942397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11539941407783091777256529 8654956055837318832942397)
              ·
                refine ⟨3245608520938994562353399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8654956055837318832942397 3245608520938994562353399)
                ·
                  refine ⟨4868412781408491843530099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3245608520938994562353399 4868412781408491843530099)
                  ·
                    refine ⟨7302619172112737765295149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4868412781408491843530099 7302619172112737765295149)
                    ·
                      refine ⟨2738482189542276661985681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7302619172112737765295149 2738482189542276661985681)
                      ·
                        rfl

theorem cell23_5333175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 2, 3, 1, 1, 3].length) (baseStart_5333175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5333175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5333175 prefixEnd_5333175 := by exact prefixLift 5333175
  have htrace : WordTrace (prefixWord ++ tailWord_5333175) baseStart_5333175 baseEnd_5333175 := by
    simpa [prefixWord, tailWord_5333175, baseEnd_5333175] using wordTrace_append hprefix tailTrace_5333175
  have hstable : (prefixWord ++ tailWord_5333175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5333175).length < 2 ^ (prefixWord ++ tailWord_5333175).sum := by decide
  have hdescent : baseEnd_5333175 < baseStart_5333175 := by decide
  rcases family_descends (prefixWord ++ tailWord_5333175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5333194 : List Nat := [3, 1, 2, 1, 3, 1, 2, 2, 1, 1, 6]
def baseStart_5333194 : Nat := 118140960795 + 5333194 * 2 ^ 59
def prefixEnd_5333194 : Nat := 4983230072969 + 3 ^ 40 * 5333194 * 2
def baseEnd_5333194 : Nat := 2738491945674712087648093

theorem tailTrace_5333194 : CollatzResearch.WordTrace tailWord_5333194 prefixEnd_5333194 2738491945674712087648093 := by
  unfold tailWord_5333194
  simp only [CollatzResearch.WordTrace]
  refine ⟨48629391360189112466217659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129678376960504299909913757 48629391360189112466217659)
  ·
    refine ⟨72944087040283668699326489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48629391360189112466217659 72944087040283668699326489)
    ·
      refine ⟨54708065280212751524494867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72944087040283668699326489 54708065280212751524494867)
      ·
        refine ⟨82062097920319127286742301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54708065280212751524494867 82062097920319127286742301)
        ·
          refine ⟨30773286720119672732528363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 82062097920319127286742301 30773286720119672732528363)
          ·
            refine ⟨46159930080179509098792545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30773286720119672732528363 46159930080179509098792545)
            ·
              refine ⟨34619947560134631824094409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46159930080179509098792545 34619947560134631824094409)
              ·
                refine ⟨25964960670100973868070807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34619947560134631824094409 25964960670100973868070807)
                ·
                  refine ⟨38947441005151460802106211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25964960670100973868070807 38947441005151460802106211)
                  ·
                    refine ⟨58421161507727191203159317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 38947441005151460802106211 58421161507727191203159317)
                    ·
                      refine ⟨2738491945674712087648093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 58421161507727191203159317 2738491945674712087648093)
                      ·
                        rfl

theorem cell23_5333194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 2, 2, 1, 1, 6].length) (baseStart_5333194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5333194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5333194 prefixEnd_5333194 := by exact prefixLift 5333194
  have htrace : WordTrace (prefixWord ++ tailWord_5333194) baseStart_5333194 baseEnd_5333194 := by
    simpa [prefixWord, tailWord_5333194, baseEnd_5333194] using wordTrace_append hprefix tailTrace_5333194
  have hstable : (prefixWord ++ tailWord_5333194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5333194).length < 2 ^ (prefixWord ++ tailWord_5333194).sum := by decide
  have hdescent : baseEnd_5333194 < baseStart_5333194 := by decide
  rcases family_descends (prefixWord ++ tailWord_5333194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5333221 : List Nat := [1, 3, 1, 4, 2, 1, 4, 7]
def baseStart_5333221 : Nat := 118140960795 + 5333221 * 2 ^ 59
def prefixEnd_5333221 : Nat := 4983230072969 + 3 ^ 40 * 5333221 * 2
def baseEnd_5333221 : Nat := 101426141098236425259647

theorem tailTrace_5333221 : CollatzResearch.WordTrace tailWord_5333221 prefixEnd_5333221 101426141098236425259647 := by
  unfold tailWord_5333221
  simp only [CollatzResearch.WordTrace]
  refine ⟨194518550211658633476103517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129679033474439088984069011 194518550211658633476103517)
  ·
    refine ⟨72944456329371987553538819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 194518550211658633476103517 72944456329371987553538819)
    ·
      refine ⟨109416684494057981330308229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72944456329371987553538819 109416684494057981330308229)
      ·
        refine ⟨20515628342635871499432793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 109416684494057981330308229 20515628342635871499432793)
        ·
          refine ⟨15386721256976903624574595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20515628342635871499432793 15386721256976903624574595)
          ·
            refine ⟨23080081885465355436861893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15386721256976903624574595 23080081885465355436861893)
            ·
              refine ⟨4327515353524754144411605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23080081885465355436861893 4327515353524754144411605)
              ·
                refine ⟨101426141098236425259647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4327515353524754144411605 101426141098236425259647)
                ·
                  rfl

theorem cell23_5333221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 4, 7].length) (baseStart_5333221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5333221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5333221 prefixEnd_5333221 := by exact prefixLift 5333221
  have htrace : WordTrace (prefixWord ++ tailWord_5333221) baseStart_5333221 baseEnd_5333221 := by
    simpa [prefixWord, tailWord_5333221, baseEnd_5333221] using wordTrace_append hprefix tailTrace_5333221
  have hstable : (prefixWord ++ tailWord_5333221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5333221).length < 2 ^ (prefixWord ++ tailWord_5333221).sum := by decide
  have hdescent : baseEnd_5333221 < baseStart_5333221 := by decide
  rcases family_descends (prefixWord ++ tailWord_5333221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5333265 : List Nat := [1, 2, 2, 1, 1, 5, 4, 1, 2, 1, 3]
def baseStart_5333265 : Nat := 118140960795 + 5333265 * 2 ^ 59
def prefixEnd_5333265 : Nat := 4983230072969 + 3 ^ 40 * 5333265 * 2
def baseEnd_5333265 : Nat := 2738528402801181309860267

theorem tailTrace_5333265 : CollatzResearch.WordTrace tailWord_5333265 prefixEnd_5333265 2738528402801181309860267 := by
  unfold tailWord_5333265
  simp only [CollatzResearch.WordTrace]
  refine ⟨194520155023499228990705249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129680103348999485993803499 194520155023499228990705249)
  ·
    refine ⟨145890116267624421743028937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 194520155023499228990705249 145890116267624421743028937)
    ·
      refine ⟨109417587200718316307271703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 145890116267624421743028937 109417587200718316307271703)
      ·
        refine ⟨164126380801077474460907555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109417587200718316307271703 164126380801077474460907555)
        ·
          refine ⟨246189571201616211691361333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 164126380801077474460907555 246189571201616211691361333)
          ·
            refine ⟨23080272300151519846065125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 246189571201616211691361333 23080272300151519846065125)
            ·
              refine ⟨4327551056278409971137211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23080272300151519846065125 4327551056278409971137211)
              ·
                refine ⟨6491326584417614956705817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4327551056278409971137211 6491326584417614956705817)
                ·
                  refine ⟨4868494938313211217529363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6491326584417614956705817 4868494938313211217529363)
                  ·
                    refine ⟨7302742407469816826294045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4868494938313211217529363 7302742407469816826294045)
                    ·
                      refine ⟨2738528402801181309860267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7302742407469816826294045 2738528402801181309860267)
                      ·
                        rfl

theorem cell23_5333265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 4, 1, 2, 1, 3].length) (baseStart_5333265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5333265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5333265 prefixEnd_5333265 := by exact prefixLift 5333265
  have htrace : WordTrace (prefixWord ++ tailWord_5333265) baseStart_5333265 baseEnd_5333265 := by
    simpa [prefixWord, tailWord_5333265, baseEnd_5333265] using wordTrace_append hprefix tailTrace_5333265
  have hstable : (prefixWord ++ tailWord_5333265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5333265).length < 2 ^ (prefixWord ++ tailWord_5333265).sum := by decide
  have hdescent : baseEnd_5333265 < baseStart_5333265 := by decide
  rcases family_descends (prefixWord ++ tailWord_5333265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5333301 : List Nat := [1, 3, 3, 1, 2, 1, 2, 2, 2, 2, 4]
def baseStart_5333301 : Nat := 118140960795 + 5333301 * 2 ^ 59
def prefixEnd_5333301 : Nat := 4983230072969 + 3 ^ 40 * 5333301 * 2
def baseEnd_5333301 : Nat := 2738546888104743169010101

theorem tailTrace_5333301 : CollatzResearch.WordTrace tailWord_5333301 prefixEnd_5333301 2738546888104743169010101 := by
  unfold tailWord_5333301
  simp only [CollatzResearch.WordTrace]
  refine ⟨194521468051368807139015757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129680978700912538092677171 194521468051368807139015757)
  ·
    refine ⟨72945550519263302677130909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 194521468051368807139015757 72945550519263302677130909)
    ·
      refine ⟨27354581444723738503924091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72945550519263302677130909 27354581444723738503924091)
      ·
        refine ⟨41031872167085607755886137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27354581444723738503924091 41031872167085607755886137)
        ·
          refine ⟨30773904125314205816914603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41031872167085607755886137 30773904125314205816914603)
          ·
            refine ⟨46160856187971308725371905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30773904125314205816914603 46160856187971308725371905)
            ·
              refine ⟨34620642140978481544028929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46160856187971308725371905 34620642140978481544028929)
              ·
                refine ⟨25965481605733861158021697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34620642140978481544028929 25965481605733861158021697)
                ·
                  refine ⟨19474111204300395868516273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25965481605733861158021697 19474111204300395868516273)
                  ·
                    refine ⟨14605583403225296901387205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19474111204300395868516273 14605583403225296901387205)
                    ·
                      refine ⟨2738546888104743169010101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14605583403225296901387205 2738546888104743169010101)
                      ·
                        rfl

theorem cell23_5333301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 2, 2, 2, 2, 4].length) (baseStart_5333301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5333301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5333301 prefixEnd_5333301 := by exact prefixLift 5333301
  have htrace : WordTrace (prefixWord ++ tailWord_5333301) baseStart_5333301 baseEnd_5333301 := by
    simpa [prefixWord, tailWord_5333301, baseEnd_5333301] using wordTrace_append hprefix tailTrace_5333301
  have hstable : (prefixWord ++ tailWord_5333301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5333301).length < 2 ^ (prefixWord ++ tailWord_5333301).sum := by decide
  have hdescent : baseEnd_5333301 < baseStart_5333301 := by decide
  rcases family_descends (prefixWord ++ tailWord_5333301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5333304 : List Nat := [2, 1, 2, 1, 3, 1, 2, 1, 1, 2, 7]
def baseStart_5333304 : Nat := 118140960795 + 5333304 * 2 ^ 59
def prefixEnd_5333304 : Nat := 4983230072969 + 3 ^ 40 * 5333304 * 2
def baseEnd_5333304 : Nat := 2738548428546706657272587

theorem tailTrace_5333304 : CollatzResearch.WordTrace tailWord_5333304 prefixEnd_5333304 2738548428546706657272587 := by
  unfold tailWord_5333304
  simp only [CollatzResearch.WordTrace]
  refine ⟨97260788735178969325687483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129681051646905292434249977 97260788735178969325687483)
  ·
    refine ⟨145891183102768453988531225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97260788735178969325687483 145891183102768453988531225)
    ·
      refine ⟨109418387327076340491398419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 145891183102768453988531225 109418387327076340491398419)
      ·
        refine ⟨164127580990614510737097629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109418387327076340491398419 164127580990614510737097629)
        ·
          refine ⟨61547842871480441526411611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 164127580990614510737097629 61547842871480441526411611)
          ·
            refine ⟨92321764307220662289617417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61547842871480441526411611 92321764307220662289617417)
            ·
              refine ⟨69241323230415496717213063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 92321764307220662289617417 69241323230415496717213063)
              ·
                refine ⟨103861984845623245075819595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 69241323230415496717213063 103861984845623245075819595)
                ·
                  refine ⟨155792977268434867613729393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 103861984845623245075819595 155792977268434867613729393)
                  ·
                    refine ⟨116844732951326150710297045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 155792977268434867613729393 116844732951326150710297045)
                    ·
                      refine ⟨2738548428546706657272587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 116844732951326150710297045 2738548428546706657272587)
                      ·
                        rfl

theorem cell23_5333304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 1, 1, 2, 7].length) (baseStart_5333304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5333304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5333304 prefixEnd_5333304 := by exact prefixLift 5333304
  have htrace : WordTrace (prefixWord ++ tailWord_5333304) baseStart_5333304 baseEnd_5333304 := by
    simpa [prefixWord, tailWord_5333304, baseEnd_5333304] using wordTrace_append hprefix tailTrace_5333304
  have hstable : (prefixWord ++ tailWord_5333304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5333304).length < 2 ^ (prefixWord ++ tailWord_5333304).sum := by decide
  have hdescent : baseEnd_5333304 < baseStart_5333304 := by decide
  rcases family_descends (prefixWord ++ tailWord_5333304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5333361 : List Nat := [1, 2, 2, 2, 1, 2, 1, 3, 4, 1, 4]
def baseStart_5333361 : Nat := 118140960795 + 5333361 * 2 ^ 59
def prefixEnd_5333361 : Nat := 4983230072969 + 3 ^ 40 * 5333361 * 2
def baseEnd_5333361 : Nat := 2738577696944012934259825

theorem tailTrace_5333361 : CollatzResearch.WordTrace tailWord_5333361 prefixEnd_5333361 2738577696944012934259825 := by
  unfold tailWord_5333361
  simp only [CollatzResearch.WordTrace]
  refine ⟨194523656431151437386199937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129682437620767624924133291 194523656431151437386199937)
  ·
    refine ⟨145892742323363578039649953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 194523656431151437386199937 145892742323363578039649953)
    ·
      refine ⟨109419556742522683529737465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 145892742323363578039649953 109419556742522683529737465)
      ·
        refine ⟨82064667556892012647303099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 109419556742522683529737465 82064667556892012647303099)
        ·
          refine ⟨123097001335338018970954649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82064667556892012647303099 123097001335338018970954649)
          ·
            refine ⟨92322751001503514228215987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 123097001335338018970954649 92322751001503514228215987)
            ·
              refine ⟨138484126502255271342323981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 92322751001503514228215987 138484126502255271342323981)
              ·
                refine ⟨51931547438345726753371493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 138484126502255271342323981 51931547438345726753371493)
                ·
                  refine ⟨9737165144689823766257155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 51931547438345726753371493 9737165144689823766257155)
                  ·
                    refine ⟨14605747717034735649385733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9737165144689823766257155 14605747717034735649385733)
                    ·
                      refine ⟨2738577696944012934259825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14605747717034735649385733 2738577696944012934259825)
                      ·
                        rfl

theorem cell23_5333361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 3, 4, 1, 4].length) (baseStart_5333361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5333361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5333361 prefixEnd_5333361 := by exact prefixLift 5333361
  have htrace : WordTrace (prefixWord ++ tailWord_5333361) baseStart_5333361 baseEnd_5333361 := by
    simpa [prefixWord, tailWord_5333361, baseEnd_5333361] using wordTrace_append hprefix tailTrace_5333361
  have hstable : (prefixWord ++ tailWord_5333361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5333361).length < 2 ^ (prefixWord ++ tailWord_5333361).sum := by decide
  have hdescent : baseEnd_5333361 < baseStart_5333361 := by decide
  rcases family_descends (prefixWord ++ tailWord_5333361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5333388 : List Nat := [2, 2, 1, 2, 1, 4, 2, 2, 3, 4]
def baseStart_5333388 : Nat := 118140960795 + 5333388 * 2 ^ 59
def prefixEnd_5333388 : Nat := 4983230072969 + 3 ^ 40 * 5333388 * 2
def baseEnd_5333388 : Nat := 912863853640561442874067

theorem tailTrace_5333388 : CollatzResearch.WordTrace tailWord_5333388 prefixEnd_5333388 912863853640561442874067 := by
  unfold tailWord_5333388
  simp only [CollatzResearch.WordTrace]
  refine ⟨97262320601026810498716409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129683094134702413998288545 97262320601026810498716409)
  ·
    refine ⟨72946740450770107874037307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97262320601026810498716409 72946740450770107874037307)
    ·
      refine ⟨109420110676155161811055961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72946740450770107874037307 109420110676155161811055961)
      ·
        refine ⟨82065083007116371358291971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 109420110676155161811055961 82065083007116371358291971)
        ·
          refine ⟨123097624510674557037437957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82065083007116371358291971 123097624510674557037437957)
          ·
            refine ⟨23080804595751479444519617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 123097624510674557037437957 23080804595751479444519617)
            ·
              refine ⟨17310603446813609583389713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23080804595751479444519617 17310603446813609583389713)
              ·
                refine ⟨12982952585110207187542285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17310603446813609583389713 12982952585110207187542285)
                ·
                  refine ⟨4868607219416327695328357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12982952585110207187542285 4868607219416327695328357)
                  ·
                    refine ⟨912863853640561442874067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4868607219416327695328357 912863853640561442874067)
                    ·
                      rfl

theorem cell23_5333388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 2, 2, 3, 4].length) (baseStart_5333388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5333388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5333388 prefixEnd_5333388 := by exact prefixLift 5333388
  have htrace : WordTrace (prefixWord ++ tailWord_5333388) baseStart_5333388 baseEnd_5333388 := by
    simpa [prefixWord, tailWord_5333388, baseEnd_5333388] using wordTrace_append hprefix tailTrace_5333388
  have hstable : (prefixWord ++ tailWord_5333388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5333388).length < 2 ^ (prefixWord ++ tailWord_5333388).sum := by decide
  have hdescent : baseEnd_5333388 < baseStart_5333388 := by decide
  rcases family_descends (prefixWord ++ tailWord_5333388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5333415 : List Nat := [1, 1, 6, 1, 1, 3, 1, 2, 2, 2, 3]
def baseStart_5333415 : Nat := 118140960795 + 5333415 * 2 ^ 59
def prefixEnd_5333415 : Nat := 4983230072969 + 3 ^ 40 * 5333415 * 2
def baseEnd_5333415 : Nat := 2738605424899355722984577

theorem tailTrace_5333415 : CollatzResearch.WordTrace tailWord_5333415 prefixEnd_5333415 2738605424899355722984577 := by
  unfold tailWord_5333415
  simp only [CollatzResearch.WordTrace]
  refine ⟨194525625972955804608665699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129683750648637203072443799 194525625972955804608665699)
  ·
    refine ⟨291788438959433706912998549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194525625972955804608665699 291788438959433706912998549)
    ·
      refine ⟨13677583076223455011546807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 291788438959433706912998549 13677583076223455011546807)
      ·
        refine ⟨20516374614335182517320211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13677583076223455011546807 20516374614335182517320211)
        ·
          refine ⟨30774561921502773775980317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20516374614335182517320211 30774561921502773775980317)
          ·
            refine ⟨11540460720563540165992619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30774561921502773775980317 11540460720563540165992619)
            ·
              refine ⟨17310691080845310248988929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11540460720563540165992619 17310691080845310248988929)
              ·
                refine ⟨12983018310633982686741697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17310691080845310248988929 12983018310633982686741697)
                ·
                  refine ⟨9737263732975487015056273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12983018310633982686741697 9737263732975487015056273)
                  ·
                    refine ⟨7302947799731615261292205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9737263732975487015056273 7302947799731615261292205)
                    ·
                      refine ⟨2738605424899355722984577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7302947799731615261292205 2738605424899355722984577)
                      ·
                        rfl

theorem cell23_5333415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 1, 2, 2, 2, 3].length) (baseStart_5333415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5333415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5333415 prefixEnd_5333415 := by exact prefixLift 5333415
  have htrace : WordTrace (prefixWord ++ tailWord_5333415) baseStart_5333415 baseEnd_5333415 := by
    simpa [prefixWord, tailWord_5333415, baseEnd_5333415] using wordTrace_append hprefix tailTrace_5333415
  have hstable : (prefixWord ++ tailWord_5333415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5333415).length < 2 ^ (prefixWord ++ tailWord_5333415).sum := by decide
  have hdescent : baseEnd_5333415 < baseStart_5333415 := by decide
  rcases family_descends (prefixWord ++ tailWord_5333415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5333448 : List Nat := [2, 1, 3, 1, 3, 3, 1, 1, 3, 5]
def baseStart_5333448 : Nat := 118140960795 + 5333448 * 2 ^ 59
def prefixEnd_5333448 : Nat := 4983230072969 + 3 ^ 40 * 5333448 * 2
def baseEnd_5333448 : Nat := 912874123253651364623975

theorem tailTrace_5333448 : CollatzResearch.WordTrace tailWord_5333448 prefixEnd_5333448 912874123253651364623975 := by
  unfold tailWord_5333448
  simp only [CollatzResearch.WordTrace]
  refine ⟨97263414790918125622308499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129684553054557500829744665 97263414790918125622308499)
  ·
    refine ⟨145895122186377188433462749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97263414790918125622308499 145895122186377188433462749)
    ·
      refine ⟨54710670819891445662548531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 145895122186377188433462749 54710670819891445662548531)
      ·
        refine ⟨82066006229837168493822797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54710670819891445662548531 82066006229837168493822797)
        ·
          refine ⟨30774752336188938185183549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 82066006229837168493822797 30774752336188938185183549)
          ·
            refine ⟨11540532126070851819443831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30774752336188938185183549 11540532126070851819443831)
            ·
              refine ⟨17310798189106277729165747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11540532126070851819443831 17310798189106277729165747)
              ·
                refine ⟨25966197283659416593748621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17310798189106277729165747 25966197283659416593748621)
                ·
                  refine ⟨9737323981372281222655733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25966197283659416593748621 9737323981372281222655733)
                  ·
                    refine ⟨912874123253651364623975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9737323981372281222655733 912874123253651364623975)
                    ·
                      rfl

theorem cell23_5333448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 1, 1, 3, 5].length) (baseStart_5333448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5333448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5333448 prefixEnd_5333448 := by exact prefixLift 5333448
  have htrace : WordTrace (prefixWord ++ tailWord_5333448) baseStart_5333448 baseEnd_5333448 := by
    simpa [prefixWord, tailWord_5333448, baseEnd_5333448] using wordTrace_append hprefix tailTrace_5333448
  have hstable : (prefixWord ++ tailWord_5333448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5333448).length < 2 ^ (prefixWord ++ tailWord_5333448).sum := by decide
  have hdescent : baseEnd_5333448 < baseStart_5333448 := by decide
  rcases family_descends (prefixWord ++ tailWord_5333448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5333465 : List Nat := [1, 2, 1, 2, 4, 1, 5, 1, 1, 5]
def baseStart_5333465 : Nat := 118140960795 + 5333465 * 2 ^ 59
def prefixEnd_5333465 : Nat := 4983230072969 + 3 ^ 40 * 5333465 * 2
def baseEnd_5333465 : Nat := 912877032977360175786449

theorem tailTrace_5333465 : CollatzResearch.WordTrace tailWord_5333465 prefixEnd_5333465 912877032977360175786449 := by
  unfold tailWord_5333465
  simp only [CollatzResearch.WordTrace]
  refine ⟨194527449622774663147985849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129684966415183108765323899 194527449622774663147985849)
  ·
    refine ⟨145895587217080997360989387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 194527449622774663147985849 145895587217080997360989387)
    ·
      refine ⟨218843380825621496041484081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145895587217080997360989387 218843380825621496041484081)
      ·
        refine ⟨164132535619216122031113061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 218843380825621496041484081 164132535619216122031113061)
        ·
          refine ⟨30774850428603022880833699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 164132535619216122031113061 30774850428603022880833699)
          ·
            refine ⟨46162275642904534321250549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30774850428603022880833699 46162275642904534321250549)
            ·
              refine ⟨4327713341522300092617239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 46162275642904534321250549 4327713341522300092617239)
              ·
                refine ⟨6491570012283450138925859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4327713341522300092617239 6491570012283450138925859)
                ·
                  refine ⟨9737355018425175208388789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6491570012283450138925859 9737355018425175208388789)
                  ·
                    refine ⟨912877032977360175786449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9737355018425175208388789 912877032977360175786449)
                    ·
                      rfl

theorem cell23_5333465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 5, 1, 1, 5].length) (baseStart_5333465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5333465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5333465 prefixEnd_5333465 := by exact prefixLift 5333465
  have htrace : WordTrace (prefixWord ++ tailWord_5333465) baseStart_5333465 baseEnd_5333465 := by
    simpa [prefixWord, tailWord_5333465, baseEnd_5333465] using wordTrace_append hprefix tailTrace_5333465
  have hstable : (prefixWord ++ tailWord_5333465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5333465).length < 2 ^ (prefixWord ++ tailWord_5333465).sum := by decide
  have hdescent : baseEnd_5333465 < baseStart_5333465 := by decide
  rcases family_descends (prefixWord ++ tailWord_5333465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5333481 : List Nat := [1, 2, 1, 1, 1, 2, 1, 6, 1, 1, 6]
def baseStart_5333481 : Nat := 118140960795 + 5333481 * 2 ^ 59
def prefixEnd_5333481 : Nat := 4983230072969 + 3 ^ 40 * 5333481 * 2
def baseEnd_5333481 : Nat := 2738639314622552464759273

theorem tailTrace_5333481 : CollatzResearch.WordTrace tailWord_5333481 prefixEnd_5333481 2738639314622552464759273 := by
  unfold tailWord_5333481
  simp only [CollatzResearch.WordTrace]
  refine ⟨194528033190716697880568297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129685355460477798587045531 194528033190716697880568297)
  ·
    refine ⟨145896024893037523410426223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 194528033190716697880568297 145896024893037523410426223)
    ·
      refine ⟨218844037339556285115639335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145896024893037523410426223 218844037339556285115639335)
      ·
        refine ⟨328266056009334427673459003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 218844037339556285115639335 328266056009334427673459003)
        ·
          refine ⟨492399084014001641510188505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 328266056009334427673459003 492399084014001641510188505)
          ·
            refine ⟨369299313010501231132641379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 492399084014001641510188505 369299313010501231132641379)
            ·
              refine ⟨553948969515751846698962069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 369299313010501231132641379 553948969515751846698962069)
              ·
                refine ⟨25966357946050867814013847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 553948969515751846698962069 25966357946050867814013847)
                ·
                  refine ⟨38949536919076301721020771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25966357946050867814013847 38949536919076301721020771)
                  ·
                    refine ⟨58424305378614452581531157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 38949536919076301721020771 58424305378614452581531157)
                    ·
                      refine ⟨2738639314622552464759273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 58424305378614452581531157 2738639314622552464759273)
                      ·
                        rfl

theorem cell23_5333481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 6, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 6, 1, 1, 6].length) (baseStart_5333481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5333481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5333481 prefixEnd_5333481 := by exact prefixLift 5333481
  have htrace : WordTrace (prefixWord ++ tailWord_5333481) baseStart_5333481 baseEnd_5333481 := by
    simpa [prefixWord, tailWord_5333481, baseEnd_5333481] using wordTrace_append hprefix tailTrace_5333481
  have hstable : (prefixWord ++ tailWord_5333481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5333481).length < 2 ^ (prefixWord ++ tailWord_5333481).sum := by decide
  have hdescent : baseEnd_5333481 < baseStart_5333481 := by decide
  rcases family_descends (prefixWord ++ tailWord_5333481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5333485 : List Nat := [1, 5, 1, 3, 1, 1, 1, 2, 3, 1, 4]
def baseStart_5333485 : Nat := 118140960795 + 5333485 * 2 ^ 59
def prefixEnd_5333485 : Nat := 4983230072969 + 3 ^ 40 * 5333485 * 2
def baseEnd_5333485 : Nat := 2738641368545170449109255

theorem tailTrace_5333485 : CollatzResearch.WordTrace tailWord_5333485 prefixEnd_5333485 2738641368545170449109255 := by
  unfold tailWord_5333485
  simp only [CollatzResearch.WordTrace]
  refine ⟨194528179082702206563713909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129685452721801471042475939 194528179082702206563713909)
  ·
    refine ⟨18237016789003331865348179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 194528179082702206563713909 18237016789003331865348179)
    ·
      refine ⟨27355525183504997798022269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18237016789003331865348179 27355525183504997798022269)
      ·
        refine ⟨10258321943814374174258351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27355525183504997798022269 10258321943814374174258351)
        ·
          refine ⟨15387482915721561261387527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10258321943814374174258351 15387482915721561261387527)
          ·
            refine ⟨23081224373582341892081291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15387482915721561261387527 23081224373582341892081291)
            ·
              refine ⟨34621836560373512838121937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23081224373582341892081291 34621836560373512838121937)
              ·
                refine ⟨25966377420280134628591453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34621836560373512838121937 25966377420280134628591453)
                ·
                  refine ⟨9737391532605050485721795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25966377420280134628591453 9737391532605050485721795)
                  ·
                    refine ⟨14606087298907575728582693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9737391532605050485721795 14606087298907575728582693)
                    ·
                      refine ⟨2738641368545170449109255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14606087298907575728582693 2738641368545170449109255)
                      ·
                        rfl

theorem cell23_5333485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 1, 2, 3, 1, 4].length) (baseStart_5333485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5333485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5333485 prefixEnd_5333485 := by exact prefixLift 5333485
  have htrace : WordTrace (prefixWord ++ tailWord_5333485) baseStart_5333485 baseEnd_5333485 := by
    simpa [prefixWord, tailWord_5333485, baseEnd_5333485] using wordTrace_append hprefix tailTrace_5333485
  have hstable : (prefixWord ++ tailWord_5333485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5333485).length < 2 ^ (prefixWord ++ tailWord_5333485).sum := by decide
  have hdescent : baseEnd_5333485 < baseStart_5333485 := by decide
  rcases family_descends (prefixWord ++ tailWord_5333485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5333488 : List Nat := [2, 1, 1, 1, 3, 3, 1, 1, 5, 2, 3]
def baseStart_5333488 : Nat := 118140960795 + 5333488 * 2 ^ 59
def prefixEnd_5333488 : Nat := 4983230072969 + 3 ^ 40 * 5333488 * 2
def baseEnd_5333488 : Nat := 2738642908987133937371741

theorem tailTrace_5333488 : CollatzResearch.WordTrace tailWord_5333488 prefixEnd_5333488 2738642908987133937371741 := by
  unfold tailWord_5333488
  simp only [CollatzResearch.WordTrace]
  refine ⟨97264144250845669038036559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129685525667794225384048745 97264144250845669038036559)
  ·
    refine ⟨145896216376268503557054839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97264144250845669038036559 145896216376268503557054839)
    ·
      refine ⟨218844324564402755335582259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145896216376268503557054839 218844324564402755335582259)
      ·
        refine ⟨328266486846604133003373389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 218844324564402755335582259 328266486846604133003373389)
        ·
          refine ⟨123099932567476549876265021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 328266486846604133003373389 123099932567476549876265021)
          ·
            refine ⟨46162474712803706203599383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 123099932567476549876265021 46162474712803706203599383)
            ·
              refine ⟨69243712069205559305399075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46162474712803706203599383 69243712069205559305399075)
              ·
                refine ⟨103865568103808338958098613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 69243712069205559305399075 103865568103808338958098613)
                ·
                  refine ⟨9737397009732031777321745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 103865568103808338958098613 9737397009732031777321745)
                  ·
                    refine ⟨7303047757299023832991309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9737397009732031777321745 7303047757299023832991309)
                    ·
                      refine ⟨2738642908987133937371741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7303047757299023832991309 2738642908987133937371741)
                      ·
                        rfl

theorem cell23_5333488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 1, 5, 2, 3].length) (baseStart_5333488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5333488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5333488 prefixEnd_5333488 := by exact prefixLift 5333488
  have htrace : WordTrace (prefixWord ++ tailWord_5333488) baseStart_5333488 baseEnd_5333488 := by
    simpa [prefixWord, tailWord_5333488, baseEnd_5333488] using wordTrace_append hprefix tailTrace_5333488
  have hstable : (prefixWord ++ tailWord_5333488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5333488).length < 2 ^ (prefixWord ++ tailWord_5333488).sum := by decide
  have hdescent : baseEnd_5333488 < baseStart_5333488 := by decide
  rcases family_descends (prefixWord ++ tailWord_5333488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5333505 : List Nat := [1, 2, 4, 1, 3, 1, 2, 1, 3, 2, 3]
def baseStart_5333505 : Nat := 118140960795 + 5333505 * 2 ^ 59
def prefixEnd_5333505 : Nat := 4983230072969 + 3 ^ 40 * 5333505 * 2
def baseEnd_5333505 : Nat := 2738651638158260370859163

theorem tailTrace_5333505 : CollatzResearch.WordTrace tailWord_5333505 prefixEnd_5333505 2738651638158260370859163 := by
  unfold tailWord_5333505
  simp only [CollatzResearch.WordTrace]
  refine ⟨194528908542629749979441969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129685939028419833319627979 194528908542629749979441969)
  ·
    refine ⟨145896681406972312484581477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 194528908542629749979441969 145896681406972312484581477)
    ·
      refine ⟨27355627763807308590859027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 145896681406972312484581477 27355627763807308590859027)
      ·
        refine ⟨41033441645710962886288541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27355627763807308590859027 41033441645710962886288541)
        ·
          refine ⟨15387540617141611082358203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41033441645710962886288541 15387540617141611082358203)
          ·
            refine ⟨23081310925712416623537305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15387540617141611082358203 23081310925712416623537305)
            ·
              refine ⟨17310983194284312467652979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23081310925712416623537305 17310983194284312467652979)
              ·
                refine ⟨25966474791426468701479469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17310983194284312467652979 25966474791426468701479469)
                ·
                  refine ⟨9737428046784925763054801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25966474791426468701479469 9737428046784925763054801)
                  ·
                    refine ⟨7303071035088694322291101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9737428046784925763054801 7303071035088694322291101)
                    ·
                      refine ⟨2738651638158260370859163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7303071035088694322291101 2738651638158260370859163)
                      ·
                        rfl

theorem cell23_5333505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 2, 1, 3, 2, 3].length) (baseStart_5333505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5333505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5333505 prefixEnd_5333505 := by exact prefixLift 5333505
  have htrace : WordTrace (prefixWord ++ tailWord_5333505) baseStart_5333505 baseEnd_5333505 := by
    simpa [prefixWord, tailWord_5333505, baseEnd_5333505] using wordTrace_append hprefix tailTrace_5333505
  have hstable : (prefixWord ++ tailWord_5333505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5333505).length < 2 ^ (prefixWord ++ tailWord_5333505).sum := by decide
  have hdescent : baseEnd_5333505 < baseStart_5333505 := by decide
  rcases family_descends (prefixWord ++ tailWord_5333505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5333506 : List Nat := [3, 4, 1, 2, 2, 2, 1, 1, 2, 3, 2]
def baseStart_5333506 : Nat := 118140960795 + 5333506 * 2 ^ 59
def prefixEnd_5333506 : Nat := 4983230072969 + 3 ^ 40 * 5333506 * 2
def baseEnd_5333506 : Nat := 2738652151638914866946659

theorem tailTrace_5333506 : CollatzResearch.WordTrace tailWord_5333506 prefixEnd_5333506 2738652151638914866946659 := by
  unfold tailWord_5333506
  simp only [CollatzResearch.WordTrace]
  refine ⟨48632236253906531787557093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129685963343750751433485581 48632236253906531787557093)
  ·
    refine ⟨9118544297607474710166955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 48632236253906531787557093 9118544297607474710166955)
    ·
      refine ⟨13677816446411212065250433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9118544297607474710166955 13677816446411212065250433)
      ·
        refine ⟨10258362334808409048937825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13677816446411212065250433 10258362334808409048937825)
        ·
          refine ⟨7693771751106306786703369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10258362334808409048937825 7693771751106306786703369)
          ·
            refine ⟨5770328813329730090027527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7693771751106306786703369 5770328813329730090027527)
            ·
              refine ⟨8655493219994595135041291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5770328813329730090027527 8655493219994595135041291)
              ·
                refine ⟨12983239829991892702561937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8655493219994595135041291 12983239829991892702561937)
                ·
                  refine ⟨9737429872493919526921453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12983239829991892702561937 9737429872493919526921453)
                  ·
                    refine ⟨3651536202185219822595545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9737429872493919526921453 3651536202185219822595545)
                    ·
                      refine ⟨2738652151638914866946659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3651536202185219822595545 2738652151638914866946659)
                      ·
                        rfl

theorem cell23_5333506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 2, 1, 1, 2, 3, 2].length) (baseStart_5333506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5333506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5333506 prefixEnd_5333506 := by exact prefixLift 5333506
  have htrace : WordTrace (prefixWord ++ tailWord_5333506) baseStart_5333506 baseEnd_5333506 := by
    simpa [prefixWord, tailWord_5333506, baseEnd_5333506] using wordTrace_append hprefix tailTrace_5333506
  have hstable : (prefixWord ++ tailWord_5333506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5333506).length < 2 ^ (prefixWord ++ tailWord_5333506).sum := by decide
  have hdescent : baseEnd_5333506 < baseStart_5333506 := by decide
  rcases family_descends (prefixWord ++ tailWord_5333506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5333521 : List Nat := [1, 2, 2, 1, 1, 2, 2, 2, 1, 9]
def baseStart_5333521 : Nat := 118140960795 + 5333521 * 2 ^ 59
def prefixEnd_5333521 : Nat := 4983230072969 + 3 ^ 40 * 5333521 * 2
def baseEnd_5333521 : Nat := 912886617949577436086363

theorem tailTrace_5333521 : CollatzResearch.WordTrace tailWord_5333521 prefixEnd_5333521 912886617949577436086363 := by
  unfold tailWord_5333521
  simp only [CollatzResearch.WordTrace]
  refine ⟨194529492110571784712024417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129686328073714523141349611 194529492110571784712024417)
  ·
    refine ⟨145897119082928838534018313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 194529492110571784712024417 145897119082928838534018313)
    ·
      refine ⟨109422839312196628900513735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 145897119082928838534018313 109422839312196628900513735)
      ·
        refine ⟨164134258968294943350770603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109422839312196628900513735 164134258968294943350770603)
        ·
          refine ⟨246201388452442415026155905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 164134258968294943350770603 246201388452442415026155905)
          ·
            refine ⟨184651041339331811269616929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 246201388452442415026155905 184651041339331811269616929)
            ·
              refine ⟨138488281004498858452212697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 184651041339331811269616929 138488281004498858452212697)
              ·
                refine ⟨103866210753374143839159523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 138488281004498858452212697 103866210753374143839159523)
                ·
                  refine ⟨155799316130061215758739285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 103866210753374143839159523 155799316130061215758739285)
                  ·
                    refine ⟨912886617949577436086363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 155799316130061215758739285 912886617949577436086363)
                    ·
                      rfl

theorem cell23_5333521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 9].length) (baseStart_5333521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5333521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5333521 prefixEnd_5333521 := by exact prefixLift 5333521
  have htrace : WordTrace (prefixWord ++ tailWord_5333521) baseStart_5333521 baseEnd_5333521 := by
    simpa [prefixWord, tailWord_5333521, baseEnd_5333521] using wordTrace_append hprefix tailTrace_5333521
  have hstable : (prefixWord ++ tailWord_5333521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5333521).length < 2 ^ (prefixWord ++ tailWord_5333521).sum := by decide
  have hdescent : baseEnd_5333521 < baseStart_5333521 := by decide
  rcases family_descends (prefixWord ++ tailWord_5333521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5333549 : List Nat := [1, 5, 4, 1, 1, 1, 1, 1, 1, 1, 6]
def baseStart_5333549 : Nat := 118140960795 + 5333549 * 2 ^ 59
def prefixEnd_5333549 : Nat := 4983230072969 + 3 ^ 40 * 5333549 * 2
def baseEnd_5333549 : Nat := 2738674231307058198708961

theorem tailTrace_5333549 : CollatzResearch.WordTrace tailWord_5333549 prefixEnd_5333549 2738674231307058198708961 := by
  unfold tailWord_5333549
  simp only [CollatzResearch.WordTrace]
  refine ⟨194530513354470345494043701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129687008902980230329362467 194530513354470345494043701)
  ·
    refine ⟨18237235626981594890066597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 194530513354470345494043701 18237235626981594890066597)
    ·
      refine ⟨3419481680059049041887487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18237235626981594890066597 3419481680059049041887487)
      ·
        refine ⟨5129222520088573562831231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3419481680059049041887487 5129222520088573562831231)
        ·
          refine ⟨7693833780132860344246847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5129222520088573562831231 7693833780132860344246847)
          ·
            refine ⟨11540750670199290516370271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7693833780132860344246847 11540750670199290516370271)
            ·
              refine ⟨17311126005298935774555407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11540750670199290516370271 17311126005298935774555407)
              ·
                refine ⟨25966689007948403661833111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17311126005298935774555407 25966689007948403661833111)
                ·
                  refine ⟨38950033511922605492749667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25966689007948403661833111 38950033511922605492749667)
                  ·
                    refine ⟨58425050267883908239124501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 38950033511922605492749667 58425050267883908239124501)
                    ·
                      refine ⟨2738674231307058198708961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 58425050267883908239124501 2738674231307058198708961)
                      ·
                        rfl

theorem cell23_5333549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 1, 1, 1, 1, 6].length) (baseStart_5333549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5333549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5333549 prefixEnd_5333549 := by exact prefixLift 5333549
  have htrace : WordTrace (prefixWord ++ tailWord_5333549) baseStart_5333549 baseEnd_5333549 := by
    simpa [prefixWord, tailWord_5333549, baseEnd_5333549] using wordTrace_append hprefix tailTrace_5333549
  have hstable : (prefixWord ++ tailWord_5333549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5333549).length < 2 ^ (prefixWord ++ tailWord_5333549).sum := by decide
  have hdescent : baseEnd_5333549 < baseStart_5333549 := by decide
  rcases family_descends (prefixWord ++ tailWord_5333549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5333556 : List Nat := [2, 5, 1, 3, 1, 1, 2, 2, 1, 2, 3]
def baseStart_5333556 : Nat := 118140960795 + 5333556 * 2 ^ 59
def prefixEnd_5333556 : Nat := 4983230072969 + 3 ^ 40 * 5333556 * 2
def baseEnd_5333556 : Nat := 2738677825671639671321429

theorem tailTrace_5333556 : CollatzResearch.WordTrace tailWord_5333556 prefixEnd_5333556 2738677825671639671321429 := by
  unfold tailWord_5333556
  simp only [CollatzResearch.WordTrace]
  refine ⟨97265384332722492844774261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129687179110296657126365681 97265384332722492844774261)
  ·
    refine ⟨9118629781192733704197587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 97265384332722492844774261 9118629781192733704197587)
    ·
      refine ⟨13677944671789100556296381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9118629781192733704197587 13677944671789100556296381)
      ·
        refine ⟨5129229251920912708611143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13677944671789100556296381 5129229251920912708611143)
        ·
          refine ⟨7693843877881369062916715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5129229251920912708611143 7693843877881369062916715)
          ·
            refine ⟨11540765816822053594375073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7693843877881369062916715 11540765816822053594375073)
            ·
              refine ⟨8655574362616540195781305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11540765816822053594375073 8655574362616540195781305)
              ·
                refine ⟨6491680771962405146835979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8655574362616540195781305 6491680771962405146835979)
                ·
                  refine ⟨9737521157943607720253969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6491680771962405146835979 9737521157943607720253969)
                  ·
                    refine ⟨7303140868457705790190477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9737521157943607720253969 7303140868457705790190477)
                    ·
                      refine ⟨2738677825671639671321429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7303140868457705790190477 2738677825671639671321429)
                      ·
                        rfl

theorem cell23_5333556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 2, 2, 1, 2, 3].length) (baseStart_5333556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5333556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5333556 prefixEnd_5333556 := by exact prefixLift 5333556
  have htrace : WordTrace (prefixWord ++ tailWord_5333556) baseStart_5333556 baseEnd_5333556 := by
    simpa [prefixWord, tailWord_5333556, baseEnd_5333556] using wordTrace_append hprefix tailTrace_5333556
  have hstable : (prefixWord ++ tailWord_5333556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5333556).length < 2 ^ (prefixWord ++ tailWord_5333556).sum := by decide
  have hdescent : baseEnd_5333556 < baseStart_5333556 := by decide
  rcases family_descends (prefixWord ++ tailWord_5333556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5333562 : List Nat := [3, 1, 1, 1, 3, 3, 1, 4, 1, 3, 2]
def baseStart_5333562 : Nat := 118140960795 + 5333562 * 2 ^ 59
def prefixEnd_5333562 : Nat := 4983230072969 + 3 ^ 40 * 5333562 * 2
def baseEnd_5333562 : Nat := 2738680906555566647846401

theorem tailTrace_5333562 : CollatzResearch.WordTrace tailWord_5333562 prefixEnd_5333562 2738680906555566647846401 := by
  unfold tailWord_5333562
  simp only [CollatzResearch.WordTrace]
  refine ⟨48632746875855812178566735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129687325002282165809511293 48632746875855812178566735)
  ·
    refine ⟨72949120313783718267850103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48632746875855812178566735 72949120313783718267850103)
    ·
      refine ⟨109423680470675577401775155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72949120313783718267850103 109423680470675577401775155)
      ·
        refine ⟨164135520706013366102662733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109423680470675577401775155 164135520706013366102662733)
        ·
          refine ⟨61550820264755012288498525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 164135520706013366102662733 61550820264755012288498525)
          ·
            refine ⟨23081557599283129608186947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 61550820264755012288498525 23081557599283129608186947)
            ·
              refine ⟨34622336398924694412280421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23081557599283129608186947 34622336398924694412280421)
              ·
                refine ⟨6491688074798380202302579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34622336398924694412280421 6491688074798380202302579)
                ·
                  refine ⟨9737532112197570303453869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6491688074798380202302579 9737532112197570303453869)
                  ·
                    refine ⟨3651574542074088863795201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9737532112197570303453869 3651574542074088863795201)
                    ·
                      refine ⟨2738680906555566647846401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3651574542074088863795201 2738680906555566647846401)
                      ·
                        rfl

theorem cell23_5333562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 1, 4, 1, 3, 2].length) (baseStart_5333562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5333562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5333562 prefixEnd_5333562 := by exact prefixLift 5333562
  have htrace : WordTrace (prefixWord ++ tailWord_5333562) baseStart_5333562 baseEnd_5333562 := by
    simpa [prefixWord, tailWord_5333562, baseEnd_5333562] using wordTrace_append hprefix tailTrace_5333562
  have hstable : (prefixWord ++ tailWord_5333562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5333562).length < 2 ^ (prefixWord ++ tailWord_5333562).sum := by decide
  have hdescent : baseEnd_5333562 < baseStart_5333562 := by decide
  rcases family_descends (prefixWord ++ tailWord_5333562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5333578 : List Nat := [3, 1, 2, 1, 1, 4, 1, 1, 1, 3, 5]
def baseStart_5333578 : Nat := 118140960795 + 5333578 * 2 ^ 59
def prefixEnd_5333578 : Nat := 4983230072969 + 3 ^ 40 * 5333578 * 2
def baseEnd_5333578 : Nat := 2738689122246038585246327

theorem tailTrace_5333578 : CollatzResearch.WordTrace tailWord_5333578 prefixEnd_5333578 2738689122246038585246327 := by
  unfold tailWord_5333578
  simp only [CollatzResearch.WordTrace]
  refine ⟨48632892767841320861712347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129687714047576855631232925 48632892767841320861712347)
  ·
    refine ⟨72949339151761981292568521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48632892767841320861712347 72949339151761981292568521)
    ·
      refine ⟨54712004363821485969426391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72949339151761981292568521 54712004363821485969426391)
      ·
        refine ⟨82068006545732228954139587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54712004363821485969426391 82068006545732228954139587)
        ·
          refine ⟨123102009818598343431209381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82068006545732228954139587 123102009818598343431209381)
          ·
            refine ⟨23081626840987189393351759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 123102009818598343431209381 23081626840987189393351759)
            ·
              refine ⟨34622440261480784090027639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23081626840987189393351759 34622440261480784090027639)
              ·
                refine ⟨51933660392221176135041459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34622440261480784090027639 51933660392221176135041459)
                ·
                  refine ⟨77900490588331764202562189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51933660392221176135041459 77900490588331764202562189)
                  ·
                    refine ⟨29212683970624411575960821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 77900490588331764202562189 29212683970624411575960821)
                    ·
                      refine ⟨2738689122246038585246327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29212683970624411575960821 2738689122246038585246327)
                      ·
                        rfl

theorem cell23_5333578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 1, 1, 1, 3, 5].length) (baseStart_5333578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5333578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5333578 prefixEnd_5333578 := by exact prefixLift 5333578
  have htrace : WordTrace (prefixWord ++ tailWord_5333578) baseStart_5333578 baseEnd_5333578 := by
    simpa [prefixWord, tailWord_5333578, baseEnd_5333578] using wordTrace_append hprefix tailTrace_5333578
  have hstable : (prefixWord ++ tailWord_5333578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5333578).length < 2 ^ (prefixWord ++ tailWord_5333578).sum := by decide
  have hdescent : baseEnd_5333578 < baseStart_5333578 := by decide
  rcases family_descends (prefixWord ++ tailWord_5333578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5333592 : List Nat := [2, 1, 2, 2, 1, 2, 4, 1, 4, 2, 2]
def baseStart_5333592 : Nat := 118140960795 + 5333592 * 2 ^ 59
def prefixEnd_5333592 : Nat := 4983230072969 + 3 ^ 40 * 5333592 * 2
def baseEnd_5333592 : Nat := 2738696310975201530471263

theorem tailTrace_5333592 : CollatzResearch.WordTrace tailWord_5333592 prefixEnd_5333592 2738696310975201530471263 := by
  unfold tailWord_5333592
  simp only [CollatzResearch.WordTrace]
  refine ⟨97266040846657281918929515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129688054462209709225239353 97266040846657281918929515)
  ·
    refine ⟨145899061269985922878394273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97266040846657281918929515 145899061269985922878394273)
    ·
      refine ⟨109424295952489442158795705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 145899061269985922878394273 109424295952489442158795705)
      ·
        refine ⟨82068221964367081619096779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 109424295952489442158795705 82068221964367081619096779)
        ·
          refine ⟨123102332946550622428645169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82068221964367081619096779 123102332946550622428645169)
          ·
            refine ⟨92326749709912966821483877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 123102332946550622428645169 92326749709912966821483877)
            ·
              refine ⟨17311265570608681279028227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 92326749709912966821483877 17311265570608681279028227)
              ·
                refine ⟨25966898355913021918542341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17311265570608681279028227 25966898355913021918542341)
                ·
                  refine ⟨4868793441733691609726689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25966898355913021918542341 4868793441733691609726689)
                  ·
                    refine ⟨3651595081300268707295017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4868793441733691609726689 3651595081300268707295017)
                    ·
                      refine ⟨2738696310975201530471263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3651595081300268707295017 2738696310975201530471263)
                      ·
                        rfl

theorem cell23_5333592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 4, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 4, 1, 4, 2, 2].length) (baseStart_5333592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5333592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5333592 prefixEnd_5333592 := by exact prefixLift 5333592
  have htrace : WordTrace (prefixWord ++ tailWord_5333592) baseStart_5333592 baseEnd_5333592 := by
    simpa [prefixWord, tailWord_5333592, baseEnd_5333592] using wordTrace_append hprefix tailTrace_5333592
  have hstable : (prefixWord ++ tailWord_5333592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5333592).length < 2 ^ (prefixWord ++ tailWord_5333592).sum := by decide
  have hdescent : baseEnd_5333592 < baseStart_5333592 := by decide
  rcases family_descends (prefixWord ++ tailWord_5333592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5333628 : List Nat := [2, 2, 2, 1, 1, 2, 2, 3, 1, 7]
def baseStart_5333628 : Nat := 118140960795 + 5333628 * 2 ^ 59
def prefixEnd_5333628 : Nat := 4983230072969 + 3 ^ 40 * 5333628 * 2
def baseEnd_5333628 : Nat := 912904932092921129873699

theorem tailTrace_5333628 : CollatzResearch.WordTrace tailWord_5333628 prefixEnd_5333628 912904932092921129873699 := by
  unfold tailWord_5333628
  simp only [CollatzResearch.WordTrace]
  refine ⟨97266697360592070993084769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129688929814122761324113025 97266697360592070993084769)
  ·
    refine ⟨72950023020444053244813577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97266697360592070993084769 72950023020444053244813577)
    ·
      refine ⟨54712517265333039933610183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72950023020444053244813577 54712517265333039933610183)
      ·
        refine ⟨82068775897999559900415275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54712517265333039933610183 82068775897999559900415275)
        ·
          refine ⟨123103163846999339850622913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82068775897999559900415275 123103163846999339850622913)
          ·
            refine ⟨92327372885249504887967185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 123103163846999339850622913 92327372885249504887967185)
            ·
              refine ⟨69245529663937128665975389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 92327372885249504887967185 69245529663937128665975389)
              ·
                refine ⟨25967073623976423249740771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 69245529663937128665975389 25967073623976423249740771)
                ·
                  refine ⟨38950610435964634874611157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25967073623976423249740771 38950610435964634874611157)
                  ·
                    refine ⟨912904932092921129873699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 38950610435964634874611157 912904932092921129873699)
                    ·
                      rfl

theorem cell23_5333628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 3, 1, 7].length) (baseStart_5333628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5333628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5333628 prefixEnd_5333628 := by exact prefixLift 5333628
  have htrace : WordTrace (prefixWord ++ tailWord_5333628) baseStart_5333628 baseEnd_5333628 := by
    simpa [prefixWord, tailWord_5333628, baseEnd_5333628] using wordTrace_append hprefix tailTrace_5333628
  have hstable : (prefixWord ++ tailWord_5333628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5333628).length < 2 ^ (prefixWord ++ tailWord_5333628).sum := by decide
  have hdescent : baseEnd_5333628 < baseStart_5333628 := by decide
  rcases family_descends (prefixWord ++ tailWord_5333628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5333648 : List Nat := [2, 1, 1, 1, 1, 1, 3, 1, 5, 3, 4]
def baseStart_5333648 : Nat := 118140960795 + 5333648 * 2 ^ 59
def prefixEnd_5333648 : Nat := 4983230072969 + 3 ^ 40 * 5333648 * 2
def baseEnd_5333648 : Nat := 2738725065891853311371005

theorem tailTrace_5333648 : CollatzResearch.WordTrace tailWord_5333648 prefixEnd_5333648 2738725065891853311371005 := by
  unfold tailWord_5333648
  simp only [CollatzResearch.WordTrace]
  refine ⟨97267062090555842700948799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129689416120741123601265065 97267062090555842700948799)
  ·
    refine ⟨145900593135833764051423199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97267062090555842700948799 145900593135833764051423199)
    ·
      refine ⟨218850889703750646077134799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145900593135833764051423199 218850889703750646077134799)
      ·
        refine ⟨328276334555625969115702199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 218850889703750646077134799 328276334555625969115702199)
        ·
          refine ⟨492414501833438953673553299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 328276334555625969115702199 492414501833438953673553299)
          ·
            refine ⟨738621752750158430510329949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 492414501833438953673553299 738621752750158430510329949)
            ·
              refine ⟨276983157281309411441373731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 738621752750158430510329949 276983157281309411441373731)
              ·
                refine ⟨415474735921964117162060597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 276983157281309411441373731 415474735921964117162060597)
                ·
                  refine ⟨38950756492684135983943181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 415474735921964117162060597 38950756492684135983943181)
                  ·
                    refine ⟨14606533684756550993978693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 38950756492684135983943181 14606533684756550993978693)
                    ·
                      refine ⟨2738725065891853311371005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14606533684756550993978693 2738725065891853311371005)
                      ·
                        rfl

theorem cell23_5333648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 1, 5, 3, 4].length) (baseStart_5333648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5333648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5333648 prefixEnd_5333648 := by exact prefixLift 5333648
  have htrace : WordTrace (prefixWord ++ tailWord_5333648) baseStart_5333648 baseEnd_5333648 := by
    simpa [prefixWord, tailWord_5333648, baseEnd_5333648] using wordTrace_append hprefix tailTrace_5333648
  have hstable : (prefixWord ++ tailWord_5333648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5333648).length < 2 ^ (prefixWord ++ tailWord_5333648).sum := by decide
  have hdescent : baseEnd_5333648 < baseStart_5333648 := by decide
  rcases family_descends (prefixWord ++ tailWord_5333648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5333722 : List Nat := [3, 1, 1, 2, 2, 2, 5, 1, 6]
def baseStart_5333722 : Nat := 118140960795 + 5333722 * 2 ^ 59
def prefixEnd_5333722 : Nat := 4983230072969 + 3 ^ 40 * 5333722 * 2
def baseEnd_5333722 : Nat := 304307007051142891316185

theorem tailTrace_5333722 : CollatzResearch.WordTrace tailWord_5333722 prefixEnd_5333722 304307007051142891316185 := by
  unfold tailWord_5333722
  simp only [CollatzResearch.WordTrace]
  refine ⟨48634205795710899010022855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129691215455229064026727613 48634205795710899010022855)
  ·
    refine ⟨72951308693566348515034283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48634205795710899010022855 72951308693566348515034283)
    ·
      refine ⟨109426963040349522772551425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72951308693566348515034283 109426963040349522772551425)
      ·
        refine ⟨82070222280262142079413569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 109426963040349522772551425 82070222280262142079413569)
        ·
          refine ⟨61552666710196606559560177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82070222280262142079413569 61552666710196606559560177)
          ·
            refine ⟨46164500032647454919670133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61552666710196606559560177 46164500032647454919670133)
            ·
              refine ⟨4327921878060698898719075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 46164500032647454919670133 4327921878060698898719075)
              ·
                refine ⟨6491882817091048348078613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4327921878060698898719075 6491882817091048348078613)
                ·
                  refine ⟨304307007051142891316185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6491882817091048348078613 304307007051142891316185)
                  ·
                    rfl

theorem cell23_5333722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 5, 1, 6].length) (baseStart_5333722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5333722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5333722 prefixEnd_5333722 := by exact prefixLift 5333722
  have htrace : WordTrace (prefixWord ++ tailWord_5333722) baseStart_5333722 baseEnd_5333722 := by
    simpa [prefixWord, tailWord_5333722, baseEnd_5333722] using wordTrace_append hprefix tailTrace_5333722
  have hstable : (prefixWord ++ tailWord_5333722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5333722).length < 2 ^ (prefixWord ++ tailWord_5333722).sum := by decide
  have hdescent : baseEnd_5333722 < baseStart_5333722 := by decide
  rcases family_descends (prefixWord ++ tailWord_5333722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5333775 : List Nat := [1, 1, 2, 1, 1, 1, 5, 4, 1, 1, 5]
def baseStart_5333775 : Nat := 118140960795 + 5333775 * 2 ^ 59
def prefixEnd_5333775 : Nat := 4983230072969 + 3 ^ 40 * 5333775 * 2
def baseEnd_5333775 : Nat := 2738790277934974314482921

theorem tailTrace_5333775 : CollatzResearch.WordTrace tailWord_5333775 prefixEnd_5333775 2738790277934974314482921 := by
  unfold tailWord_5333775
  simp only [CollatzResearch.WordTrace]
  refine ⟨194538756251651586091770779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129692504167767724061180519 194538756251651586091770779)
  ·
    refine ⟨291808134377477379137656169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194538756251651586091770779 291808134377477379137656169)
    ·
      refine ⟨218856100783108034353242127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 291808134377477379137656169 218856100783108034353242127)
      ·
        refine ⟨328284151174662051529863191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 218856100783108034353242127 328284151174662051529863191)
        ·
          refine ⟨492426226761993077294794787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 328284151174662051529863191 492426226761993077294794787)
          ·
            refine ⟨738639340142989615942192181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 492426226761993077294794787 738639340142989615942192181)
            ·
              refine ⟨69247438138405276494580517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 738639340142989615942192181 69247438138405276494580517)
              ·
                refine ⟨12983894650950989342733847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 69247438138405276494580517 12983894650950989342733847)
                ·
                  refine ⟨19475841976426484014100771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12983894650950989342733847 19475841976426484014100771)
                  ·
                    refine ⟨29213762964639726021151157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19475841976426484014100771 29213762964639726021151157)
                    ·
                      refine ⟨2738790277934974314482921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29213762964639726021151157 2738790277934974314482921)
                      ·
                        rfl

theorem cell23_5333775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 4, 1, 1, 5].length) (baseStart_5333775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5333775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5333775 prefixEnd_5333775 := by exact prefixLift 5333775
  have htrace : WordTrace (prefixWord ++ tailWord_5333775) baseStart_5333775 baseEnd_5333775 := by
    simpa [prefixWord, tailWord_5333775, baseEnd_5333775] using wordTrace_append hprefix tailTrace_5333775
  have hstable : (prefixWord ++ tailWord_5333775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5333775).length < 2 ^ (prefixWord ++ tailWord_5333775).sum := by decide
  have hdescent : baseEnd_5333775 < baseStart_5333775 := by decide
  rcases family_descends (prefixWord ++ tailWord_5333775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5333812 : List Nat := [2, 5, 1, 1, 3, 11]
def baseStart_5333812 : Nat := 118140960795 + 5333812 * 2 ^ 59
def prefixEnd_5333812 : Nat := 4983230072969 + 3 ^ 40 * 5333812 * 2
def baseEnd_5333812 : Nat := 11270820068803253784857

theorem tailTrace_5333812 : CollatzResearch.WordTrace tailWord_5333812 prefixEnd_5333812 11270820068803253784857 := by
  unfold tailWord_5333812
  simp only [CollatzResearch.WordTrace]
  refine ⟨97270052876258770705433845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129693403835011694273911793 97270052876258770705433845)
  ·
    refine ⟨9119067457149259753634423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 97270052876258770705433845 9119067457149259753634423)
    ·
      refine ⟨13678601185723889630451635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9119067457149259753634423 13678601185723889630451635)
      ·
        refine ⟨20517901778585834445677453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13678601185723889630451635 20517901778585834445677453)
        ·
          refine ⟨7694213166969687917129045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20517901778585834445677453 7694213166969687917129045)
          ·
            refine ⟨11270820068803253784857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 7694213166969687917129045 11270820068803253784857)
            ·
              rfl

theorem cell23_5333812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 11].length) (baseStart_5333812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5333812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5333812 prefixEnd_5333812 := by exact prefixLift 5333812
  have htrace : WordTrace (prefixWord ++ tailWord_5333812) baseStart_5333812 baseEnd_5333812 := by
    simpa [prefixWord, tailWord_5333812, baseEnd_5333812] using wordTrace_append hprefix tailTrace_5333812
  have hstable : (prefixWord ++ tailWord_5333812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5333812).length < 2 ^ (prefixWord ++ tailWord_5333812).sum := by decide
  have hdescent : baseEnd_5333812 < baseStart_5333812 := by decide
  rcases family_descends (prefixWord ++ tailWord_5333812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5333823 : List Nat := [1, 1, 2, 2, 5, 2, 1, 4, 1, 2, 2]
def baseStart_5333823 : Nat := 118140960795 + 5333823 * 2 ^ 59
def prefixEnd_5333823 : Nat := 4983230072969 + 3 ^ 40 * 5333823 * 2
def baseEnd_5333823 : Nat := 2738814925006390126682701

theorem tailTrace_5333823 : CollatzResearch.WordTrace tailWord_5333823 prefixEnd_5333823 2738814925006390126682701 := by
  unfold tailWord_5333823
  simp only [CollatzResearch.WordTrace]
  refine ⟨194540506955477690289518123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129693671303651793526345415 194540506955477690289518123)
  ·
    refine ⟨291810760433216535434277185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194540506955477690289518123 291810760433216535434277185)
    ·
      refine ⟨218858070324912401575707889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 291810760433216535434277185 218858070324912401575707889)
      ·
        refine ⟨164143552743684301181780917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 218858070324912401575707889 164143552743684301181780917)
        ·
          refine ⟨15388458069720403235791961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 164143552743684301181780917 15388458069720403235791961)
          ·
            refine ⟨11541343552290302426843971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15388458069720403235791961 11541343552290302426843971)
            ·
              refine ⟨17312015328435453640265957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11541343552290302426843971 17312015328435453640265957)
              ·
                refine ⟨3246002874081647557549867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17312015328435453640265957 3246002874081647557549867)
                ·
                  refine ⟨4869004311122471336324801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3246002874081647557549867 4869004311122471336324801)
                  ·
                    refine ⟨3651753233341853502243601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4869004311122471336324801 3651753233341853502243601)
                    ·
                      refine ⟨2738814925006390126682701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3651753233341853502243601 2738814925006390126682701)
                      ·
                        rfl

theorem cell23_5333823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 1, 4, 1, 2, 2].length) (baseStart_5333823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5333823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5333823 prefixEnd_5333823 := by exact prefixLift 5333823
  have htrace : WordTrace (prefixWord ++ tailWord_5333823) baseStart_5333823 baseEnd_5333823 := by
    simpa [prefixWord, tailWord_5333823, baseEnd_5333823] using wordTrace_append hprefix tailTrace_5333823
  have hstable : (prefixWord ++ tailWord_5333823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5333823).length < 2 ^ (prefixWord ++ tailWord_5333823).sum := by decide
  have hdescent : baseEnd_5333823 < baseStart_5333823 := by decide
  rcases family_descends (prefixWord ++ tailWord_5333823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5333849 : List Nat := [1, 2, 1, 2, 2, 4, 2, 1, 3, 3, 2]
def baseStart_5333849 : Nat := 118140960795 + 5333849 * 2 ^ 59
def prefixEnd_5333849 : Nat := 4983230072969 + 3 ^ 40 * 5333849 * 2
def baseEnd_5333849 : Nat := 2738828275503407024957581

theorem tailTrace_5333849 : CollatzResearch.WordTrace tailWord_5333849 prefixEnd_5333849 2738828275503407024957581 := by
  unfold tailWord_5333849
  simp only [CollatzResearch.WordTrace]
  refine ⟨194541455253383496729964601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129694303502255664486643067 194541455253383496729964601)
  ·
    refine ⟨145906091440037622547473451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 194541455253383496729964601 145906091440037622547473451)
    ·
      refine ⟨218859137160056433821210177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145906091440037622547473451 218859137160056433821210177)
      ·
        refine ⟨164144352870042325365907633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 218859137160056433821210177 164144352870042325365907633)
        ·
          refine ⟨123108264652531744024430725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 164144352870042325365907633 123108264652531744024430725)
          ·
            refine ⟨23082799622349702004580761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 123108264652531744024430725 23082799622349702004580761)
            ·
              refine ⟨17312099716762276503435571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23082799622349702004580761 17312099716762276503435571)
              ·
                refine ⟨25968149575143414755153357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17312099716762276503435571 25968149575143414755153357)
                ·
                  refine ⟨9738056090678780533182509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25968149575143414755153357 9738056090678780533182509)
                  ·
                    refine ⟨3651771034004542699943441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9738056090678780533182509 3651771034004542699943441)
                    ·
                      refine ⟨2738828275503407024957581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3651771034004542699943441 2738828275503407024957581)
                      ·
                        rfl

theorem cell23_5333849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 2, 1, 3, 3, 2].length) (baseStart_5333849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5333849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5333849 prefixEnd_5333849 := by exact prefixLift 5333849
  have htrace : WordTrace (prefixWord ++ tailWord_5333849) baseStart_5333849 baseEnd_5333849 := by
    simpa [prefixWord, tailWord_5333849, baseEnd_5333849] using wordTrace_append hprefix tailTrace_5333849
  have hstable : (prefixWord ++ tailWord_5333849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5333849).length < 2 ^ (prefixWord ++ tailWord_5333849).sum := by decide
  have hdescent : baseEnd_5333849 < baseStart_5333849 := by decide
  rcases family_descends (prefixWord ++ tailWord_5333849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5333855 : List Nat := [1, 1, 2, 3, 1, 3, 1, 2, 1, 8]
def baseStart_5333855 : Nat := 118140960795 + 5333855 * 2 ^ 59
def prefixEnd_5333855 : Nat := 4983230072969 + 3 ^ 40 * 5333855 * 2
def baseEnd_5333855 : Nat := 912943785462444667160851

theorem tailTrace_5333855 : CollatzResearch.WordTrace tailWord_5333855 prefixEnd_5333855 912943785462444667160851 := by
  unfold tailWord_5333855
  simp only [CollatzResearch.WordTrace]
  refine ⟨194541674091361759754683019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129694449394241173169788679 194541674091361759754683019)
  ·
    refine ⟨291812511137042639632024529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194541674091361759754683019 291812511137042639632024529)
    ·
      refine ⟨218859383352781979724018397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 291812511137042639632024529 218859383352781979724018397)
      ·
        refine ⟨82072268757293242396506899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 218859383352781979724018397 82072268757293242396506899)
        ·
          refine ⟨123108403135939863594760349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82072268757293242396506899 123108403135939863594760349)
          ·
            refine ⟨46165651175977448848035131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 123108403135939863594760349 46165651175977448848035131)
            ·
              refine ⟨69248476763966173272052697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46165651175977448848035131 69248476763966173272052697)
              ·
                refine ⟨51936357572974629954039523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 69248476763966173272052697 51936357572974629954039523)
                ·
                  refine ⟨77904536359461944931059285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51936357572974629954039523 77904536359461944931059285)
                  ·
                    refine ⟨912943785462444667160851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 77904536359461944931059285 912943785462444667160851)
                    ·
                      rfl

theorem cell23_5333855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 2, 1, 8].length) (baseStart_5333855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5333855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5333855 prefixEnd_5333855 := by exact prefixLift 5333855
  have htrace : WordTrace (prefixWord ++ tailWord_5333855) baseStart_5333855 baseEnd_5333855 := by
    simpa [prefixWord, tailWord_5333855, baseEnd_5333855] using wordTrace_append hprefix tailTrace_5333855
  have hstable : (prefixWord ++ tailWord_5333855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5333855).length < 2 ^ (prefixWord ++ tailWord_5333855).sum := by decide
  have hdescent : baseEnd_5333855 < baseStart_5333855 := by decide
  rcases family_descends (prefixWord ++ tailWord_5333855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5333890 : List Nat := [3, 4, 2, 2, 1, 2, 1, 1, 1, 3, 3]
def baseStart_5333890 : Nat := 118140960795 + 5333890 * 2 ^ 59
def prefixEnd_5333890 : Nat := 4983230072969 + 3 ^ 40 * 5333890 * 2
def baseEnd_5333890 : Nat := 2738849328210241364544893

theorem tailTrace_5333890 : CollatzResearch.WordTrace tailWord_5333890 prefixEnd_5333890 2738849328210241364544893 := by
  unfold tailWord_5333890
  simp only [CollatzResearch.WordTrace]
  refine ⟨48635737661558740183051781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129695300430823307154804749 48635737661558740183051781)
  ·
    refine ⟨9119200811542263784322209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 48635737661558740183051781 9119200811542263784322209)
    ·
      refine ⟨6839400608656697838241657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9119200811542263784322209 6839400608656697838241657)
      ·
        refine ⟨5129550456492523378681243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6839400608656697838241657 5129550456492523378681243)
        ·
          refine ⟨7694325684738785068021865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5129550456492523378681243 7694325684738785068021865)
          ·
            refine ⟨5770744263554088801016399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7694325684738785068021865 5770744263554088801016399)
            ·
              refine ⟨8656116395331133201524599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5770744263554088801016399 8656116395331133201524599)
              ·
                refine ⟨12984174592996699802286899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8656116395331133201524599 12984174592996699802286899)
                ·
                  refine ⟨19476261889495049703430349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12984174592996699802286899 19476261889495049703430349)
                  ·
                    refine ⟨7303598208560643638786381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19476261889495049703430349 7303598208560643638786381)
                    ·
                      refine ⟨2738849328210241364544893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7303598208560643638786381 2738849328210241364544893)
                      ·
                        rfl

theorem cell23_5333890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 2, 1, 1, 1, 3, 3].length) (baseStart_5333890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5333890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5333890 prefixEnd_5333890 := by exact prefixLift 5333890
  have htrace : WordTrace (prefixWord ++ tailWord_5333890) baseStart_5333890 baseEnd_5333890 := by
    simpa [prefixWord, tailWord_5333890, baseEnd_5333890] using wordTrace_append hprefix tailTrace_5333890
  have hstable : (prefixWord ++ tailWord_5333890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5333890).length < 2 ^ (prefixWord ++ tailWord_5333890).sum := by decide
  have hdescent : baseEnd_5333890 < baseStart_5333890 := by decide
  rcases family_descends (prefixWord ++ tailWord_5333890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5333896 : List Nat := [2, 1, 3, 3, 2, 1, 3, 1, 1, 4, 2]
def baseStart_5333896 : Nat := 118140960795 + 5333896 * 2 ^ 59
def prefixEnd_5333896 : Nat := 4983230072969 + 3 ^ 40 * 5333896 * 2
def baseEnd_5333896 : Nat := 2738852409094168341069865

theorem tailTrace_5333896 : CollatzResearch.WordTrace tailWord_5333896 prefixEnd_5333896 2738852409094168341069865 := by
  unfold tailWord_5333896
  simp only [CollatzResearch.WordTrace]
  refine ⟨97271584742106611878462771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129695446322808815837950361 97271584742106611878462771)
  ·
    refine ⟨145907377113159917817694157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97271584742106611878462771 145907377113159917817694157)
    ·
      refine ⟨54715266417434969181635309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 145907377113159917817694157 54715266417434969181635309)
      ·
        refine ⟨20518224906538113443113241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54715266417434969181635309 20518224906538113443113241)
        ·
          refine ⟨15388668679903585082334931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20518224906538113443113241 15388668679903585082334931)
          ·
            refine ⟨23083003019855377623502397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15388668679903585082334931 23083003019855377623502397)
            ·
              refine ⟨8656126132445766608813399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23083003019855377623502397 8656126132445766608813399)
              ·
                refine ⟨12984189198668649913220099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8656126132445766608813399 12984189198668649913220099)
                ·
                  refine ⟨19476283798002974869830149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12984189198668649913220099 19476283798002974869830149)
                  ·
                    refine ⟨3651803212125557788093153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19476283798002974869830149 3651803212125557788093153)
                    ·
                      refine ⟨2738852409094168341069865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3651803212125557788093153 2738852409094168341069865)
                      ·
                        rfl

theorem cell23_5333896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 3, 1, 1, 4, 2].length) (baseStart_5333896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5333896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5333896 prefixEnd_5333896 := by exact prefixLift 5333896
  have htrace : WordTrace (prefixWord ++ tailWord_5333896) baseStart_5333896 baseEnd_5333896 := by
    simpa [prefixWord, tailWord_5333896, baseEnd_5333896] using wordTrace_append hprefix tailTrace_5333896
  have hstable : (prefixWord ++ tailWord_5333896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5333896).length < 2 ^ (prefixWord ++ tailWord_5333896).sum := by decide
  have hdescent : baseEnd_5333896 < baseStart_5333896 := by decide
  rcases family_descends (prefixWord ++ tailWord_5333896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5333932 : List Nat := [2, 2, 1, 1, 1, 1, 2, 6, 2, 5]
def baseStart_5333932 : Nat := 118140960795 + 5333932 * 2 ^ 59
def prefixEnd_5333932 : Nat := 4983230072969 + 3 ^ 40 * 5333932 * 2
def baseEnd_5333932 : Nat := 912956964799243400073233

theorem tailTrace_5333932 : CollatzResearch.WordTrace tailWord_5333932 prefixEnd_5333932 912956964799243400073233 := by
  unfold tailWord_5333932
  simp only [CollatzResearch.WordTrace]
  refine ⟨97272241256041400952618025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129696321674721867936824033 97272241256041400952618025)
  ·
    refine ⟨72954180942031050714463519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97272241256041400952618025 72954180942031050714463519)
    ·
      refine ⟨109431271413046576071695279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72954180942031050714463519 109431271413046576071695279)
      ·
        refine ⟨164146907119569864107542919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109431271413046576071695279 164146907119569864107542919)
        ·
          refine ⟨246220360679354796161314379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 164146907119569864107542919 246220360679354796161314379)
          ·
            refine ⟨369330541019032194241971569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 246220360679354796161314379 369330541019032194241971569)
            ·
              refine ⟨276997905764274145681478677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 369330541019032194241971569 276997905764274145681478677)
              ·
                refine ⟨12984276832700350578819313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 276997905764274145681478677 12984276832700350578819313)
                ·
                  refine ⟨9738207624525262934114485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12984276832700350578819313 9738207624525262934114485)
                  ·
                    refine ⟨912956964799243400073233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9738207624525262934114485 912956964799243400073233)
                    ·
                      rfl

theorem cell23_5333932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 5].length) (baseStart_5333932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5333932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5333932 prefixEnd_5333932 := by exact prefixLift 5333932
  have htrace : WordTrace (prefixWord ++ tailWord_5333932) baseStart_5333932 baseEnd_5333932 := by
    simpa [prefixWord, tailWord_5333932, baseEnd_5333932] using wordTrace_append hprefix tailTrace_5333932
  have hstable : (prefixWord ++ tailWord_5333932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5333932).length < 2 ^ (prefixWord ++ tailWord_5333932).sum := by decide
  have hdescent : baseEnd_5333932 < baseStart_5333932 := by decide
  rcases family_descends (prefixWord ++ tailWord_5333932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5333969 : List Nat := [1, 2, 2, 1, 2, 1, 6, 1, 2, 1, 4]
def baseStart_5333969 : Nat := 118140960795 + 5333969 * 2 ^ 59
def prefixEnd_5333969 : Nat := 4983230072969 + 3 ^ 40 * 5333969 * 2
def baseEnd_5333969 : Nat := 2738889893181946555457029

theorem tailTrace_5333969 : CollatzResearch.WordTrace tailWord_5333969 prefixEnd_5333969 2738889893181946555457029 := by
  unfold tailWord_5333969
  simp only [CollatzResearch.WordTrace]
  refine ⟨194545832012948757224332961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129697221341965838149555307 194545832012948757224332961)
  ·
    refine ⟨145909374009711567918249721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 194545832012948757224332961 145909374009711567918249721)
    ·
      refine ⟨109432030507283675938687291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 145909374009711567918249721 109432030507283675938687291)
      ·
        refine ⟨164148045760925513908030937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109432030507283675938687291 164148045760925513908030937)
        ·
          refine ⟨123111034320694135431023203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 164148045760925513908030937 123111034320694135431023203)
          ·
            refine ⟨184666551481041203146534805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 123111034320694135431023203 184666551481041203146534805)
            ·
              refine ⟨8656244600673806397493819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 184666551481041203146534805 8656244600673806397493819)
              ·
                refine ⟨12984366901010709596240729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8656244600673806397493819 12984366901010709596240729)
                ·
                  refine ⟨9738275175758032197180547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12984366901010709596240729 9738275175758032197180547)
                  ·
                    refine ⟨14607412763637048295770821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9738275175758032197180547 14607412763637048295770821)
                    ·
                      refine ⟨2738889893181946555457029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14607412763637048295770821 2738889893181946555457029)
                      ·
                        rfl

theorem cell23_5333969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 6, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 6, 1, 2, 1, 4].length) (baseStart_5333969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5333969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5333969 prefixEnd_5333969 := by exact prefixLift 5333969
  have htrace : WordTrace (prefixWord ++ tailWord_5333969) baseStart_5333969 baseEnd_5333969 := by
    simpa [prefixWord, tailWord_5333969, baseEnd_5333969] using wordTrace_append hprefix tailTrace_5333969
  have hstable : (prefixWord ++ tailWord_5333969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5333969).length < 2 ^ (prefixWord ++ tailWord_5333969).sum := by decide
  have hdescent : baseEnd_5333969 < baseStart_5333969 := by decide
  rcases family_descends (prefixWord ++ tailWord_5333969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5333992 : List Nat := [2, 1, 4, 1, 1, 1, 2, 3, 8]
def baseStart_5333992 : Nat := 118140960795 + 5333992 * 2 ^ 59
def prefixEnd_5333992 : Nat := 4983230072969 + 3 ^ 40 * 5333992 * 2
def baseEnd_5333992 : Nat := 304322411470777773941047

theorem tailTrace_5333992 : CollatzResearch.WordTrace tailWord_5333992 prefixEnd_5333992 304322411470777773941047 := by
  unfold tailWord_5333992
  simp only [CollatzResearch.WordTrace]
  refine ⟨97273335445932716076210115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129697780594576954768280153 97273335445932716076210115)
  ·
    refine ⟨145910003168899074114315173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97273335445932716076210115 145910003168899074114315173)
    ·
      refine ⟨27358125594168576396434095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 145910003168899074114315173 27358125594168576396434095)
      ·
        refine ⟨41037188391252864594651143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27358125594168576396434095 41037188391252864594651143)
        ·
          refine ⟨61555782586879296891976715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41037188391252864594651143 61555782586879296891976715)
          ·
            refine ⟨92333673880318945337965073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61555782586879296891976715 92333673880318945337965073)
            ·
              refine ⟨69250255410239209003473805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 92333673880318945337965073 69250255410239209003473805)
              ·
                refine ⟨25968845778839703376302677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 69250255410239209003473805 25968845778839703376302677)
                ·
                  refine ⟨304322411470777773941047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 25968845778839703376302677 304322411470777773941047)
                  ·
                    rfl

theorem cell23_5333992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 3, 8].length) (baseStart_5333992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5333992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5333992 prefixEnd_5333992 := by exact prefixLift 5333992
  have htrace : WordTrace (prefixWord ++ tailWord_5333992) baseStart_5333992 baseEnd_5333992 := by
    simpa [prefixWord, tailWord_5333992, baseEnd_5333992] using wordTrace_append hprefix tailTrace_5333992
  have hstable : (prefixWord ++ tailWord_5333992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5333992).length < 2 ^ (prefixWord ++ tailWord_5333992).sum := by decide
  have hdescent : baseEnd_5333992 < baseStart_5333992 := by decide
  rcases family_descends (prefixWord ++ tailWord_5333992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5334053 : List Nat := [1, 3, 1, 2, 2, 2, 1, 6, 1, 1, 3]
def baseStart_5334053 : Nat := 118140960795 + 5334053 * 2 ^ 59
def prefixEnd_5334053 : Nat := 4983230072969 + 3 ^ 40 * 5334053 * 2
def baseEnd_5334053 : Nat := 2738933025556924226806643

theorem tailTrace_5334053 : CollatzResearch.WordTrace tailWord_5334053 prefixEnd_5334053 2738933025556924226806643 := by
  unfold tailWord_5334053
  simp only [CollatzResearch.WordTrace]
  refine ⟨194548895744644439570390813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129699263829762959713593875 194548895744644439570390813)
  ·
    refine ⟨72955835904241664838896555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 194548895744644439570390813 72955835904241664838896555)
    ·
      refine ⟨109433753856362497258344833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72955835904241664838896555 109433753856362497258344833)
      ·
        refine ⟨82075315392271872943758625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 109433753856362497258344833 82075315392271872943758625)
        ·
          refine ⟨61556486544203904707818969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82075315392271872943758625 61556486544203904707818969)
          ·
            refine ⟨46167364908152928530864227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61556486544203904707818969 46167364908152928530864227)
            ·
              refine ⟨69251047362229392796296341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46167364908152928530864227 69251047362229392796296341)
              ·
                refine ⟨3246142845104502787326391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 69251047362229392796296341 3246142845104502787326391)
                ·
                  refine ⟨4869214267656754180989587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3246142845104502787326391 4869214267656754180989587)
                  ·
                    refine ⟨7303821401485131271484381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4869214267656754180989587 7303821401485131271484381)
                    ·
                      refine ⟨2738933025556924226806643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7303821401485131271484381 2738933025556924226806643)
                      ·
                        rfl

theorem cell23_5334053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 6, 1, 1, 3].length) (baseStart_5334053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5334053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5334053 prefixEnd_5334053 := by exact prefixLift 5334053
  have htrace : WordTrace (prefixWord ++ tailWord_5334053) baseStart_5334053 baseEnd_5334053 := by
    simpa [prefixWord, tailWord_5334053, baseEnd_5334053] using wordTrace_append hprefix tailTrace_5334053
  have hstable : (prefixWord ++ tailWord_5334053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5334053).length < 2 ^ (prefixWord ++ tailWord_5334053).sum := by decide
  have hdescent : baseEnd_5334053 < baseStart_5334053 := by decide
  rcases family_descends (prefixWord ++ tailWord_5334053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5334076 : List Nat := [2, 2, 2, 2, 2, 2, 1, 4, 1, 1, 4]
def baseStart_5334076 : Nat := 118140960795 + 5334076 * 2 ^ 59
def prefixEnd_5334076 : Nat := 4983230072969 + 3 ^ 40 * 5334076 * 2
def baseEnd_5334076 : Nat := 2738944835611977636819037

theorem tailTrace_5334076 : CollatzResearch.WordTrace tailWord_5334076 prefixEnd_5334076 2738944835611977636819037 := by
  unfold tailWord_5334076
  simp only [CollatzResearch.WordTrace]
  refine ⟨97274867311780557249239041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129699823082374076332318721 97274867311780557249239041)
  ·
    refine ⟨72956150483835417936929281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97274867311780557249239041 72956150483835417936929281)
    ·
      refine ⟨54717112862876563452696961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72956150483835417936929281 54717112862876563452696961)
      ·
        refine ⟨41037834647157422589522721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54717112862876563452696961 41037834647157422589522721)
        ·
          refine ⟨30778375985368066942142041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41037834647157422589522721 30778375985368066942142041)
          ·
            refine ⟨23083781989026050206606531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30778375985368066942142041 23083781989026050206606531)
            ·
              refine ⟨34625672983539075309909797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23083781989026050206606531 34625672983539075309909797)
              ·
                refine ⟨6492313684413576620608087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34625672983539075309909797 6492313684413576620608087)
                ·
                  refine ⟨9738470526620364930912131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6492313684413576620608087 9738470526620364930912131)
                  ·
                    refine ⟨14607705789930547396368197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9738470526620364930912131 14607705789930547396368197)
                    ·
                      refine ⟨2738944835611977636819037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14607705789930547396368197 2738944835611977636819037)
                      ·
                        rfl

theorem cell23_5334076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 1, 4, 1, 1, 4].length) (baseStart_5334076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5334076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5334076 prefixEnd_5334076 := by exact prefixLift 5334076
  have htrace : WordTrace (prefixWord ++ tailWord_5334076) baseStart_5334076 baseEnd_5334076 := by
    simpa [prefixWord, tailWord_5334076, baseEnd_5334076] using wordTrace_append hprefix tailTrace_5334076
  have hstable : (prefixWord ++ tailWord_5334076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5334076).length < 2 ^ (prefixWord ++ tailWord_5334076).sum := by decide
  have hdescent : baseEnd_5334076 < baseStart_5334076 := by decide
  rcases family_descends (prefixWord ++ tailWord_5334076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5334093 : List Nat := [1, 6, 1, 1, 1, 2, 2, 3, 1, 1, 4]
def baseStart_5334093 : Nat := 118140960795 + 5334093 * 2 ^ 59
def prefixEnd_5334093 : Nat := 4983230072969 + 3 ^ 40 * 5334093 * 2
def baseEnd_5334093 : Nat := 2738953564783104070306459

theorem tailTrace_5334093 : CollatzResearch.WordTrace tailWord_5334093 prefixEnd_5334093 2738953564783104070306459 := by
  unfold tailWord_5334093
  simp only [CollatzResearch.WordTrace]
  refine ⟨194550354664499526401846933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129700236442999684267897955 194550354664499526401846933)
  ·
    refine ⟨9119547874898415300086575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 194550354664499526401846933 9119547874898415300086575)
    ·
      refine ⟨13679321812347622950129863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9119547874898415300086575 13679321812347622950129863)
      ·
        refine ⟨20518982718521434425194795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13679321812347622950129863 20518982718521434425194795)
        ·
          refine ⟨30778474077782151637792193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20518982718521434425194795 30778474077782151637792193)
          ·
            refine ⟨23083855558336613728344145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30778474077782151637792193 23083855558336613728344145)
            ·
              refine ⟨17312891668752460296258109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23083855558336613728344145 17312891668752460296258109)
              ·
                refine ⟨6492334375782172611096791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17312891668752460296258109 6492334375782172611096791)
                ·
                  refine ⟨9738501563673258916645187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6492334375782172611096791 9738501563673258916645187)
                  ·
                    refine ⟨14607752345509888374967781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9738501563673258916645187 14607752345509888374967781)
                    ·
                      refine ⟨2738953564783104070306459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14607752345509888374967781 2738953564783104070306459)
                      ·
                        rfl

theorem cell23_5334093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 2, 3, 1, 1, 4].length) (baseStart_5334093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5334093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5334093 prefixEnd_5334093 := by exact prefixLift 5334093
  have htrace : WordTrace (prefixWord ++ tailWord_5334093) baseStart_5334093 baseEnd_5334093 := by
    simpa [prefixWord, tailWord_5334093, baseEnd_5334093] using wordTrace_append hprefix tailTrace_5334093
  have hstable : (prefixWord ++ tailWord_5334093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5334093).length < 2 ^ (prefixWord ++ tailWord_5334093).sum := by decide
  have hdescent : baseEnd_5334093 < baseStart_5334093 := by decide
  rcases family_descends (prefixWord ++ tailWord_5334093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5334120 : List Nat := [2, 1, 4, 4, 1, 1, 1, 3, 2, 4]
def baseStart_5334120 : Nat := 118140960795 + 5334120 * 2 ^ 59
def prefixEnd_5334120 : Nat := 4983230072969 + 3 ^ 40 * 5334120 * 2
def baseEnd_5334120 : Nat := 912989142920258488222945

theorem tailTrace_5334120 : CollatzResearch.WordTrace tailWord_5334120 prefixEnd_5334120 912989142920258488222945 := by
  unfold tailWord_5334120
  simp only [CollatzResearch.WordTrace]
  refine ⟨97275669717700855006539907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129700892956934473342053209 97275669717700855006539907)
  ·
    refine ⟨145913504576551282509809861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97275669717700855006539907 145913504576551282509809861)
    ·
      refine ⟨27358782108103365470589349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 145913504576551282509809861 27358782108103365470589349)
      ·
        refine ⟨5129771645269381025735503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27358782108103365470589349 5129771645269381025735503)
        ·
          refine ⟨7694657467904071538603255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5129771645269381025735503 7694657467904071538603255)
          ·
            refine ⟨11541986201856107307904883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7694657467904071538603255 11541986201856107307904883)
            ·
              refine ⟨17312979302784160961857325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11541986201856107307904883 17312979302784160961857325)
              ·
                refine ⟨6492367238544060360696497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17312979302784160961857325 6492367238544060360696497)
                ·
                  refine ⟨4869275428908045270522373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6492367238544060360696497 4869275428908045270522373)
                  ·
                    refine ⟨912989142920258488222945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4869275428908045270522373 912989142920258488222945)
                    ·
                      rfl

theorem cell23_5334120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 1, 3, 2, 4].length) (baseStart_5334120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5334120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5334120 prefixEnd_5334120 := by exact prefixLift 5334120
  have htrace : WordTrace (prefixWord ++ tailWord_5334120) baseStart_5334120 baseEnd_5334120 := by
    simpa [prefixWord, tailWord_5334120, baseEnd_5334120] using wordTrace_append hprefix tailTrace_5334120
  have hstable : (prefixWord ++ tailWord_5334120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5334120).length < 2 ^ (prefixWord ++ tailWord_5334120).sum := by decide
  have hdescent : baseEnd_5334120 < baseStart_5334120 := by decide
  rcases family_descends (prefixWord ++ tailWord_5334120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5334216 : List Nat := [2, 1, 3, 1, 2, 1, 3, 2, 2, 3, 3]
def baseStart_5334216 : Nat := 118140960795 + 5334216 * 2 ^ 59
def prefixEnd_5334216 : Nat := 4983230072969 + 3 ^ 40 * 5334216 * 2
def baseEnd_5334216 : Nat := 2739016722903607089068393

theorem tailTrace_5334216 : CollatzResearch.WordTrace tailWord_5334216 prefixEnd_5334216 2739016722903607089068393 := by
  unfold tailWord_5334216
  simp only [CollatzResearch.WordTrace]
  refine ⟨97277420421526959204287251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129703227228702612272383001 97277420421526959204287251)
  ·
    refine ⟨145916130632290438806430877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97277420421526959204287251 145916130632290438806430877)
    ·
      refine ⟨54718548987108914552411579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 145916130632290438806430877 54718548987108914552411579)
      ·
        refine ⟨82077823480663371828617369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54718548987108914552411579 82077823480663371828617369)
        ·
          refine ⟨61558367610497528871463027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82077823480663371828617369 61558367610497528871463027)
          ·
            refine ⟨92337551415746293307194541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61558367610497528871463027 92337551415746293307194541)
            ·
              refine ⟨34626581780904859990197953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 92337551415746293307194541 34626581780904859990197953)
              ·
                refine ⟨25969936335678644992648465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34626581780904859990197953 25969936335678644992648465)
                ·
                  refine ⟨19477452251758983744486349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25969936335678644992648465 19477452251758983744486349)
                  ·
                    refine ⟨7304044594409618904182381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19477452251758983744486349 7304044594409618904182381)
                    ·
                      refine ⟨2739016722903607089068393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7304044594409618904182381 2739016722903607089068393)
                      ·
                        rfl

theorem cell23_5334216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 3, 2, 2, 3, 3].length) (baseStart_5334216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5334216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5334216 prefixEnd_5334216 := by exact prefixLift 5334216
  have htrace : WordTrace (prefixWord ++ tailWord_5334216) baseStart_5334216 baseEnd_5334216 := by
    simpa [prefixWord, tailWord_5334216, baseEnd_5334216] using wordTrace_append hprefix tailTrace_5334216
  have hstable : (prefixWord ++ tailWord_5334216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5334216).length < 2 ^ (prefixWord ++ tailWord_5334216).sum := by decide
  have hdescent : baseEnd_5334216 < baseStart_5334216 := by decide
  rcases family_descends (prefixWord ++ tailWord_5334216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5334273 : List Nat := [1, 2, 4, 1, 1, 4, 1, 2, 2, 1, 4]
def baseStart_5334273 : Nat := 118140960795 + 5334273 * 2 ^ 59
def prefixEnd_5334273 : Nat := 4983230072969 + 3 ^ 40 * 5334273 * 2
def baseEnd_5334273 : Nat := 2739045991300913366055631

theorem tailTrace_5334273 : CollatzResearch.WordTrace tailWord_5334273 prefixEnd_5334273 2739045991300913366055631 := by
  unfold tailWord_5334273
  simp only [CollatzResearch.WordTrace]
  refine ⟨194556919803847417143399473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129704613202564944762266315 194556919803847417143399473)
  ·
    refine ⟨145917689852885562857549605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 194556919803847417143399473 145917689852885562857549605)
    ·
      refine ⟨27359566847416043035790551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 145917689852885562857549605 27359566847416043035790551)
      ·
        refine ⟨41039350271124064553685827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27359566847416043035790551 41039350271124064553685827)
        ·
          refine ⟨61559025406686096830528741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41039350271124064553685827 61559025406686096830528741)
          ·
            refine ⟨11542317263753643155724139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 61559025406686096830528741 11542317263753643155724139)
            ·
              refine ⟨17313475895630464733586209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11542317263753643155724139 17313475895630464733586209)
              ·
                refine ⟨12985106921722848550189657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17313475895630464733586209 12985106921722848550189657)
                ·
                  refine ⟨9738830191292136412642243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12985106921722848550189657 9738830191292136412642243)
                  ·
                    refine ⟨14608245286938204618963365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9738830191292136412642243 14608245286938204618963365)
                    ·
                      refine ⟨2739045991300913366055631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14608245286938204618963365 2739045991300913366055631)
                      ·
                        rfl

theorem cell23_5334273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 1, 2, 2, 1, 4].length) (baseStart_5334273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5334273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5334273 prefixEnd_5334273 := by exact prefixLift 5334273
  have htrace : WordTrace (prefixWord ++ tailWord_5334273) baseStart_5334273 baseEnd_5334273 := by
    simpa [prefixWord, tailWord_5334273, baseEnd_5334273] using wordTrace_append hprefix tailTrace_5334273
  have hstable : (prefixWord ++ tailWord_5334273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5334273).length < 2 ^ (prefixWord ++ tailWord_5334273).sum := by decide
  have hdescent : baseEnd_5334273 < baseStart_5334273 := by decide
  rcases family_descends (prefixWord ++ tailWord_5334273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5334283 : List Nat := [1, 1, 1, 1, 5, 3, 3, 1, 3, 4]
def baseStart_5334283 : Nat := 118140960795 + 5334283 * 2 ^ 59
def prefixEnd_5334283 : Nat := 4983230072969 + 3 ^ 40 * 5334283 * 2
def baseEnd_5334283 : Nat := 913017042035819442310195

theorem tailTrace_5334283 : CollatzResearch.WordTrace tailWord_5334283 prefixEnd_5334283 913017042035819442310195 := by
  unfold tailWord_5334283
  simp only [CollatzResearch.WordTrace]
  refine ⟨194557284533811188851263503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129704856355874125900842335 194557284533811188851263503)
  ·
    refine ⟨291835926800716783276895255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194557284533811188851263503 291835926800716783276895255)
    ·
      refine ⟨437753890201075174915342883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 291835926800716783276895255 437753890201075174915342883)
      ·
        refine ⟨656630835301612762373014325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 437753890201075174915342883 656630835301612762373014325)
        ·
          refine ⟨61559140809526196472470093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 656630835301612762373014325 61559140809526196472470093)
          ·
            refine ⟨23084677803572323677176285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 61559140809526196472470093 23084677803572323677176285)
            ·
              refine ⟨8656754176339621378941107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23084677803572323677176285 8656754176339621378941107)
              ·
                refine ⟨12985131264509432068411661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8656754176339621378941107 12985131264509432068411661)
                ·
                  refine ⟨4869424224191037025654373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12985131264509432068411661 4869424224191037025654373)
                  ·
                    refine ⟨913017042035819442310195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4869424224191037025654373 913017042035819442310195)
                    ·
                      rfl

theorem cell23_5334283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 3, 1, 3, 4].length) (baseStart_5334283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5334283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5334283 prefixEnd_5334283 := by exact prefixLift 5334283
  have htrace : WordTrace (prefixWord ++ tailWord_5334283) baseStart_5334283 baseEnd_5334283 := by
    simpa [prefixWord, tailWord_5334283, baseEnd_5334283] using wordTrace_append hprefix tailTrace_5334283
  have hstable : (prefixWord ++ tailWord_5334283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5334283).length < 2 ^ (prefixWord ++ tailWord_5334283).sum := by decide
  have hdescent : baseEnd_5334283 < baseStart_5334283 := by decide
  rcases family_descends (prefixWord ++ tailWord_5334283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5334358 : List Nat := [5, 2, 3, 1, 2, 1, 1, 1, 2, 1, 4]
def baseStart_5334358 : Nat := 118140960795 + 5334358 * 2 ^ 59
def prefixEnd_5334358 : Nat := 4983230072969 + 3 ^ 40 * 5334358 * 2
def baseEnd_5334358 : Nat := 2739089637156545533492741

theorem tailTrace_5334358 : CollatzResearch.WordTrace tailWord_5334358 prefixEnd_5334358 2739089637156545533492741 := by
  unfold tailWord_5334358
  simp only [CollatzResearch.WordTrace]
  refine ⟨12160001250533717291265233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 129706680005692984440162485 12160001250533717291265233)
  ·
    refine ⟨9120000937900287968448925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12160001250533717291265233 9120000937900287968448925)
    ·
      refine ⟨3420000351712607988168347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9120000937900287968448925 3420000351712607988168347)
      ·
        refine ⟨5130000527568911982252521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3420000351712607988168347 5130000527568911982252521)
        ·
          refine ⟨3847500395676683986689391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5130000527568911982252521 3847500395676683986689391)
          ·
            refine ⟨5771250593515025980034087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3847500395676683986689391 5771250593515025980034087)
            ·
              refine ⟨8656875890272538970051131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5771250593515025980034087 8656875890272538970051131)
              ·
                refine ⟨12985313835408808455076697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8656875890272538970051131 12985313835408808455076697)
                ·
                  refine ⟨9738985376556606341307523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12985313835408808455076697 9738985376556606341307523)
                  ·
                    refine ⟨14608478064834909511961285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9738985376556606341307523 14608478064834909511961285)
                    ·
                      refine ⟨2739089637156545533492741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14608478064834909511961285 2739089637156545533492741)
                      ·
                        rfl

theorem cell23_5334358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 2, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 2, 1, 1, 1, 2, 1, 4].length) (baseStart_5334358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5334358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5334358 prefixEnd_5334358 := by exact prefixLift 5334358
  have htrace : WordTrace (prefixWord ++ tailWord_5334358) baseStart_5334358 baseEnd_5334358 := by
    simpa [prefixWord, tailWord_5334358, baseEnd_5334358] using wordTrace_append hprefix tailTrace_5334358
  have hstable : (prefixWord ++ tailWord_5334358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5334358).length < 2 ^ (prefixWord ++ tailWord_5334358).sum := by decide
  have hdescent : baseEnd_5334358 < baseStart_5334358 := by decide
  rcases family_descends (prefixWord ++ tailWord_5334358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5334373 : List Nat := [1, 3, 1, 3, 1, 2, 2, 2, 4, 4]
def baseStart_5334373 : Nat := 118140960795 + 5334373 * 2 ^ 59
def prefixEnd_5334373 : Nat := 4983230072969 + 3 ^ 40 * 5334373 * 2
def baseEnd_5334373 : Nat := 913032446455454324935057

theorem tailTrace_5334373 : CollatzResearch.WordTrace tailWord_5334373 prefixEnd_5334373 913032446455454324935057 := by
  unfold tailWord_5334373
  simp only [CollatzResearch.WordTrace]
  refine ⟨194560567103485134222039773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129707044735656756148026515 194560567103485134222039773)
  ·
    refine ⟨72960212663806925333264915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 194560567103485134222039773 72960212663806925333264915)
    ·
      refine ⟨109440318995710387999897373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72960212663806925333264915 109440318995710387999897373)
      ·
        refine ⟨41040119623391395499961515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 109440318995710387999897373 41040119623391395499961515)
        ·
          refine ⟨61560179435087093249942273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41040119623391395499961515 61560179435087093249942273)
          ·
            refine ⟨46170134576315319937456705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61560179435087093249942273 46170134576315319937456705)
            ·
              refine ⟨34627600932236489953092529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46170134576315319937456705 34627600932236489953092529)
              ·
                refine ⟨25970700699177367464819397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34627600932236489953092529 25970700699177367464819397)
                ·
                  refine ⟨4869506381095756399653637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25970700699177367464819397 4869506381095756399653637)
                  ·
                    refine ⟨913032446455454324935057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4869506381095756399653637 913032446455454324935057)
                    ·
                      rfl

theorem cell23_5334373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 2, 2, 4, 4].length) (baseStart_5334373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5334373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5334373 prefixEnd_5334373 := by exact prefixLift 5334373
  have htrace : WordTrace (prefixWord ++ tailWord_5334373) baseStart_5334373 baseEnd_5334373 := by
    simpa [prefixWord, tailWord_5334373, baseEnd_5334373] using wordTrace_append hprefix tailTrace_5334373
  have hstable : (prefixWord ++ tailWord_5334373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5334373).length < 2 ^ (prefixWord ++ tailWord_5334373).sum := by decide
  have hdescent : baseEnd_5334373 < baseStart_5334373 := by decide
  rcases family_descends (prefixWord ++ tailWord_5334373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5334380 : List Nat := [2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 4]
def baseStart_5334380 : Nat := 118140960795 + 5334380 * 2 ^ 59
def prefixEnd_5334380 : Nat := 4983230072969 + 3 ^ 40 * 5334380 * 2
def baseEnd_5334380 : Nat := 2739100933730944447417639

theorem tailTrace_5334380 : CollatzResearch.WordTrace tailWord_5334380 prefixEnd_5334380 2739100933730944447417639 := by
  unfold tailWord_5334380
  simp only [CollatzResearch.WordTrace]
  refine ⟨97280411207229887208772297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129707214942973182945029729 97280411207229887208772297)
  ·
    refine ⟨72960308405422415406579223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97280411207229887208772297 72960308405422415406579223)
    ·
      refine ⟨109440462608133623109868835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72960308405422415406579223 109440462608133623109868835)
      ·
        refine ⟨164160693912200434664803253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109440462608133623109868835 164160693912200434664803253)
        ·
          refine ⟨15390065054268790749825305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 164160693912200434664803253 15390065054268790749825305)
          ·
            refine ⟨11542548790701593062368979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15390065054268790749825305 11542548790701593062368979)
            ·
              refine ⟨17313823186052389593553469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11542548790701593062368979 17313823186052389593553469)
              ·
                refine ⟨6492683694769646097582551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17313823186052389593553469 6492683694769646097582551)
                ·
                  refine ⟨9739025542154469146373827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6492683694769646097582551 9739025542154469146373827)
                  ·
                    refine ⟨14608538313231703719560741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9739025542154469146373827 14608538313231703719560741)
                    ·
                      refine ⟨2739100933730944447417639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14608538313231703719560741 2739100933730944447417639)
                      ·
                        rfl

theorem cell23_5334380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 4].length) (baseStart_5334380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5334380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5334380 prefixEnd_5334380 := by exact prefixLift 5334380
  have htrace : WordTrace (prefixWord ++ tailWord_5334380) baseStart_5334380 baseEnd_5334380 := by
    simpa [prefixWord, tailWord_5334380, baseEnd_5334380] using wordTrace_append hprefix tailTrace_5334380
  have hstable : (prefixWord ++ tailWord_5334380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5334380).length < 2 ^ (prefixWord ++ tailWord_5334380).sum := by decide
  have hdescent : baseEnd_5334380 < baseStart_5334380 := by decide
  rcases family_descends (prefixWord ++ tailWord_5334380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5334386 : List Nat := [3, 2, 1, 2, 1, 2, 12]
def baseStart_5334386 : Nat := 118140960795 + 5334386 * 2 ^ 59
def prefixEnd_5334386 : Nat := 4983230072969 + 3 ^ 40 * 5334386 * 2
def baseEnd_5334386 : Nat := 33816098945862610172131

theorem tailTrace_5334386 : CollatzResearch.WordTrace tailWord_5334386 prefixEnd_5334386 33816098945862610172131 := by
  unfold tailWord_5334386
  simp only [CollatzResearch.WordTrace]
  refine ⟨48640260313109509360565753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129707360834958691628175341 48640260313109509360565753)
  ·
    refine ⟨36480195234832132020424315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48640260313109509360565753 36480195234832132020424315)
    ·
      refine ⟨54720292852248198030636473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36480195234832132020424315 54720292852248198030636473)
      ·
        refine ⟨41040219639186148522977355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54720292852248198030636473 41040219639186148522977355)
        ·
          refine ⟨61560329458779222784466033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41040219639186148522977355 61560329458779222784466033)
          ·
            refine ⟨46170247094084417088349525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61560329458779222784466033 46170247094084417088349525)
            ·
              refine ⟨33816098945862610172131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 46170247094084417088349525 33816098945862610172131)
              ·
                rfl

theorem cell23_5334386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 12].length) (baseStart_5334386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5334386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5334386 prefixEnd_5334386 := by exact prefixLift 5334386
  have htrace : WordTrace (prefixWord ++ tailWord_5334386) baseStart_5334386 baseEnd_5334386 := by
    simpa [prefixWord, tailWord_5334386, baseEnd_5334386] using wordTrace_append hprefix tailTrace_5334386
  have hstable : (prefixWord ++ tailWord_5334386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5334386).length < 2 ^ (prefixWord ++ tailWord_5334386).sum := by decide
  have hdescent : baseEnd_5334386 < baseStart_5334386 := by decide
  rcases family_descends (prefixWord ++ tailWord_5334386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5334397 : List Nat := [1, 4, 1, 1, 2, 2, 4, 1, 3, 2, 2]
def baseStart_5334397 : Nat := 118140960795 + 5334397 * 2 ^ 59
def prefixEnd_5334397 : Nat := 4983230072969 + 3 ^ 40 * 5334397 * 2
def baseEnd_5334397 : Nat := 2739109662902070880905061

theorem tailTrace_5334397 : CollatzResearch.WordTrace tailWord_5334397 prefixEnd_5334397 2739109662902070880905061 := by
  unfold tailWord_5334397
  simp only [CollatzResearch.WordTrace]
  refine ⟨194561442455398186320913445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129707628303598790880608963 194561442455398186320913445)
  ·
    refine ⟨36480270460387159935171271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 194561442455398186320913445 36480270460387159935171271)
    ·
      refine ⟨54720405690580739902756907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36480270460387159935171271 54720405690580739902756907)
      ·
        refine ⟨82080608535871109854135361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54720405690580739902756907 82080608535871109854135361)
        ·
          refine ⟨61560456401903332390601521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82080608535871109854135361 61560456401903332390601521)
          ·
            refine ⟨46170342301427499292951141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61560456401903332390601521 46170342301427499292951141)
            ·
              refine ⟨8656939181517656117428339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 46170342301427499292951141 8656939181517656117428339)
              ·
                refine ⟨12985408772276484176142509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8656939181517656117428339 12985408772276484176142509)
                ·
                  refine ⟨4869528289603681566053441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12985408772276484176142509 4869528289603681566053441)
                  ·
                    refine ⟨3652146217202761174540081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4869528289603681566053441 3652146217202761174540081)
                    ·
                      refine ⟨2739109662902070880905061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3652146217202761174540081 2739109662902070880905061)
                      ·
                        rfl

theorem cell23_5334397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 4, 1, 3, 2, 2].length) (baseStart_5334397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5334397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5334397 prefixEnd_5334397 := by exact prefixLift 5334397
  have htrace : WordTrace (prefixWord ++ tailWord_5334397) baseStart_5334397 baseEnd_5334397 := by
    simpa [prefixWord, tailWord_5334397, baseEnd_5334397] using wordTrace_append hprefix tailTrace_5334397
  have hstable : (prefixWord ++ tailWord_5334397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5334397).length < 2 ^ (prefixWord ++ tailWord_5334397).sum := by decide
  have hdescent : baseEnd_5334397 < baseStart_5334397 := by decide
  rcases family_descends (prefixWord ++ tailWord_5334397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5334407 : List Nat := [1, 1, 4, 2, 2, 3, 3, 1, 2, 4]
def baseStart_5334407 : Nat := 118140960795 + 5334407 * 2 ^ 59
def prefixEnd_5334407 : Nat := 4983230072969 + 3 ^ 40 * 5334407 * 2
def baseEnd_5334407 : Nat := 913038265902871947260005

theorem tailTrace_5334407 : CollatzResearch.WordTrace tailWord_5334407 prefixEnd_5334407 913038265902871947260005 := by
  unfold tailWord_5334407
  simp only [CollatzResearch.WordTrace]
  refine ⟨194561807185361958028777475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129707871456907972019184983 194561807185361958028777475)
  ·
    refine ⟨291842710778042937043166213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194561807185361958028777475 291842710778042937043166213)
    ·
      refine ⟨54720508270883050695593665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 291842710778042937043166213 54720508270883050695593665)
      ·
        refine ⟨41040381203162288021695249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54720508270883050695593665 41040381203162288021695249)
        ·
          refine ⟨30780285902371716016271437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41040381203162288021695249 30780285902371716016271437)
          ·
            refine ⟨11542607213389393506101789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30780285902371716016271437 11542607213389393506101789)
            ·
              refine ⟨4328477705021022564788171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11542607213389393506101789 4328477705021022564788171)
              ·
                refine ⟨6492716557531533847182257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4328477705021022564788171 6492716557531533847182257)
                ·
                  refine ⟨4869537418148650385386693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6492716557531533847182257 4869537418148650385386693)
                  ·
                    refine ⟨913038265902871947260005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4869537418148650385386693 913038265902871947260005)
                    ·
                      rfl

theorem cell23_5334407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 3, 1, 2, 4].length) (baseStart_5334407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5334407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5334407 prefixEnd_5334407 := by exact prefixLift 5334407
  have htrace : WordTrace (prefixWord ++ tailWord_5334407) baseStart_5334407 baseEnd_5334407 := by
    simpa [prefixWord, tailWord_5334407, baseEnd_5334407] using wordTrace_append hprefix tailTrace_5334407
  have hstable : (prefixWord ++ tailWord_5334407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5334407).length < 2 ^ (prefixWord ++ tailWord_5334407).sum := by decide
  have hdescent : baseEnd_5334407 < baseStart_5334407 := by decide
  rcases family_descends (prefixWord ++ tailWord_5334407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5334420 : List Nat := [2, 4, 2, 1, 2, 1, 4, 7]
def baseStart_5334420 : Nat := 118140960795 + 5334420 * 2 ^ 59
def prefixEnd_5334420 : Nat := 4983230072969 + 3 ^ 40 * 5334420 * 2
def baseEnd_5334420 : Nat := 101448943442856455219165

theorem tailTrace_5334420 : CollatzResearch.WordTrace tailWord_5334420 prefixEnd_5334420 101448943442856455219165 := by
  unfold tailWord_5334420
  simp only [CollatzResearch.WordTrace]
  refine ⟨97281140667157430624500357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129708187556209907499333809 97281140667157430624500357)
  ·
    refine ⟨18240213875092018242093817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 97281140667157430624500357 18240213875092018242093817)
    ·
      refine ⟨13680160406319013681570363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18240213875092018242093817 13680160406319013681570363)
      ·
        refine ⟨20520240609478520522355545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13680160406319013681570363 20520240609478520522355545)
        ·
          refine ⟨15390180457108890391766659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20520240609478520522355545 15390180457108890391766659)
          ·
            refine ⟨23085270685663335587649989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15390180457108890391766659 23085270685663335587649989)
            ·
              refine ⟨4328488253561875422684373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23085270685663335587649989 4328488253561875422684373)
              ·
                refine ⟨101448943442856455219165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4328488253561875422684373 101448943442856455219165)
                ·
                  rfl

theorem cell23_5334420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 4, 7].length) (baseStart_5334420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5334420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5334420 prefixEnd_5334420 := by exact prefixLift 5334420
  have htrace : WordTrace (prefixWord ++ tailWord_5334420) baseStart_5334420 baseEnd_5334420 := by
    simpa [prefixWord, tailWord_5334420, baseEnd_5334420] using wordTrace_append hprefix tailTrace_5334420
  have hstable : (prefixWord ++ tailWord_5334420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5334420).length < 2 ^ (prefixWord ++ tailWord_5334420).sum := by decide
  have hdescent : baseEnd_5334420 < baseStart_5334420 := by decide
  rcases family_descends (prefixWord ++ tailWord_5334420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5334431 : List Nat := [1, 1, 2, 5, 1, 4, 1, 3, 1, 2, 2]
def baseStart_5334431 : Nat := 118140960795 + 5334431 * 2 ^ 59
def prefixEnd_5334431 : Nat := 4983230072969 + 3 ^ 40 * 5334431 * 2
def baseEnd_5334431 : Nat := 2739127121244323747879905

theorem tailTrace_5334431 : CollatzResearch.WordTrace tailWord_5334431 prefixEnd_5334431 2739127121244323747879905 := by
  unfold tailWord_5334431
  simp only [CollatzResearch.WordTrace]
  refine ⟨194562682537275010127651147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129708455024850006751767431 194562682537275010127651147)
  ·
    refine ⟨291844023805912515191476721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194562682537275010127651147 291844023805912515191476721)
    ·
      refine ⟨218883017854434386393607541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 291844023805912515191476721 218883017854434386393607541)
      ·
        refine ⟨20520282923853223724400707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 218883017854434386393607541 20520282923853223724400707)
        ·
          refine ⟨30780424385779835586601061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20520282923853223724400707 30780424385779835586601061)
          ·
            refine ⟨5771329572333719172487699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30780424385779835586601061 5771329572333719172487699)
            ·
              refine ⟨8656994358500578758731549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5771329572333719172487699 8656994358500578758731549)
              ·
                refine ⟨3246372884437717034524331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8656994358500578758731549 3246372884437717034524331)
                ·
                  refine ⟨4869559326656575551786497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3246372884437717034524331 4869559326656575551786497)
                  ·
                    refine ⟨3652169494992431663839873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4869559326656575551786497 3652169494992431663839873)
                    ·
                      refine ⟨2739127121244323747879905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3652169494992431663839873 2739127121244323747879905)
                      ·
                        rfl

theorem cell23_5334431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 4, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 4, 1, 3, 1, 2, 2].length) (baseStart_5334431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5334431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5334431 prefixEnd_5334431 := by exact prefixLift 5334431
  have htrace : WordTrace (prefixWord ++ tailWord_5334431) baseStart_5334431 baseEnd_5334431 := by
    simpa [prefixWord, tailWord_5334431, baseEnd_5334431] using wordTrace_append hprefix tailTrace_5334431
  have hstable : (prefixWord ++ tailWord_5334431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5334431).length < 2 ^ (prefixWord ++ tailWord_5334431).sum := by decide
  have hdescent : baseEnd_5334431 < baseStart_5334431 := by decide
  rcases family_descends (prefixWord ++ tailWord_5334431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5334474 : List Nat := [3, 1, 2, 1, 2, 5, 1, 2, 1, 3, 2]
def baseStart_5334474 : Nat := 118140960795 + 5334474 * 2 ^ 59
def prefixEnd_5334474 : Nat := 4983230072969 + 3 ^ 40 * 5334474 * 2
def baseEnd_5334474 : Nat := 2739149200912467079642207

theorem tailTrace_5334474 : CollatzResearch.WordTrace tailWord_5334474 prefixEnd_5334474 2739149200912467079642207 := by
  unfold tailWord_5334474
  simp only [CollatzResearch.WordTrace]
  refine ⟨48641062719029807117866619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129709500584079485647644317 48641062719029807117866619)
  ·
    refine ⟨72961594078544710676799929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48641062719029807117866619 72961594078544710676799929)
    ·
      refine ⟨54721195558908533007599947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72961594078544710676799929 54721195558908533007599947)
      ·
        refine ⟨82081793338362799511399921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54721195558908533007599947 82081793338362799511399921)
        ·
          refine ⟨61561345003772099633549941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82081793338362799511399921 61561345003772099633549941)
          ·
            refine ⟨5771376094103634340645307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 61561345003772099633549941 5771376094103634340645307)
            ·
              refine ⟨8657064141155451510967961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5771376094103634340645307 8657064141155451510967961)
              ·
                refine ⟨6492798105866588633225971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8657064141155451510967961 6492798105866588633225971)
                ·
                  refine ⟨9739197158799882949838957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6492798105866588633225971 9739197158799882949838957)
                  ·
                    refine ⟨3652198934549956106189609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9739197158799882949838957 3652198934549956106189609)
                    ·
                      refine ⟨2739149200912467079642207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3652198934549956106189609 2739149200912467079642207)
                      ·
                        rfl

theorem cell23_5334474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 5, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 5, 1, 2, 1, 3, 2].length) (baseStart_5334474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5334474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5334474 prefixEnd_5334474 := by exact prefixLift 5334474
  have htrace : WordTrace (prefixWord ++ tailWord_5334474) baseStart_5334474 baseEnd_5334474 := by
    simpa [prefixWord, tailWord_5334474, baseEnd_5334474] using wordTrace_append hprefix tailTrace_5334474
  have hstable : (prefixWord ++ tailWord_5334474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5334474).length < 2 ^ (prefixWord ++ tailWord_5334474).sum := by decide
  have hdescent : baseEnd_5334474 < baseStart_5334474 := by decide
  rcases family_descends (prefixWord ++ tailWord_5334474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5334504 : List Nat := [2, 1, 4, 1, 1, 2, 4, 2, 2, 2, 2]
def baseStart_5334504 : Nat := 118140960795 + 5334504 * 2 ^ 59
def prefixEnd_5334504 : Nat := 4983230072969 + 3 ^ 40 * 5334504 * 2
def baseEnd_5334504 : Nat := 2739164605332101962267069

theorem tailTrace_5334504 : CollatzResearch.WordTrace tailWord_5334504 prefixEnd_5334504 2739164605332101962267069 := by
  unfold tailWord_5334504
  simp only [CollatzResearch.WordTrace]
  refine ⟨97282672533005271797529283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129710230044007029063372377 97282672533005271797529283)
  ·
    refine ⟨145924008799507907696293925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97282672533005271797529283 145924008799507907696293925)
    ·
      refine ⟨27360751649907732693055111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 145924008799507907696293925 27360751649907732693055111)
      ·
        refine ⟨41041127474861599039582667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27360751649907732693055111 41041127474861599039582667)
        ·
          refine ⟨61561691212292398559374001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41041127474861599039582667 61561691212292398559374001)
          ·
            refine ⟨46171268409219298919530501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61561691212292398559374001 46171268409219298919530501)
            ·
              refine ⟨8657112826728618547411969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 46171268409219298919530501 8657112826728618547411969)
              ·
                refine ⟨6492834620046463910558977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8657112826728618547411969 6492834620046463910558977)
                ·
                  refine ⟨4869625965034847932919233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6492834620046463910558977 4869625965034847932919233)
                  ·
                    refine ⟨3652219473776135949689425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4869625965034847932919233 3652219473776135949689425)
                    ·
                      refine ⟨2739164605332101962267069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3652219473776135949689425 2739164605332101962267069)
                      ·
                        rfl

theorem cell23_5334504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 4, 2, 2, 2, 2].length) (baseStart_5334504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5334504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5334504 prefixEnd_5334504 := by exact prefixLift 5334504
  have htrace : WordTrace (prefixWord ++ tailWord_5334504) baseStart_5334504 baseEnd_5334504 := by
    simpa [prefixWord, tailWord_5334504, baseEnd_5334504] using wordTrace_append hprefix tailTrace_5334504
  have hstable : (prefixWord ++ tailWord_5334504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5334504).length < 2 ^ (prefixWord ++ tailWord_5334504).sum := by decide
  have hdescent : baseEnd_5334504 < baseStart_5334504 := by decide
  rcases family_descends (prefixWord ++ tailWord_5334504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5334517 : List Nat := [1, 3, 5, 1, 1, 2, 1, 1, 2, 2, 4]
def baseStart_5334517 : Nat := 118140960795 + 5334517 * 2 ^ 59
def prefixEnd_5334517 : Nat := 4983230072969 + 3 ^ 40 * 5334517 * 2
def baseEnd_5334517 : Nat := 2739171280580610411404509

theorem tailTrace_5334517 : CollatzResearch.WordTrace tailWord_5334517 prefixEnd_5334517 2739171280580610411404509 := by
  unfold tailWord_5334517
  simp only [CollatzResearch.WordTrace]
  refine ⟨194565819214963446815281805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129710546143308964543521203 194565819214963446815281805)
  ·
    refine ⟨72962182205611292555730677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 194565819214963446815281805 72962182205611292555730677)
    ·
      refine ⟨6840204581776058677099751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 72962182205611292555730677 6840204581776058677099751)
      ·
        refine ⟨10260306872664088015649627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6840204581776058677099751 10260306872664088015649627)
        ·
          refine ⟨15390460308996132023474441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10260306872664088015649627 15390460308996132023474441)
          ·
            refine ⟨11542845231747099017605831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15390460308996132023474441 11542845231747099017605831)
            ·
              refine ⟨17314267847620648526408747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11542845231747099017605831 17314267847620648526408747)
              ·
                refine ⟨25971401771430972789613121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17314267847620648526408747 25971401771430972789613121)
                ·
                  refine ⟨19478551328573229592209841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25971401771430972789613121 19478551328573229592209841)
                  ·
                    refine ⟨14608913496429922194157381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19478551328573229592209841 14608913496429922194157381)
                    ·
                      refine ⟨2739171280580610411404509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14608913496429922194157381 2739171280580610411404509)
                      ·
                        rfl

theorem cell23_5334517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 1, 1, 2, 2, 4].length) (baseStart_5334517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5334517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5334517 prefixEnd_5334517 := by exact prefixLift 5334517
  have htrace : WordTrace (prefixWord ++ tailWord_5334517) baseStart_5334517 baseEnd_5334517 := by
    simpa [prefixWord, tailWord_5334517, baseEnd_5334517] using wordTrace_append hprefix tailTrace_5334517
  have hstable : (prefixWord ++ tailWord_5334517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5334517).length < 2 ^ (prefixWord ++ tailWord_5334517).sum := by decide
  have hdescent : baseEnd_5334517 < baseStart_5334517 := by decide
  rcases family_descends (prefixWord ++ tailWord_5334517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5334520 : List Nat := [2, 1, 2, 1, 1, 6, 1, 1, 2, 3, 3]
def baseStart_5334520 : Nat := 118140960795 + 5334520 * 2 ^ 59
def prefixEnd_5334520 : Nat := 4983230072969 + 3 ^ 40 * 5334520 * 2
def baseEnd_5334520 : Nat := 2739172821022573899666995

theorem tailTrace_5334520 : CollatzResearch.WordTrace tailWord_5334520 prefixEnd_5334520 2739172821022573899666995 := by
  unfold tailWord_5334520
  simp only [CollatzResearch.WordTrace]
  refine ⟨97282964316976289163820507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129710619089301718885094009 97282964316976289163820507)
  ·
    refine ⟨145924446475464433745730761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97282964316976289163820507 145924446475464433745730761)
    ·
      refine ⟨109443334856598325309298071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 145924446475464433745730761 109443334856598325309298071)
      ·
        refine ⟨164165002284897487963947107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109443334856598325309298071 164165002284897487963947107)
        ·
          refine ⟨246247503427346231945920661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 164165002284897487963947107 246247503427346231945920661)
          ·
            refine ⟨11542851723156854622465031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 246247503427346231945920661 11542851723156854622465031)
            ·
              refine ⟨17314277584735281933697547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11542851723156854622465031 17314277584735281933697547)
              ·
                refine ⟨25971416377102922900546321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17314277584735281933697547 25971416377102922900546321)
                ·
                  refine ⟨19478562282827192175409741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25971416377102922900546321 19478562282827192175409741)
                  ·
                    refine ⟨7304460856060197065778653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19478562282827192175409741 7304460856060197065778653)
                    ·
                      refine ⟨2739172821022573899666995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7304460856060197065778653 2739172821022573899666995)
                      ·
                        rfl

theorem cell23_5334520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 1, 1, 2, 3, 3].length) (baseStart_5334520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5334520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5334520 prefixEnd_5334520 := by exact prefixLift 5334520
  have htrace : WordTrace (prefixWord ++ tailWord_5334520) baseStart_5334520 baseEnd_5334520 := by
    simpa [prefixWord, tailWord_5334520, baseEnd_5334520] using wordTrace_append hprefix tailTrace_5334520
  have hstable : (prefixWord ++ tailWord_5334520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5334520).length < 2 ^ (prefixWord ++ tailWord_5334520).sum := by decide
  have hdescent : baseEnd_5334520 < baseStart_5334520 := by decide
  rcases family_descends (prefixWord ++ tailWord_5334520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5334540 : List Nat := [2, 2, 1, 2, 5, 1, 1, 1, 1, 7]
def baseStart_5334540 : Nat := 118140960795 + 5334540 * 2 ^ 59
def prefixEnd_5334540 : Nat := 4983230072969 + 3 ^ 40 * 5334540 * 2
def baseEnd_5334540 : Nat := 913061030211887940472301

theorem tailTrace_5334540 : CollatzResearch.WordTrace tailWord_5334540 prefixEnd_5334540 913061030211887940472301 := by
  unfold tailWord_5334540
  simp only [CollatzResearch.WordTrace]
  refine ⟨97283329046940060871684537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129711105395920081162246049 97283329046940060871684537)
  ·
    refine ⟨72962496785205045653763403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97283329046940060871684537 72962496785205045653763403)
    ·
      refine ⟨109443745177807568480645105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72962496785205045653763403 109443745177807568480645105)
      ·
        refine ⟨82082808883355676360483829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 109443745177807568480645105 82082808883355676360483829)
        ·
          refine ⟨7695263332814594658795359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 82082808883355676360483829 7695263332814594658795359)
          ·
            refine ⟨11542894999221891988193039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7695263332814594658795359 11542894999221891988193039)
            ·
              refine ⟨17314342498832837982289559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11542894999221891988193039 17314342498832837982289559)
              ·
                refine ⟨25971513748249256973434339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17314342498832837982289559 25971513748249256973434339)
                ·
                  refine ⟨38957270622373885460151509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25971513748249256973434339 38957270622373885460151509)
                  ·
                    refine ⟨913061030211887940472301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 38957270622373885460151509 913061030211887940472301)
                    ·
                      rfl

theorem cell23_5334540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 1, 1, 1, 7].length) (baseStart_5334540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5334540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5334540 prefixEnd_5334540 := by exact prefixLift 5334540
  have htrace : WordTrace (prefixWord ++ tailWord_5334540) baseStart_5334540 baseEnd_5334540 := by
    simpa [prefixWord, tailWord_5334540, baseEnd_5334540] using wordTrace_append hprefix tailTrace_5334540
  have hstable : (prefixWord ++ tailWord_5334540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5334540).length < 2 ^ (prefixWord ++ tailWord_5334540).sum := by decide
  have hdescent : baseEnd_5334540 < baseStart_5334540 := by decide
  rcases family_descends (prefixWord ++ tailWord_5334540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5334604 : List Nat := [2, 2, 1, 3, 1, 3, 3, 3, 1, 4]
def baseStart_5334604 : Nat := 118140960795 + 5334604 * 2 ^ 59
def prefixEnd_5334604 : Nat := 4983230072969 + 3 ^ 40 * 5334604 * 2
def baseEnd_5334604 : Nat := 913071984465850523672203

theorem tailTrace_5334604 : CollatzResearch.WordTrace tailWord_5334604 prefixEnd_5334604 913071984465850523672203 := by
  unfold tailWord_5334604
  simp only [CollatzResearch.WordTrace]
  refine ⟨97284496182824130336849433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129712661577098840449132577 97284496182824130336849433)
  ·
    refine ⟨72963372137118097752637075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97284496182824130336849433 72963372137118097752637075)
    ·
      refine ⟨109445058205677146628955613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72963372137118097752637075 109445058205677146628955613)
      ·
        refine ⟨41041896827128929985858355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 109445058205677146628955613 41041896827128929985858355)
        ·
          refine ⟨61562845240693394978787533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41041896827128929985858355 61562845240693394978787533)
          ·
            refine ⟨23086066965260023117045325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 61562845240693394978787533 23086066965260023117045325)
            ·
              refine ⟨8657275111972508668891997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23086066965260023117045325 8657275111972508668891997)
              ·
                refine ⟨3246478166989690750834499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8657275111972508668891997 3246478166989690750834499)
                ·
                  refine ⟨4869717250484536126251749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3246478166989690750834499 4869717250484536126251749)
                  ·
                    refine ⟨913071984465850523672203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4869717250484536126251749 913071984465850523672203)
                    ·
                      rfl

theorem cell23_5334604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 3, 3, 1, 4].length) (baseStart_5334604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5334604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5334604 prefixEnd_5334604 := by exact prefixLift 5334604
  have htrace : WordTrace (prefixWord ++ tailWord_5334604) baseStart_5334604 baseEnd_5334604 := by
    simpa [prefixWord, tailWord_5334604, baseEnd_5334604] using wordTrace_append hprefix tailTrace_5334604
  have hstable : (prefixWord ++ tailWord_5334604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5334604).length < 2 ^ (prefixWord ++ tailWord_5334604).sum := by decide
  have hdescent : baseEnd_5334604 < baseStart_5334604 := by decide
  rcases family_descends (prefixWord ++ tailWord_5334604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5334623 : List Nat := [1, 1, 2, 3, 1, 1, 1, 1, 4, 1, 7]
def baseStart_5334623 : Nat := 118140960795 + 5334623 * 2 ^ 59
def prefixEnd_5334623 : Nat := 4983230072969 + 3 ^ 40 * 5334623 * 2
def baseEnd_5334623 : Nat := 2739225709529986996679021

theorem tailTrace_5334623 : CollatzResearch.WordTrace tailWord_5334623 prefixEnd_5334623 2739225709529986996679021 := by
  unfold tailWord_5334623
  simp only [CollatzResearch.WordTrace]
  refine ⟨194569685352579426918640523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129713123568386284612427015 194569685352579426918640523)
  ·
    refine ⟨291854528028869140377960785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194569685352579426918640523 291854528028869140377960785)
    ·
      refine ⟨218890896021651855283470589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 291854528028869140377960785 218890896021651855283470589)
      ·
        refine ⟨82084086008119445731301471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 218890896021651855283470589 82084086008119445731301471)
        ·
          refine ⟨123126129012179168596952207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82084086008119445731301471 123126129012179168596952207)
          ·
            refine ⟨184689193518268752895428311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 123126129012179168596952207 184689193518268752895428311)
            ·
              refine ⟨277033790277403129343142467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 184689193518268752895428311 277033790277403129343142467)
              ·
                refine ⟨415550685416104694014713701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 277033790277403129343142467 415550685416104694014713701)
                ·
                  refine ⟨77915753515519630127758819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 415550685416104694014713701 77915753515519630127758819)
                  ·
                    refine ⟨116873630273279445191638229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 77915753515519630127758819 116873630273279445191638229)
                    ·
                      refine ⟨2739225709529986996679021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 116873630273279445191638229 2739225709529986996679021)
                      ·
                        rfl

theorem cell23_5334623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 1, 4, 1, 7].length) (baseStart_5334623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5334623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5334623 prefixEnd_5334623 := by exact prefixLift 5334623
  have htrace : WordTrace (prefixWord ++ tailWord_5334623) baseStart_5334623 baseEnd_5334623 := by
    simpa [prefixWord, tailWord_5334623, baseEnd_5334623] using wordTrace_append hprefix tailTrace_5334623
  have hstable : (prefixWord ++ tailWord_5334623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5334623).length < 2 ^ (prefixWord ++ tailWord_5334623).sum := by decide
  have hdescent : baseEnd_5334623 < baseStart_5334623 := by decide
  rcases family_descends (prefixWord ++ tailWord_5334623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5334634 : List Nat := [3, 1, 3, 2, 1, 4, 2, 1, 6]
def baseStart_5334634 : Nat := 118140960795 + 5334634 * 2 ^ 59
def prefixEnd_5334634 : Nat := 4983230072969 + 3 ^ 40 * 5334634 * 2
def baseEnd_5334634 : Nat := 304359039757465161515719

theorem tailTrace_5334634 : CollatzResearch.WordTrace tailWord_5334634 prefixEnd_5334634 304359039757465161515719 := by
  unfold tailWord_5334634
  simp only [CollatzResearch.WordTrace]
  refine ⟨48642521638884893949322739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129713391037026383864860637 48642521638884893949322739)
  ·
    refine ⟨72963782458327340923984109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48642521638884893949322739 72963782458327340923984109)
    ·
      refine ⟨27361418421872752846494041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72963782458327340923984109 27361418421872752846494041)
      ·
        refine ⟨20521063816404564634870531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27361418421872752846494041 20521063816404564634870531)
        ·
          refine ⟨30781595724606846952305797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20521063816404564634870531 30781595724606846952305797)
          ·
            refine ⟨5771549198363783803557337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30781595724606846952305797 5771549198363783803557337)
            ·
              refine ⟨4328661898772837852668003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5771549198363783803557337 4328661898772837852668003)
              ·
                refine ⟨6492992848159256779002005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4328661898772837852668003 6492992848159256779002005)
                ·
                  refine ⟨304359039757465161515719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6492992848159256779002005 304359039757465161515719)
                  ·
                    rfl

theorem cell23_5334634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 4, 2, 1, 6].length) (baseStart_5334634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5334634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5334634 prefixEnd_5334634 := by exact prefixLift 5334634
  have htrace : WordTrace (prefixWord ++ tailWord_5334634) baseStart_5334634 baseEnd_5334634 := by
    simpa [prefixWord, tailWord_5334634, baseEnd_5334634] using wordTrace_append hprefix tailTrace_5334634
  have hstable : (prefixWord ++ tailWord_5334634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5334634).length < 2 ^ (prefixWord ++ tailWord_5334634).sum := by decide
  have hdescent : baseEnd_5334634 < baseStart_5334634 := by decide
  rcases family_descends (prefixWord ++ tailWord_5334634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5334701 : List Nat := [1, 5, 2, 1, 1, 1, 3, 2, 3, 2, 2]
def baseStart_5334701 : Nat := 118140960795 + 5334701 * 2 ^ 59
def prefixEnd_5334701 : Nat := 4983230072969 + 3 ^ 40 * 5334701 * 2
def baseEnd_5334701 : Nat := 2739265761021037691503663

theorem tailTrace_5334701 : CollatzResearch.WordTrace tailWord_5334701 prefixEnd_5334701 2739265761021037691503663 := by
  unfold tailWord_5334701
  simp only [CollatzResearch.WordTrace]
  refine ⟨194572530246296846239979957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129715020164197897493319971 194572530246296846239979957)
  ·
    refine ⟨18241174710590329334998121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 194572530246296846239979957 18241174710590329334998121)
    ·
      refine ⟨13680881032942747001248591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18241174710590329334998121 13680881032942747001248591)
      ·
        refine ⟨20521321549414120501872887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13680881032942747001248591 20521321549414120501872887)
        ·
          refine ⟨30781982324121180752809331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20521321549414120501872887 30781982324121180752809331)
          ·
            refine ⟨46172973486181771129213997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30781982324121180752809331 46172973486181771129213997)
            ·
              refine ⟨17314865057318164173455249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46172973486181771129213997 17314865057318164173455249)
              ·
                refine ⟨12986148792988623130091437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17314865057318164173455249 12986148792988623130091437)
                ·
                  refine ⟨4869805797370733673784289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12986148792988623130091437 4869805797370733673784289)
                  ·
                    refine ⟨3652354348028050255338217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4869805797370733673784289 3652354348028050255338217)
                    ·
                      refine ⟨2739265761021037691503663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3652354348028050255338217 2739265761021037691503663)
                      ·
                        rfl

theorem cell23_5334701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 3, 2, 3, 2, 2].length) (baseStart_5334701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5334701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5334701 prefixEnd_5334701 := by exact prefixLift 5334701
  have htrace : WordTrace (prefixWord ++ tailWord_5334701) baseStart_5334701 baseEnd_5334701 := by
    simpa [prefixWord, tailWord_5334701, baseEnd_5334701] using wordTrace_append hprefix tailTrace_5334701
  have hstable : (prefixWord ++ tailWord_5334701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5334701).length < 2 ^ (prefixWord ++ tailWord_5334701).sum := by decide
  have hdescent : baseEnd_5334701 < baseStart_5334701 := by decide
  rcases family_descends (prefixWord ++ tailWord_5334701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5334717 : List Nat := [1, 4, 1, 2, 1, 2, 1, 4, 1, 3, 3]
def baseStart_5334717 : Nat := 118140960795 + 5334717 * 2 ^ 59
def prefixEnd_5334717 : Nat := 4983230072969 + 3 ^ 40 * 5334717 * 2
def baseEnd_5334717 : Nat := 2739273976711509628903589

theorem tailTrace_5334717 : CollatzResearch.WordTrace tailWord_5334717 prefixEnd_5334717 2739273976711509628903589 := by
  unfold tailWord_5334717
  simp only [CollatzResearch.WordTrace]
  refine ⟨194573113814238880972562405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129715409209492587315041603 194573113814238880972562405)
  ·
    refine ⟨36482458840169790182355451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 194573113814238880972562405 36482458840169790182355451)
    ·
      refine ⟨54723688260254685273533177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36482458840169790182355451 54723688260254685273533177)
      ·
        refine ⟨41042766195191013955149883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54723688260254685273533177 41042766195191013955149883)
        ·
          refine ⟨61564149292786520932724825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41042766195191013955149883 61564149292786520932724825)
          ·
            refine ⟨46173111969589890699543619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61564149292786520932724825 46173111969589890699543619)
            ·
              refine ⟨69259667954384836049315429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46173111969589890699543619 69259667954384836049315429)
              ·
                refine ⟨12986187741447156759246643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 69259667954384836049315429 12986187741447156759246643)
                ·
                  refine ⟨19479281612170735138869965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12986187741447156759246643 19479281612170735138869965)
                  ·
                    refine ⟨7304730604564025677076237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19479281612170735138869965 7304730604564025677076237)
                    ·
                      refine ⟨2739273976711509628903589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7304730604564025677076237 2739273976711509628903589)
                      ·
                        rfl

theorem cell23_5334717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 4, 1, 3, 3].length) (baseStart_5334717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5334717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5334717 prefixEnd_5334717 := by exact prefixLift 5334717
  have htrace : WordTrace (prefixWord ++ tailWord_5334717) baseStart_5334717 baseEnd_5334717 := by
    simpa [prefixWord, tailWord_5334717, baseEnd_5334717] using wordTrace_append hprefix tailTrace_5334717
  have hstable : (prefixWord ++ tailWord_5334717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5334717).length < 2 ^ (prefixWord ++ tailWord_5334717).sum := by decide
  have hdescent : baseEnd_5334717 < baseStart_5334717 := by decide
  rcases family_descends (prefixWord ++ tailWord_5334717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5334718 : List Nat := [4, 2, 1, 1, 2, 2, 1, 5, 1, 2, 2]
def baseStart_5334718 : Nat := 118140960795 + 5334718 * 2 ^ 59
def prefixEnd_5334718 : Nat := 4983230072969 + 3 ^ 40 * 5334718 * 2
def baseEnd_5334718 : Nat := 2739274490192164124991085

theorem tailTrace_5334718 : CollatzResearch.WordTrace tailWord_5334718 prefixEnd_5334718 2739274490192164124991085 := by
  unfold tailWord_5334718
  simp only [CollatzResearch.WordTrace]
  refine ⟨24321643785904407267918601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 129715433524823505428899205 24321643785904407267918601)
  ·
    refine ⟨18241232839428305450938951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24321643785904407267918601 18241232839428305450938951)
    ·
      refine ⟨27361849259142458176408427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18241232839428305450938951 27361849259142458176408427)
      ·
        refine ⟨41042773888713687264612641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27361849259142458176408427 41042773888713687264612641)
        ·
          refine ⟨30782080416535265448459481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41042773888713687264612641 30782080416535265448459481)
          ·
            refine ⟨23086560312401449086344611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30782080416535265448459481 23086560312401449086344611)
            ·
              refine ⟨34629840468602173629516917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23086560312401449086344611 34629840468602173629516917)
              ·
                refine ⟨3246547543931453777767211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 34629840468602173629516917 3246547543931453777767211)
                ·
                  refine ⟨4869821315897180666650817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3246547543931453777767211 4869821315897180666650817)
                  ·
                    refine ⟨3652365986922885499988113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4869821315897180666650817 3652365986922885499988113)
                    ·
                      refine ⟨2739274490192164124991085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3652365986922885499988113 2739274490192164124991085)
                      ·
                        rfl

theorem cell23_5334718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 1, 5, 1, 2, 2].length) (baseStart_5334718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5334718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5334718 prefixEnd_5334718 := by exact prefixLift 5334718
  have htrace : WordTrace (prefixWord ++ tailWord_5334718) baseStart_5334718 baseEnd_5334718 := by
    simpa [prefixWord, tailWord_5334718, baseEnd_5334718] using wordTrace_append hprefix tailTrace_5334718
  have hstable : (prefixWord ++ tailWord_5334718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5334718).length < 2 ^ (prefixWord ++ tailWord_5334718).sum := by decide
  have hdescent : baseEnd_5334718 < baseStart_5334718 := by decide
  rcases family_descends (prefixWord ++ tailWord_5334718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5334734 : List Nat := [4, 1, 1, 1, 3, 1, 3, 1, 4, 1, 3]
def baseStart_5334734 : Nat := 118140960795 + 5334734 * 2 ^ 59
def prefixEnd_5334734 : Nat := 4983230072969 + 3 ^ 40 * 5334734 * 2
def baseEnd_5334734 : Nat := 2739282705882636062391011

theorem tailTrace_5334734 : CollatzResearch.WordTrace tailWord_5334734 prefixEnd_5334734 2739282705882636062391011 := by
  unfold tailWord_5334734
  simp only [CollatzResearch.WordTrace]
  refine ⟨24321716731897161609491407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 129715822570118195250620837 24321716731897161609491407)
  ·
    refine ⟨36482575097845742414237111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24321716731897161609491407 36482575097845742414237111)
    ·
      refine ⟨54723862646768613621355667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36482575097845742414237111 54723862646768613621355667)
      ·
        refine ⟨82085793970152920432033501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54723862646768613621355667 82085793970152920432033501)
        ·
          refine ⟨30782172738807345162012563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 82085793970152920432033501 30782172738807345162012563)
          ·
            refine ⟨46173259108211017743018845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30782172738807345162012563 46173259108211017743018845)
            ·
              refine ⟨17314972165579131653632067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46173259108211017743018845 17314972165579131653632067)
              ·
                refine ⟨25972458248368697480448101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17314972165579131653632067 25972458248368697480448101)
                ·
                  refine ⟨4869835921569130777584019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25972458248368697480448101 4869835921569130777584019)
                  ·
                    refine ⟨7304753882353696166376029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4869835921569130777584019 7304753882353696166376029)
                    ·
                      refine ⟨2739282705882636062391011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7304753882353696166376029 2739282705882636062391011)
                      ·
                        rfl

theorem cell23_5334734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 3, 1, 4, 1, 3].length) (baseStart_5334734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5334734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5334734 prefixEnd_5334734 := by exact prefixLift 5334734
  have htrace : WordTrace (prefixWord ++ tailWord_5334734) baseStart_5334734 baseEnd_5334734 := by
    simpa [prefixWord, tailWord_5334734, baseEnd_5334734] using wordTrace_append hprefix tailTrace_5334734
  have hstable : (prefixWord ++ tailWord_5334734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5334734).length < 2 ^ (prefixWord ++ tailWord_5334734).sum := by decide
  have hdescent : baseEnd_5334734 < baseStart_5334734 := by decide
  rcases family_descends (prefixWord ++ tailWord_5334734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5334748 : List Nat := [2, 2, 5, 1, 3, 1, 1, 1, 1, 2, 4]
def baseStart_5334748 : Nat := 118140960795 + 5334748 * 2 ^ 59
def prefixEnd_5334748 : Nat := 4983230072969 + 3 ^ 40 * 5334748 * 2
def baseEnd_5334748 : Nat := 2739289894611799007615947

theorem tailTrace_5334748 : CollatzResearch.WordTrace tailWord_5334748 prefixEnd_5334748 2739289894611799007615947 := by
  unfold tailWord_5334748
  simp only [CollatzResearch.WordTrace]
  refine ⟨97287122238563286633470449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129716162984751048844627265 97287122238563286633470449)
  ·
    refine ⟨72965341678922464975102837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97287122238563286633470449 72965341678922464975102837)
    ·
      refine ⟨6840500782398981091415891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 72965341678922464975102837 6840500782398981091415891)
      ·
        refine ⟨10260751173598471637123837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6840500782398981091415891 10260751173598471637123837)
        ·
          refine ⟨3847781690099426863921439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10260751173598471637123837 3847781690099426863921439)
          ·
            refine ⟨5771672535149140295882159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3847781690099426863921439 5771672535149140295882159)
            ·
              refine ⟨8657508802723710443823239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5771672535149140295882159 8657508802723710443823239)
              ·
                refine ⟨12986263204085565665734859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8657508802723710443823239 12986263204085565665734859)
                ·
                  refine ⟨19479394806128348498602289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12986263204085565665734859 19479394806128348498602289)
                  ·
                    refine ⟨14609546104596261373951717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19479394806128348498602289 14609546104596261373951717)
                    ·
                      refine ⟨2739289894611799007615947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14609546104596261373951717 2739289894611799007615947)
                      ·
                        rfl

theorem cell23_5334748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 3, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 3, 1, 1, 1, 1, 2, 4].length) (baseStart_5334748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5334748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5334748 prefixEnd_5334748 := by exact prefixLift 5334748
  have htrace : WordTrace (prefixWord ++ tailWord_5334748) baseStart_5334748 baseEnd_5334748 := by
    simpa [prefixWord, tailWord_5334748, baseEnd_5334748] using wordTrace_append hprefix tailTrace_5334748
  have hstable : (prefixWord ++ tailWord_5334748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5334748).length < 2 ^ (prefixWord ++ tailWord_5334748).sum := by decide
  have hdescent : baseEnd_5334748 < baseStart_5334748 := by decide
  rcases family_descends (prefixWord ++ tailWord_5334748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5334751 : List Nat := [1, 1, 2, 3, 2, 2, 5, 1, 2, 1, 3]
def baseStart_5334751 : Nat := 118140960795 + 5334751 * 2 ^ 59
def prefixEnd_5334751 : Nat := 4983230072969 + 3 ^ 40 * 5334751 * 2
def baseEnd_5334751 : Nat := 2739291435053762495878433

theorem tailTrace_5334751 : CollatzResearch.WordTrace tailWord_5334751 prefixEnd_5334751 2739291435053762495878433 := by
  unfold tailWord_5334751
  simp only [CollatzResearch.WordTrace]
  refine ⟨194574353896115704779300107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129716235930743803186200071 194574353896115704779300107)
  ·
    refine ⟨291861530844173557168950161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194574353896115704779300107 291861530844173557168950161)
    ·
      refine ⟨218896148133130167876712621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 291861530844173557168950161 218896148133130167876712621)
      ·
        refine ⟨82086055549923812953767233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 218896148133130167876712621 82086055549923812953767233)
        ·
          refine ⟨61564541662442859715325425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82086055549923812953767233 61564541662442859715325425)
          ·
            refine ⟨46173406246832144786494069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61564541662442859715325425 46173406246832144786494069)
            ·
              refine ⟨4328756835640513573733819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 46173406246832144786494069 4328756835640513573733819)
              ·
                refine ⟨6493135253460770360600729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4328756835640513573733819 6493135253460770360600729)
                ·
                  refine ⟨4869851440095577770450547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6493135253460770360600729 4869851440095577770450547)
                  ·
                    refine ⟨7304777160143366655675821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4869851440095577770450547 7304777160143366655675821)
                    ·
                      refine ⟨2739291435053762495878433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7304777160143366655675821 2739291435053762495878433)
                      ·
                        rfl

theorem cell23_5334751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 5, 1, 2, 1, 3].length) (baseStart_5334751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5334751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5334751 prefixEnd_5334751 := by exact prefixLift 5334751
  have htrace : WordTrace (prefixWord ++ tailWord_5334751) baseStart_5334751 baseEnd_5334751 := by
    simpa [prefixWord, tailWord_5334751, baseEnd_5334751] using wordTrace_append hprefix tailTrace_5334751
  have hstable : (prefixWord ++ tailWord_5334751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5334751).length < 2 ^ (prefixWord ++ tailWord_5334751).sum := by decide
  have hdescent : baseEnd_5334751 < baseStart_5334751 := by decide
  rcases family_descends (prefixWord ++ tailWord_5334751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5334808 : List Nat := [2, 1, 2, 3, 1, 1, 6, 1, 2, 2, 2]
def baseStart_5334808 : Nat := 118140960795 + 5334808 * 2 ^ 59
def prefixEnd_5334808 : Nat := 4983230072969 + 3 ^ 40 * 5334808 * 2
def baseEnd_5334808 : Nat := 2739320703451068772865671

theorem tailTrace_5334808 : CollatzResearch.WordTrace tailWord_5334808 prefixEnd_5334808 2739320703451068772865671 := by
  unfold tailWord_5334808
  simp only [CollatzResearch.WordTrace]
  refine ⟨97288216428454601757062539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129717621904606135676083385 97288216428454601757062539)
  ·
    refine ⟨145932324642681902635593809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97288216428454601757062539 145932324642681902635593809)
    ·
      refine ⟨109449243482011426976695357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 145932324642681902635593809 109449243482011426976695357)
      ·
        refine ⟨41043466305754285116260759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 109449243482011426976695357 41043466305754285116260759)
        ·
          refine ⟨61565199458631427674391139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41043466305754285116260759 61565199458631427674391139)
          ·
            refine ⟨92347799187947141511586709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61565199458631427674391139 92347799187947141511586709)
            ·
              refine ⟨4328803086935022258355627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 92347799187947141511586709 4328803086935022258355627)
              ·
                refine ⟨6493204630402533387533441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4328803086935022258355627 6493204630402533387533441)
                ·
                  refine ⟨4869903472801900040650081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6493204630402533387533441 4869903472801900040650081)
                  ·
                    refine ⟨3652427604601425030487561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4869903472801900040650081 3652427604601425030487561)
                    ·
                      refine ⟨2739320703451068772865671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3652427604601425030487561 2739320703451068772865671)
                      ·
                        rfl

theorem cell23_5334808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 6, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 6, 1, 2, 2, 2].length) (baseStart_5334808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5334808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5334808 prefixEnd_5334808 := by exact prefixLift 5334808
  have htrace : WordTrace (prefixWord ++ tailWord_5334808) baseStart_5334808 baseEnd_5334808 := by
    simpa [prefixWord, tailWord_5334808, baseEnd_5334808] using wordTrace_append hprefix tailTrace_5334808
  have hstable : (prefixWord ++ tailWord_5334808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5334808).length < 2 ^ (prefixWord ++ tailWord_5334808).sum := by decide
  have hdescent : baseEnd_5334808 < baseStart_5334808 := by decide
  rcases family_descends (prefixWord ++ tailWord_5334808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5334874 : List Nat := [3, 1, 1, 2, 1, 3, 3, 2, 3, 4]
def baseStart_5334874 : Nat := 118140960795 + 5334874 * 2 ^ 59
def prefixEnd_5334874 : Nat := 4983230072969 + 3 ^ 40 * 5334874 * 2
def baseEnd_5334874 : Nat := 913118197724755171546789

theorem tailTrace_5334874 : CollatzResearch.WordTrace tailWord_5334874 prefixEnd_5334874 913118197724755171546789 := by
  unfold tailWord_5334874
  simp only [CollatzResearch.WordTrace]
  refine ⟨48644710018667524196506919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129719226716446731190685117 48644710018667524196506919)
  ·
    refine ⟨72967065028001286294760379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48644710018667524196506919 72967065028001286294760379)
    ·
      refine ⟨109450597542001929442140569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72967065028001286294760379 109450597542001929442140569)
      ·
        refine ⟨82087948156501447081605427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 109450597542001929442140569 82087948156501447081605427)
        ·
          refine ⟨123131922234752170622408141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82087948156501447081605427 123131922234752170622408141)
          ·
            refine ⟨46174470838032063983403053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 123131922234752170622408141 46174470838032063983403053)
            ·
              refine ⟨17315426564262023993776145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46174470838032063983403053 17315426564262023993776145)
              ·
                refine ⟨12986569923196517995332109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17315426564262023993776145 12986569923196517995332109)
                ·
                  refine ⟨4869963721198694248249541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12986569923196517995332109 4869963721198694248249541)
                  ·
                    refine ⟨913118197724755171546789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4869963721198694248249541 913118197724755171546789)
                    ·
                      rfl

theorem cell23_5334874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 3, 2, 3, 4].length) (baseStart_5334874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5334874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5334874 prefixEnd_5334874 := by exact prefixLift 5334874
  have htrace : WordTrace (prefixWord ++ tailWord_5334874) baseStart_5334874 baseEnd_5334874 := by
    simpa [prefixWord, tailWord_5334874, baseEnd_5334874] using wordTrace_append hprefix tailTrace_5334874
  have hstable : (prefixWord ++ tailWord_5334874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5334874).length < 2 ^ (prefixWord ++ tailWord_5334874).sum := by decide
  have hdescent : baseEnd_5334874 < baseStart_5334874 := by decide
  rcases family_descends (prefixWord ++ tailWord_5334874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5334887 : List Nat := [1, 1, 5, 1, 2, 1, 2, 2, 8]
def baseStart_5334887 : Nat := 118140960795 + 5334887 * 2 ^ 59
def prefixEnd_5334887 : Nat := 4983230072969 + 3 ^ 40 * 5334887 * 2
def baseEnd_5334887 : Nat := 304373474269197107086423

theorem tailTrace_5334887 : CollatzResearch.WordTrace tailWord_5334887 prefixEnd_5334887 304373474269197107086423 := by
  unfold tailWord_5334887
  simp only [CollatzResearch.WordTrace]
  refine ⟨194579314223623000006250915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129719542815748666670833943 194579314223623000006250915)
  ·
    refine ⟨291868971335434500009376373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194579314223623000006250915 291868971335434500009376373)
    ·
      refine ⟨27362716062696984375879035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 291868971335434500009376373 27362716062696984375879035)
      ·
        refine ⟨41044074094045476563818553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27362716062696984375879035 41044074094045476563818553)
        ·
          refine ⟨30783055570534107422863915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41044074094045476563818553 30783055570534107422863915)
          ·
            refine ⟨46174583355801161134295873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30783055570534107422863915 46174583355801161134295873)
            ·
              refine ⟨34630937516850870850721905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46174583355801161134295873 34630937516850870850721905)
              ·
                refine ⟨25973203137638153138041429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34630937516850870850721905 25973203137638153138041429)
                ·
                  refine ⟨304373474269197107086423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 25973203137638153138041429 304373474269197107086423)
                  ·
                    rfl

theorem cell23_5334887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 2, 2, 8].length) (baseStart_5334887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5334887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5334887 prefixEnd_5334887 := by exact prefixLift 5334887
  have htrace : WordTrace (prefixWord ++ tailWord_5334887) baseStart_5334887 baseEnd_5334887 := by
    simpa [prefixWord, tailWord_5334887, baseEnd_5334887] using wordTrace_append hprefix tailTrace_5334887
  have hstable : (prefixWord ++ tailWord_5334887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5334887).length < 2 ^ (prefixWord ++ tailWord_5334887).sum := by decide
  have hdescent : baseEnd_5334887 < baseStart_5334887 := by decide
  rcases family_descends (prefixWord ++ tailWord_5334887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5334894 : List Nat := [4, 1, 2, 3, 1, 1, 1, 1, 2, 1, 6]
def baseStart_5334894 : Nat := 118140960795 + 5334894 * 2 ^ 59
def prefixEnd_5334894 : Nat := 4983230072969 + 3 ^ 40 * 5334894 * 2
def baseEnd_5334894 : Nat := 2739364862787355436390275

theorem tailTrace_5334894 : CollatzResearch.WordTrace tailWord_5334894 prefixEnd_5334894 2739364862787355436390275 := by
  unfold tailWord_5334894
  simp only [CollatzResearch.WordTrace]
  refine ⟨24322446191824705025219467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 129719713023065093467837157 24322446191824705025219467)
  ·
    refine ⟨36483669287737057537829201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24322446191824705025219467 36483669287737057537829201)
    ·
      refine ⟨27362751965802793153371901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36483669287737057537829201 27362751965802793153371901)
      ·
        refine ⟨10261031987176047432514463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27362751965802793153371901 10261031987176047432514463)
        ·
          refine ⟨15391547980764071148771695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10261031987176047432514463 15391547980764071148771695)
          ·
            refine ⟨23087321971146106723157543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15391547980764071148771695 23087321971146106723157543)
            ·
              refine ⟨34630982956719160084736315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23087321971146106723157543 34630982956719160084736315)
              ·
                refine ⟨51946474435078740127104473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34630982956719160084736315 51946474435078740127104473)
                ·
                  refine ⟨38959855826309055095328355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 51946474435078740127104473 38959855826309055095328355)
                  ·
                    refine ⟨58439783739463582642992533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 38959855826309055095328355 58439783739463582642992533)
                    ·
                      refine ⟨2739364862787355436390275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 58439783739463582642992533 2739364862787355436390275)
                      ·
                        rfl

theorem cell23_5334894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 1, 1, 2, 1, 6].length) (baseStart_5334894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5334894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5334894 prefixEnd_5334894 := by exact prefixLift 5334894
  have htrace : WordTrace (prefixWord ++ tailWord_5334894) baseStart_5334894 baseEnd_5334894 := by
    simpa [prefixWord, tailWord_5334894, baseEnd_5334894] using wordTrace_append hprefix tailTrace_5334894
  have hstable : (prefixWord ++ tailWord_5334894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5334894).length < 2 ^ (prefixWord ++ tailWord_5334894).sum := by decide
  have hdescent : baseEnd_5334894 < baseStart_5334894 := by decide
  rcases family_descends (prefixWord ++ tailWord_5334894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5334941 : List Nat := [1, 4, 2, 1, 2, 2, 2, 1, 1, 5, 2]
def baseStart_5334941 : Nat := 118140960795 + 5334941 * 2 ^ 59
def prefixEnd_5334941 : Nat := 4983230072969 + 3 ^ 40 * 5334941 * 2
def baseEnd_5334941 : Nat := 2739388996378116752502559

theorem tailTrace_5334941 : CollatzResearch.WordTrace tailWord_5334941 prefixEnd_5334941 2739388996378116752502559 := by
  unfold tailWord_5334941
  simp only [CollatzResearch.WordTrace]
  refine ⟨194581283765427367228716677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129720855843618244819144451 194581283765427367228716677)
  ·
    refine ⟨36483990706017631355384377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 194581283765427367228716677 36483990706017631355384377)
    ·
      refine ⟨27362993029513223516538283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36483990706017631355384377 27362993029513223516538283)
      ·
        refine ⟨41044489544269835274807425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27362993029513223516538283 41044489544269835274807425)
        ·
          refine ⟨30783367158202376456105569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41044489544269835274807425 30783367158202376456105569)
          ·
            refine ⟨23087525368651782342079177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30783367158202376456105569 23087525368651782342079177)
            ·
              refine ⟨17315644026488836756559383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23087525368651782342079177 17315644026488836756559383)
              ·
                refine ⟨25973466039733255134839075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17315644026488836756559383 25973466039733255134839075)
                ·
                  refine ⟨38960199059599882702258613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25973466039733255134839075 38960199059599882702258613)
                  ·
                    refine ⟨3652518661837489003336745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 38960199059599882702258613 3652518661837489003336745)
                    ·
                      refine ⟨2739388996378116752502559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3652518661837489003336745 2739388996378116752502559)
                      ·
                        rfl

theorem cell23_5334941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 2, 1, 1, 5, 2].length) (baseStart_5334941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5334941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5334941 prefixEnd_5334941 := by exact prefixLift 5334941
  have htrace : WordTrace (prefixWord ++ tailWord_5334941) baseStart_5334941 baseEnd_5334941 := by
    simpa [prefixWord, tailWord_5334941, baseEnd_5334941] using wordTrace_append hprefix tailTrace_5334941
  have hstable : (prefixWord ++ tailWord_5334941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5334941).length < 2 ^ (prefixWord ++ tailWord_5334941).sum := by decide
  have hdescent : baseEnd_5334941 < baseStart_5334941 := by decide
  rcases family_descends (prefixWord ++ tailWord_5334941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5334947 : List Nat := [1, 1, 1, 4, 1, 2, 1, 3, 3, 6]
def baseStart_5334947 : Nat := 118140960795 + 5334947 * 2 ^ 59
def prefixEnd_5334947 : Nat := 4983230072969 + 3 ^ 40 * 5334947 * 2
def baseEnd_5334947 : Nat := 913130692420681243009177

theorem tailTrace_5334947 : CollatzResearch.WordTrace tailWord_5334947 prefixEnd_5334947 913130692420681243009177 := by
  unfold tailWord_5334947
  simp only [CollatzResearch.WordTrace]
  refine ⟨194581502603405630253435095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129721001735603753502290063 194581502603405630253435095)
  ·
    refine ⟨291872253905108445380152643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194581502603405630253435095 291872253905108445380152643)
    ·
      refine ⟨437808380857662668070228965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 291872253905108445380152643 437808380857662668070228965)
      ·
        refine ⟨82089071410811750263167931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 437808380857662668070228965 82089071410811750263167931)
        ·
          refine ⟨123133607116217625394751897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82089071410811750263167931 123133607116217625394751897)
          ·
            refine ⟨92350205337163219046063923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 123133607116217625394751897 92350205337163219046063923)
            ·
              refine ⟨138525308005744828569095885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 92350205337163219046063923 138525308005744828569095885)
              ·
                refine ⟨51946990502154310713410957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 138525308005744828569095885 51946990502154310713410957)
                ·
                  refine ⟨19480121438307866517529109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 51946990502154310713410957 19480121438307866517529109)
                  ·
                    refine ⟨913130692420681243009177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19480121438307866517529109 913130692420681243009177)
                    ·
                      rfl

theorem cell23_5334947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 3, 3, 6].length) (baseStart_5334947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5334947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5334947 prefixEnd_5334947 := by exact prefixLift 5334947
  have htrace : WordTrace (prefixWord ++ tailWord_5334947) baseStart_5334947 baseEnd_5334947 := by
    simpa [prefixWord, tailWord_5334947, baseEnd_5334947] using wordTrace_append hprefix tailTrace_5334947
  have hstable : (prefixWord ++ tailWord_5334947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5334947).length < 2 ^ (prefixWord ++ tailWord_5334947).sum := by decide
  have hdescent : baseEnd_5334947 < baseStart_5334947 := by decide
  rcases family_descends (prefixWord ++ tailWord_5334947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5334951 : List Nat := [1, 1, 6, 1, 2, 1, 2, 3, 1, 5]
def baseStart_5334951 : Nat := 118140960795 + 5334951 * 2 ^ 59
def prefixEnd_5334951 : Nat := 4983230072969 + 3 ^ 40 * 5334951 * 2
def baseEnd_5334951 : Nat := 913131377061553904459171

theorem tailTrace_5334951 : CollatzResearch.WordTrace tailWord_5334951 prefixEnd_5334951 913131377061553904459171 := by
  unfold tailWord_5334951
  simp only [CollatzResearch.WordTrace]
  refine ⟨194581648495391138936580707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129721098996927425957720471 194581648495391138936580707)
  ·
    refine ⟨291872472743086708404871061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194581648495391138936580707 291872472743086708404871061)
    ·
      refine ⟨13681522159832189456478331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 291872472743086708404871061 13681522159832189456478331)
      ·
        refine ⟨20522283239748284184717497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13681522159832189456478331 20522283239748284184717497)
        ·
          refine ⟨15391712429811213138538123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20522283239748284184717497 15391712429811213138538123)
          ·
            refine ⟨23087568644716819707807185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15391712429811213138538123 23087568644716819707807185)
            ·
              refine ⟨17315676483537614780855389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23087568644716819707807185 17315676483537614780855389)
              ·
                refine ⟨6493378681326605542820771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17315676483537614780855389 6493378681326605542820771)
                ·
                  refine ⟨9740068021989908314231157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6493378681326605542820771 9740068021989908314231157)
                  ·
                    refine ⟨913131377061553904459171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9740068021989908314231157 913131377061553904459171)
                    ·
                      rfl

theorem cell23_5334951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 2, 3, 1, 5].length) (baseStart_5334951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5334951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5334951 prefixEnd_5334951 := by exact prefixLift 5334951
  have htrace : WordTrace (prefixWord ++ tailWord_5334951) baseStart_5334951 baseEnd_5334951 := by
    simpa [prefixWord, tailWord_5334951, baseEnd_5334951] using wordTrace_append hprefix tailTrace_5334951
  have hstable : (prefixWord ++ tailWord_5334951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5334951).length < 2 ^ (prefixWord ++ tailWord_5334951).sum := by decide
  have hdescent : baseEnd_5334951 < baseStart_5334951 := by decide
  rcases family_descends (prefixWord ++ tailWord_5334951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5334984 : List Nat := [2, 1, 3, 1, 4, 1, 2, 1, 1, 1, 6]
def baseStart_5334984 : Nat := 118140960795 + 5334984 * 2 ^ 59
def prefixEnd_5334984 : Nat := 4983230072969 + 3 ^ 40 * 5334984 * 2
def baseEnd_5334984 : Nat := 2739411076046260084264861

theorem tailTrace_5334984 : CollatzResearch.WordTrace tailWord_5334984 prefixEnd_5334984 2739411076046260084264861 := by
  unfold tailWord_5334984
  simp only [CollatzResearch.WordTrace]
  refine ⟨97291426052135792786266003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129721901402847723715021337 97291426052135792786266003)
  ·
    refine ⟨145937139078203689179399005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97291426052135792786266003 145937139078203689179399005)
    ·
      refine ⟨54726427154326383442274627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 145937139078203689179399005 54726427154326383442274627)
      ·
        refine ⟨82089640731489575163411941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54726427154326383442274627 82089640731489575163411941)
        ·
          refine ⟨15391807637154295343139739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 82089640731489575163411941 15391807637154295343139739)
          ·
            refine ⟨23087711455731443014709609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15391807637154295343139739 23087711455731443014709609)
            ·
              refine ⟨17315783591798582261032207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23087711455731443014709609 17315783591798582261032207)
              ·
                refine ⟨25973675387697873391548311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17315783591798582261032207 25973675387697873391548311)
                ·
                  refine ⟨38960513081546810087322467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25973675387697873391548311 38960513081546810087322467)
                  ·
                    refine ⟨58440769622320215130983701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 38960513081546810087322467 58440769622320215130983701)
                    ·
                      refine ⟨2739411076046260084264861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 58440769622320215130983701 2739411076046260084264861)
                      ·
                        rfl

theorem cell23_5334984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 2, 1, 1, 1, 6].length) (baseStart_5334984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5334984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5334984 prefixEnd_5334984 := by exact prefixLift 5334984
  have htrace : WordTrace (prefixWord ++ tailWord_5334984) baseStart_5334984 baseEnd_5334984 := by
    simpa [prefixWord, tailWord_5334984, baseEnd_5334984] using wordTrace_append hprefix tailTrace_5334984
  have hstable : (prefixWord ++ tailWord_5334984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5334984).length < 2 ^ (prefixWord ++ tailWord_5334984).sum := by decide
  have hdescent : baseEnd_5334984 < baseStart_5334984 := by decide
  rcases family_descends (prefixWord ++ tailWord_5334984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5334988 : List Nat := [2, 2, 1, 4, 1, 4, 1, 2, 1, 1, 4]
def baseStart_5334988 : Nat := 118140960795 + 5334988 * 2 ^ 59
def prefixEnd_5334988 : Nat := 4983230072969 + 3 ^ 40 * 5334988 * 2
def baseEnd_5334988 : Nat := 2739413129968878068614843

theorem tailTrace_5334988 : CollatzResearch.WordTrace tailWord_5334988 prefixEnd_5334988 2739413129968878068614843 := by
  unfold tailWord_5334988
  simp only [CollatzResearch.WordTrace]
  refine ⟨97291498998128547127838809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129721998664171396170451745 97291498998128547127838809)
  ·
    refine ⟨72968624248596410345879107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97291498998128547127838809 72968624248596410345879107)
    ·
      refine ⟨109452936372894615518818661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72968624248596410345879107 109452936372894615518818661)
      ·
        refine ⟨20522425569917740409778499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 109452936372894615518818661 20522425569917740409778499)
        ·
          refine ⟨30783638354876610614667749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20522425569917740409778499 30783638354876610614667749)
          ·
            refine ⟨5771932191539364490250203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30783638354876610614667749 5771932191539364490250203)
            ·
              refine ⟨8657898287309046735375305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5771932191539364490250203 8657898287309046735375305)
              ·
                refine ⟨6493423715481785051531479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8657898287309046735375305 6493423715481785051531479)
                ·
                  refine ⟨9740135573222677577297219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6493423715481785051531479 9740135573222677577297219)
                  ·
                    refine ⟨14610203359834016365945829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9740135573222677577297219 14610203359834016365945829)
                    ·
                      refine ⟨2739413129968878068614843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14610203359834016365945829 2739413129968878068614843)
                      ·
                        rfl

theorem cell23_5334988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 4, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 4, 1, 2, 1, 1, 4].length) (baseStart_5334988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5334988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5334988 prefixEnd_5334988 := by exact prefixLift 5334988
  have htrace : WordTrace (prefixWord ++ tailWord_5334988) baseStart_5334988 baseEnd_5334988 := by
    simpa [prefixWord, tailWord_5334988, baseEnd_5334988] using wordTrace_append hprefix tailTrace_5334988
  have hstable : (prefixWord ++ tailWord_5334988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5334988).length < 2 ^ (prefixWord ++ tailWord_5334988).sum := by decide
  have hdescent : baseEnd_5334988 < baseStart_5334988 := by decide
  rcases family_descends (prefixWord ++ tailWord_5334988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5334998 : List Nat := [5, 2, 1, 1, 3, 1, 1, 2, 1, 6]
def baseStart_5334998 : Nat := 118140960795 + 5334998 * 2 ^ 59
def prefixEnd_5334998 : Nat := 4983230072969 + 3 ^ 40 * 5334998 * 2
def baseEnd_5334998 : Nat := 913139421591807676496599

theorem tailTrace_5334998 : CollatzResearch.WordTrace tailWord_5334998 prefixEnd_5334998 913139421591807676496599 := by
  unfold tailWord_5334998
  simp only [CollatzResearch.WordTrace]
  refine ⟨12161460170388804122721353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 129722241817480577309027765 12161460170388804122721353)
  ·
    refine ⟨9121095127791603092041015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12161460170388804122721353 9121095127791603092041015)
    ·
      refine ⟨13681642691687404638061523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9121095127791603092041015 13681642691687404638061523)
      ·
        refine ⟨20522464037531106957092285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13681642691687404638061523 20522464037531106957092285)
        ·
          refine ⟨7695924014074165108909607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20522464037531106957092285 7695924014074165108909607)
          ·
            refine ⟨11543886021111247663364411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7695924014074165108909607 11543886021111247663364411)
            ·
              refine ⟨17315829031666871495046617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11543886021111247663364411 17315829031666871495046617)
              ·
                refine ⟨12986871773750153621284963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17315829031666871495046617 12986871773750153621284963)
                ·
                  refine ⟨19480307660625230431927445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12986871773750153621284963 19480307660625230431927445)
                  ·
                    refine ⟨913139421591807676496599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19480307660625230431927445 913139421591807676496599)
                    ·
                      rfl

theorem cell23_5334998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 1, 2, 1, 6].length) (baseStart_5334998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5334998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5334998 prefixEnd_5334998 := by exact prefixLift 5334998
  have htrace : WordTrace (prefixWord ++ tailWord_5334998) baseStart_5334998 baseEnd_5334998 := by
    simpa [prefixWord, tailWord_5334998, baseEnd_5334998] using wordTrace_append hprefix tailTrace_5334998
  have hstable : (prefixWord ++ tailWord_5334998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5334998).length < 2 ^ (prefixWord ++ tailWord_5334998).sum := by decide
  have hdescent : baseEnd_5334998 < baseStart_5334998 := by decide
  rcases family_descends (prefixWord ++ tailWord_5334998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5335001 : List Nat := [1, 2, 1, 2, 6, 1, 1, 2, 1, 2, 4]
def baseStart_5335001 : Nat := 118140960795 + 5335001 * 2 ^ 59
def prefixEnd_5335001 : Nat := 4983230072969 + 3 ^ 40 * 5335001 * 2
def baseEnd_5335001 : Nat := 2739419805217386517752283

theorem tailTrace_5335001 : CollatzResearch.WordTrace tailWord_5335001 prefixEnd_5335001 2739419805217386517752283 := by
  unfold tailWord_5335001
  simp only [CollatzResearch.WordTrace]
  refine ⟨194583472145209997475900857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129722314763473331650600571 194583472145209997475900857)
  ·
    refine ⟨145937604108907498106925643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 194583472145209997475900857 145937604108907498106925643)
    ·
      refine ⟨218906406163361247160388465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145937604108907498106925643 218906406163361247160388465)
      ·
        refine ⟨164179804622520935370291349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 218906406163361247160388465 164179804622520935370291349)
        ·
          refine ⟨7695928341680668845482407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 164179804622520935370291349 7695928341680668845482407)
          ·
            refine ⟨11543892512521003268223611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7695928341680668845482407 11543892512521003268223611)
            ·
              refine ⟨17315838768781504902335417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11543892512521003268223611 17315838768781504902335417)
              ·
                refine ⟨12986879076586128676751563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17315838768781504902335417 12986879076586128676751563)
                ·
                  refine ⟨19480318614879193015127345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12986879076586128676751563 19480318614879193015127345)
                  ·
                    refine ⟨14610238961159394761345509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19480318614879193015127345 14610238961159394761345509)
                    ·
                      refine ⟨2739419805217386517752283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14610238961159394761345509 2739419805217386517752283)
                      ·
                        rfl

theorem cell23_5335001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 1, 2, 1, 2, 4].length) (baseStart_5335001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5335001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5335001 prefixEnd_5335001 := by exact prefixLift 5335001
  have htrace : WordTrace (prefixWord ++ tailWord_5335001) baseStart_5335001 baseEnd_5335001 := by
    simpa [prefixWord, tailWord_5335001, baseEnd_5335001] using wordTrace_append hprefix tailTrace_5335001
  have hstable : (prefixWord ++ tailWord_5335001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5335001).length < 2 ^ (prefixWord ++ tailWord_5335001).sum := by decide
  have hdescent : baseEnd_5335001 < baseStart_5335001 := by decide
  rcases family_descends (prefixWord ++ tailWord_5335001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5335005 : List Nat := [1, 4, 3, 1, 3, 1, 3, 1, 1, 1, 4]
def baseStart_5335005 : Nat := 118140960795 + 5335005 * 2 ^ 59
def prefixEnd_5335005 : Nat := 4983230072969 + 3 ^ 40 * 5335005 * 2
def baseEnd_5335005 : Nat := 2739421859140004502102265

theorem tailTrace_5335005 : CollatzResearch.WordTrace tailWord_5335005 prefixEnd_5335005 2739421859140004502102265 := by
  unfold tailWord_5335005
  simp only [CollatzResearch.WordTrace]
  refine ⟨194583618037195506159046469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129722412024797004106030979 194583618037195506159046469)
  ·
    refine ⟨36484428381974157404821213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 194583618037195506159046469 36484428381974157404821213)
    ·
      refine ⟨13681660643240309026807955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36484428381974157404821213 13681660643240309026807955)
      ·
        refine ⟨20522490964860463540211933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13681660643240309026807955 20522490964860463540211933)
        ·
          refine ⟨7695934111822673827579475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20522490964860463540211933 7695934111822673827579475)
          ·
            refine ⟨11543901167734010741369213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7695934111822673827579475 11543901167734010741369213)
            ·
              refine ⟨4328962937900254028013455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11543901167734010741369213 4328962937900254028013455)
              ·
                refine ⟨6493444406850381042020183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4328962937900254028013455 6493444406850381042020183)
                ·
                  refine ⟨9740166610275571563030275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6493444406850381042020183 9740166610275571563030275)
                  ·
                    refine ⟨14610249915413357344545413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9740166610275571563030275 14610249915413357344545413)
                    ·
                      refine ⟨2739421859140004502102265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14610249915413357344545413 2739421859140004502102265)
                      ·
                        rfl

theorem cell23_5335005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 3, 1, 1, 1, 4].length) (baseStart_5335005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5335005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5335005 prefixEnd_5335005 := by exact prefixLift 5335005
  have htrace : WordTrace (prefixWord ++ tailWord_5335005) baseStart_5335005 baseEnd_5335005 := by
    simpa [prefixWord, tailWord_5335005, baseEnd_5335005] using wordTrace_append hprefix tailTrace_5335005
  have hstable : (prefixWord ++ tailWord_5335005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5335005).length < 2 ^ (prefixWord ++ tailWord_5335005).sum := by decide
  have hdescent : baseEnd_5335005 < baseStart_5335005 := by decide
  rcases family_descends (prefixWord ++ tailWord_5335005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5335017 : List Nat := [1, 2, 1, 1, 1, 2, 1, 1, 1, 5, 7]
def baseStart_5335017 : Nat := 118140960795 + 5335017 * 2 ^ 59
def prefixEnd_5335017 : Nat := 4983230072969 + 3 ^ 40 * 5335017 * 2
def baseEnd_5335017 : Nat := 2739428020907858455152209

theorem tailTrace_5335017 : CollatzResearch.WordTrace tailWord_5335017 prefixEnd_5335017 2739428020907858455152209 := by
  unfold tailWord_5335017
  simp only [CollatzResearch.WordTrace]
  refine ⟨194584055713152032208483305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129722703808768021472322203 194584055713152032208483305)
  ·
    refine ⟨145938041784864024156362479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 194584055713152032208483305 145938041784864024156362479)
    ·
      refine ⟨218907062677296036234543719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145938041784864024156362479 218907062677296036234543719)
      ·
        refine ⟨328360594015944054351815579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 218907062677296036234543719 328360594015944054351815579)
        ·
          refine ⟨492540891023916081527723369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 328360594015944054351815579 492540891023916081527723369)
          ·
            refine ⟨369405668267937061145792527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 492540891023916081527723369 369405668267937061145792527)
            ·
              refine ⟨554108502401905591718688791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 369405668267937061145792527 554108502401905591718688791)
              ·
                refine ⟨831162753602858387578033187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 554108502401905591718688791 831162753602858387578033187)
                ·
                  refine ⟨1246744130404287581367049781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 831162753602858387578033187 1246744130404287581367049781)
                  ·
                    refine ⟨116882262225401960753160917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1246744130404287581367049781 116882262225401960753160917)
                    ·
                      refine ⟨2739428020907858455152209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 116882262225401960753160917 2739428020907858455152209)
                      ·
                        rfl

theorem cell23_5335017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 5, 7].length) (baseStart_5335017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5335017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5335017 prefixEnd_5335017 := by exact prefixLift 5335017
  have htrace : WordTrace (prefixWord ++ tailWord_5335017) baseStart_5335017 baseEnd_5335017 := by
    simpa [prefixWord, tailWord_5335017, baseEnd_5335017] using wordTrace_append hprefix tailTrace_5335017
  have hstable : (prefixWord ++ tailWord_5335017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5335017).length < 2 ^ (prefixWord ++ tailWord_5335017).sum := by decide
  have hdescent : baseEnd_5335017 < baseStart_5335017 := by decide
  rcases family_descends (prefixWord ++ tailWord_5335017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5335022 : List Nat := [4, 1, 2, 1, 3, 2, 1, 4, 1, 2, 2]
def baseStart_5335022 : Nat := 118140960795 + 5335022 * 2 ^ 59
def prefixEnd_5335022 : Nat := 4983230072969 + 3 ^ 40 * 5335022 * 2
def baseEnd_5335022 : Nat := 2739430588311130935589687

theorem tailTrace_5335022 : CollatzResearch.WordTrace tailWord_5335022 prefixEnd_5335022 2739430588311130935589687 := by
  unfold tailWord_5335022
  simp only [CollatzResearch.WordTrace]
  refine ⟨24323029759766739757801915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 129722825385422612041610213 24323029759766739757801915)
  ·
    refine ⟨36484544639650109636702873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24323029759766739757801915 36484544639650109636702873)
    ·
      refine ⟨27363408479737582227527155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36484544639650109636702873 27363408479737582227527155)
      ·
        refine ⟨41045112719606373341290733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27363408479737582227527155 41045112719606373341290733)
        ·
          refine ⟨15391917269852390002984025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41045112719606373341290733 15391917269852390002984025)
          ·
            refine ⟨11543937952389292502238019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15391917269852390002984025 11543937952389292502238019)
            ·
              refine ⟨17315906928583938753357029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11543937952389292502238019 17315906928583938753357029)
              ·
                refine ⟨3246732549109488516254443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17315906928583938753357029 3246732549109488516254443)
                ·
                  refine ⟨4870098823664232774381665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3246732549109488516254443 4870098823664232774381665)
                  ·
                    refine ⟨3652574117748174580786249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4870098823664232774381665 3652574117748174580786249)
                    ·
                      refine ⟨2739430588311130935589687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3652574117748174580786249 2739430588311130935589687)
                      ·
                        rfl

theorem cell23_5335022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 1, 4, 1, 2, 2].length) (baseStart_5335022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5335022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5335022 prefixEnd_5335022 := by exact prefixLift 5335022
  have htrace : WordTrace (prefixWord ++ tailWord_5335022) baseStart_5335022 baseEnd_5335022 := by
    simpa [prefixWord, tailWord_5335022, baseEnd_5335022] using wordTrace_append hprefix tailTrace_5335022
  have hstable : (prefixWord ++ tailWord_5335022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5335022).length < 2 ^ (prefixWord ++ tailWord_5335022).sum := by decide
  have hdescent : baseEnd_5335022 < baseStart_5335022 := by decide
  rcases family_descends (prefixWord ++ tailWord_5335022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5335038 : List Nat := [4, 2, 2, 2, 1, 1, 1, 3, 1, 3, 3]
def baseStart_5335038 : Nat := 118140960795 + 5335038 * 2 ^ 59
def prefixEnd_5335038 : Nat := 4983230072969 + 3 ^ 40 * 5335038 * 2
def baseEnd_5335038 : Nat := 2739438804001602872989613

theorem tailTrace_5335038 : CollatzResearch.WordTrace tailWord_5335038 prefixEnd_5335038 2739438804001602872989613 := by
  unfold tailWord_5335038
  simp only [CollatzResearch.WordTrace]
  refine ⟨24323102705759494099374721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 129723214430717301863331845 24323102705759494099374721)
  ·
    refine ⟨18242327029319620574531041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24323102705759494099374721 18242327029319620574531041)
    ·
      refine ⟨13681745271989715430898281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18242327029319620574531041 13681745271989715430898281)
      ·
        refine ⟨10261308953992286573173711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13681745271989715430898281 10261308953992286573173711)
        ·
          refine ⟨15391963430988429859760567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10261308953992286573173711 15391963430988429859760567)
          ·
            refine ⟨23087945146482644789640851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15391963430988429859760567 23087945146482644789640851)
            ·
              refine ⟨34631917719723967184461277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23087945146482644789640851 34631917719723967184461277)
              ·
                refine ⟨12986969144896487694172979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34631917719723967184461277 12986969144896487694172979)
                ·
                  refine ⟨19480453717344731541259469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12986969144896487694172979 19480453717344731541259469)
                  ·
                    refine ⟨7305170144004274327972301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19480453717344731541259469 7305170144004274327972301)
                    ·
                      refine ⟨2739438804001602872989613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7305170144004274327972301 2739438804001602872989613)
                      ·
                        rfl

theorem cell23_5335038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 1, 3, 1, 3, 3].length) (baseStart_5335038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5335038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5335038 prefixEnd_5335038 := by exact prefixLift 5335038
  have htrace : WordTrace (prefixWord ++ tailWord_5335038) baseStart_5335038 baseEnd_5335038 := by
    simpa [prefixWord, tailWord_5335038, baseEnd_5335038] using wordTrace_append hprefix tailTrace_5335038
  have hstable : (prefixWord ++ tailWord_5335038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5335038).length < 2 ^ (prefixWord ++ tailWord_5335038).sum := by decide
  have hdescent : baseEnd_5335038 < baseStart_5335038 := by decide
  rcases family_descends (prefixWord ++ tailWord_5335038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5335048 : List Nat := [2, 1, 3, 2, 1, 2, 2, 4, 1, 3, 2]
def baseStart_5335048 : Nat := 118140960795 + 5335048 * 2 ^ 59
def prefixEnd_5335048 : Nat := 4983230072969 + 3 ^ 40 * 5335048 * 2
def baseEnd_5335048 : Nat := 2739443938808147833864567

theorem tailTrace_5335048 : CollatzResearch.WordTrace tailWord_5335048 prefixEnd_5335048 2739443938808147833864567 := by
  unfold tailWord_5335048
  simp only [CollatzResearch.WordTrace]
  refine ⟨97292593188019862251430899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129723457584026483001907865 97292593188019862251430899)
  ·
    refine ⟨145938889782029793377146349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97292593188019862251430899 145938889782029793377146349)
    ·
      refine ⟨54727083668261172516429881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 145938889782029793377146349 54727083668261172516429881)
      ·
        refine ⟨41045312751195879387322411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54727083668261172516429881 41045312751195879387322411)
        ·
          refine ⟨61567969126793819080983617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41045312751195879387322411 61567969126793819080983617)
          ·
            refine ⟨46175976845095364310737713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61567969126793819080983617 46175976845095364310737713)
            ·
              refine ⟨34631982633821523233053285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46175976845095364310737713 34631982633821523233053285)
              ·
                refine ⟨6493496743841535606197491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34631982633821523233053285 6493496743841535606197491)
                ·
                  refine ⟨9740245115762303409296237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6493496743841535606197491 9740245115762303409296237)
                  ·
                    refine ⟨3652591918410863778486089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9740245115762303409296237 3652591918410863778486089)
                    ·
                      refine ⟨2739443938808147833864567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3652591918410863778486089 2739443938808147833864567)
                      ·
                        rfl

theorem cell23_5335048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 2, 4, 1, 3, 2].length) (baseStart_5335048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5335048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5335048 prefixEnd_5335048 := by exact prefixLift 5335048
  have htrace : WordTrace (prefixWord ++ tailWord_5335048) baseStart_5335048 baseEnd_5335048 := by
    simpa [prefixWord, tailWord_5335048, baseEnd_5335048] using wordTrace_append hprefix tailTrace_5335048
  have hstable : (prefixWord ++ tailWord_5335048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5335048).length < 2 ^ (prefixWord ++ tailWord_5335048).sum := by decide
  have hdescent : baseEnd_5335048 < baseStart_5335048 := by decide
  rcases family_descends (prefixWord ++ tailWord_5335048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5335054 : List Nat := [4, 1, 1, 2, 2, 1, 1, 2, 1, 8]
def baseStart_5335054 : Nat := 118140960795 + 5335054 * 2 ^ 59
def prefixEnd_5335054 : Nat := 4983230072969 + 3 ^ 40 * 5335054 * 2
def baseEnd_5335054 : Nat := 913149006564024936796513

theorem tailTrace_5335054 : CollatzResearch.WordTrace tailWord_5335054 prefixEnd_5335054 913149006564024936796513 := by
  unfold tailWord_5335054
  simp only [CollatzResearch.WordTrace]
  refine ⟨24323175651752248440947527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 129723603476011991685053477 24323175651752248440947527)
  ·
    refine ⟨36484763477628372661421291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24323175651752248440947527 36484763477628372661421291)
    ·
      refine ⟨54727145216442558992131937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36484763477628372661421291 54727145216442558992131937)
      ·
        refine ⟨41045358912331919244098953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54727145216442558992131937 41045358912331919244098953)
        ·
          refine ⟨30784019184248939433074215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41045358912331919244098953 30784019184248939433074215)
          ·
            refine ⟨46176028776373409149611323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30784019184248939433074215 46176028776373409149611323)
            ·
              refine ⟨69264043164560113724416985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46176028776373409149611323 69264043164560113724416985)
              ·
                refine ⟨51948032373420085293312739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 69264043164560113724416985 51948032373420085293312739)
                ·
                  refine ⟨77922048560130127939969109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51948032373420085293312739 77922048560130127939969109)
                  ·
                    refine ⟨913149006564024936796513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 77922048560130127939969109 913149006564024936796513)
                    ·
                      rfl

theorem cell23_5335054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 2, 1, 8].length) (baseStart_5335054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5335054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5335054 prefixEnd_5335054 := by exact prefixLift 5335054
  have htrace : WordTrace (prefixWord ++ tailWord_5335054) baseStart_5335054 baseEnd_5335054 := by
    simpa [prefixWord, tailWord_5335054, baseEnd_5335054] using wordTrace_append hprefix tailTrace_5335054
  have hstable : (prefixWord ++ tailWord_5335054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5335054).length < 2 ^ (prefixWord ++ tailWord_5335054).sum := by decide
  have hdescent : baseEnd_5335054 < baseStart_5335054 := by decide
  rcases family_descends (prefixWord ++ tailWord_5335054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5335064 : List Nat := [2, 1, 2, 3, 2, 1, 2, 1, 1, 3, 5]
def baseStart_5335064 : Nat := 118140960795 + 5335064 * 2 ^ 59
def prefixEnd_5335064 : Nat := 4983230072969 + 3 ^ 40 * 5335064 * 2
def baseEnd_5335064 : Nat := 2739452154498619771264493

theorem tailTrace_5335064 : CollatzResearch.WordTrace tailWord_5335064 prefixEnd_5335064 2739452154498619771264493 := by
  unfold tailWord_5335064
  simp only [CollatzResearch.WordTrace]
  refine ⟨97292884971990879617722123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129723846629321172823629497 97292884971990879617722123)
  ·
    refine ⟨145939327457986319426583185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97292884971990879617722123 145939327457986319426583185)
    ·
      refine ⟨109454495593489739569937389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 145939327457986319426583185 109454495593489739569937389)
      ·
        refine ⟨41045435847558652338726521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 109454495593489739569937389 41045435847558652338726521)
        ·
          refine ⟨30784076885668989254044891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41045435847558652338726521 30784076885668989254044891)
          ·
            refine ⟨46176115328503483881067337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30784076885668989254044891 46176115328503483881067337)
            ·
              refine ⟨34632086496377612910800503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46176115328503483881067337 34632086496377612910800503)
              ·
                refine ⟨51948129744566419366200755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34632086496377612910800503 51948129744566419366200755)
                ·
                  refine ⟨77922194616849629049301133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51948129744566419366200755 77922194616849629049301133)
                  ·
                    refine ⟨29220822981318610893487925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 77922194616849629049301133 29220822981318610893487925)
                    ·
                      refine ⟨2739452154498619771264493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29220822981318610893487925 2739452154498619771264493)
                      ·
                        rfl

theorem cell23_5335064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 2, 1, 1, 3, 5].length) (baseStart_5335064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5335064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5335064 prefixEnd_5335064 := by exact prefixLift 5335064
  have htrace : WordTrace (prefixWord ++ tailWord_5335064) baseStart_5335064 baseEnd_5335064 := by
    simpa [prefixWord, tailWord_5335064, baseEnd_5335064] using wordTrace_append hprefix tailTrace_5335064
  have hstable : (prefixWord ++ tailWord_5335064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5335064).length < 2 ^ (prefixWord ++ tailWord_5335064).sum := by decide
  have hdescent : baseEnd_5335064 < baseStart_5335064 := by decide
  rcases family_descends (prefixWord ++ tailWord_5335064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5335118 : List Nat := [4, 1, 1, 1, 1, 4, 3, 3, 5]
def baseStart_5335118 : Nat := 118140960795 + 5335118 * 2 ^ 59
def prefixEnd_5335118 : Nat := 4983230072969 + 3 ^ 40 * 5335118 * 2
def baseEnd_5335118 : Nat := 304386653605995839998805

theorem tailTrace_5335118 : CollatzResearch.WordTrace tailWord_5335118 prefixEnd_5335118 304386653605995839998805 := by
  unfold tailWord_5335118
  simp only [CollatzResearch.WordTrace]
  refine ⟨24323467435723265807238751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 129725159657190750971940005 24323467435723265807238751)
  ·
    refine ⟨36485201153584898710858127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24323467435723265807238751 36485201153584898710858127)
    ·
      refine ⟨54727801730377348066287191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36485201153584898710858127 54727801730377348066287191)
      ·
        refine ⟨82091702595566022099430787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54727801730377348066287191 82091702595566022099430787)
        ·
          refine ⟨123137553893349033149146181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82091702595566022099430787 123137553893349033149146181)
          ·
            refine ⟨23088291355002943715464909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 123137553893349033149146181 23088291355002943715464909)
            ·
              refine ⟨8658109258126103893299341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23088291355002943715464909 8658109258126103893299341)
              ·
                refine ⟨3246790971797288959987253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8658109258126103893299341 3246790971797288959987253)
                ·
                  refine ⟨304386653605995839998805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3246790971797288959987253 304386653605995839998805)
                  ·
                    rfl

theorem cell23_5335118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 3, 3, 5].length) (baseStart_5335118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5335118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5335118 prefixEnd_5335118 := by exact prefixLift 5335118
  have htrace : WordTrace (prefixWord ++ tailWord_5335118) baseStart_5335118 baseEnd_5335118 := by
    simpa [prefixWord, tailWord_5335118, baseEnd_5335118] using wordTrace_append hprefix tailTrace_5335118
  have hstable : (prefixWord ++ tailWord_5335118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5335118).length < 2 ^ (prefixWord ++ tailWord_5335118).sum := by decide
  have hdescent : baseEnd_5335118 < baseStart_5335118 := by decide
  rcases family_descends (prefixWord ++ tailWord_5335118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5335121 : List Nat := [1, 2, 2, 1, 3, 1, 1, 2, 1, 7, 2]
def baseStart_5335121 : Nat := 118140960795 + 5335121 * 2 ^ 59
def prefixEnd_5335121 : Nat := 4983230072969 + 3 ^ 40 * 5335121 * 2
def baseEnd_5335121 : Nat := 2739481422895926048251731

theorem tailTrace_5335121 : CollatzResearch.WordTrace tailWord_5335121 prefixEnd_5335121 2739481422895926048251731 := by
  unfold tailWord_5335121
  simp only [CollatzResearch.WordTrace]
  refine ⟨194587848904775257970269217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129725232603183505313512811 194587848904775257970269217)
  ·
    refine ⟨145940886678581443477701913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 194587848904775257970269217 145940886678581443477701913)
    ·
      refine ⟨109455665008936082608276435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 145940886678581443477701913 109455665008936082608276435)
      ·
        refine ⟨164183497513404123912414653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109455665008936082608276435 164183497513404123912414653)
        ·
          refine ⟨61568811567526546467155495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 164183497513404123912414653 61568811567526546467155495)
          ·
            refine ⟨92353217351289819700733243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61568811567526546467155495 92353217351289819700733243)
            ·
              refine ⟨138529826026934729551099865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 92353217351289819700733243 138529826026934729551099865)
              ·
                refine ⟨103897369520201047163324899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 138529826026934729551099865 103897369520201047163324899)
                ·
                  refine ⟨155846054280301570744987349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 103897369520201047163324899 155846054280301570744987349)
                  ·
                    refine ⟨3652641897194568064335641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 155846054280301570744987349 3652641897194568064335641)
                    ·
                      refine ⟨2739481422895926048251731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3652641897194568064335641 2739481422895926048251731)
                      ·
                        rfl

theorem cell23_5335121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 2, 1, 7, 2].length) (baseStart_5335121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5335121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5335121 prefixEnd_5335121 := by exact prefixLift 5335121
  have htrace : WordTrace (prefixWord ++ tailWord_5335121) baseStart_5335121 baseEnd_5335121 := by
    simpa [prefixWord, tailWord_5335121, baseEnd_5335121] using wordTrace_append hprefix tailTrace_5335121
  have hstable : (prefixWord ++ tailWord_5335121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5335121).length < 2 ^ (prefixWord ++ tailWord_5335121).sum := by decide
  have hdescent : baseEnd_5335121 < baseStart_5335121 := by decide
  rcases family_descends (prefixWord ++ tailWord_5335121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5335141 : List Nat := [1, 3, 1, 3, 2, 3, 1, 1, 1, 2, 5]
def baseStart_5335141 : Nat := 118140960795 + 5335141 * 2 ^ 59
def prefixEnd_5335141 : Nat := 4983230072969 + 3 ^ 40 * 5335141 * 2
def baseEnd_5335141 : Nat := 2739491692509015970001639

theorem tailTrace_5335141 : CollatzResearch.WordTrace tailWord_5335141 prefixEnd_5335141 2739491692509015970001639 := by
  unfold tailWord_5335141
  simp only [CollatzResearch.WordTrace]
  refine ⟨194588578364702801385997277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129725718909801867590664851 194588578364702801385997277)
  ·
    refine ⟨72970716886763550519748979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 194588578364702801385997277 72970716886763550519748979)
    ·
      refine ⟨109456075330145325779623469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72970716886763550519748979 109456075330145325779623469)
      ·
        refine ⟨41046028248804497167358801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 109456075330145325779623469 41046028248804497167358801)
        ·
          refine ⟨30784521186603372875519101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41046028248804497167358801 30784521186603372875519101)
          ·
            refine ⟨11544195444976264828319663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30784521186603372875519101 11544195444976264828319663)
            ·
              refine ⟨17316293167464397242479495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11544195444976264828319663 17316293167464397242479495)
              ·
                refine ⟨25974439751196595863719243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17316293167464397242479495 25974439751196595863719243)
                ·
                  refine ⟨38961659626794893795578865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25974439751196595863719243 38961659626794893795578865)
                  ·
                    refine ⟨29221244720096170346684149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 38961659626794893795578865 29221244720096170346684149)
                    ·
                      refine ⟨2739491692509015970001639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29221244720096170346684149 2739491692509015970001639)
                      ·
                        rfl

theorem cell23_5335141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 1, 1, 1, 2, 5].length) (baseStart_5335141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5335141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5335141 prefixEnd_5335141 := by exact prefixLift 5335141
  have htrace : WordTrace (prefixWord ++ tailWord_5335141) baseStart_5335141 baseEnd_5335141 := by
    simpa [prefixWord, tailWord_5335141, baseEnd_5335141] using wordTrace_append hprefix tailTrace_5335141
  have hstable : (prefixWord ++ tailWord_5335141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5335141).length < 2 ^ (prefixWord ++ tailWord_5335141).sum := by decide
  have hdescent : baseEnd_5335141 < baseStart_5335141 := by decide
  rcases family_descends (prefixWord ++ tailWord_5335141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5335146 : List Nat := [3, 1, 3, 2, 4, 1, 2, 1, 2, 2, 2]
def baseStart_5335146 : Nat := 118140960795 + 5335146 * 2 ^ 59
def prefixEnd_5335146 : Nat := 4983230072969 + 3 ^ 40 * 5335146 * 2
def baseEnd_5335146 : Nat := 2739494259912288450439117

theorem tailTrace_5335146 : CollatzResearch.WordTrace tailWord_5335146 prefixEnd_5335146 2739494259912288450439117 := by
  unfold tailWord_5335146
  simp only [CollatzResearch.WordTrace]
  refine ⟨48647190182421171809982323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129725840486456458159952861 48647190182421171809982323)
  ·
    refine ⟨72970785273631757714973485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48647190182421171809982323 72970785273631757714973485)
    ·
      refine ⟨27364044477611909143115057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72970785273631757714973485 27364044477611909143115057)
      ·
        refine ⟨20523033358208931857336293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27364044477611909143115057 20523033358208931857336293)
        ·
          refine ⟨3848068754664174723250555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20523033358208931857336293 3848068754664174723250555)
          ·
            refine ⟨5772103131996262084875833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3848068754664174723250555 5772103131996262084875833)
            ·
              refine ⟨4329077348997196563656875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5772103131996262084875833 4329077348997196563656875)
              ·
                refine ⟨6493616023495794845485313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4329077348997196563656875 6493616023495794845485313)
                ·
                  refine ⟨4870212017621846134113985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6493616023495794845485313 4870212017621846134113985)
                  ·
                    refine ⟨3652659013216384600585489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4870212017621846134113985 3652659013216384600585489)
                    ·
                      refine ⟨2739494259912288450439117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3652659013216384600585489 2739494259912288450439117)
                      ·
                        rfl

theorem cell23_5335146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 4, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 4, 1, 2, 1, 2, 2, 2].length) (baseStart_5335146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5335146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5335146 prefixEnd_5335146 := by exact prefixLift 5335146
  have htrace : WordTrace (prefixWord ++ tailWord_5335146) baseStart_5335146 baseEnd_5335146 := by
    simpa [prefixWord, tailWord_5335146, baseEnd_5335146] using wordTrace_append hprefix tailTrace_5335146
  have hstable : (prefixWord ++ tailWord_5335146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5335146).length < 2 ^ (prefixWord ++ tailWord_5335146).sum := by decide
  have hdescent : baseEnd_5335146 < baseStart_5335146 := by decide
  rcases family_descends (prefixWord ++ tailWord_5335146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5335241 : List Nat := [1, 2, 1, 1, 2, 1, 1, 4, 5, 1, 4]
def baseStart_5335241 : Nat := 118140960795 + 5335241 * 2 ^ 59
def prefixEnd_5335241 : Nat := 4983230072969 + 3 ^ 40 * 5335241 * 2
def baseEnd_5335241 : Nat := 2739543040574465578751179

theorem tailTrace_5335241 : CollatzResearch.WordTrace tailWord_5335241 prefixEnd_5335241 2739543040574465578751179 := by
  unfold tailWord_5335241
  simp only [CollatzResearch.WordTrace]
  refine ⟨194592225664340518464637577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129728150442893678976425051 194592225664340518464637577)
  ·
    refine ⟨145944169248255388848478183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 194592225664340518464637577 145944169248255388848478183)
    ·
      refine ⟨218916253872383083272717275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145944169248255388848478183 218916253872383083272717275)
      ·
        refine ⟨328374380808574624909075913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 218916253872383083272717275 328374380808574624909075913)
        ·
          refine ⟨246280785606430968681806935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 328374380808574624909075913 246280785606430968681806935)
          ·
            refine ⟨369421178409646453022710403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 246280785606430968681806935 369421178409646453022710403)
            ·
              refine ⟨554131767614469679534065605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 369421178409646453022710403 554131767614469679534065605)
              ·
                refine ⟨103899706427713064912637301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 554131767614469679534065605 103899706427713064912637301)
                ·
                  refine ⟨9740597477598099835559747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 103899706427713064912637301 9740597477598099835559747)
                  ·
                    refine ⟨14610896216397149753339621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9740597477598099835559747 14610896216397149753339621)
                    ·
                      refine ⟨2739543040574465578751179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14610896216397149753339621 2739543040574465578751179)
                      ·
                        rfl

theorem cell23_5335241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 4, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 4, 5, 1, 4].length) (baseStart_5335241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5335241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5335241 prefixEnd_5335241 := by exact prefixLift 5335241
  have htrace : WordTrace (prefixWord ++ tailWord_5335241) baseStart_5335241 baseEnd_5335241 := by
    simpa [prefixWord, tailWord_5335241, baseEnd_5335241] using wordTrace_append hprefix tailTrace_5335241
  have hstable : (prefixWord ++ tailWord_5335241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5335241).length < 2 ^ (prefixWord ++ tailWord_5335241).sum := by decide
  have hdescent : baseEnd_5335241 < baseStart_5335241 := by decide
  rcases family_descends (prefixWord ++ tailWord_5335241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5335275 : List Nat := [1, 1, 1, 1, 2, 5, 1, 4, 3, 2, 2]
def baseStart_5335275 : Nat := 118140960795 + 5335275 * 2 ^ 59
def prefixEnd_5335275 : Nat := 4983230072969 + 3 ^ 40 * 5335275 * 2
def baseEnd_5335275 : Nat := 2739560498916718445726023

theorem tailTrace_5335275 : CollatzResearch.WordTrace tailWord_5335275 prefixEnd_5335275 2739560498916718445726023 := by
  unfold tailWord_5335275
  simp only [CollatzResearch.WordTrace]
  refine ⟨194593465746217342271375279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129728977164144894847583519 194593465746217342271375279)
  ·
    refine ⟨291890198619326013407062919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194593465746217342271375279 291890198619326013407062919)
    ·
      refine ⟨437835297928989020110594379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 291890198619326013407062919 437835297928989020110594379)
      ·
        refine ⟨656752946893483530165891569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 437835297928989020110594379 656752946893483530165891569)
        ·
          refine ⟨492564710170112647624418677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 656752946893483530165891569 492564710170112647624418677)
          ·
            refine ⟨46177941578448060714789251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 492564710170112647624418677 46177941578448060714789251)
            ·
              refine ⟨69266912367672091072183877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46177941578448060714789251 69266912367672091072183877)
              ·
                refine ⟨12987546068938517076034477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 69266912367672091072183877 12987546068938517076034477)
                ·
                  refine ⟨4870329775851943903512929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12987546068938517076034477 4870329775851943903512929)
                  ·
                    refine ⟨3652747331888957927634697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4870329775851943903512929 3652747331888957927634697)
                    ·
                      refine ⟨2739560498916718445726023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3652747331888957927634697 2739560498916718445726023)
                      ·
                        rfl

theorem cell23_5335275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 4, 3, 2, 2].length) (baseStart_5335275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5335275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5335275 prefixEnd_5335275 := by exact prefixLift 5335275
  have htrace : WordTrace (prefixWord ++ tailWord_5335275) baseStart_5335275 baseEnd_5335275 := by
    simpa [prefixWord, tailWord_5335275, baseEnd_5335275] using wordTrace_append hprefix tailTrace_5335275
  have hstable : (prefixWord ++ tailWord_5335275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5335275).length < 2 ^ (prefixWord ++ tailWord_5335275).sum := by decide
  have hdescent : baseEnd_5335275 < baseStart_5335275 := by decide
  rcases family_descends (prefixWord ++ tailWord_5335275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5335298 : List Nat := [3, 4, 1, 1, 2, 1, 11]
def baseStart_5335298 : Nat := 118140960795 + 5335298 * 2 ^ 59
def prefixEnd_5335298 : Nat := 4983230072969 + 3 ^ 40 * 5335298 * 2
def baseEnd_5335298 : Nat := 33821880357676195749857

theorem tailTrace_5335298 : CollatzResearch.WordTrace tailWord_5335298 prefixEnd_5335298 33821880357676195749857 := by
  unfold tailWord_5335298
  simp only [CollatzResearch.WordTrace]
  refine ⟨48648576156283504299865637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129729536416756011466308365 48648576156283504299865637)
  ·
    refine ⟨9121608029303157056224807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 48648576156283504299865637 9121608029303157056224807)
    ·
      refine ⟨13682412043954735584337211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9121608029303157056224807 13682412043954735584337211)
      ·
        refine ⟨20523618065932103376505817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13682412043954735584337211 20523618065932103376505817)
        ·
          refine ⟨15392713549449077532379363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20523618065932103376505817 15392713549449077532379363)
          ·
            refine ⟨23089070324173616298569045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15392713549449077532379363 23089070324173616298569045)
            ·
              refine ⟨33821880357676195749857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 23089070324173616298569045 33821880357676195749857)
              ·
                rfl

theorem cell23_5335298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 11].length) (baseStart_5335298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5335298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5335298 prefixEnd_5335298 := by exact prefixLift 5335298
  have htrace : WordTrace (prefixWord ++ tailWord_5335298) baseStart_5335298 baseEnd_5335298 := by
    simpa [prefixWord, tailWord_5335298, baseEnd_5335298] using wordTrace_append hprefix tailTrace_5335298
  have hstable : (prefixWord ++ tailWord_5335298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5335298).length < 2 ^ (prefixWord ++ tailWord_5335298).sum := by decide
  have hdescent : baseEnd_5335298 < baseStart_5335298 := by decide
  rcases family_descends (prefixWord ++ tailWord_5335298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5335368 : List Nat := [2, 1, 3, 1, 1, 2, 3, 1, 2, 4, 3]
def baseStart_5335368 : Nat := 118140960795 + 5335368 * 2 ^ 59
def prefixEnd_5335368 : Nat := 4983230072969 + 3 ^ 40 * 5335368 * 2
def baseEnd_5335368 : Nat := 2739608252617586581863095

theorem tailTrace_5335368 : CollatzResearch.WordTrace tailWord_5335368 prefixEnd_5335368 2739608252617586581863095 := by
  unfold tailWord_5335368
  simp only [CollatzResearch.WordTrace]
  refine ⟨97298428867440209577255379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129731238489920279436340505 97298428867440209577255379)
  ·
    refine ⟨145947643301160314365883069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97298428867440209577255379 145947643301160314365883069)
    ·
      refine ⟨54730366237935117887206151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 145947643301160314365883069 54730366237935117887206151)
      ·
        refine ⟨82095549356902676830809227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54730366237935117887206151 82095549356902676830809227)
        ·
          refine ⟨123143324035354015246213841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82095549356902676830809227 123143324035354015246213841)
          ·
            refine ⟨92357493026515511434660381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 123143324035354015246213841 92357493026515511434660381)
            ·
              refine ⟨34634059884943316787997643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 92357493026515511434660381 34634059884943316787997643)
              ·
                refine ⟨51951089827414975181996465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34634059884943316787997643 51951089827414975181996465)
                ·
                  refine ⟨38963317370561231386497349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 51951089827414975181996465 38963317370561231386497349)
                  ·
                    refine ⟨7305622006980230884968253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 38963317370561231386497349 7305622006980230884968253)
                    ·
                      refine ⟨2739608252617586581863095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7305622006980230884968253 2739608252617586581863095)
                      ·
                        rfl

theorem cell23_5335368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 3, 1, 2, 4, 3].length) (baseStart_5335368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5335368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5335368 prefixEnd_5335368 := by exact prefixLift 5335368
  have htrace : WordTrace (prefixWord ++ tailWord_5335368) baseStart_5335368 baseEnd_5335368 := by
    simpa [prefixWord, tailWord_5335368, baseEnd_5335368] using wordTrace_append hprefix tailTrace_5335368
  have hstable : (prefixWord ++ tailWord_5335368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5335368).length < 2 ^ (prefixWord ++ tailWord_5335368).sum := by decide
  have hdescent : baseEnd_5335368 < baseStart_5335368 := by decide
  rcases family_descends (prefixWord ++ tailWord_5335368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5335378 : List Nat := [3, 2, 2, 1, 1, 1, 3, 1, 1, 4, 4]
def baseStart_5335378 : Nat := 118140960795 + 5335378 * 2 ^ 59
def prefixEnd_5335378 : Nat := 4983230072969 + 3 ^ 40 * 5335378 * 2
def baseEnd_5335378 : Nat := 2739613387424131542738049

theorem tailTrace_5335378 : CollatzResearch.WordTrace tailWord_5335378 prefixEnd_5335378 2739613387424131542738049 := by
  unfold tailWord_5335378
  simp only [CollatzResearch.WordTrace]
  refine ⟨48649305616211047715593697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129731481643229460574916525 48649305616211047715593697)
  ·
    refine ⟨36486979212158285786695273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48649305616211047715593697 36486979212158285786695273)
    ·
      refine ⟨27365234409118714340021455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36486979212158285786695273 27365234409118714340021455)
      ·
        refine ⟨41047851613678071510032183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27365234409118714340021455 41047851613678071510032183)
        ·
          refine ⟨61571777420517107265048275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41047851613678071510032183 61571777420517107265048275)
          ·
            refine ⟨92357666130775660897572413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61571777420517107265048275 92357666130775660897572413)
            ·
              refine ⟨34634124799040872836589655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 92357666130775660897572413 34634124799040872836589655)
              ·
                refine ⟨51951187198561309254884483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34634124799040872836589655 51951187198561309254884483)
                ·
                  refine ⟨77926780797841963882326725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51951187198561309254884483 77926780797841963882326725)
                  ·
                    refine ⟨14611271399595368227936261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 77926780797841963882326725 14611271399595368227936261)
                    ·
                      refine ⟨2739613387424131542738049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14611271399595368227936261 2739613387424131542738049)
                      ·
                        rfl

theorem cell23_5335378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 3, 1, 1, 4, 4].length) (baseStart_5335378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5335378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5335378 prefixEnd_5335378 := by exact prefixLift 5335378
  have htrace : WordTrace (prefixWord ++ tailWord_5335378) baseStart_5335378 baseEnd_5335378 := by
    simpa [prefixWord, tailWord_5335378, baseEnd_5335378] using wordTrace_append hprefix tailTrace_5335378
  have hstable : (prefixWord ++ tailWord_5335378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5335378).length < 2 ^ (prefixWord ++ tailWord_5335378).sum := by decide
  have hdescent : baseEnd_5335378 < baseStart_5335378 := by decide
  rcases family_descends (prefixWord ++ tailWord_5335378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5335428 : List Nat := [2, 3, 2, 1, 1, 2, 2, 1, 1, 1, 7]
def baseStart_5335428 : Nat := 118140960795 + 5335428 * 2 ^ 59
def prefixEnd_5335428 : Nat := 4983230072969 + 3 ^ 40 * 5335428 * 2
def baseEnd_5335428 : Nat := 2739639061456856347112819

theorem tailTrace_5335428 : CollatzResearch.WordTrace tailWord_5335428 prefixEnd_5335428 2739639061456856347112819 := by
  unfold tailWord_5335428
  simp only [CollatzResearch.WordTrace]
  refine ⟨97299523057331524700847469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129732697409775366267796625 97299523057331524700847469)
  ·
    refine ⟨36487321146499321762817801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 97299523057331524700847469 36487321146499321762817801)
    ·
      refine ⟨27365490859874491322113351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36487321146499321762817801 27365490859874491322113351)
      ·
        refine ⟨41048236289811736983170027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27365490859874491322113351 41048236289811736983170027)
        ·
          refine ⟨61572354434717605474755041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41048236289811736983170027 61572354434717605474755041)
          ·
            refine ⟨46179265826038204106066281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61572354434717605474755041 46179265826038204106066281)
            ·
              refine ⟨34634449369528653079549711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46179265826038204106066281 34634449369528653079549711)
              ·
                refine ⟨51951674054292979619324567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34634449369528653079549711 51951674054292979619324567)
                ·
                  refine ⟨77927511081439469428986851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51951674054292979619324567 77927511081439469428986851)
                  ·
                    refine ⟨116891266622159204143480277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 77927511081439469428986851 116891266622159204143480277)
                    ·
                      refine ⟨2739639061456856347112819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 116891266622159204143480277 2739639061456856347112819)
                      ·
                        rfl

theorem cell23_5335428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 2, 1, 1, 1, 7].length) (baseStart_5335428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5335428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5335428 prefixEnd_5335428 := by exact prefixLift 5335428
  have htrace : WordTrace (prefixWord ++ tailWord_5335428) baseStart_5335428 baseEnd_5335428 := by
    simpa [prefixWord, tailWord_5335428, baseEnd_5335428] using wordTrace_append hprefix tailTrace_5335428
  have hstable : (prefixWord ++ tailWord_5335428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5335428).length < 2 ^ (prefixWord ++ tailWord_5335428).sum := by decide
  have hdescent : baseEnd_5335428 < baseStart_5335428 := by decide
  rcases family_descends (prefixWord ++ tailWord_5335428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5335455 : List Nat := [1, 1, 2, 5, 1, 1, 2, 3, 2, 1, 4]
def baseStart_5335455 : Nat := 118140960795 + 5335455 * 2 ^ 59
def prefixEnd_5335455 : Nat := 4983230072969 + 3 ^ 40 * 5335455 * 2
def baseEnd_5335455 : Nat := 2739652925434527741475195

theorem tailTrace_5335455 : CollatzResearch.WordTrace tailWord_5335455 prefixEnd_5335455 2739652925434527741475195 := by
  unfold tailWord_5335455
  simp only [CollatzResearch.WordTrace]
  refine ⟨194600030885565233012927819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129733353923710155341951879 194600030885565233012927819)
  ·
    refine ⟨291900046328347849519391729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194600030885565233012927819 291900046328347849519391729)
    ·
      refine ⟨218925034746260887139543797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 291900046328347849519391729 218925034746260887139543797)
      ·
        refine ⟨20524222007461958169332231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 218925034746260887139543797 20524222007461958169332231)
        ·
          refine ⟨30786333011192937253998347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20524222007461958169332231 30786333011192937253998347)
          ·
            refine ⟨46179499516789405880997521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30786333011192937253998347 46179499516789405880997521)
            ·
              refine ⟨34634624637592054410748141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46179499516789405880997521 34634624637592054410748141)
              ·
                refine ⟨12987984239097020404030553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34634624637592054410748141 12987984239097020404030553)
                ·
                  refine ⟨9740988179322765303022915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12987984239097020404030553 9740988179322765303022915)
                  ·
                    refine ⟨14611482268984147954534373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9740988179322765303022915 14611482268984147954534373)
                    ·
                      refine ⟨2739652925434527741475195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14611482268984147954534373 2739652925434527741475195)
                      ·
                        rfl

theorem cell23_5335455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 2, 3, 2, 1, 4].length) (baseStart_5335455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5335455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5335455 prefixEnd_5335455 := by exact prefixLift 5335455
  have htrace : WordTrace (prefixWord ++ tailWord_5335455) baseStart_5335455 baseEnd_5335455 := by
    simpa [prefixWord, tailWord_5335455, baseEnd_5335455] using wordTrace_append hprefix tailTrace_5335455
  have hstable : (prefixWord ++ tailWord_5335455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5335455).length < 2 ^ (prefixWord ++ tailWord_5335455).sum := by decide
  have hdescent : baseEnd_5335455 < baseStart_5335455 := by decide
  rcases family_descends (prefixWord ++ tailWord_5335455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5335482 : List Nat := [3, 1, 1, 1, 2, 1, 1, 8, 1, 4]
def baseStart_5335482 : Nat := 118140960795 + 5335482 * 2 ^ 59
def prefixEnd_5335482 : Nat := 4983230072969 + 3 ^ 40 * 5335482 * 2
def baseEnd_5335482 : Nat := 913222263137399711945857

theorem tailTrace_5335482 : CollatzResearch.WordTrace tailWord_5335482 prefixEnd_5335482 913222263137399711945857 := by
  unfold tailWord_5335482
  simp only [CollatzResearch.WordTrace]
  refine ⟨48650253914116854156040175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129734010437644944416107133 48650253914116854156040175)
  ·
    refine ⟨72975380871175281234060263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48650253914116854156040175 72975380871175281234060263)
    ·
      refine ⟨109463071306762921851090395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72975380871175281234060263 109463071306762921851090395)
      ·
        refine ⟨164194606960144382776635593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109463071306762921851090395 164194606960144382776635593)
        ·
          refine ⟨123145955220108287082476695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 164194606960144382776635593 123145955220108287082476695)
          ·
            refine ⟨184718932830162430623715043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 123145955220108287082476695 184718932830162430623715043)
            ·
              refine ⟨277078399245243645935572565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 184718932830162430623715043 277078399245243645935572565)
              ·
                refine ⟨3247012491155198975807491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 277078399245243645935572565 3247012491155198975807491)
                ·
                  refine ⟨4870518736732798463711237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3247012491155198975807491 4870518736732798463711237)
                  ·
                    refine ⟨913222263137399711945857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4870518736732798463711237 913222263137399711945857)
                    ·
                      rfl

theorem cell23_5335482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 8, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 8, 1, 4].length) (baseStart_5335482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5335482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5335482 prefixEnd_5335482 := by exact prefixLift 5335482
  have htrace : WordTrace (prefixWord ++ tailWord_5335482) baseStart_5335482 baseEnd_5335482 := by
    simpa [prefixWord, tailWord_5335482, baseEnd_5335482] using wordTrace_append hprefix tailTrace_5335482
  have hstable : (prefixWord ++ tailWord_5335482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5335482).length < 2 ^ (prefixWord ++ tailWord_5335482).sum := by decide
  have hdescent : baseEnd_5335482 < baseStart_5335482 := by decide
  rcases family_descends (prefixWord ++ tailWord_5335482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5335495 : List Nat := [1, 1, 4, 1, 1, 5, 1, 3, 6]
def baseStart_5335495 : Nat := 118140960795 + 5335495 * 2 ^ 59
def prefixEnd_5335495 : Nat := 4983230072969 + 3 ^ 40 * 5335495 * 2
def baseEnd_5335495 : Nat := 304408162740078620552779

theorem tailTrace_5335495 : CollatzResearch.WordTrace tailWord_5335495 prefixEnd_5335495 304408162740078620552779 := by
  unfold tailWord_5335495
  simp only [CollatzResearch.WordTrace]
  refine ⟨194601489805420319844383939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129734326536946879896255959 194601489805420319844383939)
  ·
    refine ⟨291902234708130479766575909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194601489805420319844383939 291902234708130479766575909)
    ·
      refine ⟨54731669007774464956232983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 291902234708130479766575909 54731669007774464956232983)
      ·
        refine ⟨82097503511661697434349475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54731669007774464956232983 82097503511661697434349475)
        ·
          refine ⟨123146255267492546151524213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82097503511661697434349475 123146255267492546151524213)
          ·
            refine ⟨11544961431327426201705395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 123146255267492546151524213 11544961431327426201705395)
            ·
              refine ⟨17317442146991139302558093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11544961431327426201705395 17317442146991139302558093)
              ·
                refine ⟨6494040805121677238459285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17317442146991139302558093 6494040805121677238459285)
                ·
                  refine ⟨304408162740078620552779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6494040805121677238459285 304408162740078620552779)
                  ·
                    rfl

theorem cell23_5335495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 1, 3, 6].length) (baseStart_5335495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5335495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5335495 prefixEnd_5335495 := by exact prefixLift 5335495
  have htrace : WordTrace (prefixWord ++ tailWord_5335495) baseStart_5335495 baseEnd_5335495 := by
    simpa [prefixWord, tailWord_5335495, baseEnd_5335495] using wordTrace_append hprefix tailTrace_5335495
  have hstable : (prefixWord ++ tailWord_5335495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5335495).length < 2 ^ (prefixWord ++ tailWord_5335495).sum := by decide
  have hdescent : baseEnd_5335495 < baseStart_5335495 := by decide
  rcases family_descends (prefixWord ++ tailWord_5335495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5335532 : List Nat := [2, 2, 1, 1, 2, 1, 3, 4, 2, 3, 2]
def baseStart_5335532 : Nat := 118140960795 + 5335532 * 2 ^ 59
def prefixEnd_5335532 : Nat := 4983230072969 + 3 ^ 40 * 5335532 * 2
def baseEnd_5335532 : Nat := 2739692463444923940212341

theorem tailTrace_5335532 : CollatzResearch.WordTrace tailWord_5335532 prefixEnd_5335532 2739692463444923940212341 := by
  unfold tailWord_5335532
  simp only [CollatzResearch.WordTrace]
  refine ⟨97301419653143137581740425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129735226204190850108987233 97301419653143137581740425)
  ·
    refine ⟨72976064739857353186305319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97301419653143137581740425 72976064739857353186305319)
    ·
      refine ⟨109464097109786029779457979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72976064739857353186305319 109464097109786029779457979)
      ·
        refine ⟨164196145664679044669186969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109464097109786029779457979 164196145664679044669186969)
        ·
          refine ⟨123147109248509283501890227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 164196145664679044669186969 123147109248509283501890227)
          ·
            refine ⟨184720663872763925252835341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 123147109248509283501890227 184720663872763925252835341)
            ·
              refine ⟨69270248952286471969813253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 184720663872763925252835341 69270248952286471969813253)
              ·
                refine ⟨12988171678553713494339985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 69270248952286471969813253 12988171678553713494339985)
                ·
                  refine ⟨9741128758915285120754989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12988171678553713494339985 9741128758915285120754989)
                  ·
                    refine ⟨3652923284593231920283121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9741128758915285120754989 3652923284593231920283121)
                    ·
                      refine ⟨2739692463444923940212341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3652923284593231920283121 2739692463444923940212341)
                      ·
                        rfl

theorem cell23_5335532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 3, 2].length) (baseStart_5335532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5335532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5335532 prefixEnd_5335532 := by exact prefixLift 5335532
  have htrace : WordTrace (prefixWord ++ tailWord_5335532) baseStart_5335532 baseEnd_5335532 := by
    simpa [prefixWord, tailWord_5335532, baseEnd_5335532] using wordTrace_append hprefix tailTrace_5335532
  have hstable : (prefixWord ++ tailWord_5335532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5335532).length < 2 ^ (prefixWord ++ tailWord_5335532).sum := by decide
  have hdescent : baseEnd_5335532 < baseStart_5335532 := by decide
  rcases family_descends (prefixWord ++ tailWord_5335532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5335533 : List Nat := [1, 5, 1, 3, 1, 3, 2, 2, 1, 4]
def baseStart_5335533 : Nat := 118140960795 + 5335533 * 2 ^ 59
def prefixEnd_5335533 : Nat := 4983230072969 + 3 ^ 40 * 5335533 * 2
def baseEnd_5335533 : Nat := 913230992308526145433279

theorem tailTrace_5335533 : CollatzResearch.WordTrace tailWord_5335533 prefixEnd_5335533 913230992308526145433279 := by
  unfold tailWord_5335533
  simp only [CollatzResearch.WordTrace]
  refine ⟨194602875779282652334267253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129735250519521768222844835 194602875779282652334267253)
  ·
    refine ⟨18244019604307748656337555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 194602875779282652334267253 18244019604307748656337555)
    ·
      refine ⟨27366029406461622984506333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18244019604307748656337555 27366029406461622984506333)
      ·
        refine ⟨10262261027423108619189875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27366029406461622984506333 10262261027423108619189875)
        ·
          refine ⟨15393391541134662928784813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10262261027423108619189875 15393391541134662928784813)
          ·
            refine ⟨5772521827925498598294305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15393391541134662928784813 5772521827925498598294305)
            ·
              refine ⟨4329391370944123948720729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5772521827925498598294305 4329391370944123948720729)
              ·
                refine ⟨3247043528208092961540547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4329391370944123948720729 3247043528208092961540547)
                ·
                  refine ⟨4870565292312139442310821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3247043528208092961540547 4870565292312139442310821)
                  ·
                    refine ⟨913230992308526145433279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4870565292312139442310821 913230992308526145433279)
                    ·
                      rfl

theorem cell23_5335533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 3, 2, 2, 1, 4].length) (baseStart_5335533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5335533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5335533 prefixEnd_5335533 := by exact prefixLift 5335533
  have htrace : WordTrace (prefixWord ++ tailWord_5335533) baseStart_5335533 baseEnd_5335533 := by
    simpa [prefixWord, tailWord_5335533, baseEnd_5335533] using wordTrace_append hprefix tailTrace_5335533
  have hstable : (prefixWord ++ tailWord_5335533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5335533).length < 2 ^ (prefixWord ++ tailWord_5335533).sum := by decide
  have hdescent : baseEnd_5335533 < baseStart_5335533 := by decide
  rcases family_descends (prefixWord ++ tailWord_5335533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5335539 : List Nat := [1, 1, 1, 2, 2, 2, 5, 4, 1, 1, 3]
def baseStart_5335539 : Nat := 118140960795 + 5335539 * 2 ^ 59
def prefixEnd_5335539 : Nat := 4983230072969 + 3 ^ 40 * 5335539 * 2
def baseEnd_5335539 : Nat := 2739696057809505412824809

theorem tailTrace_5335539 : CollatzResearch.WordTrace tailWord_5335539 prefixEnd_5335539 2739696057809505412824809 := by
  unfold tailWord_5335539
  simp only [CollatzResearch.WordTrace]
  refine ⟨194603094617260915358985671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129735396411507276905990447 194603094617260915358985671)
  ·
    refine ⟨291904641925891373038478507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194603094617260915358985671 291904641925891373038478507)
    ·
      refine ⟨437856962888837059557717761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 291904641925891373038478507 437856962888837059557717761)
      ·
        refine ⟨328392722166627794668288321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 437856962888837059557717761 328392722166627794668288321)
        ·
          refine ⟨246294541624970846001216241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 328392722166627794668288321 246294541624970846001216241)
          ·
            refine ⟨184720906218728134500912181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 246294541624970846001216241 184720906218728134500912181)
            ·
              refine ⟨17317584958005762609460517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 184720906218728134500912181 17317584958005762609460517)
              ·
                refine ⟨3247047179626080489273847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17317584958005762609460517 3247047179626080489273847)
                ·
                  refine ⟨4870570769439120733910771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3247047179626080489273847 4870570769439120733910771)
                  ·
                    refine ⟨7305856154158681100866157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4870570769439120733910771 7305856154158681100866157)
                    ·
                      refine ⟨2739696057809505412824809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7305856154158681100866157 2739696057809505412824809)
                      ·
                        rfl

theorem cell23_5335539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 5, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 5, 4, 1, 1, 3].length) (baseStart_5335539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5335539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5335539 prefixEnd_5335539 := by exact prefixLift 5335539
  have htrace : WordTrace (prefixWord ++ tailWord_5335539) baseStart_5335539 baseEnd_5335539 := by
    simpa [prefixWord, tailWord_5335539, baseEnd_5335539] using wordTrace_append hprefix tailTrace_5335539
  have hstable : (prefixWord ++ tailWord_5335539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5335539).length < 2 ^ (prefixWord ++ tailWord_5335539).sum := by decide
  have hdescent : baseEnd_5335539 < baseStart_5335539 := by decide
  rcases family_descends (prefixWord ++ tailWord_5335539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5335545 : List Nat := [1, 2, 1, 3, 1, 2, 3, 2, 3, 1, 4]
def baseStart_5335545 : Nat := 118140960795 + 5335545 * 2 ^ 59
def prefixEnd_5335545 : Nat := 4983230072969 + 3 ^ 40 * 5335545 * 2
def baseEnd_5335545 : Nat := 2739699138693432389349781

theorem tailTrace_5335545 : CollatzResearch.WordTrace tailWord_5335545 prefixEnd_5335545 2739699138693432389349781 := by
  unfold tailWord_5335545
  simp only [CollatzResearch.WordTrace]
  refine ⟨194603313455239178383704089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129735542303492785589136059 194603313455239178383704089)
  ·
    refine ⟨145952485091429383787778067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 194603313455239178383704089 145952485091429383787778067)
    ·
      refine ⟨218928727637144075681667101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145952485091429383787778067 218928727637144075681667101)
      ·
        refine ⟨82098272863929028380625163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 218928727637144075681667101 82098272863929028380625163)
        ·
          refine ⟨123147409295893542570937745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82098272863929028380625163 123147409295893542570937745)
          ·
            refine ⟨92360556971920156928203309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 123147409295893542570937745 92360556971920156928203309)
            ·
              refine ⟨34635208864470058848076241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 92360556971920156928203309 34635208864470058848076241)
              ·
                refine ⟨25976406648352544136057181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34635208864470058848076241 25976406648352544136057181)
                ·
                  refine ⟨9741152493132204051021443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25976406648352544136057181 9741152493132204051021443)
                  ·
                    refine ⟨14611728739698306076532165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9741152493132204051021443 14611728739698306076532165)
                    ·
                      refine ⟨2739699138693432389349781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14611728739698306076532165 2739699138693432389349781)
                      ·
                        rfl

theorem cell23_5335545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 3, 2, 3, 1, 4].length) (baseStart_5335545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5335545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5335545 prefixEnd_5335545 := by exact prefixLift 5335545
  have htrace : WordTrace (prefixWord ++ tailWord_5335545) baseStart_5335545 baseEnd_5335545 := by
    simpa [prefixWord, tailWord_5335545, baseEnd_5335545] using wordTrace_append hprefix tailTrace_5335545
  have hstable : (prefixWord ++ tailWord_5335545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5335545).length < 2 ^ (prefixWord ++ tailWord_5335545).sum := by decide
  have hdescent : baseEnd_5335545 < baseStart_5335545 := by decide
  rcases family_descends (prefixWord ++ tailWord_5335545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5335555 : List Nat := [1, 1, 1, 3, 2, 1, 6, 1, 1, 6]
def baseStart_5335555 : Nat := 118140960795 + 5335555 * 2 ^ 59
def prefixEnd_5335555 : Nat := 4983230072969 + 3 ^ 40 * 5335555 * 2
def baseEnd_5335555 : Nat := 913234757833325783408245

theorem tailTrace_5335555 : CollatzResearch.WordTrace tailWord_5335555 prefixEnd_5335555 913234757833325783408245 := by
  unfold tailWord_5335555
  simp only [CollatzResearch.WordTrace]
  refine ⟨194603678185202950091568119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129735785456801966727712079 194603678185202950091568119)
  ·
    refine ⟨291905517277804425137352179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194603678185202950091568119 291905517277804425137352179)
    ·
      refine ⟨437858275916706637706028269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 291905517277804425137352179 437858275916706637706028269)
      ·
        refine ⟨164196853468764989139760601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 437858275916706637706028269 164196853468764989139760601)
        ·
          refine ⟨123147640101573741854820451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 164196853468764989139760601 123147640101573741854820451)
          ·
            refine ⟨184721460152360612782230677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 123147640101573741854820451 184721460152360612782230677)
            ·
              refine ⟨8658818444641903724167063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 184721460152360612782230677 8658818444641903724167063)
              ·
                refine ⟨12988227666962855586250595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8658818444641903724167063 12988227666962855586250595)
                ·
                  refine ⟨19482341500444283379375893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12988227666962855586250595 19482341500444283379375893)
                  ·
                    refine ⟨913234757833325783408245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19482341500444283379375893 913234757833325783408245)
                    ·
                      rfl

theorem cell23_5335555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 6, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 6, 1, 1, 6].length) (baseStart_5335555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5335555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5335555 prefixEnd_5335555 := by exact prefixLift 5335555
  have htrace : WordTrace (prefixWord ++ tailWord_5335555) baseStart_5335555 baseEnd_5335555 := by
    simpa [prefixWord, tailWord_5335555, baseEnd_5335555] using wordTrace_append hprefix tailTrace_5335555
  have hstable : (prefixWord ++ tailWord_5335555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5335555).length < 2 ^ (prefixWord ++ tailWord_5335555).sum := by decide
  have hdescent : baseEnd_5335555 < baseStart_5335555 := by decide
  rcases family_descends (prefixWord ++ tailWord_5335555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5335562 : List Nat := [3, 1, 2, 2, 2, 1, 2, 4, 1, 1, 4]
def baseStart_5335562 : Nat := 118140960795 + 5335562 * 2 ^ 59
def prefixEnd_5335562 : Nat := 4983230072969 + 3 ^ 40 * 5335562 * 2
def baseEnd_5335562 : Nat := 2739707867864558822837203

theorem tailTrace_5335562 : CollatzResearch.WordTrace tailWord_5335562 prefixEnd_5335562 2739707867864558822837203 := by
  unfold tailWord_5335562
  simp only [CollatzResearch.WordTrace]
  refine ⟨48650983374044397571768235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129735955664118393524715293 48650983374044397571768235)
  ·
    refine ⟨72976475061066596357652353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48650983374044397571768235 72976475061066596357652353)
    ·
      refine ⟨54732356295799947268239265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72976475061066596357652353 54732356295799947268239265)
      ·
        refine ⟨41049267221849960451179449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54732356295799947268239265 41049267221849960451179449)
        ·
          refine ⟨30786950416387470338384587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41049267221849960451179449 30786950416387470338384587)
          ·
            refine ⟨46180425624581205507576881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30786950416387470338384587 46180425624581205507576881)
            ·
              refine ⟨34635319218435904130682661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46180425624581205507576881 34635319218435904130682661)
              ·
                refine ⟨6494122353456732024502999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34635319218435904130682661 6494122353456732024502999)
                ·
                  refine ⟨9741183530185098036754499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6494122353456732024502999 9741183530185098036754499)
                  ·
                    refine ⟨14611775295277647055131749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9741183530185098036754499 14611775295277647055131749)
                    ·
                      refine ⟨2739707867864558822837203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14611775295277647055131749 2739707867864558822837203)
                      ·
                        rfl

theorem cell23_5335562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 2, 4, 1, 1, 4].length) (baseStart_5335562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5335562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5335562 prefixEnd_5335562 := by exact prefixLift 5335562
  have htrace : WordTrace (prefixWord ++ tailWord_5335562) baseStart_5335562 baseEnd_5335562 := by
    simpa [prefixWord, tailWord_5335562, baseEnd_5335562] using wordTrace_append hprefix tailTrace_5335562
  have hstable : (prefixWord ++ tailWord_5335562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5335562).length < 2 ^ (prefixWord ++ tailWord_5335562).sum := by decide
  have hdescent : baseEnd_5335562 < baseStart_5335562 := by decide
  rcases family_descends (prefixWord ++ tailWord_5335562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5335566 : List Nat := [4, 1, 1, 2, 3, 3, 1, 1, 2, 3, 2]
def baseStart_5335566 : Nat := 118140960795 + 5335566 * 2 ^ 59
def prefixEnd_5335566 : Nat := 4983230072969 + 3 ^ 40 * 5335566 * 2
def baseEnd_5335566 : Nat := 2739709921787176807187185

theorem tailTrace_5335566 : CollatzResearch.WordTrace tailWord_5335566 prefixEnd_5335566 2739709921787176807187185 := by
  unfold tailWord_5335566
  simp only [CollatzResearch.WordTrace]
  refine ⟨24325509923520387371277319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 129736052925442065980145701 24325509923520387371277319)
  ·
    refine ⟨36488264885280581056915979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24325509923520387371277319 36488264885280581056915979)
    ·
      refine ⟨54732397327920871585373969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36488264885280581056915979 54732397327920871585373969)
      ·
        refine ⟨41049297995940653689030477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54732397327920871585373969 41049297995940653689030477)
        ·
          refine ⟨15393486748477745133386429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41049297995940653689030477 15393486748477745133386429)
          ·
            refine ⟨5772557530679154425019911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15393486748477745133386429 5772557530679154425019911)
            ·
              refine ⟨8658836296018731637529867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5772557530679154425019911 8658836296018731637529867)
              ·
                refine ⟨12988254444028097456294801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8658836296018731637529867 12988254444028097456294801)
                ·
                  refine ⟨9741190833021073092221101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12988254444028097456294801 9741190833021073092221101)
                  ·
                    refine ⟨3652946562382902409582913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9741190833021073092221101 3652946562382902409582913)
                    ·
                      refine ⟨2739709921787176807187185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3652946562382902409582913 2739709921787176807187185)
                      ·
                        rfl

theorem cell23_5335566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 3, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 3, 1, 1, 2, 3, 2].length) (baseStart_5335566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5335566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5335566 prefixEnd_5335566 := by exact prefixLift 5335566
  have htrace : WordTrace (prefixWord ++ tailWord_5335566) baseStart_5335566 baseEnd_5335566 := by
    simpa [prefixWord, tailWord_5335566, baseEnd_5335566] using wordTrace_append hprefix tailTrace_5335566
  have hstable : (prefixWord ++ tailWord_5335566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5335566).length < 2 ^ (prefixWord ++ tailWord_5335566).sum := by decide
  have hdescent : baseEnd_5335566 < baseStart_5335566 := by decide
  rcases family_descends (prefixWord ++ tailWord_5335566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5335595 : List Nat := [1, 1, 1, 1, 2, 1, 3, 4, 3, 3, 3]
def baseStart_5335595 : Nat := 118140960795 + 5335595 * 2 ^ 59
def prefixEnd_5335595 : Nat := 4983230072969 + 3 ^ 40 * 5335595 * 2
def baseEnd_5335595 : Nat := 2739724812726157193724551

theorem tailTrace_5335595 : CollatzResearch.WordTrace tailWord_5335595 prefixEnd_5335595 2739724812726157193724551 := by
  unfold tailWord_5335595
  simp only [CollatzResearch.WordTrace]
  refine ⟨194605137105058036923024239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129736758070038691282016159 194605137105058036923024239)
  ·
    refine ⟨291907705657587055384536359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194605137105058036923024239 291907705657587055384536359)
    ·
      refine ⟨437861558486380583076804539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 291907705657587055384536359 437861558486380583076804539)
      ·
        refine ⟨656792337729570874615206809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 437861558486380583076804539 656792337729570874615206809)
        ·
          refine ⟨492594253297178155961405107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 656792337729570874615206809 492594253297178155961405107)
          ·
            refine ⟨738891379945767233942107661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 492594253297178155961405107 738891379945767233942107661)
            ·
              refine ⟨277084267479662712728290373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 738891379945767233942107661 277084267479662712728290373)
              ·
                refine ⟨51953300152436758636554445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 277084267479662712728290373 51953300152436758636554445)
                ·
                  refine ⟨19482487557163784488707917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 51953300152436758636554445 19482487557163784488707917)
                  ·
                    refine ⟨7305932833936419183265469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19482487557163784488707917 7305932833936419183265469)
                    ·
                      refine ⟨2739724812726157193724551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7305932833936419183265469 2739724812726157193724551)
                      ·
                        rfl

theorem cell23_5335595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 4, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 4, 3, 3, 3].length) (baseStart_5335595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5335595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5335595 prefixEnd_5335595 := by exact prefixLift 5335595
  have htrace : WordTrace (prefixWord ++ tailWord_5335595) baseStart_5335595 baseEnd_5335595 := by
    simpa [prefixWord, tailWord_5335595, baseEnd_5335595] using wordTrace_append hprefix tailTrace_5335595
  have hstable : (prefixWord ++ tailWord_5335595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5335595).length < 2 ^ (prefixWord ++ tailWord_5335595).sum := by decide
  have hdescent : baseEnd_5335595 < baseStart_5335595 := by decide
  rcases family_descends (prefixWord ++ tailWord_5335595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5335639 : List Nat := [1, 1, 3, 2, 2, 2, 1, 5, 1, 3, 2]
def baseStart_5335639 : Nat := 118140960795 + 5335639 * 2 ^ 59
def prefixEnd_5335639 : Nat := 4983230072969 + 3 ^ 40 * 5335639 * 2
def baseEnd_5335639 : Nat := 2739747405874955021574349

theorem tailTrace_5335639 : CollatzResearch.WordTrace tailWord_5335639 prefixEnd_5335639 2739747405874955021574349 := by
  unfold tailWord_5335639
  simp only [CollatzResearch.WordTrace]
  refine ⟨194606741916898632437625971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129737827944599088291750647 194606741916898632437625971)
  ·
    refine ⟨291910112875347948656438957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194606741916898632437625971 291910112875347948656438957)
    ·
      refine ⟨109466292328255480746164609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 291910112875347948656438957 109466292328255480746164609)
      ·
        refine ⟨82099719246191610559623457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 109466292328255480746164609 82099719246191610559623457)
        ·
          refine ⟨61574789434643707919717593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82099719246191610559623457 61574789434643707919717593)
          ·
            refine ⟨46181092075982780939788195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61574789434643707919717593 46181092075982780939788195)
            ·
              refine ⟨69271638113974171409682293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46181092075982780939788195 69271638113974171409682293)
              ·
                refine ⟨6494216073185078569657715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 69271638113974171409682293 6494216073185078569657715)
                ·
                  refine ⟨9741324109777617854486573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6494216073185078569657715 9741324109777617854486573)
                  ·
                    refine ⟨3652996541166606695432465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9741324109777617854486573 3652996541166606695432465)
                    ·
                      refine ⟨2739747405874955021574349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3652996541166606695432465 2739747405874955021574349)
                      ·
                        rfl

theorem cell23_5335639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 5, 1, 3, 2].length) (baseStart_5335639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5335639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5335639 prefixEnd_5335639 := by exact prefixLift 5335639
  have htrace : WordTrace (prefixWord ++ tailWord_5335639) baseStart_5335639 baseEnd_5335639 := by
    simpa [prefixWord, tailWord_5335639, baseEnd_5335639] using wordTrace_append hprefix tailTrace_5335639
  have hstable : (prefixWord ++ tailWord_5335639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5335639).length < 2 ^ (prefixWord ++ tailWord_5335639).sum := by decide
  have hdescent : baseEnd_5335639 < baseStart_5335639 := by decide
  rcases family_descends (prefixWord ++ tailWord_5335639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5335655 : List Nat := [1, 1, 5, 1, 1, 1, 1, 1, 3, 3, 5]
def baseStart_5335655 : Nat := 118140960795 + 5335655 * 2 ^ 59
def prefixEnd_5335655 : Nat := 4983230072969 + 3 ^ 40 * 5335655 * 2
def baseEnd_5335655 : Nat := 2739755621565426958974275

theorem tailTrace_5335655 : CollatzResearch.WordTrace tailWord_5335655 prefixEnd_5335655 2739755621565426958974275 := by
  unfold tailWord_5335655
  simp only [CollatzResearch.WordTrace]
  refine ⟨194607325484840667170208419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129738216989893778113472279 194607325484840667170208419)
  ·
    refine ⟨291910988227261000755312629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194607325484840667170208419 291910988227261000755312629)
    ·
      refine ⟨27366655146305718820810559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 291910988227261000755312629 27366655146305718820810559)
      ·
        refine ⟨41049982719458578231215839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27366655146305718820810559 41049982719458578231215839)
        ·
          refine ⟨61574974079187867346823759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41049982719458578231215839 61574974079187867346823759)
          ·
            refine ⟨92362461118781801020235639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61574974079187867346823759 92362461118781801020235639)
            ·
              refine ⟨138543691678172701530353459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 92362461118781801020235639 138543691678172701530353459)
              ·
                refine ⟨207815537517259052295530189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 138543691678172701530353459 207815537517259052295530189)
                ·
                  refine ⟨77930826568972144610823821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 207815537517259052295530189 77930826568972144610823821)
                  ·
                    refine ⟨29224059963364554229058933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 77930826568972144610823821 29224059963364554229058933)
                    ·
                      refine ⟨2739755621565426958974275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29224059963364554229058933 2739755621565426958974275)
                      ·
                        rfl

theorem cell23_5335655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 1, 3, 3, 5].length) (baseStart_5335655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5335655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5335655 prefixEnd_5335655 := by exact prefixLift 5335655
  have htrace : WordTrace (prefixWord ++ tailWord_5335655) baseStart_5335655 baseEnd_5335655 := by
    simpa [prefixWord, tailWord_5335655, baseEnd_5335655] using wordTrace_append hprefix tailTrace_5335655
  have hstable : (prefixWord ++ tailWord_5335655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5335655).length < 2 ^ (prefixWord ++ tailWord_5335655).sum := by decide
  have hdescent : baseEnd_5335655 < baseStart_5335655 := by decide
  rcases family_descends (prefixWord ++ tailWord_5335655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5335715 : List Nat := [1, 1, 1, 4, 1, 1, 2, 3, 1, 1, 7]
def baseStart_5335715 : Nat := 118140960795 + 5335715 * 2 ^ 59
def prefixEnd_5335715 : Nat := 4983230072969 + 3 ^ 40 * 5335715 * 2
def baseEnd_5335715 : Nat := 2739786430404696724223999

theorem tailTrace_5335715 : CollatzResearch.WordTrace tailWord_5335715 prefixEnd_5335715 2739786430404696724223999 := by
  unfold tailWord_5335715
  simp only [CollatzResearch.WordTrace]
  refine ⟨194609513864623297417392599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129739675909748864944928399 194609513864623297417392599)
  ·
    refine ⟨291914270796934946126088899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194609513864623297417392599 291914270796934946126088899)
    ·
      refine ⟨437871406195402419189133349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 291914270796934946126088899 437871406195402419189133349)
      ·
        refine ⟨82100888661637953597962503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 437871406195402419189133349 82100888661637953597962503)
        ·
          refine ⟨123151332992456930396943755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82100888661637953597962503 123151332992456930396943755)
          ·
            refine ⟨184726999488685395595415633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 123151332992456930396943755 184726999488685395595415633)
            ·
              refine ⟨138545249616514046696561725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 184726999488685395595415633 138545249616514046696561725)
              ·
                refine ⟨51954468606192767511210647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 138545249616514046696561725 51954468606192767511210647)
                ·
                  refine ⟨77931702909289151266815971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51954468606192767511210647 77931702909289151266815971)
                  ·
                    refine ⟨116897554363933726900223957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 77931702909289151266815971 116897554363933726900223957)
                    ·
                      refine ⟨2739786430404696724223999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 116897554363933726900223957 2739786430404696724223999)
                      ·
                        rfl

theorem cell23_5335715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 3, 1, 1, 7].length) (baseStart_5335715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5335715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5335715 prefixEnd_5335715 := by exact prefixLift 5335715
  have htrace : WordTrace (prefixWord ++ tailWord_5335715) baseStart_5335715 baseEnd_5335715 := by
    simpa [prefixWord, tailWord_5335715, baseEnd_5335715] using wordTrace_append hprefix tailTrace_5335715
  have hstable : (prefixWord ++ tailWord_5335715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5335715).length < 2 ^ (prefixWord ++ tailWord_5335715).sum := by decide
  have hdescent : baseEnd_5335715 < baseStart_5335715 := by decide
  rcases family_descends (prefixWord ++ tailWord_5335715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5335769 : List Nat := [1, 2, 1, 2, 3, 2, 4, 1, 3, 4]
def baseStart_5335769 : Nat := 118140960795 + 5335769 * 2 ^ 59
def prefixEnd_5335769 : Nat := 4983230072969 + 3 ^ 40 * 5335769 * 2
def baseEnd_5335769 : Nat := 913271386120013170982917

theorem tailTrace_5335769 : CollatzResearch.WordTrace tailWord_5335769 prefixEnd_5335769 913271386120013170982917 := by
  unfold tailWord_5335769
  simp only [CollatzResearch.WordTrace]
  refine ⟨194611483406427664639858361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129740988937618443093238907 194611483406427664639858361)
  ·
    refine ⟨145958612554820748479893771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 194611483406427664639858361 145958612554820748479893771)
    ·
      refine ⟨218937918832231122719840657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145958612554820748479893771 218937918832231122719840657)
      ·
        refine ⟨164203439124173342039880493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 218937918832231122719840657 164203439124173342039880493)
        ·
          refine ⟨61576289671565003264955185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 164203439124173342039880493 61576289671565003264955185)
          ·
            refine ⟨46182217253673752448716389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61576289671565003264955185 46182217253673752448716389)
            ·
              refine ⟨8659165735063828584134323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 46182217253673752448716389 8659165735063828584134323)
              ·
                refine ⟨12988748602595742876201485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8659165735063828584134323 12988748602595742876201485)
                ·
                  refine ⟨4870780725973403578575557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12988748602595742876201485 4870780725973403578575557)
                  ·
                    refine ⟨913271386120013170982917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4870780725973403578575557 913271386120013170982917)
                    ·
                      rfl

theorem cell23_5335769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 4, 1, 3, 4].length) (baseStart_5335769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5335769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5335769 prefixEnd_5335769 := by exact prefixLift 5335769
  have htrace : WordTrace (prefixWord ++ tailWord_5335769) baseStart_5335769 baseEnd_5335769 := by
    simpa [prefixWord, tailWord_5335769, baseEnd_5335769] using wordTrace_append hprefix tailTrace_5335769
  have hstable : (prefixWord ++ tailWord_5335769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5335769).length < 2 ^ (prefixWord ++ tailWord_5335769).sum := by decide
  have hdescent : baseEnd_5335769 < baseStart_5335769 := by decide
  rcases family_descends (prefixWord ++ tailWord_5335769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5335779 : List Nat := [1, 1, 1, 7, 1, 1, 1, 2, 1, 4, 3]
def baseStart_5335779 : Nat := 118140960795 + 5335779 * 2 ^ 59
def prefixEnd_5335779 : Nat := 4983230072969 + 3 ^ 40 * 5335779 * 2
def baseEnd_5335779 : Nat := 2739819293166584473823705

theorem tailTrace_5335779 : CollatzResearch.WordTrace tailWord_5335779 prefixEnd_5335779 2739819293166584473823705 := by
  unfold tailWord_5335779
  simp only [CollatzResearch.WordTrace]
  refine ⟨194611848136391436347722391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129741232090927624231814927 194611848136391436347722391)
  ·
    refine ⟨291917772204587154521583587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194611848136391436347722391 291917772204587154521583587)
    ·
      refine ⟨437876658306880731782375381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 291917772204587154521583587 437876658306880731782375381)
      ·
        refine ⟨10262734179067517151149423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 437876658306880731782375381 10262734179067517151149423)
        ·
          refine ⟨15394101268601275726724135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10262734179067517151149423 15394101268601275726724135)
          ·
            refine ⟨23091151902901913590086203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15394101268601275726724135 23091151902901913590086203)
            ·
              refine ⟨34636727854352870385129305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23091151902901913590086203 34636727854352870385129305)
              ·
                refine ⟨25977545890764652788846979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34636727854352870385129305 25977545890764652788846979)
                ·
                  refine ⟨38966318836146979183270469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25977545890764652788846979 38966318836146979183270469)
                  ·
                    refine ⟨7306184781777558596863213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 38966318836146979183270469 7306184781777558596863213)
                    ·
                      refine ⟨2739819293166584473823705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7306184781777558596863213 2739819293166584473823705)
                      ·
                        rfl

theorem cell23_5335779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 1, 2, 1, 4, 3].length) (baseStart_5335779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5335779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5335779 prefixEnd_5335779 := by exact prefixLift 5335779
  have htrace : WordTrace (prefixWord ++ tailWord_5335779) baseStart_5335779 baseEnd_5335779 := by
    simpa [prefixWord, tailWord_5335779, baseEnd_5335779] using wordTrace_append hprefix tailTrace_5335779
  have hstable : (prefixWord ++ tailWord_5335779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5335779).length < 2 ^ (prefixWord ++ tailWord_5335779).sum := by decide
  have hdescent : baseEnd_5335779 < baseStart_5335779 := by decide
  rcases family_descends (prefixWord ++ tailWord_5335779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5335792 : List Nat := [2, 1, 1, 1, 3, 1, 3, 1, 2, 5, 3]
def baseStart_5335792 : Nat := 118140960795 + 5335792 * 2 ^ 59
def prefixEnd_5335792 : Nat := 4983230072969 + 3 ^ 40 * 5335792 * 2
def baseEnd_5335792 : Nat := 2739825968415092922961145

theorem tailTrace_5335792 : CollatzResearch.WordTrace tailWord_5335792 prefixEnd_5335792 2739825968415092922961145 := by
  unfold tailWord_5335792
  simp only [CollatzResearch.WordTrace]
  refine ⟨97306161142672169783972815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129741548190229559711963753 97306161142672169783972815)
  ·
    refine ⟨145959241714008254675959223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97306161142672169783972815 145959241714008254675959223)
    ·
      refine ⟨218938862571012382013938835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145959241714008254675959223 218938862571012382013938835)
      ·
        refine ⟨328408293856518573020908253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 218938862571012382013938835 328408293856518573020908253)
        ·
          refine ⟨123153110196194464882840595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 328408293856518573020908253 123153110196194464882840595)
          ·
            refine ⟨184729665294291697324260893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 123153110196194464882840595 184729665294291697324260893)
            ·
              refine ⟨69273624485359386496597835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 184729665294291697324260893 69273624485359386496597835)
              ·
                refine ⟨103910436728039079744896753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 69273624485359386496597835 103910436728039079744896753)
                ·
                  refine ⟨77932827546029309808672565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 103910436728039079744896753 77932827546029309808672565)
                  ·
                    refine ⟨7306202582440247794563053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 77932827546029309808672565 7306202582440247794563053)
                    ·
                      refine ⟨2739825968415092922961145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7306202582440247794563053 2739825968415092922961145)
                      ·
                        rfl

theorem cell23_5335792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 1, 2, 5, 3].length) (baseStart_5335792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5335792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5335792 prefixEnd_5335792 := by exact prefixLift 5335792
  have htrace : WordTrace (prefixWord ++ tailWord_5335792) baseStart_5335792 baseEnd_5335792 := by
    simpa [prefixWord, tailWord_5335792, baseEnd_5335792] using wordTrace_append hprefix tailTrace_5335792
  have hstable : (prefixWord ++ tailWord_5335792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5335792).length < 2 ^ (prefixWord ++ tailWord_5335792).sum := by decide
  have hdescent : baseEnd_5335792 < baseStart_5335792 := by decide
  rcases family_descends (prefixWord ++ tailWord_5335792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5335822 : List Nat := [4, 1, 1, 2, 1, 1, 1, 2, 2, 1, 7]
def baseStart_5335822 : Nat := 118140960795 + 5335822 * 2 ^ 59
def prefixEnd_5335822 : Nat := 4983230072969 + 3 ^ 40 * 5335822 * 2
def baseEnd_5335822 : Nat := 2739841372834727805586007

theorem tailTrace_5335822 : CollatzResearch.WordTrace tailWord_5335822 prefixEnd_5335822 2739841372834727805586007 := by
  unfold tailWord_5335822
  simp only [CollatzResearch.WordTrace]
  refine ⟨24326677059404456836442215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 129742277650157103127691813 24326677059404456836442215)
  ·
    refine ⟨36490015589106685254663323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24326677059404456836442215 36490015589106685254663323)
    ·
      refine ⟨54735023383660027881994985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36490015589106685254663323 54735023383660027881994985)
      ·
        refine ⟨41051267537745020911496239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54735023383660027881994985 41051267537745020911496239)
        ·
          refine ⟨61576901306617531367244359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41051267537745020911496239 61576901306617531367244359)
          ·
            refine ⟨92365351959926297050866539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61576901306617531367244359 92365351959926297050866539)
            ·
              refine ⟨138548027939889445576299809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 92365351959926297050866539 138548027939889445576299809)
              ·
                refine ⟨103911020954917084182224857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 138548027939889445576299809 103911020954917084182224857)
                ·
                  refine ⟨77933265716187813136668643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 103911020954917084182224857 77933265716187813136668643)
                  ·
                    refine ⟨116899898574281719705002965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 77933265716187813136668643 116899898574281719705002965)
                    ·
                      refine ⟨2739841372834727805586007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 116899898574281719705002965 2739841372834727805586007)
                      ·
                        rfl

theorem cell23_5335822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 2, 2, 1, 7].length) (baseStart_5335822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5335822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5335822 prefixEnd_5335822 := by exact prefixLift 5335822
  have htrace : WordTrace (prefixWord ++ tailWord_5335822) baseStart_5335822 baseEnd_5335822 := by
    simpa [prefixWord, tailWord_5335822, baseEnd_5335822] using wordTrace_append hprefix tailTrace_5335822
  have hstable : (prefixWord ++ tailWord_5335822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5335822).length < 2 ^ (prefixWord ++ tailWord_5335822).sum := by decide
  have hdescent : baseEnd_5335822 < baseStart_5335822 := by decide
  rcases family_descends (prefixWord ++ tailWord_5335822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5335832 : List Nat := [2, 1, 2, 3, 1, 1, 1, 1, 2, 5, 4]
def baseStart_5335832 : Nat := 118140960795 + 5335832 * 2 ^ 59
def prefixEnd_5335832 : Nat := 4983230072969 + 3 ^ 40 * 5335832 * 2
def baseEnd_5335832 : Nat := 2739846507641272766460961

theorem tailTrace_5335832 : CollatzResearch.WordTrace tailWord_5335832 prefixEnd_5335832 2739846507641272766460961 := by
  unfold tailWord_5335832
  simp only [CollatzResearch.WordTrace]
  refine ⟨97306890602599713199700875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129742520803466284266267833 97306890602599713199700875)
  ·
    refine ⟨145960335903899569799551313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97306890602599713199700875 145960335903899569799551313)
    ·
      refine ⟨109470251927924677349663485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 145960335903899569799551313 109470251927924677349663485)
      ·
        refine ⟨41051344472971754006123807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 109470251927924677349663485 41051344472971754006123807)
        ·
          refine ⟨61577016709457631009185711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41051344472971754006123807 61577016709457631009185711)
          ·
            refine ⟨92365525064186446513778567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61577016709457631009185711 92365525064186446513778567)
            ·
              refine ⟨138548287596279669770667851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 92365525064186446513778567 138548287596279669770667851)
              ·
                refine ⟨207822431394419504656001777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 138548287596279669770667851 207822431394419504656001777)
                ·
                  refine ⟨155866823545814628492001333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 207822431394419504656001777 155866823545814628492001333)
                  ·
                    refine ⟨14612514707420121421125125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 155866823545814628492001333 14612514707420121421125125)
                    ·
                      refine ⟨2739846507641272766460961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14612514707420121421125125 2739846507641272766460961)
                      ·
                        rfl

theorem cell23_5335832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 1, 2, 5, 4].length) (baseStart_5335832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5335832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5335832 prefixEnd_5335832 := by exact prefixLift 5335832
  have htrace : WordTrace (prefixWord ++ tailWord_5335832) baseStart_5335832 baseEnd_5335832 := by
    simpa [prefixWord, tailWord_5335832, baseEnd_5335832] using wordTrace_append hprefix tailTrace_5335832
  have hstable : (prefixWord ++ tailWord_5335832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5335832).length < 2 ^ (prefixWord ++ tailWord_5335832).sum := by decide
  have hdescent : baseEnd_5335832 < baseStart_5335832 := by decide
  rcases family_descends (prefixWord ++ tailWord_5335832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5335859 : List Nat := [1, 1, 1, 2, 6, 2, 1, 2, 1, 6]
def baseStart_5335859 : Nat := 118140960795 + 5335859 * 2 ^ 59
def prefixEnd_5335859 : Nat := 4983230072969 + 3 ^ 40 * 5335859 * 2
def baseEnd_5335859 : Nat := 913286790539648053607779

theorem tailTrace_5335859 : CollatzResearch.WordTrace tailWord_5335859 prefixEnd_5335859 913286790539648053607779 := by
  unfold tailWord_5335859
  simp only [CollatzResearch.WordTrace]
  refine ⟨194614765976101610010634631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129743177317401073340423087 194614765976101610010634631)
  ·
    refine ⟨291922148964152415015951947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194614765976101610010634631 291922148964152415015951947)
    ·
      refine ⟨437883223446228622523927921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 291922148964152415015951947 437883223446228622523927921)
      ·
        refine ⟨328412417584671466892945941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 437883223446228622523927921 328412417584671466892945941)
        ·
          refine ⟨15394332074281475010606841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 328412417584671466892945941 15394332074281475010606841)
          ·
            refine ⟨11545749055711106257955131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15394332074281475010606841 11545749055711106257955131)
            ·
              refine ⟨17318623583566659386932697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11545749055711106257955131 17318623583566659386932697)
              ·
                refine ⟨12988967687674994540199523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17318623583566659386932697 12988967687674994540199523)
                ·
                  refine ⟨19483451531512491810299285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12988967687674994540199523 19483451531512491810299285)
                  ·
                    refine ⟨913286790539648053607779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19483451531512491810299285 913286790539648053607779)
                    ·
                      rfl

theorem cell23_5335859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 1, 2, 1, 6].length) (baseStart_5335859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5335859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5335859 prefixEnd_5335859 := by exact prefixLift 5335859
  have htrace : WordTrace (prefixWord ++ tailWord_5335859) baseStart_5335859 baseEnd_5335859 := by
    simpa [prefixWord, tailWord_5335859, baseEnd_5335859] using wordTrace_append hprefix tailTrace_5335859
  have hstable : (prefixWord ++ tailWord_5335859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5335859).length < 2 ^ (prefixWord ++ tailWord_5335859).sum := by decide
  have hdescent : baseEnd_5335859 < baseStart_5335859 := by decide
  rcases family_descends (prefixWord ++ tailWord_5335859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5335882 : List Nat := [3, 1, 2, 1, 1, 1, 2, 1, 2, 2, 7]
def baseStart_5335882 : Nat := 118140960795 + 5335882 * 2 ^ 59
def prefixEnd_5335882 : Nat := 4983230072969 + 3 ^ 40 * 5335882 * 2
def baseEnd_5335882 : Nat := 2739872181673997570835731

theorem tailTrace_5335882 : CollatzResearch.WordTrace tailWord_5335882 prefixEnd_5335882 2739872181673997570835731 := by
  unfold tailWord_5335882
  simp only [CollatzResearch.WordTrace]
  refine ⟨48653901213754571234680475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129743736570012189959147933 48653901213754571234680475)
  ·
    refine ⟨72980851820631856852020713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48653901213754571234680475 72980851820631856852020713)
    ·
      refine ⟨54735638865473892639015535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72980851820631856852020713 54735638865473892639015535)
      ·
        refine ⟨82103458298210838958523303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54735638865473892639015535 82103458298210838958523303)
        ·
          refine ⟨123155187447316258437784955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82103458298210838958523303 123155187447316258437784955)
          ·
            refine ⟨184732781170974387656677433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 123155187447316258437784955 184732781170974387656677433)
            ·
              refine ⟨138549585878230790742508075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 184732781170974387656677433 138549585878230790742508075)
              ·
                refine ⟨207824378817346186113762113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 138549585878230790742508075 207824378817346186113762113)
                ·
                  refine ⟨155868284113009639585321585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 207824378817346186113762113 155868284113009639585321585)
                  ·
                    refine ⟨116901213084757229688991189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 155868284113009639585321585 116901213084757229688991189)
                    ·
                      refine ⟨2739872181673997570835731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 116901213084757229688991189 2739872181673997570835731)
                      ·
                        rfl

theorem cell23_5335882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 1, 2, 2, 7].length) (baseStart_5335882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5335882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5335882 prefixEnd_5335882 := by exact prefixLift 5335882
  have htrace : WordTrace (prefixWord ++ tailWord_5335882) baseStart_5335882 baseEnd_5335882 := by
    simpa [prefixWord, tailWord_5335882, baseEnd_5335882] using wordTrace_append hprefix tailTrace_5335882
  have hstable : (prefixWord ++ tailWord_5335882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5335882).length < 2 ^ (prefixWord ++ tailWord_5335882).sum := by decide
  have hdescent : baseEnd_5335882 < baseStart_5335882 := by decide
  rcases family_descends (prefixWord ++ tailWord_5335882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5335900 : List Nat := [2, 2, 4, 2, 1, 2, 1, 2, 3, 2, 2]
def baseStart_5335900 : Nat := 118140960795 + 5335900 * 2 ^ 59
def prefixEnd_5335900 : Nat := 4983230072969 + 3 ^ 40 * 5335900 * 2
def baseEnd_5335900 : Nat := 2739881424325778500410649

theorem tailTrace_5335900 : CollatzResearch.WordTrace tailWord_5335900 prefixEnd_5335900 2739881424325778500410649 := by
  unfold tailWord_5335900
  simp only [CollatzResearch.WordTrace]
  refine ⟨97308130684476537006438577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129744174245968716008584769 97308130684476537006438577)
  ·
    refine ⟨72981098013357402754828933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97308130684476537006438577 72981098013357402754828933)
    ·
      refine ⟨13683955877504513016530425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 72981098013357402754828933 13683955877504513016530425)
      ·
        refine ⟨10262966908128384762397819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13683955877504513016530425 10262966908128384762397819)
        ·
          refine ⟨15394450362192577143596729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10262966908128384762397819 15394450362192577143596729)
          ·
            refine ⟨11545837771644432857697547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15394450362192577143596729 11545837771644432857697547)
            ·
              refine ⟨17318756657466649286546321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11545837771644432857697547 17318756657466649286546321)
              ·
                refine ⟨12989067493099986964909741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17318756657466649286546321 12989067493099986964909741)
                ·
                  refine ⟨4870900309912495111841153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12989067493099986964909741 4870900309912495111841153)
                  ·
                    refine ⟨3653175232434371333880865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4870900309912495111841153 3653175232434371333880865)
                    ·
                      refine ⟨2739881424325778500410649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3653175232434371333880865 2739881424325778500410649)
                      ·
                        rfl

theorem cell23_5335900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 1, 2, 3, 2, 2].length) (baseStart_5335900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5335900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5335900 prefixEnd_5335900 := by exact prefixLift 5335900
  have htrace : WordTrace (prefixWord ++ tailWord_5335900) baseStart_5335900 baseEnd_5335900 := by
    simpa [prefixWord, tailWord_5335900, baseEnd_5335900] using wordTrace_append hprefix tailTrace_5335900
  have hstable : (prefixWord ++ tailWord_5335900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5335900).length < 2 ^ (prefixWord ++ tailWord_5335900).sum := by decide
  have hdescent : baseEnd_5335900 < baseStart_5335900 := by decide
  rcases family_descends (prefixWord ++ tailWord_5335900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5335916 : List Nat := [2, 2, 1, 1, 4, 1, 2, 2, 4, 1, 3]
def baseStart_5335916 : Nat := 118140960795 + 5335916 * 2 ^ 59
def prefixEnd_5335916 : Nat := 4983230072969 + 3 ^ 40 * 5335916 * 2
def baseEnd_5335916 : Nat := 2739889640016250437810575

theorem tailTrace_5335916 : CollatzResearch.WordTrace tailWord_5335916 prefixEnd_5335916 2739889640016250437810575 := by
  unfold tailWord_5335916
  simp only [CollatzResearch.WordTrace]
  refine ⟨97308422468447554372729801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129744563291263405830306401 97308422468447554372729801)
  ·
    refine ⟨72981316851335665779547351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97308422468447554372729801 72981316851335665779547351)
    ·
      refine ⟨109471975277003498669321027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72981316851335665779547351 109471975277003498669321027)
      ·
        refine ⟨164207962915505248003981541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109471975277003498669321027 164207962915505248003981541)
        ·
          refine ⟨30788993046657234000746539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 164207962915505248003981541 30788993046657234000746539)
          ·
            refine ⟨46183489569985851001119809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30788993046657234000746539 46183489569985851001119809)
            ·
              refine ⟨34637617177489388250839857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46183489569985851001119809 34637617177489388250839857)
              ·
                refine ⟨25978212883117041188129893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34637617177489388250839857 25978212883117041188129893)
                ·
                  refine ⟨4870914915584445222774355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25978212883117041188129893 4870914915584445222774355)
                  ·
                    refine ⟨7306372373376667834161533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4870914915584445222774355 7306372373376667834161533)
                    ·
                      refine ⟨2739889640016250437810575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7306372373376667834161533 2739889640016250437810575)
                      ·
                        rfl

theorem cell23_5335916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 4, 1, 3].length) (baseStart_5335916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5335916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5335916 prefixEnd_5335916 := by exact prefixLift 5335916
  have htrace : WordTrace (prefixWord ++ tailWord_5335916) baseStart_5335916 baseEnd_5335916 := by
    simpa [prefixWord, tailWord_5335916, baseEnd_5335916] using wordTrace_append hprefix tailTrace_5335916
  have hstable : (prefixWord ++ tailWord_5335916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5335916).length < 2 ^ (prefixWord ++ tailWord_5335916).sum := by decide
  have hdescent : baseEnd_5335916 < baseStart_5335916 := by decide
  rcases family_descends (prefixWord ++ tailWord_5335916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5335933 : List Nat := [1, 4, 1, 1, 2, 1, 5, 2, 2, 1, 3]
def baseStart_5335933 : Nat := 118140960795 + 5335933 * 2 ^ 59
def prefixEnd_5335933 : Nat := 4983230072969 + 3 ^ 40 * 5335933 * 2
def baseEnd_5335933 : Nat := 2739898369187376871297997

theorem tailTrace_5335933 : CollatzResearch.WordTrace tailWord_5335933 prefixEnd_5335933 2739898369187376871297997 := by
  unfold tailWord_5335933
  simp only [CollatzResearch.WordTrace]
  refine ⟨194617464977833520648828453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129744976651889013765885635 194617464977833520648828453)
  ·
    refine ⟨36490774683343785121655335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 194617464977833520648828453 36490774683343785121655335)
    ·
      refine ⟨54736162025015677682483003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36490774683343785121655335 54736162025015677682483003)
      ·
        refine ⟨82104243037523516523724505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54736162025015677682483003 82104243037523516523724505)
        ·
          refine ⟨61578182278142637392793379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82104243037523516523724505 61578182278142637392793379)
          ·
            refine ⟨92367273417213956089190069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61578182278142637392793379 92367273417213956089190069)
            ·
              refine ⟨8659431882863808383361569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 92367273417213956089190069 8659431882863808383361569)
              ·
                refine ⟨6494573912147856287521177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8659431882863808383361569 6494573912147856287521177)
                ·
                  refine ⟨4870930434110892215640883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6494573912147856287521177 4870930434110892215640883)
                  ·
                    refine ⟨7306395651166338323461325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4870930434110892215640883 7306395651166338323461325)
                    ·
                      refine ⟨2739898369187376871297997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7306395651166338323461325 2739898369187376871297997)
                      ·
                        rfl

theorem cell23_5335933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 5, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 5, 2, 2, 1, 3].length) (baseStart_5335933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5335933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5335933 prefixEnd_5335933 := by exact prefixLift 5335933
  have htrace : WordTrace (prefixWord ++ tailWord_5335933) baseStart_5335933 baseEnd_5335933 := by
    simpa [prefixWord, tailWord_5335933, baseEnd_5335933] using wordTrace_append hprefix tailTrace_5335933
  have hstable : (prefixWord ++ tailWord_5335933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5335933).length < 2 ^ (prefixWord ++ tailWord_5335933).sum := by decide
  have hdescent : baseEnd_5335933 < baseStart_5335933 := by decide
  rcases family_descends (prefixWord ++ tailWord_5335933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5335959 : List Nat := [1, 1, 3, 3, 1, 2, 2, 2, 2, 1, 5]
def baseStart_5335959 : Nat := 118140960795 + 5335959 * 2 ^ 59
def prefixEnd_5335959 : Nat := 4983230072969 + 3 ^ 40 * 5335959 * 2
def baseEnd_5335959 : Nat := 2739911719684393769572877

theorem tailTrace_5335959 : CollatzResearch.WordTrace tailWord_5335959 prefixEnd_5335959 2739911719684393769572877 := by
  unfold tailWord_5335959
  simp only [CollatzResearch.WordTrace]
  refine ⟨194618413275739327089274931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129745608850492884726183287 194618413275739327089274931)
  ·
    refine ⟨291927619913608990633912397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194618413275739327089274931 291927619913608990633912397)
    ·
      refine ⟨109472857467603371487717149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 291927619913608990633912397 109472857467603371487717149)
      ·
        refine ⟨41052321550351264307893931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 109472857467603371487717149 41052321550351264307893931)
        ·
          refine ⟨61578482325526896461840897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41052321550351264307893931 61578482325526896461840897)
          ·
            refine ⟨46183861744145172346380673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61578482325526896461840897 46183861744145172346380673)
            ·
              refine ⟨34637896308108879259785505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46183861744145172346380673 34637896308108879259785505)
              ·
                refine ⟨25978422231081659444839129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34637896308108879259785505 25978422231081659444839129)
                ·
                  refine ⟨19483816673311244583629347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25978422231081659444839129 19483816673311244583629347)
                  ·
                    refine ⟨29225725009966866875444021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19483816673311244583629347 29225725009966866875444021)
                    ·
                      refine ⟨2739911719684393769572877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29225725009966866875444021 2739911719684393769572877)
                      ·
                        rfl

theorem cell23_5335959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 2, 2, 2, 1, 5].length) (baseStart_5335959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5335959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5335959 prefixEnd_5335959 := by exact prefixLift 5335959
  have htrace : WordTrace (prefixWord ++ tailWord_5335959) baseStart_5335959 baseEnd_5335959 := by
    simpa [prefixWord, tailWord_5335959, baseEnd_5335959] using wordTrace_append hprefix tailTrace_5335959
  have hstable : (prefixWord ++ tailWord_5335959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5335959).length < 2 ^ (prefixWord ++ tailWord_5335959).sum := by decide
  have hdescent : baseEnd_5335959 < baseStart_5335959 := by decide
  rcases family_descends (prefixWord ++ tailWord_5335959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5335989 : List Nat := [1, 3, 3, 2, 1, 1, 1, 1, 1, 2, 7]
def baseStart_5335989 : Nat := 118140960795 + 5335989 * 2 ^ 59
def prefixEnd_5335989 : Nat := 4983230072969 + 3 ^ 40 * 5335989 * 2
def baseEnd_5335989 : Nat := 2739927124104028652197739

theorem tailTrace_5335989 : CollatzResearch.WordTrace tailWord_5335989 prefixEnd_5335989 2739927124104028652197739 := by
  unfold tailWord_5335989
  simp only [CollatzResearch.WordTrace]
  refine ⟨194619507465630642212867021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129746338310420428141911347 194619507465630642212867021)
  ·
    refine ⟨72982315299611490829825133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 194619507465630642212867021 72982315299611490829825133)
    ·
      refine ⟨27368368237354309061184425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72982315299611490829825133 27368368237354309061184425)
      ·
        refine ⟨20526276178015731795888319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27368368237354309061184425 20526276178015731795888319)
        ·
          refine ⟨30789414267023597693832479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20526276178015731795888319 30789414267023597693832479)
          ·
            refine ⟨46184121400535396540748719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30789414267023597693832479 46184121400535396540748719)
            ·
              refine ⟨69276182100803094811123079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46184121400535396540748719 69276182100803094811123079)
              ·
                refine ⟨103914273151204642216684619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 69276182100803094811123079 103914273151204642216684619)
                ·
                  refine ⟨155871409726806963325026929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 103914273151204642216684619 155871409726806963325026929)
                  ·
                    refine ⟨116903557295105222493770197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 155871409726806963325026929 116903557295105222493770197)
                    ·
                      refine ⟨2739927124104028652197739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 116903557295105222493770197 2739927124104028652197739)
                      ·
                        rfl

theorem cell23_5335989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 1, 1, 2, 7].length) (baseStart_5335989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5335989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5335989 prefixEnd_5335989 := by exact prefixLift 5335989
  have htrace : WordTrace (prefixWord ++ tailWord_5335989) baseStart_5335989 baseEnd_5335989 := by
    simpa [prefixWord, tailWord_5335989, baseEnd_5335989] using wordTrace_append hprefix tailTrace_5335989
  have hstable : (prefixWord ++ tailWord_5335989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5335989).length < 2 ^ (prefixWord ++ tailWord_5335989).sum := by decide
  have hdescent : baseEnd_5335989 < baseStart_5335989 := by decide
  rcases family_descends (prefixWord ++ tailWord_5335989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5336026 : List Nat := [3, 1, 1, 2, 4, 1, 1, 3, 2, 5]
def baseStart_5336026 : Nat := 118140960795 + 5336026 * 2 ^ 59
def prefixEnd_5336026 : Nat := 4983230072969 + 3 ^ 40 * 5336026 * 2
def baseEnd_5336026 : Nat := 913315374296081669145023

theorem tailTrace_5336026 : CollatzResearch.WordTrace tailWord_5336026 prefixEnd_5336026 913315374296081669145023 := by
  unfold tailWord_5336026
  simp only [CollatzResearch.WordTrace]
  refine ⟨48655214241624149382990983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129747237977664398354642621 48655214241624149382990983)
  ·
    refine ⟨72982821362436224074486475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48655214241624149382990983 72982821362436224074486475)
    ·
      refine ⟨109474232043654336111729713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72982821362436224074486475 109474232043654336111729713)
      ·
        refine ⟨82105674032740752083797285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 109474232043654336111729713 82105674032740752083797285)
        ·
          refine ⟨15394813881138891015711991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 82105674032740752083797285 15394813881138891015711991)
          ·
            refine ⟨23092220821708336523567987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15394813881138891015711991 23092220821708336523567987)
            ·
              refine ⟨34638331232562504785351981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23092220821708336523567987 34638331232562504785351981)
              ·
                refine ⟨12989374212210939294506993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34638331232562504785351981 12989374212210939294506993)
                ·
                  refine ⟨9742030659158204470880245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12989374212210939294506993 9742030659158204470880245)
                  ·
                    refine ⟨913315374296081669145023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9742030659158204470880245 913315374296081669145023)
                    ·
                      rfl

theorem cell23_5336026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 1, 3, 2, 5].length) (baseStart_5336026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5336026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5336026 prefixEnd_5336026 := by exact prefixLift 5336026
  have htrace : WordTrace (prefixWord ++ tailWord_5336026) baseStart_5336026 baseEnd_5336026 := by
    simpa [prefixWord, tailWord_5336026, baseEnd_5336026] using wordTrace_append hprefix tailTrace_5336026
  have hstable : (prefixWord ++ tailWord_5336026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5336026).length < 2 ^ (prefixWord ++ tailWord_5336026).sum := by decide
  have hdescent : baseEnd_5336026 < baseStart_5336026 := by decide
  rcases family_descends (prefixWord ++ tailWord_5336026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5336056 : List Nat := [2, 1, 2, 1, 1, 3, 1, 5, 3, 4]
def baseStart_5336056 : Nat := 118140960795 + 5336056 * 2 ^ 59
def prefixEnd_5336056 : Nat := 4983230072969 + 3 ^ 40 * 5336056 * 2
def baseEnd_5336056 : Nat := 913320509102626630019977

theorem tailTrace_5336056 : CollatzResearch.WordTrace tailWord_5336056 prefixEnd_5336056 913320509102626630019977 := by
  unfold tailWord_5336056
  simp only [CollatzResearch.WordTrace]
  refine ⟨97310975578193956327778011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129747967437591941770370681 97310975578193956327778011)
  ·
    refine ⟨145966463367290934491667017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97310975578193956327778011 145966463367290934491667017)
    ·
      refine ⟨109474847525468200868750263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 145966463367290934491667017 109474847525468200868750263)
      ·
        refine ⟨164212271288202301303125395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109474847525468200868750263 164212271288202301303125395)
        ·
          refine ⟨246318406932303451954688093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 164212271288202301303125395 246318406932303451954688093)
          ·
            refine ⟨92369402599613794483008035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 246318406932303451954688093 92369402599613794483008035)
            ·
              refine ⟨138554103899420691724512053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 92369402599613794483008035 138554103899420691724512053)
              ·
                refine ⟨12989447240570689849173005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 138554103899420691724512053 12989447240570689849173005)
                ·
                  refine ⟨4871042715214008693439877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12989447240570689849173005 4871042715214008693439877)
                  ·
                    refine ⟨913320509102626630019977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4871042715214008693439877 913320509102626630019977)
                    ·
                      rfl

theorem cell23_5336056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 5, 3, 4].length) (baseStart_5336056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5336056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5336056 prefixEnd_5336056 := by exact prefixLift 5336056
  have htrace : WordTrace (prefixWord ++ tailWord_5336056) baseStart_5336056 baseEnd_5336056 := by
    simpa [prefixWord, tailWord_5336056, baseEnd_5336056] using wordTrace_append hprefix tailTrace_5336056
  have hstable : (prefixWord ++ tailWord_5336056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5336056).length < 2 ^ (prefixWord ++ tailWord_5336056).sum := by decide
  have hdescent : baseEnd_5336056 < baseStart_5336056 := by decide
  rcases family_descends (prefixWord ++ tailWord_5336056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5336059 : List Nat := [1, 1, 1, 1, 1, 3, 3, 2, 2, 4, 4]
def baseStart_5336059 : Nat := 118140960795 + 5336059 * 2 ^ 59
def prefixEnd_5336059 : Nat := 4983230072969 + 3 ^ 40 * 5336059 * 2
def baseEnd_5336059 : Nat := 2739963067749843378322417

theorem tailTrace_5336059 : CollatzResearch.WordTrace tailWord_5336059 prefixEnd_5336059 2739963067749843378322417 := by
  unfold tailWord_5336059
  simp only [CollatzResearch.WordTrace]
  refine ⟨194622060575377044167915231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129748040383584696111943487 194622060575377044167915231)
  ·
    refine ⟨291933090863065566251872847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194622060575377044167915231 291933090863065566251872847)
    ·
      refine ⟨437899636294598349377809271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 291933090863065566251872847 437899636294598349377809271)
      ·
        refine ⟨656849454441897524066713907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 437899636294598349377809271 656849454441897524066713907)
        ·
          refine ⟨985274181662846286100070861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 656849454441897524066713907 985274181662846286100070861)
          ·
            refine ⟨369477818123567357287526573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 985274181662846286100070861 369477818123567357287526573)
            ·
              refine ⟨138554181796337758982822465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 369477818123567357287526573 138554181796337758982822465)
              ·
                refine ⟨103915636347253319237116849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 138554181796337758982822465 103915636347253319237116849)
                ·
                  refine ⟨77936727260439989427837637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 103915636347253319237116849 77936727260439989427837637)
                  ·
                    refine ⟨14613136361332498017719557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 77936727260439989427837637 14613136361332498017719557)
                    ·
                      refine ⟨2739963067749843378322417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14613136361332498017719557 2739963067749843378322417)
                      ·
                        rfl

theorem cell23_5336059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 2, 2, 4, 4].length) (baseStart_5336059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5336059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5336059 prefixEnd_5336059 := by exact prefixLift 5336059
  have htrace : WordTrace (prefixWord ++ tailWord_5336059) baseStart_5336059 baseEnd_5336059 := by
    simpa [prefixWord, tailWord_5336059, baseEnd_5336059] using wordTrace_append hprefix tailTrace_5336059
  have hstable : (prefixWord ++ tailWord_5336059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5336059).length < 2 ^ (prefixWord ++ tailWord_5336059).sum := by decide
  have hdescent : baseEnd_5336059 < baseStart_5336059 := by decide
  rcases family_descends (prefixWord ++ tailWord_5336059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5336090 : List Nat := [3, 1, 1, 3, 1, 2, 4, 3, 1, 4]
def baseStart_5336090 : Nat := 118140960795 + 5336090 * 2 ^ 59
def prefixEnd_5336090 : Nat := 4983230072969 + 3 ^ 40 * 5336090 * 2
def baseEnd_5336090 : Nat := 913326328550044252344925

theorem tailTrace_5336090 : CollatzResearch.WordTrace tailWord_5336090 prefixEnd_5336090 913326328550044252344925 := by
  unfold tailWord_5336090
  simp only [CollatzResearch.WordTrace]
  refine ⟨48655797809566184115573431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129748794158843157641529149 48655797809566184115573431)
  ·
    refine ⟨72983696714349276173360147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48655797809566184115573431 72983696714349276173360147)
    ·
      refine ⟨109475545071523914260040221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72983696714349276173360147 109475545071523914260040221)
      ·
        refine ⟨41053329401821467847515083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 109475545071523914260040221 41053329401821467847515083)
        ·
          refine ⟨61579994102732201771272625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41053329401821467847515083 61579994102732201771272625)
          ·
            refine ⟨46184995577049151328454469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61579994102732201771272625 46184995577049151328454469)
            ·
              refine ⟨8659686670696715874085213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 46184995577049151328454469 8659686670696715874085213)
              ·
                refine ⟨3247382501511268452781955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8659686670696715874085213 3247382501511268452781955)
                ·
                  refine ⟨4871073752266902679172933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3247382501511268452781955 4871073752266902679172933)
                  ·
                    refine ⟨913326328550044252344925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4871073752266902679172933 913326328550044252344925)
                    ·
                      rfl

theorem cell23_5336090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 4, 3, 1, 4].length) (baseStart_5336090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5336090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5336090 prefixEnd_5336090 := by exact prefixLift 5336090
  have htrace : WordTrace (prefixWord ++ tailWord_5336090) baseStart_5336090 baseEnd_5336090 := by
    simpa [prefixWord, tailWord_5336090, baseEnd_5336090] using wordTrace_append hprefix tailTrace_5336090
  have hstable : (prefixWord ++ tailWord_5336090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5336090).length < 2 ^ (prefixWord ++ tailWord_5336090).sum := by decide
  have hdescent : baseEnd_5336090 < baseStart_5336090 := by decide
  rcases family_descends (prefixWord ++ tailWord_5336090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5336103 : List Nat := [1, 1, 7, 1, 1, 2, 1, 1, 8]
def baseStart_5336103 : Nat := 118140960795 + 5336103 * 2 ^ 59
def prefixEnd_5336103 : Nat := 4983230072969 + 3 ^ 40 * 5336103 * 2
def baseEnd_5336103 : Nat := 304442851210960134019135

theorem tailTrace_5336103 : CollatzResearch.WordTrace tailWord_5336103 prefixEnd_5336103 304442851210960134019135 := by
  unfold tailWord_5336103
  simp only [CollatzResearch.WordTrace]
  refine ⟨194623665387217639682516963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129749110258145093121677975 194623665387217639682516963)
  ·
    refine ⟨291935498080826459523775445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194623665387217639682516963 291935498080826459523775445)
    ·
      refine ⟨6842238236269370145088487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 291935498080826459523775445 6842238236269370145088487)
      ·
        refine ⟨10263357354404055217632731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6842238236269370145088487 10263357354404055217632731)
        ·
          refine ⟨15395036031606082826449097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10263357354404055217632731 15395036031606082826449097)
          ·
            refine ⟨11546277023704562119836823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15395036031606082826449097 11546277023704562119836823)
            ·
              refine ⟨17319415535556843179755235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11546277023704562119836823 17319415535556843179755235)
              ·
                refine ⟨25979123303335264769632853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17319415535556843179755235 25979123303335264769632853)
                ·
                  refine ⟨304442851210960134019135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 25979123303335264769632853 304442851210960134019135)
                  ·
                    rfl

theorem cell23_5336103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 1, 1, 8].length) (baseStart_5336103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5336103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5336103 prefixEnd_5336103 := by exact prefixLift 5336103
  have htrace : WordTrace (prefixWord ++ tailWord_5336103) baseStart_5336103 baseEnd_5336103 := by
    simpa [prefixWord, tailWord_5336103, baseEnd_5336103] using wordTrace_append hprefix tailTrace_5336103
  have hstable : (prefixWord ++ tailWord_5336103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5336103).length < 2 ^ (prefixWord ++ tailWord_5336103).sum := by decide
  have hdescent : baseEnd_5336103 < baseStart_5336103 := by decide
  rcases family_descends (prefixWord ++ tailWord_5336103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5336163 : List Nat := [1, 1, 1, 5, 1, 1, 1, 6, 2, 4]
def baseStart_5336163 : Nat := 118140960795 + 5336163 * 2 ^ 59
def prefixEnd_5336163 : Nat := 4983230072969 + 3 ^ 40 * 5336163 * 2
def baseEnd_5336163 : Nat := 913338823245970323807313

theorem tailTrace_5336163 : CollatzResearch.WordTrace tailWord_5336163 prefixEnd_5336163 913338823245970323807313 := by
  unfold tailWord_5336163
  simp only [CollatzResearch.WordTrace]
  refine ⟨194625853767000269929701143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129750569178000179953134095 194625853767000269929701143)
  ·
    refine ⟨291938780650500404894551715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194625853767000269929701143 291938780650500404894551715)
    ·
      refine ⟨437908170975750607341827573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 291938780650500404894551715 437908170975750607341827573)
      ·
        refine ⟨41053891028976619438296335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 437908170975750607341827573 41053891028976619438296335)
        ·
          refine ⟨61580836543464929157444503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41053891028976619438296335 61580836543464929157444503)
          ·
            refine ⟨92371254815197393736166755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61580836543464929157444503 92371254815197393736166755)
            ·
              refine ⟨138556882222796090604250133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 92371254815197393736166755 138556882222796090604250133)
              ·
                refine ⟨6494853854193566747074225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 138556882222796090604250133 6494853854193566747074225)
                ·
                  refine ⟨4871140390645175060305669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6494853854193566747074225 4871140390645175060305669)
                  ·
                    refine ⟨913338823245970323807313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4871140390645175060305669 913338823245970323807313)
                    ·
                      rfl

theorem cell23_5336163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 6, 2, 4].length) (baseStart_5336163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5336163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5336163 prefixEnd_5336163 := by exact prefixLift 5336163
  have htrace : WordTrace (prefixWord ++ tailWord_5336163) baseStart_5336163 baseEnd_5336163 := by
    simpa [prefixWord, tailWord_5336163, baseEnd_5336163] using wordTrace_append hprefix tailTrace_5336163
  have hstable : (prefixWord ++ tailWord_5336163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5336163).length < 2 ^ (prefixWord ++ tailWord_5336163).sum := by decide
  have hdescent : baseEnd_5336163 < baseStart_5336163 := by decide
  rcases family_descends (prefixWord ++ tailWord_5336163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5336173 : List Nat := [1, 5, 1, 1, 2, 2, 2, 2, 1, 1, 5]
def baseStart_5336173 : Nat := 118140960795 + 5336173 * 2 ^ 59
def prefixEnd_5336173 : Nat := 4983230072969 + 3 ^ 40 * 5336173 * 2
def baseEnd_5336173 : Nat := 2740021604544455932296893

theorem tailTrace_5336173 : CollatzResearch.WordTrace tailWord_5336173 prefixEnd_5336173 2740021604544455932296893 := by
  unfold tailWord_5336173
  simp only [CollatzResearch.WordTrace]
  refine ⟨194626218496964041637565173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129750812331309361091710115 194626218496964041637565173)
  ·
    refine ⟨18246207984090378903521735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 194626218496964041637565173 18246207984090378903521735)
    ·
      refine ⟨27369311976135568355282603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18246207984090378903521735 27369311976135568355282603)
      ·
        refine ⟨41053967964203352532923905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27369311976135568355282603 41053967964203352532923905)
        ·
          refine ⟨30790475973152514399692929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41053967964203352532923905 30790475973152514399692929)
          ·
            refine ⟨23092856979864385799769697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30790475973152514399692929 23092856979864385799769697)
            ·
              refine ⟨17319642734898289349827273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23092856979864385799769697 17319642734898289349827273)
              ·
                refine ⟨12989732051173717012370455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17319642734898289349827273 12989732051173717012370455)
                ·
                  refine ⟨19484598076760575518555683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12989732051173717012370455 19484598076760575518555683)
                  ·
                    refine ⟨29226897115140863277833525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19484598076760575518555683 29226897115140863277833525)
                    ·
                      refine ⟨2740021604544455932296893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29226897115140863277833525 2740021604544455932296893)
                      ·
                        rfl

theorem cell23_5336173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 2, 2, 1, 1, 5].length) (baseStart_5336173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5336173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5336173 prefixEnd_5336173 := by exact prefixLift 5336173
  have htrace : WordTrace (prefixWord ++ tailWord_5336173) baseStart_5336173 baseEnd_5336173 := by
    simpa [prefixWord, tailWord_5336173, baseEnd_5336173] using wordTrace_append hprefix tailTrace_5336173
  have hstable : (prefixWord ++ tailWord_5336173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5336173).length < 2 ^ (prefixWord ++ tailWord_5336173).sum := by decide
  have hdescent : baseEnd_5336173 < baseStart_5336173 := by decide
  rcases family_descends (prefixWord ++ tailWord_5336173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5336176 : List Nat := [2, 1, 1, 1, 5, 1, 4, 8]
def baseStart_5336176 : Nat := 118140960795 + 5336176 * 2 ^ 59
def prefixEnd_5336176 : Nat := 4983230072969 + 3 ^ 40 * 5336176 * 2
def baseEnd_5336176 : Nat := 101482338703200719279977

theorem tailTrace_5336176 : CollatzResearch.WordTrace tailWord_5336176 prefixEnd_5336176 101482338703200719279977 := by
  unfold tailWord_5336176
  simp only [CollatzResearch.WordTrace]
  refine ⟨97313163957976586574962191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129750885277302115433282921 97313163957976586574962191)
  ·
    refine ⟨145969745936964879862443287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97313163957976586574962191 145969745936964879862443287)
    ·
      refine ⟨218954618905447319793664931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145969745936964879862443287 218954618905447319793664931)
      ·
        refine ⟨328431928358170979690497397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 218954618905447319793664931 328431928358170979690497397)
        ·
          refine ⟨30790493283578529345984131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 328431928358170979690497397 30790493283578529345984131)
          ·
            refine ⟨46185739925367794018976197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30790493283578529345984131 46185739925367794018976197)
            ·
              refine ⟨8659826236006461378558037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 46185739925367794018976197 8659826236006461378558037)
              ·
                refine ⟨101482338703200719279977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8659826236006461378558037 101482338703200719279977)
                ·
                  rfl

theorem cell23_5336176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 4, 8].length) (baseStart_5336176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5336176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5336176 prefixEnd_5336176 := by exact prefixLift 5336176
  have htrace : WordTrace (prefixWord ++ tailWord_5336176) baseStart_5336176 baseEnd_5336176 := by
    simpa [prefixWord, tailWord_5336176, baseEnd_5336176] using wordTrace_append hprefix tailTrace_5336176
  have hstable : (prefixWord ++ tailWord_5336176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5336176).length < 2 ^ (prefixWord ++ tailWord_5336176).sum := by decide
  have hdescent : baseEnd_5336176 < baseStart_5336176 := by decide
  rcases family_descends (prefixWord ++ tailWord_5336176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5336200 : List Nat := [2, 1, 3, 4, 2, 1, 1, 2, 1, 2, 4]
def baseStart_5336200 : Nat := 118140960795 + 5336200 * 2 ^ 59
def prefixEnd_5336200 : Nat := 4983230072969 + 3 ^ 40 * 5336200 * 2
def baseEnd_5336200 : Nat := 2740035468522127326659269

theorem tailTrace_5336200 : CollatzResearch.WordTrace tailWord_5336200 prefixEnd_5336200 2740035468522127326659269 := by
  unfold tailWord_5336200
  simp only [CollatzResearch.WordTrace]
  refine ⟨97313601633933112624399027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129751468845244150165865369 97313601633933112624399027)
  ·
    refine ⟨145970402450899668936598541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97313601633933112624399027 145970402450899668936598541)
    ·
      refine ⟨54738900919087375851224453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 145970402450899668936598541 54738900919087375851224453)
      ·
        refine ⟨10263543922328882972104585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 54738900919087375851224453 10263543922328882972104585)
        ·
          refine ⟨7697657941746662229078439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10263543922328882972104585 7697657941746662229078439)
          ·
            refine ⟨11546486912619993343617659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7697657941746662229078439 11546486912619993343617659)
            ·
              refine ⟨17319730368929990015426489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11546486912619993343617659 17319730368929990015426489)
              ·
                refine ⟨12989797776697492511569867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17319730368929990015426489 12989797776697492511569867)
                ·
                  refine ⟨19484696665046238767354801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12989797776697492511569867 19484696665046238767354801)
                  ·
                    refine ⟨14613522498784679075516101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19484696665046238767354801 14613522498784679075516101)
                    ·
                      refine ⟨2740035468522127326659269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14613522498784679075516101 2740035468522127326659269)
                      ·
                        rfl

theorem cell23_5336200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 1, 2, 1, 2, 4].length) (baseStart_5336200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5336200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5336200 prefixEnd_5336200 := by exact prefixLift 5336200
  have htrace : WordTrace (prefixWord ++ tailWord_5336200) baseStart_5336200 baseEnd_5336200 := by
    simpa [prefixWord, tailWord_5336200, baseEnd_5336200] using wordTrace_append hprefix tailTrace_5336200
  have hstable : (prefixWord ++ tailWord_5336200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5336200).length < 2 ^ (prefixWord ++ tailWord_5336200).sum := by decide
  have hdescent : baseEnd_5336200 < baseStart_5336200 := by decide
  rcases family_descends (prefixWord ++ tailWord_5336200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5336203 : List Nat := [1, 1, 1, 1, 4, 1, 1, 3, 6, 1, 3]
def baseStart_5336203 : Nat := 118140960795 + 5336203 * 2 ^ 59
def prefixEnd_5336203 : Nat := 4983230072969 + 3 ^ 40 * 5336203 * 2
def baseEnd_5336203 : Nat := 2740037008964090814921755

theorem tailTrace_5336203 : CollatzResearch.WordTrace tailWord_5336203 prefixEnd_5336203 2740037008964090814921755 := by
  unfold tailWord_5336203
  simp only [CollatzResearch.WordTrace]
  refine ⟨194627312686855356761157263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129751541791236904507438175 194627312686855356761157263)
  ·
    refine ⟨291940969030283035141735895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194627312686855356761157263 291940969030283035141735895)
    ·
      refine ⟨437911453545424552712603843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 291940969030283035141735895 437911453545424552712603843)
      ·
        refine ⟨656867180318136829068905765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 437911453545424552712603843 656867180318136829068905765)
        ·
          refine ⟨123162596309650655450419831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 656867180318136829068905765 123162596309650655450419831)
          ·
            refine ⟨184743894464475983175629747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 123162596309650655450419831 184743894464475983175629747)
            ·
              refine ⟨277115841696713974763444621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 184743894464475983175629747 277115841696713974763444621)
              ·
                refine ⟨103918440636267740536291733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 277115841696713974763444621 103918440636267740536291733)
                ·
                  refine ⟨4871176904825050337638675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 103918440636267740536291733 4871176904825050337638675)
                  ·
                    refine ⟨7306765357237575506458013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4871176904825050337638675 7306765357237575506458013)
                    ·
                      refine ⟨2740037008964090814921755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7306765357237575506458013 2740037008964090814921755)
                      ·
                        rfl

theorem cell23_5336203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 3, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 3, 6, 1, 3].length) (baseStart_5336203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5336203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5336203 prefixEnd_5336203 := by exact prefixLift 5336203
  have htrace : WordTrace (prefixWord ++ tailWord_5336203) baseStart_5336203 baseEnd_5336203 := by
    simpa [prefixWord, tailWord_5336203, baseEnd_5336203] using wordTrace_append hprefix tailTrace_5336203
  have hstable : (prefixWord ++ tailWord_5336203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5336203).length < 2 ^ (prefixWord ++ tailWord_5336203).sum := by decide
  have hdescent : baseEnd_5336203 < baseStart_5336203 := by decide
  rcases family_descends (prefixWord ++ tailWord_5336203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5336237 : List Nat := [1, 5, 2, 1, 3, 1, 2, 1, 1, 3, 3]
def baseStart_5336237 : Nat := 118140960795 + 5336237 * 2 ^ 59
def prefixEnd_5336237 : Nat := 4983230072969 + 3 ^ 40 * 5336237 * 2
def baseEnd_5336237 : Nat := 2740054467306343681896599

theorem tailTrace_5336237 : CollatzResearch.WordTrace tailWord_5336237 prefixEnd_5336237 2740054467306343681896599 := by
  unfold tailWord_5336237
  simp only [CollatzResearch.WordTrace]
  refine ⟨194628552768732180567894965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129752368512488120378596643 194628552768732180567894965)
  ·
    refine ⟨18246426822068641928240153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 194628552768732180567894965 18246426822068641928240153)
    ·
      refine ⟨13684820116551481446180115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18246426822068641928240153 13684820116551481446180115)
      ·
        refine ⟨20527230174827222169270173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13684820116551481446180115 20527230174827222169270173)
        ·
          refine ⟨7697711315560208313476315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20527230174827222169270173 7697711315560208313476315)
          ·
            refine ⟨11546566973340312470214473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7697711315560208313476315 11546566973340312470214473)
            ·
              refine ⟨8659925230005234352660855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11546566973340312470214473 8659925230005234352660855)
              ·
                refine ⟨12989887845007851528991283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8659925230005234352660855 12989887845007851528991283)
                ·
                  refine ⟨19484831767511777293486925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12989887845007851528991283 19484831767511777293486925)
                  ·
                    refine ⟨7306811912816916485057597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19484831767511777293486925 7306811912816916485057597)
                    ·
                      refine ⟨2740054467306343681896599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7306811912816916485057597 2740054467306343681896599)
                      ·
                        rfl

theorem cell23_5336237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 2, 1, 1, 3, 3].length) (baseStart_5336237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5336237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5336237 prefixEnd_5336237 := by exact prefixLift 5336237
  have htrace : WordTrace (prefixWord ++ tailWord_5336237) baseStart_5336237 baseEnd_5336237 := by
    simpa [prefixWord, tailWord_5336237, baseEnd_5336237] using wordTrace_append hprefix tailTrace_5336237
  have hstable : (prefixWord ++ tailWord_5336237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5336237).length < 2 ^ (prefixWord ++ tailWord_5336237).sum := by decide
  have hdescent : baseEnd_5336237 < baseStart_5336237 := by decide
  rcases family_descends (prefixWord ++ tailWord_5336237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5336258 : List Nat := [3, 5, 1, 1, 2, 2, 2, 1, 1, 2, 3]
def baseStart_5336258 : Nat := 118140960795 + 5336258 * 2 ^ 59
def prefixEnd_5336258 : Nat := 4983230072969 + 3 ^ 40 * 5336258 * 2
def baseEnd_5336258 : Nat := 2740065250400088099734003

theorem tailTrace_5336258 : CollatzResearch.WordTrace tailWord_5336258 prefixEnd_5336258 2740065250400088099734003 := by
  unfold tailWord_5336258
  simp only [CollatzResearch.WordTrace]
  refine ⟨48657329675414025288602357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129752879134437400769606285 48657329675414025288602357)
  ·
    refine ⟨4561624657070064870806471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 48657329675414025288602357 4561624657070064870806471)
    ·
      refine ⟨6842436985605097306209707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4561624657070064870806471 6842436985605097306209707)
      ·
        refine ⟨10263655478407645959314561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6842436985605097306209707 10263655478407645959314561)
        ·
          refine ⟨7697741608805734469485921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10263655478407645959314561 7697741608805734469485921)
          ·
            refine ⟨5773306206604300852114441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7697741608805734469485921 5773306206604300852114441)
            ·
              refine ⟨4329979654953225639085831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5773306206604300852114441 4329979654953225639085831)
              ·
                refine ⟨6494969482429838458628747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4329979654953225639085831 6494969482429838458628747)
                ·
                  refine ⟨9742454223644757687943121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6494969482429838458628747 9742454223644757687943121)
                  ·
                    refine ⟨7306840667733568265957341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9742454223644757687943121 7306840667733568265957341)
                    ·
                      refine ⟨2740065250400088099734003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7306840667733568265957341 2740065250400088099734003)
                      ·
                        rfl

theorem cell23_5336258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 2, 2, 1, 1, 2, 3].length) (baseStart_5336258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5336258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5336258 prefixEnd_5336258 := by exact prefixLift 5336258
  have htrace : WordTrace (prefixWord ++ tailWord_5336258) baseStart_5336258 baseEnd_5336258 := by
    simpa [prefixWord, tailWord_5336258, baseEnd_5336258] using wordTrace_append hprefix tailTrace_5336258
  have hstable : (prefixWord ++ tailWord_5336258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5336258).length < 2 ^ (prefixWord ++ tailWord_5336258).sum := by decide
  have hdescent : baseEnd_5336258 < baseStart_5336258 := by decide
  rcases family_descends (prefixWord ++ tailWord_5336258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5336313 : List Nat := [1, 2, 1, 3, 1, 1, 4, 3, 2, 5]
def baseStart_5336313 : Nat := 118140960795 + 5336313 * 2 ^ 59
def prefixEnd_5336313 : Nat := 4983230072969 + 3 ^ 40 * 5336313 * 2
def baseEnd_5336313 : Nat := 913364497278695128182083

theorem tailTrace_5336313 : CollatzResearch.WordTrace tailWord_5336313 prefixEnd_5336313 913364497278695128182083 := by
  unfold tailWord_5336313
  simp only [CollatzResearch.WordTrace]
  refine ⟨194631324716456845547661593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129754216477637897031774395 194631324716456845547661593)
  ·
    refine ⟨145973493537342634160746195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 194631324716456845547661593 145973493537342634160746195)
    ·
      refine ⟨218960240306013951241119293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145973493537342634160746195 218960240306013951241119293)
      ·
        refine ⟨82110090114755231715419735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 218960240306013951241119293 82110090114755231715419735)
        ·
          refine ⟨123165135172132847573129603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82110090114755231715419735 123165135172132847573129603)
          ·
            refine ⟨184747702758199271359694405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 123165135172132847573129603 184747702758199271359694405)
            ·
              refine ⟨34640194267162363379942701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 184747702758199271359694405 34640194267162363379942701)
              ·
                refine ⟨12990072850185886267478513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34640194267162363379942701 12990072850185886267478513)
                ·
                  refine ⟨9742554637639414700608885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12990072850185886267478513 9742554637639414700608885)
                  ·
                    refine ⟨913364497278695128182083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9742554637639414700608885 913364497278695128182083)
                    ·
                      rfl

theorem cell23_5336313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 4, 3, 2, 5].length) (baseStart_5336313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5336313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5336313 prefixEnd_5336313 := by exact prefixLift 5336313
  have htrace : WordTrace (prefixWord ++ tailWord_5336313) baseStart_5336313 baseEnd_5336313 := by
    simpa [prefixWord, tailWord_5336313, baseEnd_5336313] using wordTrace_append hprefix tailTrace_5336313
  have hstable : (prefixWord ++ tailWord_5336313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5336313).length < 2 ^ (prefixWord ++ tailWord_5336313).sum := by decide
  have hdescent : baseEnd_5336313 < baseStart_5336313 := by decide
  rcases family_descends (prefixWord ++ tailWord_5336313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5336403 : List Nat := [1, 1, 1, 2, 1, 1, 5, 1, 5, 5]
def baseStart_5336403 : Nat := 118140960795 + 5336403 * 2 ^ 59
def prefixEnd_5336403 : Nat := 4983230072969 + 3 ^ 40 * 5336403 * 2
def baseEnd_5336403 : Nat := 913379901698330010806945

theorem tailTrace_5336403 : CollatzResearch.WordTrace tailWord_5336403 prefixEnd_5336403 913379901698330010806945 := by
  unfold tailWord_5336403
  simp only [CollatzResearch.WordTrace]
  refine ⟨194634607286130790918437863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129756404857420527278958575 194634607286130790918437863)
  ·
    refine ⟨291951910929196186377656795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194634607286130790918437863 291951910929196186377656795)
    ·
      refine ⟨437927866393794279566485193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 291951910929196186377656795 437927866393794279566485193)
      ·
        refine ⟨328445899795345709674863895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 437927866393794279566485193 328445899795345709674863895)
        ·
          refine ⟨492668849693018564512295843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 328445899795345709674863895 492668849693018564512295843)
          ·
            refine ⟨739003274539527846768443765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 492668849693018564512295843 739003274539527846768443765)
            ·
              refine ⟨69281556988080735634541603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 739003274539527846768443765 69281556988080735634541603)
              ·
                refine ⟨103922335482121103451812405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 69281556988080735634541603 103922335482121103451812405)
                ·
                  refine ⟨9742718951448853448607413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 103922335482121103451812405 9742718951448853448607413)
                  ·
                    refine ⟨913379901698330010806945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9742718951448853448607413 913379901698330010806945)
                    ·
                      rfl

theorem cell23_5336403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 1, 5, 5].length) (baseStart_5336403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5336403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5336403 prefixEnd_5336403 := by exact prefixLift 5336403
  have htrace : WordTrace (prefixWord ++ tailWord_5336403) baseStart_5336403 baseEnd_5336403 := by
    simpa [prefixWord, tailWord_5336403, baseEnd_5336403] using wordTrace_append hprefix tailTrace_5336403
  have hstable : (prefixWord ++ tailWord_5336403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5336403).length < 2 ^ (prefixWord ++ tailWord_5336403).sum := by decide
  have hdescent : baseEnd_5336403 < baseStart_5336403 := by decide
  rcases family_descends (prefixWord ++ tailWord_5336403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5336420 : List Nat := [2, 3, 1, 1, 3, 2, 2, 1, 3, 5]
def baseStart_5336420 : Nat := 118140960795 + 5336420 * 2 ^ 59
def prefixEnd_5336420 : Nat := 4983230072969 + 3 ^ 40 * 5336420 * 2
def baseEnd_5336420 : Nat := 913382811422038821969419

theorem tailTrace_5336420 : CollatzResearch.WordTrace tailWord_5336420 prefixEnd_5336420 913382811422038821969419 := by
  unfold tailWord_5336420
  simp only [CollatzResearch.WordTrace]
  refine ⟨97317613663534601410903357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129756818218046135214537809 97317613663534601410903357)
  ·
    refine ⟨36494105123825475529088759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 97317613663534601410903357 36494105123825475529088759)
    ·
      refine ⟨54741157685738213293633139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36494105123825475529088759 54741157685738213293633139)
      ·
        refine ⟨82111736528607319940449709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54741157685738213293633139 82111736528607319940449709)
        ·
          refine ⟨30791901198227744977668641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 82111736528607319940449709 30791901198227744977668641)
          ·
            refine ⟨23093925898670808733251481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30791901198227744977668641 23093925898670808733251481)
            ·
              refine ⟨17320444424003106549938611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23093925898670808733251481 17320444424003106549938611)
              ·
                refine ⟨25980666636004659824907917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17320444424003106549938611 25980666636004659824907917)
                ·
                  refine ⟨9742749988501747434340469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25980666636004659824907917 9742749988501747434340469)
                  ·
                    refine ⟨913382811422038821969419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9742749988501747434340469 913382811422038821969419)
                    ·
                      rfl

theorem cell23_5336420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 2, 1, 3, 5].length) (baseStart_5336420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5336420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5336420 prefixEnd_5336420 := by exact prefixLift 5336420
  have htrace : WordTrace (prefixWord ++ tailWord_5336420) baseStart_5336420 baseEnd_5336420 := by
    simpa [prefixWord, tailWord_5336420, baseEnd_5336420] using wordTrace_append hprefix tailTrace_5336420
  have hstable : (prefixWord ++ tailWord_5336420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5336420).length < 2 ^ (prefixWord ++ tailWord_5336420).sum := by decide
  have hdescent : baseEnd_5336420 < baseStart_5336420 := by decide
  rcases family_descends (prefixWord ++ tailWord_5336420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5336440 : List Nat := [2, 1, 2, 1, 1, 1, 1, 1, 3, 8, 2]
def baseStart_5336440 : Nat := 118140960795 + 5336440 * 2 ^ 59
def prefixEnd_5336440 : Nat := 4983230072969 + 3 ^ 40 * 5336440 * 2
def baseEnd_5336440 : Nat := 2740158703879206387658165

theorem tailTrace_5336440 : CollatzResearch.WordTrace tailWord_5336440 prefixEnd_5336440 2740158703879206387658165 := by
  unfold tailWord_5336440
  simp only [CollatzResearch.WordTrace]
  refine ⟨97317978393498373118767387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129757304524664497491689849 97317978393498373118767387)
  ·
    refine ⟨145976967590247559678151081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97317978393498373118767387 145976967590247559678151081)
    ·
      refine ⟨109482725692685669758613311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 145976967590247559678151081 109482725692685669758613311)
      ·
        refine ⟨164224088539028504637919967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109482725692685669758613311 164224088539028504637919967)
        ·
          refine ⟨246336132808542756956879951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 164224088539028504637919967 246336132808542756956879951)
          ·
            refine ⟨369504199212814135435319927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 246336132808542756956879951 369504199212814135435319927)
            ·
              refine ⟨554256298819221203152979891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 369504199212814135435319927 554256298819221203152979891)
              ·
                refine ⟨831384448228831804729469837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 554256298819221203152979891 831384448228831804729469837)
                ·
                  refine ⟨311769168085811926773551189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 831384448228831804729469837 311769168085811926773551189)
                  ·
                    refine ⟨3653544938505608516877553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 311769168085811926773551189 3653544938505608516877553)
                    ·
                      refine ⟨2740158703879206387658165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3653544938505608516877553 2740158703879206387658165)
                      ·
                        rfl

theorem cell23_5336440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 3, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 3, 8, 2].length) (baseStart_5336440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5336440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5336440 prefixEnd_5336440 := by exact prefixLift 5336440
  have htrace : WordTrace (prefixWord ++ tailWord_5336440) baseStart_5336440 baseEnd_5336440 := by
    simpa [prefixWord, tailWord_5336440, baseEnd_5336440] using wordTrace_append hprefix tailTrace_5336440
  have hstable : (prefixWord ++ tailWord_5336440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5336440).length < 2 ^ (prefixWord ++ tailWord_5336440).sum := by decide
  have hdescent : baseEnd_5336440 < baseStart_5336440 := by decide
  rcases family_descends (prefixWord ++ tailWord_5336440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5336460 : List Nat := [2, 2, 1, 2, 1, 3, 3, 2, 1, 1, 5]
def baseStart_5336460 : Nat := 118140960795 + 5336460 * 2 ^ 59
def prefixEnd_5336460 : Nat := 4983230072969 + 3 ^ 40 * 5336460 * 2
def baseEnd_5336460 : Nat := 2740168973492296309408073

theorem tailTrace_5336460 : CollatzResearch.WordTrace tailWord_5336460 prefixEnd_5336460 2740168973492296309408073 := by
  unfold tailWord_5336460
  simp only [CollatzResearch.WordTrace]
  refine ⟨97318343123462144826631417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129757790831282859768841889 97318343123462144826631417)
  ·
    refine ⟨72988757342596608619973563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97318343123462144826631417 72988757342596608619973563)
    ·
      refine ⟨109483136013894912929960345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72988757342596608619973563 109483136013894912929960345)
      ·
        refine ⟨82112352010421184697470259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 109483136013894912929960345 82112352010421184697470259)
        ·
          refine ⟨123168528015631777046205389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82112352010421184697470259 123168528015631777046205389)
          ·
            refine ⟨46188198005861916392327021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 123168528015631777046205389 46188198005861916392327021)
            ·
              refine ⟨17320574252198218647122633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46188198005861916392327021 17320574252198218647122633)
              ·
                refine ⟨12990430689148663985341975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17320574252198218647122633 12990430689148663985341975)
                ·
                  refine ⟨19485646033722995978012963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12990430689148663985341975 19485646033722995978012963)
                  ·
                    refine ⟨29228469050584493967019445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19485646033722995978012963 29228469050584493967019445)
                    ·
                      refine ⟨2740168973492296309408073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29228469050584493967019445 2740168973492296309408073)
                      ·
                        rfl

theorem cell23_5336460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 3, 2, 1, 1, 5].length) (baseStart_5336460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5336460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5336460 prefixEnd_5336460 := by exact prefixLift 5336460
  have htrace : WordTrace (prefixWord ++ tailWord_5336460) baseStart_5336460 baseEnd_5336460 := by
    simpa [prefixWord, tailWord_5336460, baseEnd_5336460] using wordTrace_append hprefix tailTrace_5336460
  have hstable : (prefixWord ++ tailWord_5336460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5336460).length < 2 ^ (prefixWord ++ tailWord_5336460).sum := by decide
  have hdescent : baseEnd_5336460 < baseStart_5336460 := by decide
  rcases family_descends (prefixWord ++ tailWord_5336460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5336474 : List Nat := [3, 1, 1, 4, 1, 1, 1, 4, 3, 2, 2]
def baseStart_5336474 : Nat := 118140960795 + 5336474 * 2 ^ 59
def prefixEnd_5336474 : Nat := 4983230072969 + 3 ^ 40 * 5336474 * 2
def baseEnd_5336474 : Nat := 2740176162221459254633009

theorem tailTrace_5336474 : CollatzResearch.WordTrace tailWord_5336474 prefixEnd_5336474 2740176162221459254633009 := by
  unfold tailWord_5336474
  simp only [CollatzResearch.WordTrace]
  refine ⟨48659299217218392511068119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129758131245915713362848317 48659299217218392511068119)
  ·
    refine ⟨72988948825827588766602179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48659299217218392511068119 72988948825827588766602179)
    ·
      refine ⟨109483423238741383149903269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72988948825827588766602179 109483423238741383149903269)
      ·
        refine ⟨20528141857264009340606863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 109483423238741383149903269 20528141857264009340606863)
        ·
          refine ⟨30792212785896014010910295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20528141857264009340606863 30792212785896014010910295)
          ·
            refine ⟨46188319178844021016365443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30792212785896014010910295 46188319178844021016365443)
            ·
              refine ⟨69282478768266031524548165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46188319178844021016365443 69282478768266031524548165)
              ·
                refine ⟨12990464769049880910852781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 69282478768266031524548165 12990464769049880910852781)
                ·
                  refine ⟨4871424288393705341569793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12990464769049880910852781 4871424288393705341569793)
                  ·
                    refine ⟨3653568216295279006177345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4871424288393705341569793 3653568216295279006177345)
                    ·
                      refine ⟨2740176162221459254633009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3653568216295279006177345 2740176162221459254633009)
                      ·
                        rfl

theorem cell23_5336474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 4, 3, 2, 2].length) (baseStart_5336474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5336474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5336474 prefixEnd_5336474 := by exact prefixLift 5336474
  have htrace : WordTrace (prefixWord ++ tailWord_5336474) baseStart_5336474 baseEnd_5336474 := by
    simpa [prefixWord, tailWord_5336474, baseEnd_5336474] using wordTrace_append hprefix tailTrace_5336474
  have hstable : (prefixWord ++ tailWord_5336474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5336474).length < 2 ^ (prefixWord ++ tailWord_5336474).sum := by decide
  have hdescent : baseEnd_5336474 < baseStart_5336474 := by decide
  rcases family_descends (prefixWord ++ tailWord_5336474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5336508 : List Nat := [2, 2, 2, 4, 2, 2, 1, 1, 3, 2, 2]
def baseStart_5336508 : Nat := 118140960795 + 5336508 * 2 ^ 59
def prefixEnd_5336508 : Nat := 4983230072969 + 3 ^ 40 * 5336508 * 2
def baseEnd_5336508 : Nat := 2740193620563712121607853

theorem tailTrace_5336508 : CollatzResearch.WordTrace tailWord_5336508 prefixEnd_5336508 2740193620563712121607853 := by
  unfold tailWord_5336508
  simp only [CollatzResearch.WordTrace]
  refine ⟨97319218475375196925505089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129758957967166929234006785 97319218475375196925505089)
  ·
    refine ⟨72989413856531397694128817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97319218475375196925505089 72989413856531397694128817)
    ·
      refine ⟨54742060392398548270596613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72989413856531397694128817 54742060392398548270596613)
      ·
        refine ⟨10264136323574727800736865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 54742060392398548270596613 10264136323574727800736865)
        ·
          refine ⟨7698102242681045850552649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10264136323574727800736865 7698102242681045850552649)
          ·
            refine ⟨5773576682010784387914487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7698102242681045850552649 5773576682010784387914487)
            ·
              refine ⟨8660365023016176581871731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5773576682010784387914487 8660365023016176581871731)
              ·
                refine ⟨12990547534524264872807597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8660365023016176581871731 12990547534524264872807597)
                ·
                  refine ⟨4871455325446599327302849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12990547534524264872807597 4871455325446599327302849)
                  ·
                    refine ⟨3653591494084949495477137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4871455325446599327302849 3653591494084949495477137)
                    ·
                      refine ⟨2740193620563712121607853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3653591494084949495477137 2740193620563712121607853)
                      ·
                        rfl

theorem cell23_5336508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 2, 1, 1, 3, 2, 2].length) (baseStart_5336508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5336508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5336508 prefixEnd_5336508 := by exact prefixLift 5336508
  have htrace : WordTrace (prefixWord ++ tailWord_5336508) baseStart_5336508 baseEnd_5336508 := by
    simpa [prefixWord, tailWord_5336508, baseEnd_5336508] using wordTrace_append hprefix tailTrace_5336508
  have hstable : (prefixWord ++ tailWord_5336508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5336508).length < 2 ^ (prefixWord ++ tailWord_5336508).sum := by decide
  have hdescent : baseEnd_5336508 < baseStart_5336508 := by decide
  rcases family_descends (prefixWord ++ tailWord_5336508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5336510 : List Nat := [4, 2, 1, 1, 1, 1, 1, 3, 2, 7]
def baseStart_5336510 : Nat := 118140960795 + 5336510 * 2 ^ 59
def prefixEnd_5336510 : Nat := 4983230072969 + 3 ^ 40 * 5336510 * 2
def baseEnd_5336510 : Nat := 913398215841673704594281

theorem tailTrace_5336510 : CollatzResearch.WordTrace tailWord_5336510 prefixEnd_5336510 913398215841673704594281 := by
  unfold tailWord_5336510
  simp only [CollatzResearch.WordTrace]
  refine ⟨24329813737092893524072873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 129759006597828765461721989 24329813737092893524072873)
  ·
    refine ⟨18247360302819670143054655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24329813737092893524072873 18247360302819670143054655)
    ·
      refine ⟨27371040454229505214581983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18247360302819670143054655 27371040454229505214581983)
      ·
        refine ⟨41056560681344257821872975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27371040454229505214581983 41056560681344257821872975)
        ·
          refine ⟨61584841022016386732809463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41056560681344257821872975 61584841022016386732809463)
          ·
            refine ⟨92377261533024580099214195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61584841022016386732809463 92377261533024580099214195)
            ·
              refine ⟨138565892299536870148821293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 92377261533024580099214195 138565892299536870148821293)
              ·
                refine ⟨51962209612326326305807985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 138565892299536870148821293 51962209612326326305807985)
                ·
                  refine ⟨38971657209244744729355989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 51962209612326326305807985 38971657209244744729355989)
                  ·
                    refine ⟨913398215841673704594281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 38971657209244744729355989 913398215841673704594281)
                    ·
                      rfl

theorem cell23_5336510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 3, 2, 7].length) (baseStart_5336510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5336510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5336510 prefixEnd_5336510 := by exact prefixLift 5336510
  have htrace : WordTrace (prefixWord ++ tailWord_5336510) baseStart_5336510 baseEnd_5336510 := by
    simpa [prefixWord, tailWord_5336510, baseEnd_5336510] using wordTrace_append hprefix tailTrace_5336510
  have hstable : (prefixWord ++ tailWord_5336510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5336510).length < 2 ^ (prefixWord ++ tailWord_5336510).sum := by decide
  have hdescent : baseEnd_5336510 < baseStart_5336510 := by decide
  rcases family_descends (prefixWord ++ tailWord_5336510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5336570 : List Nat := [3, 1, 1, 1, 1, 2, 4, 3, 7]
def baseStart_5336570 : Nat := 118140960795 + 5336570 * 2 ^ 59
def prefixEnd_5336570 : Nat := 4983230072969 + 3 ^ 40 * 5336570 * 2
def baseEnd_5336570 : Nat := 304469495151587875448063

theorem tailTrace_5336570 : CollatzResearch.WordTrace tailWord_5336570 prefixEnd_5336570 304469495151587875448063 := by
  unfold tailWord_5336570
  simp only [CollatzResearch.WordTrace]
  refine ⟨48660174569131444609941791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129760465517683852293178109 48660174569131444609941791)
  ·
    refine ⟨72990261853697166914912687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48660174569131444609941791 72990261853697166914912687)
    ·
      refine ⟨109485392780545750372369031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72990261853697166914912687 109485392780545750372369031)
      ·
        refine ⟨164228089170818625558553547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109485392780545750372369031 164228089170818625558553547)
        ·
          refine ⟨246342133756227938337830321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 164228089170818625558553547 246342133756227938337830321)
          ·
            refine ⟨184756600317170953753372741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 246342133756227938337830321 184756600317170953753372741)
            ·
              refine ⟨34641862559469553828757389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 184756600317170953753372741 34641862559469553828757389)
              ·
                refine ⟨12990698459801082685784021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34641862559469553828757389 12990698459801082685784021)
                ·
                  refine ⟨304469495151587875448063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12990698459801082685784021 304469495151587875448063)
                  ·
                    rfl

theorem cell23_5336570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 4, 3, 7].length) (baseStart_5336570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5336570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5336570 prefixEnd_5336570 := by exact prefixLift 5336570
  have htrace : WordTrace (prefixWord ++ tailWord_5336570) baseStart_5336570 baseEnd_5336570 := by
    simpa [prefixWord, tailWord_5336570, baseEnd_5336570] using wordTrace_append hprefix tailTrace_5336570
  have hstable : (prefixWord ++ tailWord_5336570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5336570).length < 2 ^ (prefixWord ++ tailWord_5336570).sum := by decide
  have hdescent : baseEnd_5336570 < baseStart_5336570 := by decide
  rcases family_descends (prefixWord ++ tailWord_5336570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5336587 : List Nat := [1, 1, 1, 1, 8, 1, 1, 2, 7]
def baseStart_5336587 : Nat := 118140960795 + 5336587 * 2 ^ 59
def prefixEnd_5336587 : Nat := 4983230072969 + 3 ^ 40 * 5336587 * 2
def baseEnd_5336587 : Nat := 304470465059490812502221

theorem tailTrace_5336587 : CollatzResearch.WordTrace tailWord_5336587 prefixEnd_5336587 304470465059490812502221 := by
  unfold tailWord_5336587
  simp only [CollatzResearch.WordTrace]
  refine ⟨194641318317464190343136015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129760878878309460228757343 194641318317464190343136015)
  ·
    refine ⟨291961977476196285514704023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194641318317464190343136015 291961977476196285514704023)
    ·
      refine ⟨437942966214294428272056035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 291961977476196285514704023 437942966214294428272056035)
      ·
        refine ⟨656914449321441642408084053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 437942966214294428272056035 656914449321441642408084053)
        ·
          refine ⟨7698216202985644246969735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 656914449321441642408084053 7698216202985644246969735)
          ·
            refine ⟨11547324304478466370454603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7698216202985644246969735 11547324304478466370454603)
            ·
              refine ⟨17320986456717699555681905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11547324304478466370454603 17320986456717699555681905)
              ·
                refine ⟨12990739842538274666761429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17320986456717699555681905 12990739842538274666761429)
                ·
                  refine ⟨304470465059490812502221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12990739842538274666761429 304470465059490812502221)
                  ·
                    rfl

theorem cell23_5336587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 1, 2, 7].length) (baseStart_5336587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5336587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5336587 prefixEnd_5336587 := by exact prefixLift 5336587
  have htrace : WordTrace (prefixWord ++ tailWord_5336587) baseStart_5336587 baseEnd_5336587 := by
    simpa [prefixWord, tailWord_5336587, baseEnd_5336587] using wordTrace_append hprefix tailTrace_5336587
  have hstable : (prefixWord ++ tailWord_5336587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5336587).length < 2 ^ (prefixWord ++ tailWord_5336587).sum := by decide
  have hdescent : baseEnd_5336587 < baseStart_5336587 := by decide
  rcases family_descends (prefixWord ++ tailWord_5336587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5336604 : List Nat := [2, 2, 3, 1, 2, 1, 4, 3, 5]
def baseStart_5336604 : Nat := 118140960795 + 5336604 * 2 ^ 59
def prefixEnd_5336604 : Nat := 4983230072969 + 3 ^ 40 * 5336604 * 2
def baseEnd_5336604 : Nat := 304471434967393749556379

theorem tailTrace_5336604 : CollatzResearch.WordTrace tailWord_5336604 prefixEnd_5336604 304471434967393749556379 := by
  unfold tailWord_5336604
  simp only [CollatzResearch.WordTrace]
  refine ⟨97320969179201301123252433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129761292238935068164336577 97320969179201301123252433)
  ·
    refine ⟨72990726884400975842439325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97320969179201301123252433 72990726884400975842439325)
    ·
      refine ⟨27371522581650365940914747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72990726884400975842439325 27371522581650365940914747)
      ·
        refine ⟨41057283872475548911372121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27371522581650365940914747 41057283872475548911372121)
        ·
          refine ⟨30792962904356661683529091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41057283872475548911372121 30792962904356661683529091)
          ·
            refine ⟨46189444356534992525293637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30792962904356661683529091 46189444356534992525293637)
            ·
              refine ⟨8660520816850311098492557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 46189444356534992525293637 8660520816850311098492557)
              ·
                refine ⟨3247695306318866661934709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8660520816850311098492557 3247695306318866661934709)
                ·
                  refine ⟨304471434967393749556379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3247695306318866661934709 304471434967393749556379)
                  ·
                    rfl

theorem cell23_5336604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 4, 3, 5].length) (baseStart_5336604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5336604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5336604 prefixEnd_5336604 := by exact prefixLift 5336604
  have htrace : WordTrace (prefixWord ++ tailWord_5336604) baseStart_5336604 baseEnd_5336604 := by
    simpa [prefixWord, tailWord_5336604, baseEnd_5336604] using wordTrace_append hprefix tailTrace_5336604
  have hstable : (prefixWord ++ tailWord_5336604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5336604).length < 2 ^ (prefixWord ++ tailWord_5336604).sum := by decide
  have hdescent : baseEnd_5336604 < baseStart_5336604 := by decide
  rcases family_descends (prefixWord ++ tailWord_5336604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5336657 : List Nat := [1, 2, 2, 1, 3, 2, 1, 3, 1, 4, 3]
def baseStart_5336657 : Nat := 118140960795 + 5336657 * 2 ^ 59
def prefixEnd_5336657 : Nat := 4983230072969 + 3 ^ 40 * 5336657 * 2
def baseEnd_5336657 : Nat := 2740270129181232038644667

theorem tailTrace_5336657 : CollatzResearch.WordTrace tailWord_5336657 prefixEnd_5336657 2740270129181232038644667 := by
  unfold tailWord_5336657
  simp only [CollatzResearch.WordTrace]
  refine ⟨194643871427210592298184225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129762580951473728198789483 194643871427210592298184225)
  ·
    refine ⟨145982903570407944223638169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 194643871427210592298184225 145982903570407944223638169)
    ·
      refine ⟨109487177677805958167728627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 145982903570407944223638169 109487177677805958167728627)
      ·
        refine ⟨164230766516708937251592941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109487177677805958167728627 164230766516708937251592941)
        ·
          refine ⟨61586537443765851469347353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 164230766516708937251592941 61586537443765851469347353)
          ·
            refine ⟨46189903082824388602010515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61586537443765851469347353 46189903082824388602010515)
            ·
              refine ⟨69284854624236582903015773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46189903082824388602010515 69284854624236582903015773)
              ·
                refine ⟨25981820484088718588630915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 69284854624236582903015773 25981820484088718588630915)
                ·
                  refine ⟨38972730726133077882946373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25981820484088718588630915 38972730726133077882946373)
                  ·
                    refine ⟨7307387011149952103052445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 38972730726133077882946373 7307387011149952103052445)
                    ·
                      refine ⟨2740270129181232038644667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7307387011149952103052445 2740270129181232038644667)
                      ·
                        rfl

theorem cell23_5336657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 3, 1, 4, 3].length) (baseStart_5336657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5336657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5336657 prefixEnd_5336657 := by exact prefixLift 5336657
  have htrace : WordTrace (prefixWord ++ tailWord_5336657) baseStart_5336657 baseEnd_5336657 := by
    simpa [prefixWord, tailWord_5336657, baseEnd_5336657] using wordTrace_append hprefix tailTrace_5336657
  have hstable : (prefixWord ++ tailWord_5336657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5336657).length < 2 ^ (prefixWord ++ tailWord_5336657).sum := by decide
  have hdescent : baseEnd_5336657 < baseStart_5336657 := by decide
  rcases family_descends (prefixWord ++ tailWord_5336657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5336677 : List Nat := [1, 3, 1, 3, 3, 1, 2, 1, 8]
def baseStart_5336677 : Nat := 118140960795 + 5336677 * 2 ^ 59
def prefixEnd_5336677 : Nat := 4983230072969 + 3 ^ 40 * 5336677 * 2
def baseEnd_5336677 : Nat := 304475599866035773377175

theorem tailTrace_5336677 : CollatzResearch.WordTrace tailWord_5336677 prefixEnd_5336677 304475599866035773377175 := by
  unfold tailWord_5336677
  simp only [CollatzResearch.WordTrace]
  refine ⟨194644600887138135713912285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129763067258092090475941523 194644600887138135713912285)
  ·
    refine ⟨72991725332676800892717107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 194644600887138135713912285 72991725332676800892717107)
    ·
      refine ⟨109487587999015201339075661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72991725332676800892717107 109487587999015201339075661)
      ·
        refine ⟨41057845499630700502153373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 109487587999015201339075661 41057845499630700502153373)
        ·
          refine ⟨15396692062361512688307515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41057845499630700502153373 15396692062361512688307515)
          ·
            refine ⟨23095038093542269032461273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15396692062361512688307515 23095038093542269032461273)
            ·
              refine ⟨17321278570156701774345955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23095038093542269032461273 17321278570156701774345955)
              ·
                refine ⟨25981917855235052661518933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17321278570156701774345955 25981917855235052661518933)
                ·
                  refine ⟨304475599866035773377175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 25981917855235052661518933 304475599866035773377175)
                  ·
                    rfl

theorem cell23_5336677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 2, 1, 8].length) (baseStart_5336677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5336677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5336677 prefixEnd_5336677 := by exact prefixLift 5336677
  have htrace : WordTrace (prefixWord ++ tailWord_5336677) baseStart_5336677 baseEnd_5336677 := by
    simpa [prefixWord, tailWord_5336677, baseEnd_5336677] using wordTrace_append hprefix tailTrace_5336677
  have hstable : (prefixWord ++ tailWord_5336677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5336677).length < 2 ^ (prefixWord ++ tailWord_5336677).sum := by decide
  have hdescent : baseEnd_5336677 < baseStart_5336677 := by decide
  rcases family_descends (prefixWord ++ tailWord_5336677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5336704 : List Nat := [2, 1, 1, 2, 1, 4, 2, 1, 5, 1, 3]
def baseStart_5336704 : Nat := 118140960795 + 5336704 * 2 ^ 59
def prefixEnd_5336704 : Nat := 4983230072969 + 3 ^ 40 * 5336704 * 2
def baseEnd_5336704 : Nat := 2740294262771993354756951

theorem tailTrace_5336704 : CollatzResearch.WordTrace tailWord_5336704 prefixEnd_5336704 2740294262771993354756951 := by
  unfold tailWord_5336704
  simp only [CollatzResearch.WordTrace]
  refine ⟨97322792829020159662572583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129763723772026879550096777 97322792829020159662572583)
  ·
    refine ⟨145984189243530239493858875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97322792829020159662572583 145984189243530239493858875)
    ·
      refine ⟨218976283865295359240788313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145984189243530239493858875 218976283865295359240788313)
      ·
        refine ⟨164232212898971519430591235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 218976283865295359240788313 164232212898971519430591235)
        ·
          refine ⟨246348319348457279145886853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 164232212898971519430591235 246348319348457279145886853)
          ·
            refine ⟨46190309877835739839853785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 246348319348457279145886853 46190309877835739839853785)
            ·
              refine ⟨34642732408376804879890339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46190309877835739839853785 34642732408376804879890339)
              ·
                refine ⟨51964098612565207319835509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34642732408376804879890339 51964098612565207319835509)
                ·
                  refine ⟨4871634244927988186234579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 51964098612565207319835509 4871634244927988186234579)
                  ·
                    refine ⟨7307451367391982279351869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4871634244927988186234579 7307451367391982279351869)
                    ·
                      refine ⟨2740294262771993354756951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7307451367391982279351869 2740294262771993354756951)
                      ·
                        rfl

theorem cell23_5336704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 2, 1, 5, 1, 3].length) (baseStart_5336704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5336704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5336704 prefixEnd_5336704 := by exact prefixLift 5336704
  have htrace : WordTrace (prefixWord ++ tailWord_5336704) baseStart_5336704 baseEnd_5336704 := by
    simpa [prefixWord, tailWord_5336704, baseEnd_5336704] using wordTrace_append hprefix tailTrace_5336704
  have hstable : (prefixWord ++ tailWord_5336704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5336704).length < 2 ^ (prefixWord ++ tailWord_5336704).sum := by decide
  have hdescent : baseEnd_5336704 < baseStart_5336704 := by decide
  rcases family_descends (prefixWord ++ tailWord_5336704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5336732 : List Nat := [2, 2, 3, 2, 4, 1, 2, 2, 1, 4]
def baseStart_5336732 : Nat := 118140960795 + 5336732 * 2 ^ 59
def prefixEnd_5336732 : Nat := 4983230072969 + 3 ^ 40 * 5336732 * 2
def baseEnd_5336732 : Nat := 913436213410106415068941

theorem tailTrace_5336732 : CollatzResearch.WordTrace tailWord_5336732 prefixEnd_5336732 913436213410106415068941 := by
  unfold tailWord_5336732
  simp only [CollatzResearch.WordTrace]
  refine ⟨97323303450969440053582225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129764404601292586738109633 97323303450969440053582225)
  ·
    refine ⟨72992477588227080040186669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97323303450969440053582225 72992477588227080040186669)
    ·
      refine ⟨27372179095585155015070001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72992477588227080040186669 27372179095585155015070001)
      ·
        refine ⟨20529134321688866261302501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27372179095585155015070001 20529134321688866261302501)
        ·
          refine ⟨3849212685316662423994219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20529134321688866261302501 3849212685316662423994219)
          ·
            refine ⟨5773819027974993635991329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3849212685316662423994219 5773819027974993635991329)
            ·
              refine ⟨4330364270981245226993497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5773819027974993635991329 4330364270981245226993497)
              ·
                refine ⟨3247773203235933920245123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4330364270981245226993497 3247773203235933920245123)
                ·
                  refine ⟨4871659804853900880367685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3247773203235933920245123 4871659804853900880367685)
                  ·
                    refine ⟨913436213410106415068941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4871659804853900880367685 913436213410106415068941)
                    ·
                      rfl

theorem cell23_5336732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 4, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 4, 1, 2, 2, 1, 4].length) (baseStart_5336732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5336732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5336732 prefixEnd_5336732 := by exact prefixLift 5336732
  have htrace : WordTrace (prefixWord ++ tailWord_5336732) baseStart_5336732 baseEnd_5336732 := by
    simpa [prefixWord, tailWord_5336732, baseEnd_5336732] using wordTrace_append hprefix tailTrace_5336732
  have hstable : (prefixWord ++ tailWord_5336732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5336732).length < 2 ^ (prefixWord ++ tailWord_5336732).sum := by decide
  have hdescent : baseEnd_5336732 < baseStart_5336732 := by decide
  rcases family_descends (prefixWord ++ tailWord_5336732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5336761 : List Nat := [1, 2, 1, 4, 1, 1, 3, 1, 5, 2, 2]
def baseStart_5336761 : Nat := 118140960795 + 5336761 * 2 ^ 59
def prefixEnd_5336761 : Nat := 4983230072969 + 3 ^ 40 * 5336761 * 2
def baseEnd_5336761 : Nat := 2740323531169299631744189

theorem tailTrace_5336761 : CollatzResearch.WordTrace tailWord_5336761 prefixEnd_5336761 2740323531169299631744189 := by
  unfold tailWord_5336761
  simp only [CollatzResearch.WordTrace]
  refine ⟨194647664618833818059970137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129765109745889212039980091 194647664618833818059970137)
  ·
    refine ⟨145985748464125363544977603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 194647664618833818059970137 145985748464125363544977603)
    ·
      refine ⟨218978622696188045317466405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145985748464125363544977603 218978622696188045317466405)
      ·
        refine ⟨41058491755535258497024951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 218978622696188045317466405 41058491755535258497024951)
        ·
          refine ⟨61587737633302887745537427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41058491755535258497024951 61587737633302887745537427)
          ·
            refine ⟨92381606449954331618306141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61587737633302887745537427 92381606449954331618306141)
            ·
              refine ⟨34643102418732874356864803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 92381606449954331618306141 34643102418732874356864803)
              ·
                refine ⟨51964653628099311535297205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34643102418732874356864803 51964653628099311535297205)
                ·
                  refine ⟨4871686277634310456434113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 51964653628099311535297205 4871686277634310456434113)
                  ·
                    refine ⟨3653764708225732842325585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4871686277634310456434113 3653764708225732842325585)
                    ·
                      refine ⟨2740323531169299631744189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3653764708225732842325585 2740323531169299631744189)
                      ·
                        rfl

theorem cell23_5336761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 3, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 3, 1, 5, 2, 2].length) (baseStart_5336761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5336761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5336761 prefixEnd_5336761 := by exact prefixLift 5336761
  have htrace : WordTrace (prefixWord ++ tailWord_5336761) baseStart_5336761 baseEnd_5336761 := by
    simpa [prefixWord, tailWord_5336761, baseEnd_5336761] using wordTrace_append hprefix tailTrace_5336761
  have hstable : (prefixWord ++ tailWord_5336761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5336761).length < 2 ^ (prefixWord ++ tailWord_5336761).sum := by decide
  have hdescent : baseEnd_5336761 < baseStart_5336761 := by decide
  rcases family_descends (prefixWord ++ tailWord_5336761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5336788 : List Nat := [2, 4, 1, 3, 1, 1, 3, 2, 2, 4]
def baseStart_5336788 : Nat := 118140960795 + 5336788 * 2 ^ 59
def prefixEnd_5336788 : Nat := 4983230072969 + 3 ^ 40 * 5336788 * 2
def baseEnd_5336788 : Nat := 913445798382323675368855

theorem tailTrace_5336788 : CollatzResearch.WordTrace tailWord_5336788 prefixEnd_5336788 913445798382323675368855 := by
  unfold tailWord_5336788
  simp only [CollatzResearch.WordTrace]
  refine ⟨97324324694868000835601509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129765766259824001114135345 97324324694868000835601509)
  ·
    refine ⟨18248310880287750156675283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 97324324694868000835601509 18248310880287750156675283)
    ·
      refine ⟨27372466320431625235012925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18248310880287750156675283 27372466320431625235012925)
      ·
        refine ⟨10264674870161859463129847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27372466320431625235012925 10264674870161859463129847)
        ·
          refine ⟨15397012305242789194694771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10264674870161859463129847 15397012305242789194694771)
          ·
            refine ⟨23095518457864183792042157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15397012305242789194694771 23095518457864183792042157)
            ·
              refine ⟨8660819421699068922015809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23095518457864183792042157 8660819421699068922015809)
              ·
                refine ⟨6495614566274301691511857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8660819421699068922015809 6495614566274301691511857)
                ·
                  refine ⟨4871710924705726268633893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6495614566274301691511857 4871710924705726268633893)
                  ·
                    refine ⟨913445798382323675368855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4871710924705726268633893 913445798382323675368855)
                    ·
                      rfl

theorem cell23_5336788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 3, 2, 2, 4].length) (baseStart_5336788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5336788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5336788 prefixEnd_5336788 := by exact prefixLift 5336788
  have htrace : WordTrace (prefixWord ++ tailWord_5336788) baseStart_5336788 baseEnd_5336788 := by
    simpa [prefixWord, tailWord_5336788, baseEnd_5336788] using wordTrace_append hprefix tailTrace_5336788
  have hstable : (prefixWord ++ tailWord_5336788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5336788).length < 2 ^ (prefixWord ++ tailWord_5336788).sum := by decide
  have hdescent : baseEnd_5336788 < baseStart_5336788 := by decide
  rcases family_descends (prefixWord ++ tailWord_5336788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5336811 : List Nat := [1, 1, 1, 1, 2, 4, 2, 5, 2, 1, 3]
def baseStart_5336811 : Nat := 118140960795 + 5336811 * 2 ^ 59
def prefixEnd_5336811 : Nat := 4983230072969 + 3 ^ 40 * 5336811 * 2
def baseEnd_5336811 : Nat := 2740349205202024436118959

theorem tailTrace_5336811 : CollatzResearch.WordTrace tailWord_5336811 prefixEnd_5336811 2740349205202024436118959 := by
  unfold tailWord_5336811
  simp only [CollatzResearch.WordTrace]
  refine ⟨194649488268652676599290287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129766325512435117732860191 194649488268652676599290287)
  ·
    refine ⟨291974232402979014898935431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194649488268652676599290287 291974232402979014898935431)
    ·
      refine ⟨437961348604468522348403147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 291974232402979014898935431 437961348604468522348403147)
      ·
        refine ⟨656942022906702783522604721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 437961348604468522348403147 656942022906702783522604721)
        ·
          refine ⟨492706517180027087641953541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 656942022906702783522604721 492706517180027087641953541)
          ·
            refine ⟨92382471971255078932866289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 492706517180027087641953541 92382471971255078932866289)
            ·
              refine ⟨69286853978441309199649717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 92382471971255078932866289 69286853978441309199649717)
              ·
                refine ⟨6495642560478872737467161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 69286853978441309199649717 6495642560478872737467161)
                ·
                  refine ⟨4871731920359154553100371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6495642560478872737467161 4871731920359154553100371)
                  ·
                    refine ⟨7307597880538731829650557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4871731920359154553100371 7307597880538731829650557)
                    ·
                      refine ⟨2740349205202024436118959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7307597880538731829650557 2740349205202024436118959)
                      ·
                        rfl

theorem cell23_5336811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 5, 2, 1, 3].length) (baseStart_5336811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5336811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5336811 prefixEnd_5336811 := by exact prefixLift 5336811
  have htrace : WordTrace (prefixWord ++ tailWord_5336811) baseStart_5336811 baseEnd_5336811 := by
    simpa [prefixWord, tailWord_5336811, baseEnd_5336811] using wordTrace_append hprefix tailTrace_5336811
  have hstable : (prefixWord ++ tailWord_5336811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5336811).length < 2 ^ (prefixWord ++ tailWord_5336811).sum := by decide
  have hdescent : baseEnd_5336811 < baseStart_5336811 := by decide
  rcases family_descends (prefixWord ++ tailWord_5336811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5336827 : List Nat := [1, 1, 1, 1, 1, 3, 1, 4, 4, 6]
def baseStart_5336827 : Nat := 118140960795 + 5336827 * 2 ^ 59
def prefixEnd_5336827 : Nat := 4983230072969 + 3 ^ 40 * 5336827 * 2
def baseEnd_5336827 : Nat := 913452473630832124506295

theorem tailTrace_5336827 : CollatzResearch.WordTrace tailWord_5336827 prefixEnd_5336827 913452473630832124506295 := by
  unfold tailWord_5336827
  simp only [CollatzResearch.WordTrace]
  refine ⟨194650071836594711331872735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129766714557729807554581823 194650071836594711331872735)
  ·
    refine ⟨291975107754892066997809103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194650071836594711331872735 291975107754892066997809103)
    ·
      refine ⟨437962661632338100496713655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 291975107754892066997809103 437962661632338100496713655)
      ·
        refine ⟨656943992448507150745070483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 437962661632338100496713655 656943992448507150745070483)
        ·
          refine ⟨985415988672760726117605725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 656943992448507150745070483 985415988672760726117605725)
          ·
            refine ⟨369530995752285272294102147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 985415988672760726117605725 369530995752285272294102147)
            ·
              refine ⟨554296493628427908441153221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 369530995752285272294102147 554296493628427908441153221)
              ·
                refine ⟨103930592555330232832716229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 554296493628427908441153221 103930592555330232832716229)
                ·
                  refine ⟨19486986104124418656134293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 103930592555330232832716229 19486986104124418656134293)
                  ·
                    refine ⟨913452473630832124506295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19486986104124418656134293 913452473630832124506295)
                    ·
                      rfl

theorem cell23_5336827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 4, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 4, 4, 6].length) (baseStart_5336827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5336827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5336827 prefixEnd_5336827 := by exact prefixLift 5336827
  have htrace : WordTrace (prefixWord ++ tailWord_5336827) baseStart_5336827 baseEnd_5336827 := by
    simpa [prefixWord, tailWord_5336827, baseEnd_5336827] using wordTrace_append hprefix tailTrace_5336827
  have hstable : (prefixWord ++ tailWord_5336827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5336827).length < 2 ^ (prefixWord ++ tailWord_5336827).sum := by decide
  have hdescent : baseEnd_5336827 < baseStart_5336827 := by decide
  rcases family_descends (prefixWord ++ tailWord_5336827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5336847 : List Nat := [1, 1, 2, 1, 1, 1, 4, 1, 2, 3, 6]
def baseStart_5336847 : Nat := 118140960795 + 5336847 * 2 ^ 59
def prefixEnd_5336847 : Nat := 4983230072969 + 3 ^ 40 * 5336847 * 2
def baseEnd_5336847 : Nat := 2740367690505586295268793

theorem tailTrace_5336847 : CollatzResearch.WordTrace tailWord_5336847 prefixEnd_5336847 2740367690505586295268793 := by
  unfold tailWord_5336847
  simp only [CollatzResearch.WordTrace]
  refine ⟨194650801296522254747600795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129767200864348169831733863 194650801296522254747600795)
  ·
    refine ⟨291976201944783382121401193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194650801296522254747600795 291976201944783382121401193)
    ·
      refine ⟨218982151458587536591050895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 291976201944783382121401193 218982151458587536591050895)
      ·
        refine ⟨328473227187881304886576343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 218982151458587536591050895 328473227187881304886576343)
        ·
          refine ⟨492709840781821957329864515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 328473227187881304886576343 492709840781821957329864515)
          ·
            refine ⟨739064761172732935994796773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 492709840781821957329864515 739064761172732935994796773)
            ·
              refine ⟨138574642719887425499024395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 739064761172732935994796773 138574642719887425499024395)
              ·
                refine ⟨207861964079831138248536593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 138574642719887425499024395 207861964079831138248536593)
                ·
                  refine ⟨155896473059873353686402445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 207861964079831138248536593 155896473059873353686402445)
                  ·
                    refine ⟨58461177397452507632400917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 155896473059873353686402445 58461177397452507632400917)
                    ·
                      refine ⟨2740367690505586295268793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 58461177397452507632400917 2740367690505586295268793)
                      ·
                        rfl

theorem cell23_5336847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 1, 2, 3, 6].length) (baseStart_5336847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5336847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5336847 prefixEnd_5336847 := by exact prefixLift 5336847
  have htrace : WordTrace (prefixWord ++ tailWord_5336847) baseStart_5336847 baseEnd_5336847 := by
    simpa [prefixWord, tailWord_5336847, baseEnd_5336847] using wordTrace_append hprefix tailTrace_5336847
  have hstable : (prefixWord ++ tailWord_5336847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5336847).length < 2 ^ (prefixWord ++ tailWord_5336847).sum := by decide
  have hdescent : baseEnd_5336847 < baseStart_5336847 := by decide
  rcases family_descends (prefixWord ++ tailWord_5336847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5336864 : List Nat := [2, 1, 1, 5, 1, 1, 2, 1, 1, 4, 4]
def baseStart_5336864 : Nat := 118140960795 + 5336864 * 2 ^ 59
def prefixEnd_5336864 : Nat := 4983230072969 + 3 ^ 40 * 5336864 * 2
def baseEnd_5336864 : Nat := 2740376419676712728756215

theorem tailTrace_5336864 : CollatzResearch.WordTrace tailWord_5336864 prefixEnd_5336864 2740376419676712728756215 := by
  unfold tailWord_5336864
  simp only [CollatzResearch.WordTrace]
  refine ⟨97325710668730333325484823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129767614224973777767313097 97325710668730333325484823)
  ·
    refine ⟨145988566003095499988227235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97325710668730333325484823 145988566003095499988227235)
    ·
      refine ⟨218982849004643249982340853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145988566003095499988227235 218982849004643249982340853)
      ·
        refine ⟨20529642094185304685844455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 218982849004643249982340853 20529642094185304685844455)
        ·
          refine ⟨30794463141277957028766683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20529642094185304685844455 30794463141277957028766683)
          ·
            refine ⟨46191694711916935543150025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30794463141277957028766683 46191694711916935543150025)
            ·
              refine ⟨34643771033937701657362519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46191694711916935543150025 34643771033937701657362519)
              ·
                refine ⟨51965656550906552486043779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34643771033937701657362519 51965656550906552486043779)
                ·
                  refine ⟨77948484826359828729065669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51965656550906552486043779 77948484826359828729065669)
                  ·
                    refine ⟨14615340904942467886699813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 77948484826359828729065669 14615340904942467886699813)
                    ·
                      refine ⟨2740376419676712728756215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14615340904942467886699813 2740376419676712728756215)
                      ·
                        rfl

theorem cell23_5336864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 2, 1, 1, 4, 4].length) (baseStart_5336864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5336864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5336864 prefixEnd_5336864 := by exact prefixLift 5336864
  have htrace : WordTrace (prefixWord ++ tailWord_5336864) baseStart_5336864 baseEnd_5336864 := by
    simpa [prefixWord, tailWord_5336864, baseEnd_5336864] using wordTrace_append hprefix tailTrace_5336864
  have hstable : (prefixWord ++ tailWord_5336864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5336864).length < 2 ^ (prefixWord ++ tailWord_5336864).sum := by decide
  have hdescent : baseEnd_5336864 < baseStart_5336864 := by decide
  rcases family_descends (prefixWord ++ tailWord_5336864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5336908 : List Nat := [2, 2, 1, 3, 4, 1, 1, 4, 5]
def baseStart_5336908 : Nat := 118140960795 + 5336908 * 2 ^ 59
def prefixEnd_5336908 : Nat := 4983230072969 + 3 ^ 40 * 5336908 * 2
def baseEnd_5336908 : Nat := 304488779202834506289557

theorem tailTrace_5336908 : CollatzResearch.WordTrace tailWord_5336908 prefixEnd_5336908 304488779202834506289557 := by
  unfold tailWord_5336908
  simp only [CollatzResearch.WordTrace]
  refine ⟨97326513074650631082785689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129768684099534174777047585 97326513074650631082785689)
  ·
    refine ⟨72994884805987973312089267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97326513074650631082785689 72994884805987973312089267)
    ·
      refine ⟨109492327208981959968133901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72994884805987973312089267 109492327208981959968133901)
      ·
        refine ⟨41059622703368234988050213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 109492327208981959968133901 41059622703368234988050213)
        ·
          refine ⟨7698679256881544060259415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 41059622703368234988050213 7698679256881544060259415)
          ·
            refine ⟨11548018885322316090389123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7698679256881544060259415 11548018885322316090389123)
            ·
              refine ⟨17322028327983474135583685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11548018885322316090389123 17322028327983474135583685)
              ·
                refine ⟨3247880311496901400421941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17322028327983474135583685 3247880311496901400421941)
                ·
                  refine ⟨304488779202834506289557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3247880311496901400421941 304488779202834506289557)
                  ·
                    rfl

theorem cell23_5336908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 1, 4, 5].length) (baseStart_5336908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5336908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5336908 prefixEnd_5336908 := by exact prefixLift 5336908
  have htrace : WordTrace (prefixWord ++ tailWord_5336908) baseStart_5336908 baseEnd_5336908 := by
    simpa [prefixWord, tailWord_5336908, baseEnd_5336908] using wordTrace_append hprefix tailTrace_5336908
  have hstable : (prefixWord ++ tailWord_5336908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5336908).length < 2 ^ (prefixWord ++ tailWord_5336908).sum := by decide
  have hdescent : baseEnd_5336908 < baseStart_5336908 := by decide
  rcases family_descends (prefixWord ++ tailWord_5336908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5336938 : List Nat := [3, 1, 3, 4, 1, 1, 1, 1, 1, 7]
def baseStart_5336938 : Nat := 118140960795 + 5336938 * 2 ^ 59
def prefixEnd_5336938 : Nat := 4983230072969 + 3 ^ 40 * 5336938 * 2
def baseEnd_5336938 : Nat := 913471472415048479743625

theorem tailTrace_5336938 : CollatzResearch.WordTrace tailWord_5336938 prefixEnd_5336938 913471472415048479743625 := by
  unfold tailWord_5336938
  simp only [CollatzResearch.WordTrace]
  refine ⟨48663530084798144322290867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129769413559461718192775645 48663530084798144322290867)
  ·
    refine ⟨72995295127197216483436301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48663530084798144322290867 72995295127197216483436301)
    ·
      refine ⟨27373235672698956181288613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72995295127197216483436301 27373235672698956181288613)
      ·
        refine ⟨5132481688631054283991615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27373235672698956181288613 5132481688631054283991615)
        ·
          refine ⟨7698722532946581425987423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5132481688631054283991615 7698722532946581425987423)
          ·
            refine ⟨11548083799419872138981135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7698722532946581425987423 11548083799419872138981135)
            ·
              refine ⟨17322125699129808208471703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11548083799419872138981135 17322125699129808208471703)
              ·
                refine ⟨25983188548694712312707555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17322125699129808208471703 25983188548694712312707555)
                ·
                  refine ⟨38974782823042068469061333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25983188548694712312707555 38974782823042068469061333)
                  ·
                    refine ⟨913471472415048479743625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 38974782823042068469061333 913471472415048479743625)
                    ·
                      rfl

theorem cell23_5336938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 1, 1, 1, 7].length) (baseStart_5336938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5336938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5336938 prefixEnd_5336938 := by exact prefixLift 5336938
  have htrace : WordTrace (prefixWord ++ tailWord_5336938) baseStart_5336938 baseEnd_5336938 := by
    simpa [prefixWord, tailWord_5336938, baseEnd_5336938] using wordTrace_append hprefix tailTrace_5336938
  have hstable : (prefixWord ++ tailWord_5336938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5336938).length < 2 ^ (prefixWord ++ tailWord_5336938).sum := by decide
  have hdescent : baseEnd_5336938 < baseStart_5336938 := by decide
  rcases family_descends (prefixWord ++ tailWord_5336938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5336954 : List Nat := [3, 1, 1, 1, 1, 1, 5, 1, 2, 1, 6]
def baseStart_5336954 : Nat := 118140960795 + 5336954 * 2 ^ 59
def prefixEnd_5336954 : Nat := 4983230072969 + 3 ^ 40 * 5336954 * 2
def baseEnd_5336954 : Nat := 2740422632935617376630801

theorem tailTrace_5336954 : CollatzResearch.WordTrace tailWord_5336954 prefixEnd_5336954 2740422632935617376630801 := by
  unfold tailWord_5336954
  simp only [CollatzResearch.WordTrace]
  refine ⟨48663675976783653005436479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129769802604756408014497277 48663675976783653005436479)
  ·
    refine ⟨72995513965175479508154719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48663675976783653005436479 72995513965175479508154719)
    ·
      refine ⟨109493270947763219262232079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72995513965175479508154719 109493270947763219262232079)
      ·
        refine ⟨164239906421644828893348119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109493270947763219262232079 164239906421644828893348119)
        ·
          refine ⟨246359859632467243340022179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 164239906421644828893348119 246359859632467243340022179)
          ·
            refine ⟨369539789448700865010033269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 246359859632467243340022179 369539789448700865010033269)
            ·
              refine ⟨34644355260815706094690619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 369539789448700865010033269 34644355260815706094690619)
              ·
                refine ⟨51966532891223559142035929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34644355260815706094690619 51966532891223559142035929)
                ·
                  refine ⟨38974899668417669356526947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 51966532891223559142035929 38974899668417669356526947)
                  ·
                    refine ⟨58462349502626504034790421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 38974899668417669356526947 58462349502626504034790421)
                    ·
                      refine ⟨2740422632935617376630801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 58462349502626504034790421 2740422632935617376630801)
                      ·
                        rfl

theorem cell23_5336954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 5, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 5, 1, 2, 1, 6].length) (baseStart_5336954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5336954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5336954 prefixEnd_5336954 := by exact prefixLift 5336954
  have htrace : WordTrace (prefixWord ++ tailWord_5336954) baseStart_5336954 baseEnd_5336954 := by
    simpa [prefixWord, tailWord_5336954, baseEnd_5336954] using wordTrace_append hprefix tailTrace_5336954
  have hstable : (prefixWord ++ tailWord_5336954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5336954).length < 2 ^ (prefixWord ++ tailWord_5336954).sum := by decide
  have hdescent : baseEnd_5336954 < baseStart_5336954 := by decide
  rcases family_descends (prefixWord ++ tailWord_5336954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5336978 : List Nat := [3, 2, 3, 2, 1, 1, 1, 2, 1, 4, 3]
def baseStart_5336978 : Nat := 118140960795 + 5336978 * 2 ^ 59
def prefixEnd_5336978 : Nat := 4983230072969 + 3 ^ 40 * 5336978 * 2
def baseEnd_5336978 : Nat := 2740434956471325282730691

theorem tailTrace_5336978 : CollatzResearch.WordTrace tailWord_5336978 prefixEnd_5336978 2740434956471325282730691 := by
  unfold tailWord_5336978
  simp only [CollatzResearch.WordTrace]
  refine ⟨48663894814761916030154897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129770386172698442747079725 48663894814761916030154897)
  ·
    refine ⟨36497921111071437022616173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48663894814761916030154897 36497921111071437022616173)
    ·
      refine ⟨13686720416651788883481065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36497921111071437022616173 13686720416651788883481065)
      ·
        refine ⟨10265040312488841662610799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13686720416651788883481065 10265040312488841662610799)
        ·
          refine ⟨15397560468733262493916199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10265040312488841662610799 15397560468733262493916199)
          ·
            refine ⟨23096340703099893740874299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15397560468733262493916199 23096340703099893740874299)
            ·
              refine ⟨34644511054649840611311449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23096340703099893740874299 34644511054649840611311449)
              ·
                refine ⟨25983383290987380458483587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34644511054649840611311449 25983383290987380458483587)
                ·
                  refine ⟨38975074936481070687725381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25983383290987380458483587 38975074936481070687725381)
                  ·
                    refine ⟨7307826550590200753948509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 38975074936481070687725381 7307826550590200753948509)
                    ·
                      refine ⟨2740434956471325282730691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7307826550590200753948509 2740434956471325282730691)
                      ·
                        rfl

theorem cell23_5336978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 1, 2, 1, 4, 3].length) (baseStart_5336978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5336978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5336978 prefixEnd_5336978 := by exact prefixLift 5336978
  have htrace : WordTrace (prefixWord ++ tailWord_5336978) baseStart_5336978 baseEnd_5336978 := by
    simpa [prefixWord, tailWord_5336978, baseEnd_5336978] using wordTrace_append hprefix tailTrace_5336978
  have hstable : (prefixWord ++ tailWord_5336978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5336978).length < 2 ^ (prefixWord ++ tailWord_5336978).sum := by decide
  have hdescent : baseEnd_5336978 < baseStart_5336978 := by decide
  rcases family_descends (prefixWord ++ tailWord_5336978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5337004 : List Nat := [2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 5]
def baseStart_5337004 : Nat := 118140960795 + 5337004 * 2 ^ 59
def prefixEnd_5337004 : Nat := 4983230072969 + 3 ^ 40 * 5337004 * 2
def baseEnd_5337004 : Nat := 2740448306968342181005571

theorem tailTrace_5337004 : CollatzResearch.WordTrace tailWord_5337004 prefixEnd_5337004 2740448306968342181005571 := by
  unfold tailWord_5337004
  simp only [CollatzResearch.WordTrace]
  refine ⟨97328263778476735280533033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129771018371302313707377377 97328263778476735280533033)
  ·
    refine ⟨72996197833857551460399775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97328263778476735280533033 72996197833857551460399775)
    ·
      refine ⟨109494296750786327190599663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72996197833857551460399775 109494296750786327190599663)
      ·
        refine ⟨164241445126179490785899495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109494296750786327190599663 164241445126179490785899495)
        ·
          refine ⟨246362167689269236178849243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 164241445126179490785899495 246362167689269236178849243)
          ·
            refine ⟨369543251533903854268273865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 246362167689269236178849243 369543251533903854268273865)
            ·
              refine ⟨277157438650427890701205399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 369543251533903854268273865 277157438650427890701205399)
              ·
                refine ⟨415736157975641836051808099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 277157438650427890701205399 415736157975641836051808099)
                ·
                  refine ⟨623604236963462754077712149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 415736157975641836051808099 623604236963462754077712149)
                  ·
                    refine ⟨29231448607662316597392757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 623604236963462754077712149 29231448607662316597392757)
                    ·
                      refine ⟨2740448306968342181005571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29231448607662316597392757 2740448306968342181005571)
                      ·
                        rfl

theorem cell23_5337004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 5].length) (baseStart_5337004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5337004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5337004 prefixEnd_5337004 := by exact prefixLift 5337004
  have htrace : WordTrace (prefixWord ++ tailWord_5337004) baseStart_5337004 baseEnd_5337004 := by
    simpa [prefixWord, tailWord_5337004, baseEnd_5337004] using wordTrace_append hprefix tailTrace_5337004
  have hstable : (prefixWord ++ tailWord_5337004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5337004).length < 2 ^ (prefixWord ++ tailWord_5337004).sum := by decide
  have hdescent : baseEnd_5337004 < baseStart_5337004 := by decide
  rcases family_descends (prefixWord ++ tailWord_5337004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5337011 : List Nat := [1, 1, 1, 2, 3, 1, 3, 5, 1, 5]
def baseStart_5337011 : Nat := 118140960795 + 5337011 * 2 ^ 59
def prefixEnd_5337011 : Nat := 4983230072969 + 3 ^ 40 * 5337011 * 2
def baseEnd_5337011 : Nat := 913483967110974551206013

theorem tailTrace_5337011 : CollatzResearch.WordTrace tailWord_5337011 prefixEnd_5337011 913483967110974551206013 := by
  unfold tailWord_5337011
  simp only [CollatzResearch.WordTrace]
  refine ⟨194656782867928110756570887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129771188578618740504380591 194656782867928110756570887)
  ·
    refine ⟨291985174301892166134856331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194656782867928110756570887 291985174301892166134856331)
    ·
      refine ⟨437977761452838249202284497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 291985174301892166134856331 437977761452838249202284497)
      ·
        refine ⟨328483321089628686901713373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 437977761452838249202284497 328483321089628686901713373)
        ·
          refine ⟨123181245408610757588142515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 328483321089628686901713373 123181245408610757588142515)
          ·
            refine ⟨184771868112916136382213773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 123181245408610757588142515 184771868112916136382213773)
            ·
              refine ⟨69289450542343551143330165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 184771868112916136382213773 69289450542343551143330165)
              ·
                refine ⟨6495885988344707919687203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 69289450542343551143330165 6495885988344707919687203)
                ·
                  refine ⟨9743828982517061879530805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6495885988344707919687203 9743828982517061879530805)
                  ·
                    refine ⟨913483967110974551206013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9743828982517061879530805 913483967110974551206013)
                    ·
                      rfl

theorem cell23_5337011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 5, 1, 5].length) (baseStart_5337011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5337011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5337011 prefixEnd_5337011 := by exact prefixLift 5337011
  have htrace : WordTrace (prefixWord ++ tailWord_5337011) baseStart_5337011 baseEnd_5337011 := by
    simpa [prefixWord, tailWord_5337011, baseEnd_5337011] using wordTrace_append hprefix tailTrace_5337011
  have hstable : (prefixWord ++ tailWord_5337011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5337011).length < 2 ^ (prefixWord ++ tailWord_5337011).sum := by decide
  have hdescent : baseEnd_5337011 < baseStart_5337011 := by decide
  rcases family_descends (prefixWord ++ tailWord_5337011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5337012 : List Nat := [2, 5, 2, 1, 2, 1, 1, 2, 2, 2, 3]
def baseStart_5337012 : Nat := 118140960795 + 5337012 * 2 ^ 59
def prefixEnd_5337012 : Nat := 4983230072969 + 3 ^ 40 * 5337012 * 2
def baseEnd_5337012 : Nat := 2740452414813578149705535

theorem tailTrace_5337012 : CollatzResearch.WordTrace tailWord_5337012 prefixEnd_5337012 2740452414813578149705535 := by
  unfold tailWord_5337012
  simp only [CollatzResearch.WordTrace]
  refine ⟨97328409670462243963678645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129771212893949658618238193 97328409670462243963678645)
  ·
    refine ⟨9124538406605835371594873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 97328409670462243963678645 9124538406605835371594873)
    ·
      refine ⟨6843403804954376528696155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9124538406605835371594873 6843403804954376528696155)
      ·
        refine ⟨10265105707431564793044233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6843403804954376528696155 10265105707431564793044233)
        ·
          refine ⟨7698829280573673594783175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10265105707431564793044233 7698829280573673594783175)
          ·
            refine ⟨11548243920860510392174763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7698829280573673594783175 11548243920860510392174763)
            ·
              refine ⟨17322365881290765588262145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11548243920860510392174763 17322365881290765588262145)
              ·
                refine ⟨12991774410968074191196609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17322365881290765588262145 12991774410968074191196609)
                ·
                  refine ⟨9743830808226055643397457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12991774410968074191196609 9743830808226055643397457)
                  ·
                    refine ⟨7307873106169541732548093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9743830808226055643397457 7307873106169541732548093)
                    ·
                      refine ⟨2740452414813578149705535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7307873106169541732548093 2740452414813578149705535)
                      ·
                        rfl

theorem cell23_5337012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 1, 2, 2, 2, 3].length) (baseStart_5337012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5337012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5337012 prefixEnd_5337012 := by exact prefixLift 5337012
  have htrace : WordTrace (prefixWord ++ tailWord_5337012) baseStart_5337012 baseEnd_5337012 := by
    simpa [prefixWord, tailWord_5337012, baseEnd_5337012] using wordTrace_append hprefix tailTrace_5337012
  have hstable : (prefixWord ++ tailWord_5337012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5337012).length < 2 ^ (prefixWord ++ tailWord_5337012).sum := by decide
  have hdescent : baseEnd_5337012 < baseStart_5337012 := by decide
  rcases family_descends (prefixWord ++ tailWord_5337012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5337031 : List Nat := [1, 1, 4, 1, 1, 2, 1, 4, 3, 1, 4]
def baseStart_5337031 : Nat := 118140960795 + 5337031 * 2 ^ 59
def prefixEnd_5337031 : Nat := 4983230072969 + 3 ^ 40 * 5337031 * 2
def baseEnd_5337031 : Nat := 2740462170946013575367947

theorem tailTrace_5337031 : CollatzResearch.WordTrace tailWord_5337031 prefixEnd_5337031 2740462170946013575367947 := by
  unfold tailWord_5337031
  simp only [CollatzResearch.WordTrace]
  refine ⟨194657512327855654172298947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129771674885237102781532631 194657512327855654172298947)
  ·
    refine ⟨291986268491783481258448421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194657512327855654172298947 291986268491783481258448421)
    ·
      refine ⟨54747425342209402735959079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 291986268491783481258448421 54747425342209402735959079)
      ·
        refine ⟨82121138013314104103938619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54747425342209402735959079 82121138013314104103938619)
        ·
          refine ⟨123181707019971156155907929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82121138013314104103938619 123181707019971156155907929)
          ·
            refine ⟨92386280264978367116930947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 123181707019971156155907929 92386280264978367116930947)
            ·
              refine ⟨138579420397467550675396421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 92386280264978367116930947 138579420397467550675396421)
              ·
                refine ⟨25983641324525165751636829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 138579420397467550675396421 25983641324525165751636829)
                ·
                  refine ⟨9743865496696937156863811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25983641324525165751636829 9743865496696937156863811)
                  ·
                    refine ⟨14615798245045405735295717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9743865496696937156863811 14615798245045405735295717)
                    ·
                      refine ⟨2740462170946013575367947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14615798245045405735295717 2740462170946013575367947)
                      ·
                        rfl

theorem cell23_5337031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 4, 3, 1, 4].length) (baseStart_5337031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5337031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5337031 prefixEnd_5337031 := by exact prefixLift 5337031
  have htrace : WordTrace (prefixWord ++ tailWord_5337031) baseStart_5337031 baseEnd_5337031 := by
    simpa [prefixWord, tailWord_5337031, baseEnd_5337031] using wordTrace_append hprefix tailTrace_5337031
  have hstable : (prefixWord ++ tailWord_5337031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5337031).length < 2 ^ (prefixWord ++ tailWord_5337031).sum := by decide
  have hdescent : baseEnd_5337031 < baseStart_5337031 := by decide
  rcases family_descends (prefixWord ++ tailWord_5337031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5337041 : List Nat := [1, 2, 2, 1, 2, 1, 2, 2, 6, 4]
def baseStart_5337041 : Nat := 118140960795 + 5337041 * 2 ^ 59
def prefixEnd_5337041 : Nat := 4983230072969 + 3 ^ 40 * 5337041 * 2
def baseEnd_5337041 : Nat := 913489101917519512080967

theorem tailTrace_5337041 : CollatzResearch.WordTrace tailWord_5337041 prefixEnd_5337041 913489101917519512080967 := by
  unfold tailWord_5337041
  simp only [CollatzResearch.WordTrace]
  refine ⟨194657877057819425880162977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129771918038546283920108651 194657877057819425880162977)
  ·
    refine ⟨145993407793364569410122233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 194657877057819425880162977 145993407793364569410122233)
    ·
      refine ⟨109495055845023427057591675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 145993407793364569410122233 109495055845023427057591675)
      ·
        refine ⟨164242583767535140586387513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109495055845023427057591675 164242583767535140586387513)
        ·
          refine ⟨123181937825651355439790635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 164242583767535140586387513 123181937825651355439790635)
          ·
            refine ⟨184772906738477033159685953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 123181937825651355439790635 184772906738477033159685953)
            ·
              refine ⟨138579680053857774869764465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 184772906738477033159685953 138579680053857774869764465)
              ·
                refine ⟨103934760040393331152323349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 138579680053857774869764465 103934760040393331152323349)
                ·
                  refine ⟨4871941876893437397765157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 103934760040393331152323349 4871941876893437397765157)
                  ·
                    refine ⟨913489101917519512080967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4871941876893437397765157 913489101917519512080967)
                    ·
                      rfl

theorem cell23_5337041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 2, 6, 4].length) (baseStart_5337041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5337041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5337041 prefixEnd_5337041 := by exact prefixLift 5337041
  have htrace : WordTrace (prefixWord ++ tailWord_5337041) baseStart_5337041 baseEnd_5337041 := by
    simpa [prefixWord, tailWord_5337041, baseEnd_5337041] using wordTrace_append hprefix tailTrace_5337041
  have hstable : (prefixWord ++ tailWord_5337041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5337041).length < 2 ^ (prefixWord ++ tailWord_5337041).sum := by decide
  have hdescent : baseEnd_5337041 < baseStart_5337041 := by decide
  rcases family_descends (prefixWord ++ tailWord_5337041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5337045 : List Nat := [1, 3, 2, 3, 2, 3, 1, 2, 1, 5]
def baseStart_5337045 : Nat := 118140960795 + 5337045 * 2 ^ 59
def prefixEnd_5337045 : Nat := 4983230072969 + 3 ^ 40 * 5337045 * 2
def baseEnd_5337045 : Nat := 913489786558392173530961

theorem tailTrace_5337045 : CollatzResearch.WordTrace tailWord_5337045 prefixEnd_5337045 913489786558392173530961 := by
  unfold tailWord_5337045
  simp only [CollatzResearch.WordTrace]
  refine ⟨194658022949804934563308589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129772015299869956375539059 194658022949804934563308589)
  ·
    refine ⟨72996758606176850461240721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 194658022949804934563308589 72996758606176850461240721)
    ·
      refine ⟨54747568954632637845930541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72996758606176850461240721 54747568954632637845930541)
      ·
        refine ⟨20530338357987239192223953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54747568954632637845930541 20530338357987239192223953)
        ·
          refine ⟨15397753768490429394167965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20530338357987239192223953 15397753768490429394167965)
          ·
            refine ⟨5774157663183911022812987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15397753768490429394167965 5774157663183911022812987)
            ·
              refine ⟨8661236494775866534219481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5774157663183911022812987 8661236494775866534219481)
              ·
                refine ⟨6495927371081899900664611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8661236494775866534219481 6495927371081899900664611)
                ·
                  refine ⟨9743891056622849850996917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6495927371081899900664611 9743891056622849850996917)
                  ·
                    refine ⟨913489786558392173530961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9743891056622849850996917 913489786558392173530961)
                    ·
                      rfl

theorem cell23_5337045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 3, 1, 2, 1, 5].length) (baseStart_5337045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5337045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5337045 prefixEnd_5337045 := by exact prefixLift 5337045
  have htrace : WordTrace (prefixWord ++ tailWord_5337045) baseStart_5337045 baseEnd_5337045 := by
    simpa [prefixWord, tailWord_5337045, baseEnd_5337045] using wordTrace_append hprefix tailTrace_5337045
  have hstable : (prefixWord ++ tailWord_5337045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5337045).length < 2 ^ (prefixWord ++ tailWord_5337045).sum := by decide
  have hdescent : baseEnd_5337045 < baseStart_5337045 := by decide
  rcases family_descends (prefixWord ++ tailWord_5337045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5337068 : List Nat := [2, 2, 1, 1, 2, 1, 1, 7, 1, 2, 3]
def baseStart_5337068 : Nat := 118140960795 + 5337068 * 2 ^ 59
def prefixEnd_5337068 : Nat := 4983230072969 + 3 ^ 40 * 5337068 * 2
def baseEnd_5337068 : Nat := 2740481169730229930605277

theorem tailTrace_5337068 : CollatzResearch.WordTrace tailWord_5337068 prefixEnd_5337068 2740481169730229930605277 := by
  unfold tailWord_5337068
  simp only [CollatzResearch.WordTrace]
  refine ⟨97329430914360804745697929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129772574552481072994263905 97329430914360804745697929)
  ·
    refine ⟨72997073185770603559273447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97329430914360804745697929 72997073185770603559273447)
    ·
      refine ⟨109495609778655905338910171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72997073185770603559273447 109495609778655905338910171)
      ·
        refine ⟨164243414667983858008365257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109495609778655905338910171 164243414667983858008365257)
        ·
          refine ⟨123182561000987893506273943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 164243414667983858008365257 123182561000987893506273943)
          ·
            refine ⟨184773841501481840259410915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 123182561000987893506273943 184773841501481840259410915)
            ·
              refine ⟨277160762252222760389116373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 184773841501481840259410915 277160762252222760389116373)
              ·
                refine ⟨6495955365286470946619915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 277160762252222760389116373 6495955365286470946619915)
                ·
                  refine ⟨9743933047929706419929873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6495955365286470946619915 9743933047929706419929873)
                  ·
                    refine ⟨7307949785947279814947405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9743933047929706419929873 7307949785947279814947405)
                    ·
                      refine ⟨2740481169730229930605277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7307949785947279814947405 2740481169730229930605277)
                      ·
                        rfl

theorem cell23_5337068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 2, 3].length) (baseStart_5337068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5337068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5337068 prefixEnd_5337068 := by exact prefixLift 5337068
  have htrace : WordTrace (prefixWord ++ tailWord_5337068) baseStart_5337068 baseEnd_5337068 := by
    simpa [prefixWord, tailWord_5337068, baseEnd_5337068] using wordTrace_append hprefix tailTrace_5337068
  have hstable : (prefixWord ++ tailWord_5337068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5337068).length < 2 ^ (prefixWord ++ tailWord_5337068).sum := by decide
  have hdescent : baseEnd_5337068 < baseStart_5337068 := by decide
  rcases family_descends (prefixWord ++ tailWord_5337068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5337161 : List Nat := [1, 2, 1, 1, 2, 2, 3, 4, 7]
def baseStart_5337161 : Nat := 118140960795 + 5337161 * 2 ^ 59
def prefixEnd_5337161 : Nat := 4983230072969 + 3 ^ 40 * 5337161 * 2
def baseEnd_5337161 : Nat := 304503213714566451860261

theorem tailTrace_5337161 : CollatzResearch.WordTrace tailWord_5337161 prefixEnd_5337161 304503213714566451860261 := by
  unfold tailWord_5337161
  simp only [CollatzResearch.WordTrace]
  refine ⟨194662253817384686374531337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129774835878256457583020891 194662253817384686374531337)
  ·
    refine ⟨145996690363038514780898503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 194662253817384686374531337 145996690363038514780898503)
    ·
      refine ⟨218995035544557772171347755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145996690363038514780898503 218995035544557772171347755)
      ·
        refine ⟨328492553316836658257021633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 218995035544557772171347755 328492553316836658257021633)
        ·
          refine ⟨246369414987627493692766225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 328492553316836658257021633 246369414987627493692766225)
          ·
            refine ⟨184777061240720620269574669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 246369414987627493692766225 184777061240720620269574669)
            ·
              refine ⟨69291397965270232601090501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 184777061240720620269574669 69291397965270232601090501)
              ·
                refine ⟨12992137118488168612704469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 69291397965270232601090501 12992137118488168612704469)
                ·
                  refine ⟨304503213714566451860261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12992137118488168612704469 304503213714566451860261)
                  ·
                    rfl

theorem cell23_5337161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 4, 7].length) (baseStart_5337161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5337161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5337161 prefixEnd_5337161 := by exact prefixLift 5337161
  have htrace : WordTrace (prefixWord ++ tailWord_5337161) baseStart_5337161 baseEnd_5337161 := by
    simpa [prefixWord, tailWord_5337161, baseEnd_5337161] using wordTrace_append hprefix tailTrace_5337161
  have hstable : (prefixWord ++ tailWord_5337161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5337161).length < 2 ^ (prefixWord ++ tailWord_5337161).sum := by decide
  have hdescent : baseEnd_5337161 < baseStart_5337161 := by decide
  rcases family_descends (prefixWord ++ tailWord_5337161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5337188 : List Nat := [2, 3, 1, 1, 2, 1, 2, 1, 4, 3, 3]
def baseStart_5337188 : Nat := 118140960795 + 5337188 * 2 ^ 59
def prefixEnd_5337188 : Nat := 4983230072969 + 3 ^ 40 * 5337188 * 2
def baseEnd_5337188 : Nat := 2740542787408769461104725

theorem tailTrace_5337188 : CollatzResearch.WordTrace tailWord_5337188 prefixEnd_5337188 2740542787408769461104725 := by
  unfold tailWord_5337188
  simp only [CollatzResearch.WordTrace]
  refine ⟨97331619294143434992882109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129775492392191246657176145 97331619294143434992882109)
  ·
    refine ⟨36499357235303788122330791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 97331619294143434992882109 36499357235303788122330791)
    ·
      refine ⟨54749035852955682183496187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36499357235303788122330791 54749035852955682183496187)
      ·
        refine ⟨82123553779433523275244281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54749035852955682183496187 82123553779433523275244281)
        ·
          refine ⟨61592665334575142456433211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82123553779433523275244281 61592665334575142456433211)
          ·
            refine ⟨92388998001862713684649817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61592665334575142456433211 92388998001862713684649817)
            ·
              refine ⟨69291748501397035263487363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 92388998001862713684649817 69291748501397035263487363)
              ·
                refine ⟨103937622752095552895231045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 69291748501397035263487363 103937622752095552895231045)
                ·
                  refine ⟨19488304266017916167855821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 103937622752095552895231045 19488304266017916167855821)
                  ·
                    refine ⟨7308114099756718562945933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19488304266017916167855821 7308114099756718562945933)
                    ·
                      refine ⟨2740542787408769461104725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7308114099756718562945933 2740542787408769461104725)
                      ·
                        rfl

theorem cell23_5337188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 1, 4, 3, 3].length) (baseStart_5337188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5337188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5337188 prefixEnd_5337188 := by exact prefixLift 5337188
  have htrace : WordTrace (prefixWord ++ tailWord_5337188) baseStart_5337188 baseEnd_5337188 := by
    simpa [prefixWord, tailWord_5337188, baseEnd_5337188] using wordTrace_append hprefix tailTrace_5337188
  have hstable : (prefixWord ++ tailWord_5337188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5337188).length < 2 ^ (prefixWord ++ tailWord_5337188).sum := by decide
  have hdescent : baseEnd_5337188 < baseStart_5337188 := by decide
  rcases family_descends (prefixWord ++ tailWord_5337188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5337206 : List Nat := [5, 1, 1, 2, 1, 2, 4, 1, 2, 2, 2]
def baseStart_5337206 : Nat := 118140960795 + 5337206 * 2 ^ 59
def prefixEnd_5337206 : Nat := 4983230072969 + 3 ^ 40 * 5337206 * 2
def baseEnd_5337206 : Nat := 2740552030060550390679643

theorem tailTrace_5337206 : CollatzResearch.WordTrace tailWord_5337206 prefixEnd_5337206 2740552030060550390679643 := by
  unfold tailWord_5337206
  simp only [CollatzResearch.WordTrace]
  refine ⟨12166493443888853691244967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 129775930068147772706612981 12166493443888853691244967)
  ·
    refine ⟨18249740165833280536867451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12166493443888853691244967 18249740165833280536867451)
    ·
      refine ⟨27374610248749920805301177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18249740165833280536867451 27374610248749920805301177)
      ·
        refine ⟨20530957686562440603975883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27374610248749920805301177 20530957686562440603975883)
        ·
          refine ⟨30796436529843660905963825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20530957686562440603975883 30796436529843660905963825)
          ·
            refine ⟨23097327397382745679472869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30796436529843660905963825 23097327397382745679472869)
            ·
              refine ⟨4330748887009264814901163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23097327397382745679472869 4330748887009264814901163)
              ·
                refine ⟨6496123330513897222351745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4330748887009264814901163 6496123330513897222351745)
                ·
                  refine ⟨4872092497885422916763809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6496123330513897222351745 4872092497885422916763809)
                  ·
                    refine ⟨3654069373414067187572857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4872092497885422916763809 3654069373414067187572857)
                    ·
                      refine ⟨2740552030060550390679643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3654069373414067187572857 2740552030060550390679643)
                      ·
                        rfl

theorem cell23_5337206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 4, 1, 2, 2, 2].length) (baseStart_5337206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5337206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5337206 prefixEnd_5337206 := by exact prefixLift 5337206
  have htrace : WordTrace (prefixWord ++ tailWord_5337206) baseStart_5337206 baseEnd_5337206 := by
    simpa [prefixWord, tailWord_5337206, baseEnd_5337206] using wordTrace_append hprefix tailTrace_5337206
  have hstable : (prefixWord ++ tailWord_5337206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5337206).length < 2 ^ (prefixWord ++ tailWord_5337206).sum := by decide
  have hdescent : baseEnd_5337206 < baseStart_5337206 := by decide
  rcases family_descends (prefixWord ++ tailWord_5337206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5337245 : List Nat := [1, 4, 2, 1, 1, 3, 2, 2, 2, 1, 4]
def baseStart_5337245 : Nat := 118140960795 + 5337245 * 2 ^ 59
def prefixEnd_5337245 : Nat := 4983230072969 + 3 ^ 40 * 5337245 * 2
def baseEnd_5337245 : Nat := 2740572055806075738091963

theorem tailTrace_5337245 : CollatzResearch.WordTrace tailWord_5337245 prefixEnd_5337245 2740572055806075738091963 := by
  unfold tailWord_5337245
  simp only [CollatzResearch.WordTrace]
  refine ⟨194665317549080368720589189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129776878366053579147059459 194665317549080368720589189)
  ·
    refine ⟨36499747040452569135110473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 194665317549080368720589189 36499747040452569135110473)
    ·
      refine ⟨27374810280339426851332855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36499747040452569135110473 27374810280339426851332855)
      ·
        refine ⟨41062215420509140276999283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27374810280339426851332855 41062215420509140276999283)
        ·
          refine ⟨61593323130763710415498925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41062215420509140276999283 61593323130763710415498925)
          ·
            refine ⟨23097496174036391405812097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 61593323130763710415498925 23097496174036391405812097)
            ·
              refine ⟨17323122130527293554359073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23097496174036391405812097 17323122130527293554359073)
              ·
                refine ⟨12992341597895470165769305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17323122130527293554359073 12992341597895470165769305)
                ·
                  refine ⟨9744256198421602624326979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12992341597895470165769305 9744256198421602624326979)
                  ·
                    refine ⟨14616384297632403936490469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9744256198421602624326979 14616384297632403936490469)
                    ·
                      refine ⟨2740572055806075738091963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14616384297632403936490469 2740572055806075738091963)
                      ·
                        rfl

theorem cell23_5337245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 2, 2, 2, 1, 4].length) (baseStart_5337245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5337245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5337245 prefixEnd_5337245 := by exact prefixLift 5337245
  have htrace : WordTrace (prefixWord ++ tailWord_5337245) baseStart_5337245 baseEnd_5337245 := by
    simpa [prefixWord, tailWord_5337245, baseEnd_5337245] using wordTrace_append hprefix tailTrace_5337245
  have hstable : (prefixWord ++ tailWord_5337245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5337245).length < 2 ^ (prefixWord ++ tailWord_5337245).sum := by decide
  have hdescent : baseEnd_5337245 < baseStart_5337245 := by decide
  rcases family_descends (prefixWord ++ tailWord_5337245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5337246 : List Nat := [4, 3, 1, 1, 3, 2, 2, 2, 5]
def baseStart_5337246 : Nat := 118140960795 + 5337246 * 2 ^ 59
def prefixEnd_5337246 : Nat := 4983230072969 + 3 ^ 40 * 5337246 * 2
def baseEnd_5337246 : Nat := 304508063254081137131051

theorem tailTrace_5337246 : CollatzResearch.WordTrace tailWord_5337246 prefixEnd_5337246 304508063254081137131051 := by
  unfold tailWord_5337246
  simp only [CollatzResearch.WordTrace]
  refine ⟨24333169252759593236421949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 129776902681384497260917061 24333169252759593236421949)
  ·
    refine ⟨9124938469784847463658231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24333169252759593236421949 9124938469784847463658231)
    ·
      refine ⟨13687407704677271195487347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9124938469784847463658231 13687407704677271195487347)
      ·
        refine ⟨20531111557015906793231021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13687407704677271195487347 20531111557015906793231021)
        ·
          refine ⟨7699166833880965047461633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20531111557015906793231021 7699166833880965047461633)
          ·
            refine ⟨5774375125410723785596225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7699166833880965047461633 5774375125410723785596225)
            ·
              refine ⟨4330781344058042839197169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5774375125410723785596225 4330781344058042839197169)
              ·
                refine ⟨3248086008043532129397877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4330781344058042839197169 3248086008043532129397877)
                ·
                  refine ⟨304508063254081137131051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3248086008043532129397877 304508063254081137131051)
                  ·
                    rfl

theorem cell23_5337246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 2, 2, 2, 5].length) (baseStart_5337246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5337246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5337246 prefixEnd_5337246 := by exact prefixLift 5337246
  have htrace : WordTrace (prefixWord ++ tailWord_5337246) baseStart_5337246 baseEnd_5337246 := by
    simpa [prefixWord, tailWord_5337246, baseEnd_5337246] using wordTrace_append hprefix tailTrace_5337246
  have hstable : (prefixWord ++ tailWord_5337246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5337246).length < 2 ^ (prefixWord ++ tailWord_5337246).sum := by decide
  have hdescent : baseEnd_5337246 < baseStart_5337246 := by decide
  rcases family_descends (prefixWord ++ tailWord_5337246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5337295 : List Nat := [1, 1, 2, 1, 1, 3, 3, 2, 5, 1, 3]
def baseStart_5337295 : Nat := 118140960795 + 5337295 * 2 ^ 59
def prefixEnd_5337295 : Nat := 4983230072969 + 3 ^ 40 * 5337295 * 2
def baseEnd_5337295 : Nat := 2740597729838800542466733

theorem tailTrace_5337295 : CollatzResearch.WordTrace tailWord_5337295 prefixEnd_5337295 2740597729838800542466733 := by
  unfold tailWord_5337295
  simp only [CollatzResearch.WordTrace]
  refine ⟨194667141198899227259909339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129778094132599484839939559 194667141198899227259909339)
  ·
    refine ⟨292000711798348840889864009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194667141198899227259909339 292000711798348840889864009)
    ·
      refine ⟨219000533848761630667398007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 292000711798348840889864009 219000533848761630667398007)
      ·
        refine ⟨328500800773142446001097011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 219000533848761630667398007 328500800773142446001097011)
        ·
          refine ⟨492751201159713669001645517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 328500800773142446001097011 492751201159713669001645517)
          ·
            refine ⟨184781700434892625875617069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 492751201159713669001645517 184781700434892625875617069)
            ·
              refine ⟨69293137663084734703356401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 184781700434892625875617069 69293137663084734703356401)
              ·
                refine ⟨51969853247313551027517301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 69293137663084734703356401 51969853247313551027517301)
                ·
                  refine ⟨4872173741935645408829747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 51969853247313551027517301 4872173741935645408829747)
                  ·
                    refine ⟨7308260612903468113244621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4872173741935645408829747 7308260612903468113244621)
                    ·
                      refine ⟨2740597729838800542466733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7308260612903468113244621 2740597729838800542466733)
                      ·
                        rfl

theorem cell23_5337295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 2, 5, 1, 3].length) (baseStart_5337295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5337295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5337295 prefixEnd_5337295 := by exact prefixLift 5337295
  have htrace : WordTrace (prefixWord ++ tailWord_5337295) baseStart_5337295 baseEnd_5337295 := by
    simpa [prefixWord, tailWord_5337295, baseEnd_5337295] using wordTrace_append hprefix tailTrace_5337295
  have hstable : (prefixWord ++ tailWord_5337295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5337295).length < 2 ^ (prefixWord ++ tailWord_5337295).sum := by decide
  have hdescent : baseEnd_5337295 < baseStart_5337295 := by decide
  rcases family_descends (prefixWord ++ tailWord_5337295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5337302 : List Nat := [5, 2, 1, 2, 1, 2, 1, 1, 8]
def baseStart_5337302 : Nat := 118140960795 + 5337302 * 2 ^ 59
def prefixEnd_5337302 : Nat := 4983230072969 + 3 ^ 40 * 5337302 * 2
def baseEnd_5337302 : Nat := 304511258244820223897689

theorem tailTrace_5337302 : CollatzResearch.WordTrace tailWord_5337302 prefixEnd_5337302 304511258244820223897689 := by
  unfold tailWord_5337302
  simp only [CollatzResearch.WordTrace]
  refine ⟨12166712281867116715963385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 129778264339915911636942773 12166712281867116715963385)
  ·
    refine ⟨9125034211400337536972539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12166712281867116715963385 9125034211400337536972539)
    ·
      refine ⟨13687551317100506305458809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9125034211400337536972539 13687551317100506305458809)
      ·
        refine ⟨10265663487825379729094107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13687551317100506305458809 10265663487825379729094107)
        ·
          refine ⟨15398495231738069593641161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10265663487825379729094107 15398495231738069593641161)
          ·
            refine ⟨11548871423803552195230871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15398495231738069593641161 11548871423803552195230871)
            ·
              refine ⟨17323307135705328292846307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11548871423803552195230871 17323307135705328292846307)
              ·
                refine ⟨25984960703557992439269461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17323307135705328292846307 25984960703557992439269461)
                ·
                  refine ⟨304511258244820223897689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 25984960703557992439269461 304511258244820223897689)
                  ·
                    rfl

theorem cell23_5337302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 1, 1, 8].length) (baseStart_5337302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5337302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5337302 prefixEnd_5337302 := by exact prefixLift 5337302
  have htrace : WordTrace (prefixWord ++ tailWord_5337302) baseStart_5337302 baseEnd_5337302 := by
    simpa [prefixWord, tailWord_5337302, baseEnd_5337302] using wordTrace_append hprefix tailTrace_5337302
  have hstable : (prefixWord ++ tailWord_5337302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5337302).length < 2 ^ (prefixWord ++ tailWord_5337302).sum := by decide
  have hdescent : baseEnd_5337302 < baseStart_5337302 := by decide
  rcases family_descends (prefixWord ++ tailWord_5337302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5337312 : List Nat := [2, 1, 1, 3, 1, 3, 4, 1, 3, 1, 3]
def baseStart_5337312 : Nat := 118140960795 + 5337312 * 2 ^ 59
def prefixEnd_5337312 : Nat := 4983230072969 + 3 ^ 40 * 5337312 * 2
def baseEnd_5337312 : Nat := 2740606459009926975954155

theorem tailTrace_5337312 : CollatzResearch.WordTrace tailWord_5337312 prefixEnd_5337312 2740606459009926975954155 := by
  unfold tailWord_5337312
  simp only [CollatzResearch.WordTrace]
  refine ⟨97333880619918819581639095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129778507493225092775518793 97333880619918819581639095)
  ·
    refine ⟨146000820929878229372458643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97333880619918819581639095 146000820929878229372458643)
    ·
      refine ⟨219001231394817344058687965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146000820929878229372458643 219001231394817344058687965)
      ·
        refine ⟨82125461773056504022007987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 219001231394817344058687965 82125461773056504022007987)
        ·
          refine ⟨123188192659584756033011981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82125461773056504022007987 123188192659584756033011981)
          ·
            refine ⟨46195572247344283512379493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 123188192659584756033011981 46195572247344283512379493)
            ·
              refine ⟨8661669796377053158571155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 46195572247344283512379493 8661669796377053158571155)
              ·
                refine ⟨12992504694565579737856733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8661669796377053158571155 12992504694565579737856733)
                ·
                  refine ⟨4872189260462092401696275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12992504694565579737856733 4872189260462092401696275)
                  ·
                    refine ⟨7308283890693138602544413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4872189260462092401696275 7308283890693138602544413)
                    ·
                      refine ⟨2740606459009926975954155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7308283890693138602544413 2740606459009926975954155)
                      ·
                        rfl

theorem cell23_5337312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 4, 1, 3, 1, 3].length) (baseStart_5337312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5337312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5337312 prefixEnd_5337312 := by exact prefixLift 5337312
  have htrace : WordTrace (prefixWord ++ tailWord_5337312) baseStart_5337312 baseEnd_5337312 := by
    simpa [prefixWord, tailWord_5337312, baseEnd_5337312] using wordTrace_append hprefix tailTrace_5337312
  have hstable : (prefixWord ++ tailWord_5337312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5337312).length < 2 ^ (prefixWord ++ tailWord_5337312).sum := by decide
  have hdescent : baseEnd_5337312 < baseStart_5337312 := by decide
  rcases family_descends (prefixWord ++ tailWord_5337312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5337345 : List Nat := [1, 2, 4, 1, 1, 2, 1, 1, 6, 4]
def baseStart_5337345 : Nat := 118140960795 + 5337345 * 2 ^ 59
def prefixEnd_5337345 : Nat := 4983230072969 + 3 ^ 40 * 5337345 * 2
def baseEnd_5337345 : Nat := 913541134623841782280501

theorem tailTrace_5337345 : CollatzResearch.WordTrace tailWord_5337345 prefixEnd_5337345 913541134623841782280501 := by
  unfold tailWord_5337345
  simp only [CollatzResearch.WordTrace]
  refine ⟨194668964848718085799229489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129779309899145390532819659 194668964848718085799229489)
  ·
    refine ⟨146001723636538564349422117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 194668964848718085799229489 146001723636538564349422117)
    ·
      refine ⟨27375323181850980815516647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 146001723636538564349422117 27375323181850980815516647)
      ·
        refine ⟨41062984772776471223274971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27375323181850980815516647 41062984772776471223274971)
        ·
          refine ⟨61594477159164706834912457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41062984772776471223274971 61594477159164706834912457)
          ·
            refine ⟨46195857869373530126184343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61594477159164706834912457 46195857869373530126184343)
            ·
              refine ⟨69293786804060295189276515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46195857869373530126184343 69293786804060295189276515)
              ·
                refine ⟨103940680206090442783914773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 69293786804060295189276515 103940680206090442783914773)
                ·
                  refine ⟨4872219384660489505496005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 103940680206090442783914773 4872219384660489505496005)
                  ·
                    refine ⟨913541134623841782280501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4872219384660489505496005 913541134623841782280501)
                    ·
                      rfl

theorem cell23_5337345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 1, 6, 4].length) (baseStart_5337345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5337345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5337345 prefixEnd_5337345 := by exact prefixLift 5337345
  have htrace : WordTrace (prefixWord ++ tailWord_5337345) baseStart_5337345 baseEnd_5337345 := by
    simpa [prefixWord, tailWord_5337345, baseEnd_5337345] using wordTrace_append hprefix tailTrace_5337345
  have hstable : (prefixWord ++ tailWord_5337345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5337345).length < 2 ^ (prefixWord ++ tailWord_5337345).sum := by decide
  have hdescent : baseEnd_5337345 < baseStart_5337345 := by decide
  rcases family_descends (prefixWord ++ tailWord_5337345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5337352 : List Nat := [2, 1, 3, 2, 3, 1, 2, 3, 1, 1, 4]
def baseStart_5337352 : Nat := 118140960795 + 5337352 * 2 ^ 59
def prefixEnd_5337352 : Nat := 4983230072969 + 3 ^ 40 * 5337352 * 2
def baseEnd_5337352 : Nat := 2740626998236106819453971

theorem tailTrace_5337352 : CollatzResearch.WordTrace tailWord_5337352 prefixEnd_5337352 2740626998236106819453971 := by
  unfold tailWord_5337352
  simp only [CollatzResearch.WordTrace]
  refine ⟨97334610079846362997367155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129779480106461817329822873 97334610079846362997367155)
  ·
    refine ⟨146001915119769544496050733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97334610079846362997367155 146001915119769544496050733)
    ·
      refine ⟨54750718169913579186019025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 146001915119769544496050733 54750718169913579186019025)
      ·
        refine ⟨41063038627435184389514269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54750718169913579186019025 41063038627435184389514269)
        ·
          refine ⟨15398639485288194146067851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41063038627435184389514269 15398639485288194146067851)
          ·
            refine ⟨23097959227932291219101777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15398639485288194146067851 23097959227932291219101777)
            ·
              refine ⟨17323469420949218414326333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23097959227932291219101777 17323469420949218414326333)
              ·
                refine ⟨6496301032855956905372375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17323469420949218414326333 6496301032855956905372375)
                ·
                  refine ⟨9744451549283935358058563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6496301032855956905372375 9744451549283935358058563)
                  ·
                    refine ⟨14616677323925903037087845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9744451549283935358058563 14616677323925903037087845)
                    ·
                      refine ⟨2740626998236106819453971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14616677323925903037087845 2740626998236106819453971)
                      ·
                        rfl

theorem cell23_5337352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 2, 3, 1, 1, 4].length) (baseStart_5337352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5337352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5337352 prefixEnd_5337352 := by exact prefixLift 5337352
  have htrace : WordTrace (prefixWord ++ tailWord_5337352) baseStart_5337352 baseEnd_5337352 := by
    simpa [prefixWord, tailWord_5337352, baseEnd_5337352] using wordTrace_append hprefix tailTrace_5337352
  have hstable : (prefixWord ++ tailWord_5337352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5337352).length < 2 ^ (prefixWord ++ tailWord_5337352).sum := by decide
  have hdescent : baseEnd_5337352 < baseStart_5337352 := by decide
  rcases family_descends (prefixWord ++ tailWord_5337352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5337355 : List Nat := [1, 1, 1, 1, 5, 2, 4, 1, 1, 1, 5]
def baseStart_5337355 : Nat := 118140960795 + 5337355 * 2 ^ 59
def prefixEnd_5337355 : Nat := 4983230072969 + 3 ^ 40 * 5337355 * 2
def baseEnd_5337355 : Nat := 2740628538678070307716457

theorem tailTrace_5337355 : CollatzResearch.WordTrace tailWord_5337355 prefixEnd_5337355 2740628538678070307716457 := by
  unfold tailWord_5337355
  simp only [CollatzResearch.WordTrace]
  refine ⟨194669329578681857507093519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129779553052454571671395679 194669329578681857507093519)
  ·
    refine ⟨292003994368022786260640279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194669329578681857507093519 292003994368022786260640279)
    ·
      refine ⟨438005991552034179390960419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 292003994368022786260640279 438005991552034179390960419)
      ·
        refine ⟨657008987328051269086440629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 438005991552034179390960419 657008987328051269086440629)
        ·
          refine ⟨61594592562004806476853809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 657008987328051269086440629 61594592562004806476853809)
          ·
            refine ⟨46195944421503604857640357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61594592562004806476853809 46195944421503604857640357)
            ·
              refine ⟨8661739579031925910807567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 46195944421503604857640357 8661739579031925910807567)
              ·
                refine ⟨12992609368547888866211351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8661739579031925910807567 12992609368547888866211351)
                ·
                  refine ⟨19488914052821833299317027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12992609368547888866211351 19488914052821833299317027)
                  ·
                    refine ⟨29233371079232749948975541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19488914052821833299317027 29233371079232749948975541)
                    ·
                      refine ⟨2740628538678070307716457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29233371079232749948975541 2740628538678070307716457)
                      ·
                        rfl

theorem cell23_5337355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 4, 1, 1, 1, 5].length) (baseStart_5337355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5337355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5337355 prefixEnd_5337355 := by exact prefixLift 5337355
  have htrace : WordTrace (prefixWord ++ tailWord_5337355) baseStart_5337355 baseEnd_5337355 := by
    simpa [prefixWord, tailWord_5337355, baseEnd_5337355] using wordTrace_append hprefix tailTrace_5337355
  have hstable : (prefixWord ++ tailWord_5337355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5337355).length < 2 ^ (prefixWord ++ tailWord_5337355).sum := by decide
  have hdescent : baseEnd_5337355 < baseStart_5337355 := by decide
  rcases family_descends (prefixWord ++ tailWord_5337355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5337375 : List Nat := [1, 1, 2, 4, 3, 2, 2, 8]
def baseStart_5337375 : Nat := 118140960795 + 5337375 * 2 ^ 59
def prefixEnd_5337375 : Nat := 4983230072969 + 3 ^ 40 * 5337375 * 2
def baseEnd_5337375 : Nat := 101505141047820749239495

theorem tailTrace_5337375 : CollatzResearch.WordTrace tailWord_5337375 prefixEnd_5337375 101505141047820749239495 := by
  unfold tailWord_5337375
  simp only [CollatzResearch.WordTrace]
  refine ⟨194670059038609400922821579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129780039359072933948547719 194670059038609400922821579)
  ·
    refine ⟨292005088557914101384232369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194670059038609400922821579 292005088557914101384232369)
    ·
      refine ⟨219003816418435576038174277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 292005088557914101384232369 219003816418435576038174277)
      ·
        refine ⟨41063215578456670507157677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 219003816418435576038174277 41063215578456670507157677)
        ·
          refine ⟨15398705841921251440184129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41063215578456670507157677 15398705841921251440184129)
          ·
            refine ⟨11549029381440938580138097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15398705841921251440184129 11549029381440938580138097)
            ·
              refine ⟨8661772036080703935103573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11549029381440938580138097 8661772036080703935103573)
              ·
                refine ⟨101505141047820749239495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8661772036080703935103573 101505141047820749239495)
                ·
                  rfl

theorem cell23_5337375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 2, 8].length) (baseStart_5337375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5337375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5337375 prefixEnd_5337375 := by exact prefixLift 5337375
  have htrace : WordTrace (prefixWord ++ tailWord_5337375) baseStart_5337375 baseEnd_5337375 := by
    simpa [prefixWord, tailWord_5337375, baseEnd_5337375] using wordTrace_append hprefix tailTrace_5337375
  have hstable : (prefixWord ++ tailWord_5337375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5337375).length < 2 ^ (prefixWord ++ tailWord_5337375).sum := by decide
  have hdescent : baseEnd_5337375 < baseStart_5337375 := by decide
  rcases family_descends (prefixWord ++ tailWord_5337375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5337383 : List Nat := [1, 1, 8, 1, 1, 2, 1, 2, 1, 5]
def baseStart_5337383 : Nat := 118140960795 + 5337383 * 2 ^ 59
def prefixEnd_5337383 : Nat := 4983230072969 + 3 ^ 40 * 5337383 * 2
def baseEnd_5337383 : Nat := 913547638712132066055443

theorem tailTrace_5337383 : CollatzResearch.WordTrace tailWord_5337383 prefixEnd_5337383 913547638712132066055443 := by
  unfold tailWord_5337383
  simp only [CollatzResearch.WordTrace]
  refine ⟨194670350822580418289112803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129780233881720278859408535 194670350822580418289112803)
  ·
    refine ⟨292005526233870627433669205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194670350822580418289112803 292005526233870627433669205)
    ·
      refine ⟨3421939760553171415238311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 292005526233870627433669205 3421939760553171415238311)
      ·
        refine ⟨5132909640829757122857467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3421939760553171415238311 5132909640829757122857467)
        ·
          refine ⟨7699364461244635684286201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5132909640829757122857467 7699364461244635684286201)
          ·
            refine ⟨5774523345933476763214651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7699364461244635684286201 5774523345933476763214651)
            ·
              refine ⟨8661785018900215144821977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5774523345933476763214651 8661785018900215144821977)
              ·
                refine ⟨6496338764175161358616483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8661785018900215144821977 6496338764175161358616483)
                ·
                  refine ⟨9744508146262742037924725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6496338764175161358616483 9744508146262742037924725)
                  ·
                    refine ⟨913547638712132066055443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9744508146262742037924725 913547638712132066055443)
                    ·
                      rfl

theorem cell23_5337383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 2, 1, 2, 1, 5].length) (baseStart_5337383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5337383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5337383 prefixEnd_5337383 := by exact prefixLift 5337383
  have htrace : WordTrace (prefixWord ++ tailWord_5337383) baseStart_5337383 baseEnd_5337383 := by
    simpa [prefixWord, tailWord_5337383, baseEnd_5337383] using wordTrace_append hprefix tailTrace_5337383
  have hstable : (prefixWord ++ tailWord_5337383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5337383).length < 2 ^ (prefixWord ++ tailWord_5337383).sum := by decide
  have hdescent : baseEnd_5337383 < baseStart_5337383 := by decide
  rcases family_descends (prefixWord ++ tailWord_5337383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5337386 : List Nat := [3, 1, 4, 2, 2, 2, 1, 2, 1, 1, 4]
def baseStart_5337386 : Nat := 118140960795 + 5337386 * 2 ^ 59
def prefixEnd_5337386 : Nat := 4983230072969 + 3 ^ 40 * 5337386 * 2
def baseEnd_5337386 : Nat := 2740644456578359686428815

theorem tailTrace_5337386 : CollatzResearch.WordTrace tailWord_5337386 prefixEnd_5337386 2740644456578359686428815 := by
  unfold tailWord_5337386
  simp only [CollatzResearch.WordTrace]
  refine ⟨48667615060392387450368003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129780306827713033200981341 48667615060392387450368003)
  ·
    refine ⟨73001422590588581175552005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48667615060392387450368003 73001422590588581175552005)
    ·
      refine ⟨13687766735735358970416001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 73001422590588581175552005 13687766735735358970416001)
      ·
        refine ⟨10265825051801519227812001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13687766735735358970416001 10265825051801519227812001)
        ·
          refine ⟨7699368788851139420859001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10265825051801519227812001 7699368788851139420859001)
          ·
            refine ⟨5774526591638354565644251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7699368788851139420859001 5774526591638354565644251)
            ·
              refine ⟨8661789887457531848466377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5774526591638354565644251 8661789887457531848466377)
              ·
                refine ⟨6496342415593148886349783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8661789887457531848466377 6496342415593148886349783)
                ·
                  refine ⟨9744513623389723329524675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6496342415593148886349783 9744513623389723329524675)
                  ·
                    refine ⟨14616770435084584994287013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9744513623389723329524675 14616770435084584994287013)
                    ·
                      refine ⟨2740644456578359686428815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14616770435084584994287013 2740644456578359686428815)
                      ·
                        rfl

theorem cell23_5337386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 2, 1, 2, 1, 1, 4].length) (baseStart_5337386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5337386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5337386 prefixEnd_5337386 := by exact prefixLift 5337386
  have htrace : WordTrace (prefixWord ++ tailWord_5337386) baseStart_5337386 baseEnd_5337386 := by
    simpa [prefixWord, tailWord_5337386, baseEnd_5337386] using wordTrace_append hprefix tailTrace_5337386
  have hstable : (prefixWord ++ tailWord_5337386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5337386).length < 2 ^ (prefixWord ++ tailWord_5337386).sum := by decide
  have hdescent : baseEnd_5337386 < baseStart_5337386 := by decide
  rcases family_descends (prefixWord ++ tailWord_5337386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5337402 : List Nat := [3, 1, 1, 1, 4, 3, 1, 2, 1, 3, 3]
def baseStart_5337402 : Nat := 118140960795 + 5337402 * 2 ^ 59
def prefixEnd_5337402 : Nat := 4983230072969 + 3 ^ 40 * 5337402 * 2
def baseEnd_5337402 : Nat := 2740652672268831623828741

theorem tailTrace_5337402 : CollatzResearch.WordTrace tailWord_5337402 prefixEnd_5337402 2740652672268831623828741 := by
  unfold tailWord_5337402
  simp only [CollatzResearch.WordTrace]
  refine ⟨48667760952377896133513615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129780695873007723022702973 48667760952377896133513615)
  ·
    refine ⟨73001641428566844200270423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48667760952377896133513615 73001641428566844200270423)
    ·
      refine ⟨109502462142850266300405635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73001641428566844200270423 109502462142850266300405635)
      ·
        refine ⟨164253693214275399450608453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109502462142850266300405635 164253693214275399450608453)
        ·
          refine ⟨30797567477676637396989085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 164253693214275399450608453 30797567477676637396989085)
          ·
            refine ⟨11549087804128739023870907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30797567477676637396989085 11549087804128739023870907)
            ·
              refine ⟨17323631706193108535806361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11549087804128739023870907 17323631706193108535806361)
              ·
                refine ⟨12992723779644831401854771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17323631706193108535806361 12992723779644831401854771)
                ·
                  refine ⟨19489085669467247102782157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12992723779644831401854771 19489085669467247102782157)
                  ·
                    refine ⟨7308407126050217663543309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19489085669467247102782157 7308407126050217663543309)
                    ·
                      refine ⟨2740652672268831623828741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7308407126050217663543309 2740652672268831623828741)
                      ·
                        rfl

theorem cell23_5337402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 1, 2, 1, 3, 3].length) (baseStart_5337402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5337402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5337402 prefixEnd_5337402 := by exact prefixLift 5337402
  have htrace : WordTrace (prefixWord ++ tailWord_5337402) baseStart_5337402 baseEnd_5337402 := by
    simpa [prefixWord, tailWord_5337402, baseEnd_5337402] using wordTrace_append hprefix tailTrace_5337402
  have hstable : (prefixWord ++ tailWord_5337402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5337402).length < 2 ^ (prefixWord ++ tailWord_5337402).sum := by decide
  have hdescent : baseEnd_5337402 < baseStart_5337402 := by decide
  rcases family_descends (prefixWord ++ tailWord_5337402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5337406 : List Nat := [4, 2, 1, 2, 1, 3, 3, 1, 1, 2, 3]
def baseStart_5337406 : Nat := 118140960795 + 5337406 * 2 ^ 59
def prefixEnd_5337406 : Nat := 4983230072969 + 3 ^ 40 * 5337406 * 2
def baseEnd_5337406 : Nat := 2740654726191449608178723

theorem tailTrace_5337406 : CollatzResearch.WordTrace tailWord_5337406 prefixEnd_5337406 2740654726191449608178723 := by
  unfold tailWord_5337406
  simp only [CollatzResearch.WordTrace]
  refine ⟨24333898712687136652150009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 129780793134331395478133381 24333898712687136652150009)
  ·
    refine ⟨18250424034515352489112507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24333898712687136652150009 18250424034515352489112507)
    ·
      refine ⟨27375636051773028733668761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18250424034515352489112507 27375636051773028733668761)
      ·
        refine ⟨20531727038829771550251571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27375636051773028733668761 20531727038829771550251571)
        ·
          refine ⟨30797590558244657325377357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20531727038829771550251571 30797590558244657325377357)
          ·
            refine ⟨11549096459341746497016509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30797590558244657325377357 11549096459341746497016509)
            ·
              refine ⟨4330911172253154936381191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11549096459341746497016509 4330911172253154936381191)
              ·
                refine ⟨6496366758379732404571787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4330911172253154936381191 6496366758379732404571787)
                ·
                  refine ⟨9744550137569598606857681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6496366758379732404571787 9744550137569598606857681)
                  ·
                    refine ⟨7308412603177198955143261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9744550137569598606857681 7308412603177198955143261)
                    ·
                      refine ⟨2740654726191449608178723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7308412603177198955143261 2740654726191449608178723)
                      ·
                        rfl

theorem cell23_5337406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 3, 1, 1, 2, 3].length) (baseStart_5337406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5337406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5337406 prefixEnd_5337406 := by exact prefixLift 5337406
  have htrace : WordTrace (prefixWord ++ tailWord_5337406) baseStart_5337406 baseEnd_5337406 := by
    simpa [prefixWord, tailWord_5337406, baseEnd_5337406] using wordTrace_append hprefix tailTrace_5337406
  have hstable : (prefixWord ++ tailWord_5337406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5337406).length < 2 ^ (prefixWord ++ tailWord_5337406).sum := by decide
  have hdescent : baseEnd_5337406 < baseStart_5337406 := by decide
  rcases family_descends (prefixWord ++ tailWord_5337406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5337425 : List Nat := [1, 2, 2, 1, 4, 2, 1, 1, 2, 3, 4]
def baseStart_5337425 : Nat := 118140960795 + 5337425 * 2 ^ 59
def prefixEnd_5337425 : Nat := 4983230072969 + 3 ^ 40 * 5337425 * 2
def baseEnd_5337425 : Nat := 2740664482323885033841135

theorem tailTrace_5337425 : CollatzResearch.WordTrace tailWord_5337425 prefixEnd_5337425 2740664482323885033841135 := by
  unfold tailWord_5337425
  simp only [CollatzResearch.WordTrace]
  refine ⟨194671882688428259462141729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129781255125618839641427819 194671882688428259462141729)
  ·
    refine ⟨146003912016321194596606297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 194671882688428259462141729 146003912016321194596606297)
    ·
      refine ⟨109502934012240895947454723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 146003912016321194596606297 109502934012240895947454723)
      ·
        refine ⟨164254401018361343921182085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109502934012240895947454723 164254401018361343921182085)
        ·
          refine ⟨30797700190942751985221641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 164254401018361343921182085 30797700190942751985221641)
          ·
            refine ⟨23098275143207063988916231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30797700190942751985221641 23098275143207063988916231)
            ·
              refine ⟨34647412714810595983374347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23098275143207063988916231 34647412714810595983374347)
              ·
                refine ⟨51971119072215893975061521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34647412714810595983374347 51971119072215893975061521)
                ·
                  refine ⟨38978339304161920481296141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 51971119072215893975061521 38978339304161920481296141)
                  ·
                    refine ⟨14616877239060720180486053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 38978339304161920481296141 14616877239060720180486053)
                    ·
                      refine ⟨2740664482323885033841135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14616877239060720180486053 2740664482323885033841135)
                      ·
                        rfl

theorem cell23_5337425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 1, 1, 2, 3, 4].length) (baseStart_5337425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5337425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5337425 prefixEnd_5337425 := by exact prefixLift 5337425
  have htrace : WordTrace (prefixWord ++ tailWord_5337425) baseStart_5337425 baseEnd_5337425 := by
    simpa [prefixWord, tailWord_5337425, baseEnd_5337425] using wordTrace_append hprefix tailTrace_5337425
  have hstable : (prefixWord ++ tailWord_5337425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5337425).length < 2 ^ (prefixWord ++ tailWord_5337425).sum := by decide
  have hdescent : baseEnd_5337425 < baseStart_5337425 := by decide
  rcases family_descends (prefixWord ++ tailWord_5337425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5337436 : List Nat := [2, 2, 4, 3, 1, 1, 2, 1, 1, 3, 3]
def baseStart_5337436 : Nat := 118140960795 + 5337436 * 2 ^ 59
def prefixEnd_5337436 : Nat := 4983230072969 + 3 ^ 40 * 5337436 * 2
def baseEnd_5337436 : Nat := 2740670130611084490803585

theorem tailTrace_5337436 : CollatzResearch.WordTrace tailWord_5337436 prefixEnd_5337436 2740670130611084490803585 := by
  unfold tailWord_5337436
  simp only [CollatzResearch.WordTrace]
  refine ⟨97336141945694204170396081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129781522594258938893861441 97336141945694204170396081)
  ·
    refine ⟨73002106459270653127797061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97336141945694204170396081 73002106459270653127797061)
    ·
      refine ⟨13687894961113247461461949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 73002106459270653127797061 13687894961113247461461949)
      ·
        refine ⟨5132960610417467798048231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13687894961113247461461949 5132960610417467798048231)
        ·
          refine ⟨7699440915626201697072347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5132960610417467798048231 7699440915626201697072347)
          ·
            refine ⟨11549161373439302545608521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7699440915626201697072347 11549161373439302545608521)
            ·
              refine ⟨8661871030079476909206391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11549161373439302545608521 8661871030079476909206391)
              ·
                refine ⟨12992806545119215363809587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8661871030079476909206391 12992806545119215363809587)
                ·
                  refine ⟨19489209817678823045714381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12992806545119215363809587 19489209817678823045714381)
                  ·
                    refine ⟨7308453681629558642142893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19489209817678823045714381 7308453681629558642142893)
                    ·
                      refine ⟨2740670130611084490803585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7308453681629558642142893 2740670130611084490803585)
                      ·
                        rfl

theorem cell23_5337436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 2, 1, 1, 3, 3].length) (baseStart_5337436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5337436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5337436 prefixEnd_5337436 := by exact prefixLift 5337436
  have htrace : WordTrace (prefixWord ++ tailWord_5337436) baseStart_5337436 baseEnd_5337436 := by
    simpa [prefixWord, tailWord_5337436, baseEnd_5337436] using wordTrace_append hprefix tailTrace_5337436
  have hstable : (prefixWord ++ tailWord_5337436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5337436).length < 2 ^ (prefixWord ++ tailWord_5337436).sum := by decide
  have hdescent : baseEnd_5337436 < baseStart_5337436 := by decide
  rcases family_descends (prefixWord ++ tailWord_5337436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5337495 : List Nat := [1, 1, 3, 3, 1, 1, 3, 2, 1, 7]
def baseStart_5337495 : Nat := 118140960795 + 5337495 * 2 ^ 59
def prefixEnd_5337495 : Nat := 4983230072969 + 3 ^ 40 * 5337495 * 2
def baseEnd_5337495 : Nat := 913566808656566586655271

theorem tailTrace_5337495 : CollatzResearch.WordTrace tailWord_5337495 prefixEnd_5337495 913566808656566586655271 := by
  unfold tailWord_5337495
  simp only [CollatzResearch.WordTrace]
  refine ⟨194674435798174661417189939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129782957198783107611459959 194674435798174661417189939)
  ·
    refine ⟨292011653697261992125784909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194674435798174661417189939 292011653697261992125784909)
    ·
      refine ⟨109504370136473247047169341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 292011653697261992125784909 109504370136473247047169341)
      ·
        refine ⟨41064138801177467642688503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 109504370136473247047169341 41064138801177467642688503)
        ·
          refine ⟨61596208201766201464032755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41064138801177467642688503 61596208201766201464032755)
          ·
            refine ⟨92394312302649302196049133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61596208201766201464032755 92394312302649302196049133)
            ·
              refine ⟨34647867113493488323518425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 92394312302649302196049133 34647867113493488323518425)
              ·
                refine ⟨25985900335120116242638819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34647867113493488323518425 25985900335120116242638819)
                ·
                  refine ⟨38978850502680174363958229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25985900335120116242638819 38978850502680174363958229)
                  ·
                    refine ⟨913566808656566586655271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 38978850502680174363958229 913566808656566586655271)
                    ·
                      rfl

theorem cell23_5337495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 3, 2, 1, 7].length) (baseStart_5337495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5337495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5337495 prefixEnd_5337495 := by exact prefixLift 5337495
  have htrace : WordTrace (prefixWord ++ tailWord_5337495) baseStart_5337495 baseEnd_5337495 := by
    simpa [prefixWord, tailWord_5337495, baseEnd_5337495] using wordTrace_append hprefix tailTrace_5337495
  have hstable : (prefixWord ++ tailWord_5337495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5337495).length < 2 ^ (prefixWord ++ tailWord_5337495).sum := by decide
  have hdescent : baseEnd_5337495 < baseStart_5337495 := by decide
  rcases family_descends (prefixWord ++ tailWord_5337495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5337545 : List Nat := [1, 2, 1, 1, 2, 1, 4, 2, 2, 1, 6]
def baseStart_5337545 : Nat := 118140960795 + 5337545 * 2 ^ 59
def prefixEnd_5337545 : Nat := 4983230072969 + 3 ^ 40 * 5337545 * 2
def baseEnd_5337545 : Nat := 2740726100002424564340583

theorem tailTrace_5337545 : CollatzResearch.WordTrace tailWord_5337545 prefixEnd_5337545 2740726100002424564340583 := by
  unfold tailWord_5337545
  simp only [CollatzResearch.WordTrace]
  refine ⟨194676259447993519956510089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129784172965329013304340059 194676259447993519956510089)
  ·
    refine ⟨146007194585995139967382567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 194676259447993519956510089 146007194585995139967382567)
    ·
      refine ⟨219010791878992709951073851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146007194585995139967382567 219010791878992709951073851)
      ·
        refine ⟨328516187818489064926610777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 219010791878992709951073851 328516187818489064926610777)
        ·
          refine ⟨246387140863866798694958083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 328516187818489064926610777 246387140863866798694958083)
          ·
            refine ⟨369580711295800198042437125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 246387140863866798694958083 369580711295800198042437125)
            ·
              refine ⟨69296383367962537132956961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 369580711295800198042437125 69296383367962537132956961)
              ·
                refine ⟨51972287525971902849717721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 69296383367962537132956961 51972287525971902849717721)
                ·
                  refine ⟨38979215644478927137288291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 51972287525971902849717721 38979215644478927137288291)
                  ·
                    refine ⟨58468823466718390705932437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 38979215644478927137288291 58468823466718390705932437)
                    ·
                      refine ⟨2740726100002424564340583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 58468823466718390705932437 2740726100002424564340583)
                      ·
                        rfl

theorem cell23_5337545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 2, 2, 1, 6].length) (baseStart_5337545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5337545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5337545 prefixEnd_5337545 := by exact prefixLift 5337545
  have htrace : WordTrace (prefixWord ++ tailWord_5337545) baseStart_5337545 baseEnd_5337545 := by
    simpa [prefixWord, tailWord_5337545, baseEnd_5337545] using wordTrace_append hprefix tailTrace_5337545
  have hstable : (prefixWord ++ tailWord_5337545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5337545).length < 2 ^ (prefixWord ++ tailWord_5337545).sum := by decide
  have hdescent : baseEnd_5337545 < baseStart_5337545 := by decide
  rcases family_descends (prefixWord ++ tailWord_5337545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5337569 : List Nat := [1, 2, 3, 1, 2, 2, 4, 1, 2, 2, 3]
def baseStart_5337569 : Nat := 118140960795 + 5337569 * 2 ^ 59
def prefixEnd_5337569 : Nat := 4983230072969 + 3 ^ 40 * 5337569 * 2
def baseEnd_5337569 : Nat := 2740738423538132470440473

theorem tailTrace_5337569 : CollatzResearch.WordTrace tailWord_5337569 prefixEnd_5337569 2740738423538132470440473 := by
  unfold tailWord_5337569
  simp only [CollatzResearch.WordTrace]
  refine ⟨194677134799906572055383761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129784756533271048036922507 194677134799906572055383761)
  ·
    refine ⟨146007851099929929041537821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 194677134799906572055383761 146007851099929929041537821)
    ·
      refine ⟨54752944162473723390576683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 146007851099929929041537821 54752944162473723390576683)
      ·
        refine ⟨82129416243710585085865025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54752944162473723390576683 82129416243710585085865025)
        ·
          refine ⟨61597062182782938814398769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82129416243710585085865025 61597062182782938814398769)
          ·
            refine ⟨46197796637087204110799077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61597062182782938814398769 46197796637087204110799077)
            ·
              refine ⟨8662086869453850770774827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 46197796637087204110799077 8662086869453850770774827)
              ·
                refine ⟨12993130304180776156162241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8662086869453850770774827 12993130304180776156162241)
                ·
                  refine ⟨9744847728135582117121681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12993130304180776156162241 9744847728135582117121681)
                  ·
                    refine ⟨7308635796101686587841261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9744847728135582117121681 7308635796101686587841261)
                    ·
                      refine ⟨2740738423538132470440473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7308635796101686587841261 2740738423538132470440473)
                      ·
                        rfl

theorem cell23_5337569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 4, 1, 2, 2, 3].length) (baseStart_5337569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5337569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5337569 prefixEnd_5337569 := by exact prefixLift 5337569
  have htrace : WordTrace (prefixWord ++ tailWord_5337569) baseStart_5337569 baseEnd_5337569 := by
    simpa [prefixWord, tailWord_5337569, baseEnd_5337569] using wordTrace_append hprefix tailTrace_5337569
  have hstable : (prefixWord ++ tailWord_5337569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5337569).length < 2 ^ (prefixWord ++ tailWord_5337569).sum := by decide
  have hdescent : baseEnd_5337569 < baseStart_5337569 := by decide
  rcases family_descends (prefixWord ++ tailWord_5337569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5337595 : List Nat := [1, 1, 1, 1, 1, 3, 2, 1, 4, 1, 7]
def baseStart_5337595 : Nat := 118140960795 + 5337595 * 2 ^ 59
def prefixEnd_5337595 : Nat := 4983230072969 + 3 ^ 40 * 5337595 * 2
def baseEnd_5337595 : Nat := 2740751774035149368715353

theorem tailTrace_5337595 : CollatzResearch.WordTrace tailWord_5337595 prefixEnd_5337595 2740751774035149368715353 := by
  unfold tailWord_5337595
  simp only [CollatzResearch.WordTrace]
  refine ⟨194678083097812378495830239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129785388731874918997220159 194678083097812378495830239)
  ·
    refine ⟨292017124646718567743745359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194678083097812378495830239 292017124646718567743745359)
    ·
      refine ⟨438025686970077851615618039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 292017124646718567743745359 438025686970077851615618039)
      ·
        refine ⟨657038530455116777423427059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 438025686970077851615618039 657038530455116777423427059)
        ·
          refine ⟨985557795682675166135140589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 657038530455116777423427059 985557795682675166135140589)
          ·
            refine ⟨369584173381003187300677721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 985557795682675166135140589 369584173381003187300677721)
            ·
              refine ⟨277188130035752390475508291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 369584173381003187300677721 277188130035752390475508291)
              ·
                refine ⟨415782195053628585713262437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 277188130035752390475508291 415782195053628585713262437)
                ·
                  refine ⟨77959161572555359821236707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 415782195053628585713262437 77959161572555359821236707)
                  ·
                    refine ⟨116938742358833039731855061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 77959161572555359821236707 116938742358833039731855061)
                    ·
                      refine ⟨2740751774035149368715353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 116938742358833039731855061 2740751774035149368715353)
                      ·
                        rfl

theorem cell23_5337595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 1, 4, 1, 7].length) (baseStart_5337595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5337595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5337595 prefixEnd_5337595 := by exact prefixLift 5337595
  have htrace : WordTrace (prefixWord ++ tailWord_5337595) baseStart_5337595 baseEnd_5337595 := by
    simpa [prefixWord, tailWord_5337595, baseEnd_5337595] using wordTrace_append hprefix tailTrace_5337595
  have hstable : (prefixWord ++ tailWord_5337595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5337595).length < 2 ^ (prefixWord ++ tailWord_5337595).sum := by decide
  have hdescent : baseEnd_5337595 < baseStart_5337595 := by decide
  rcases family_descends (prefixWord ++ tailWord_5337595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5337599 : List Nat := [1, 1, 2, 2, 1, 2, 4, 3, 3, 1, 3]
def baseStart_5337599 : Nat := 118140960795 + 5337599 * 2 ^ 59
def prefixEnd_5337599 : Nat := 4983230072969 + 3 ^ 40 * 5337599 * 2
def baseEnd_5337599 : Nat := 2740753827957767353065335

theorem tailTrace_5337599 : CollatzResearch.WordTrace tailWord_5337599 prefixEnd_5337599 2740753827957767353065335 := by
  unfold tailWord_5337599
  simp only [CollatzResearch.WordTrace]
  refine ⟨194678228989797887178975851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129785485993198591452650567 194678228989797887178975851)
  ·
    refine ⟨292017343484696830768463777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194678228989797887178975851 292017343484696830768463777)
    ·
      refine ⟨219013007613522623076347833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 292017343484696830768463777 219013007613522623076347833)
      ·
        refine ⟨164259755710141967307260875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 219013007613522623076347833 164259755710141967307260875)
        ·
          refine ⟨246389633565212950960891313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 164259755710141967307260875 246389633565212950960891313)
          ·
            refine ⟨184792225173909713220668485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 246389633565212950960891313 184792225173909713220668485)
            ·
              refine ⟨34648542220108071228875341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 184792225173909713220668485 34648542220108071228875341)
              ·
                refine ⟨12993203332540526710828253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34648542220108071228875341 12993203332540526710828253)
                ·
                  refine ⟨4872451249702697516560595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12993203332540526710828253 4872451249702697516560595)
                  ·
                    refine ⟨7308676874554046274840893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4872451249702697516560595 7308676874554046274840893)
                    ·
                      refine ⟨2740753827957767353065335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7308676874554046274840893 2740753827957767353065335)
                      ·
                        rfl

theorem cell23_5337599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 4, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 4, 3, 3, 1, 3].length) (baseStart_5337599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5337599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5337599 prefixEnd_5337599 := by exact prefixLift 5337599
  have htrace : WordTrace (prefixWord ++ tailWord_5337599) baseStart_5337599 baseEnd_5337599 := by
    simpa [prefixWord, tailWord_5337599, baseEnd_5337599] using wordTrace_append hprefix tailTrace_5337599
  have hstable : (prefixWord ++ tailWord_5337599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5337599).length < 2 ^ (prefixWord ++ tailWord_5337599).sum := by decide
  have hdescent : baseEnd_5337599 < baseStart_5337599 := by decide
  rcases family_descends (prefixWord ++ tailWord_5337599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5337626 : List Nat := [3, 1, 1, 3, 1, 1, 5, 1, 2, 3, 2]
def baseStart_5337626 : Nat := 118140960795 + 5337626 * 2 ^ 59
def prefixEnd_5337626 : Nat := 4983230072969 + 3 ^ 40 * 5337626 * 2
def baseEnd_5337626 : Nat := 2740767691935438747427711

theorem tailTrace_5337626 : CollatzResearch.WordTrace tailWord_5337626 prefixEnd_5337626 2740767691935438747427711 := by
  unfold tailWord_5337626
  simp only [CollatzResearch.WordTrace]
  refine ⟨48669803440175017697552183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129786142507133380526805821 48669803440175017697552183)
  ·
    refine ⟨73004705160262526546328275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48669803440175017697552183 73004705160262526546328275)
    ·
      refine ⟨109507057740393789819492413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73004705160262526546328275 109507057740393789819492413)
      ·
        refine ⟨41065146652647671182309655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 109507057740393789819492413 41065146652647671182309655)
        ·
          refine ⟨61597719978971506773464483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41065146652647671182309655 61597719978971506773464483)
          ·
            refine ⟨92396579968457260160196725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61597719978971506773464483 92396579968457260160196725)
            ·
              refine ⟨8662179372042868140018443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 92396579968457260160196725 8662179372042868140018443)
              ·
                refine ⟨12993269058064302210027665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8662179372042868140018443 12993269058064302210027665)
                ·
                  refine ⟨9744951793548226657520749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12993269058064302210027665 9744951793548226657520749)
                  ·
                    refine ⟨3654356922580584996570281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9744951793548226657520749 3654356922580584996570281)
                    ·
                      refine ⟨2740767691935438747427711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3654356922580584996570281 2740767691935438747427711)
                      ·
                        rfl

theorem cell23_5337626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 5, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 5, 1, 2, 3, 2].length) (baseStart_5337626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5337626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5337626 prefixEnd_5337626 := by exact prefixLift 5337626
  have htrace : WordTrace (prefixWord ++ tailWord_5337626) baseStart_5337626 baseEnd_5337626 := by
    simpa [prefixWord, tailWord_5337626, baseEnd_5337626] using wordTrace_append hprefix tailTrace_5337626
  have hstable : (prefixWord ++ tailWord_5337626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5337626).length < 2 ^ (prefixWord ++ tailWord_5337626).sum := by decide
  have hdescent : baseEnd_5337626 < baseStart_5337626 := by decide
  rcases family_descends (prefixWord ++ tailWord_5337626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5337633 : List Nat := [1, 2, 3, 2, 2, 1, 4, 3, 1, 1, 3]
def baseStart_5337633 : Nat := 118140960795 + 5337633 * 2 ^ 59
def prefixEnd_5337633 : Nat := 4983230072969 + 3 ^ 40 * 5337633 * 2
def baseEnd_5337633 : Nat := 2740771286300020220040179

theorem tailTrace_5337633 : CollatzResearch.WordTrace tailWord_5337633 prefixEnd_5337633 2740771286300020220040179 := by
  unfold tailWord_5337633
  simp only [CollatzResearch.WordTrace]
  refine ⟨194679469071674710985713553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129786312714449807323809035 194679469071674710985713553)
  ·
    refine ⟨146009601803756033239285165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 194679469071674710985713553 146009601803756033239285165)
    ·
      refine ⟨54753600676408512464731937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 146009601803756033239285165 54753600676408512464731937)
      ·
        refine ⟨41065200507306384348548953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54753600676408512464731937 41065200507306384348548953)
        ·
          refine ⟨30798900380479788261411715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41065200507306384348548953 30798900380479788261411715)
          ·
            refine ⟨46198350570719682392117573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30798900380479788261411715 46198350570719682392117573)
            ·
              refine ⟨8662190732009940448522045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 46198350570719682392117573 8662190732009940448522045)
              ·
                refine ⟨3248321524503727668195767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8662190732009940448522045 3248321524503727668195767)
                ·
                  refine ⟨4872482286755591502293651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3248321524503727668195767 4872482286755591502293651)
                  ·
                    refine ⟨7308723430133387253440477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4872482286755591502293651 7308723430133387253440477)
                    ·
                      refine ⟨2740771286300020220040179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7308723430133387253440477 2740771286300020220040179)
                      ·
                        rfl

theorem cell23_5337633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 4, 3, 1, 1, 3].length) (baseStart_5337633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5337633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5337633 prefixEnd_5337633 := by exact prefixLift 5337633
  have htrace : WordTrace (prefixWord ++ tailWord_5337633) baseStart_5337633 baseEnd_5337633 := by
    simpa [prefixWord, tailWord_5337633, baseEnd_5337633] using wordTrace_append hprefix tailTrace_5337633
  have hstable : (prefixWord ++ tailWord_5337633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5337633).length < 2 ^ (prefixWord ++ tailWord_5337633).sum := by decide
  have hdescent : baseEnd_5337633 < baseStart_5337633 := by decide
  rcases family_descends (prefixWord ++ tailWord_5337633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5337669 : List Nat := [1, 3, 1, 1, 1, 5, 3, 1, 1, 2, 4]
def baseStart_5337669 : Nat := 118140960795 + 5337669 * 2 ^ 59
def prefixEnd_5337669 : Nat := 4983230072969 + 3 ^ 40 * 5337669 * 2
def baseEnd_5337669 : Nat := 2740789771603582079190013

theorem tailTrace_5337669 : CollatzResearch.WordTrace tailWord_5337669 prefixEnd_5337669 2740789771603582079190013 := by
  unfold tailWord_5337669
  simp only [CollatzResearch.WordTrace]
  refine ⟨194680782099544289134024061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129787188066362859422682707 194680782099544289134024061)
  ·
    refine ⟨73005293287329108425259023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 194680782099544289134024061 73005293287329108425259023)
    ·
      refine ⟨109507939930993662637888535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73005293287329108425259023 109507939930993662637888535)
      ·
        refine ⟨164261909896490493956832803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109507939930993662637888535 164261909896490493956832803)
        ·
          refine ⟨246392864844735740935249205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 164261909896490493956832803 246392864844735740935249205)
          ·
            refine ⟨23099331079193975712679613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 246392864844735740935249205 23099331079193975712679613)
            ·
              refine ⟨8662249154697740892254855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23099331079193975712679613 8662249154697740892254855)
              ·
                refine ⟨12993373732046611338382283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8662249154697740892254855 12993373732046611338382283)
                ·
                  refine ⟨19490060598069917007573425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12993373732046611338382283 19490060598069917007573425)
                  ·
                    refine ⟨14617545448552437755680069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19490060598069917007573425 14617545448552437755680069)
                    ·
                      refine ⟨2740789771603582079190013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14617545448552437755680069 2740789771603582079190013)
                      ·
                        rfl

theorem cell23_5337669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 3, 1, 1, 2, 4].length) (baseStart_5337669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5337669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5337669 prefixEnd_5337669 := by exact prefixLift 5337669
  have htrace : WordTrace (prefixWord ++ tailWord_5337669) baseStart_5337669 baseEnd_5337669 := by
    simpa [prefixWord, tailWord_5337669, baseEnd_5337669] using wordTrace_append hprefix tailTrace_5337669
  have hstable : (prefixWord ++ tailWord_5337669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5337669).length < 2 ^ (prefixWord ++ tailWord_5337669).sum := by decide
  have hdescent : baseEnd_5337669 < baseStart_5337669 := by decide
  rcases family_descends (prefixWord ++ tailWord_5337669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5337676 : List Nat := [2, 2, 1, 3, 1, 2, 4, 2, 1, 2, 3]
def baseStart_5337676 : Nat := 118140960795 + 5337676 * 2 ^ 59
def prefixEnd_5337676 : Nat := 4983230072969 + 3 ^ 40 * 5337676 * 2
def baseEnd_5337676 : Nat := 2740793365968163551802481

theorem tailTrace_5337676 : CollatzResearch.WordTrace tailWord_5337676 prefixEnd_5337676 2740793365968163551802481 := by
  unfold tailWord_5337676
  simp only [CollatzResearch.WordTrace]
  refine ⟨97340518705259464664764441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129787358273679286219685921 97340518705259464664764441)
  ·
    refine ⟨73005389028944598498573331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97340518705259464664764441 73005389028944598498573331)
    ·
      refine ⟨109508083543416897747859997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73005389028944598498573331 109508083543416897747859997)
      ·
        refine ⟨41065531328781336655447499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 109508083543416897747859997 41065531328781336655447499)
        ·
          refine ⟨61598296993172004983171249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41065531328781336655447499 61598296993172004983171249)
          ·
            refine ⟨46198722744879003737378437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61598296993172004983171249 46198722744879003737378437)
            ·
              refine ⟨8662260514664813200758457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 46198722744879003737378437 8662260514664813200758457)
              ·
                refine ⟨6496695385998609900568843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8662260514664813200758457 6496695385998609900568843)
                ·
                  refine ⟨9745043078997914850853265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6496695385998609900568843 9745043078997914850853265)
                  ·
                    refine ⟨7308782309248436138139949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9745043078997914850853265 7308782309248436138139949)
                    ·
                      refine ⟨2740793365968163551802481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7308782309248436138139949 2740793365968163551802481)
                      ·
                        rfl

theorem cell23_5337676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 4, 2, 1, 2, 3].length) (baseStart_5337676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5337676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5337676 prefixEnd_5337676 := by exact prefixLift 5337676
  have htrace : WordTrace (prefixWord ++ tailWord_5337676) baseStart_5337676 baseEnd_5337676 := by
    simpa [prefixWord, tailWord_5337676, baseEnd_5337676] using wordTrace_append hprefix tailTrace_5337676
  have hstable : (prefixWord ++ tailWord_5337676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5337676).length < 2 ^ (prefixWord ++ tailWord_5337676).sum := by decide
  have hdescent : baseEnd_5337676 < baseStart_5337676 := by decide
  rcases family_descends (prefixWord ++ tailWord_5337676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5337706 : List Nat := [3, 1, 3, 2, 1, 1, 1, 3, 4, 1, 3]
def baseStart_5337706 : Nat := 118140960795 + 5337706 * 2 ^ 59
def prefixEnd_5337706 : Nat := 4983230072969 + 3 ^ 40 * 5337706 * 2
def baseEnd_5337706 : Nat := 2740808770387798434427343

theorem tailTrace_5337706 : CollatzResearch.WordTrace tailWord_5337706 prefixEnd_5337706 2740808770387798434427343 := by
  unfold tailWord_5337706
  simp only [CollatzResearch.WordTrace]
  refine ⟨48670532900102561113280243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129788087733606829635413981 48670532900102561113280243)
  ·
    refine ⟨73005799350153841669920365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48670532900102561113280243 73005799350153841669920365)
    ·
      refine ⟨27377174756307690626220137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73005799350153841669920365 27377174756307690626220137)
      ·
        refine ⟨20532881067230767969665103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27377174756307690626220137 20532881067230767969665103)
        ·
          refine ⟨30799321600846151954497655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20532881067230767969665103 30799321600846151954497655)
          ·
            refine ⟨46198982401269227931746483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30799321600846151954497655 46198982401269227931746483)
            ·
              refine ⟨69298473601903841897619725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46198982401269227931746483 69298473601903841897619725)
              ·
                refine ⟨25986927600713940711607397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 69298473601903841897619725 25986927600713940711607397)
                ·
                  refine ⟨4872548925133863883426387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25986927600713940711607397 4872548925133863883426387)
                  ·
                    refine ⟨7308823387700795825139581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4872548925133863883426387 7308823387700795825139581)
                    ·
                      refine ⟨2740808770387798434427343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7308823387700795825139581 2740808770387798434427343)
                      ·
                        rfl

theorem cell23_5337706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 3, 4, 1, 3].length) (baseStart_5337706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5337706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5337706 prefixEnd_5337706 := by exact prefixLift 5337706
  have htrace : WordTrace (prefixWord ++ tailWord_5337706) baseStart_5337706 baseEnd_5337706 := by
    simpa [prefixWord, tailWord_5337706, baseEnd_5337706] using wordTrace_append hprefix tailTrace_5337706
  have hstable : (prefixWord ++ tailWord_5337706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5337706).length < 2 ^ (prefixWord ++ tailWord_5337706).sum := by decide
  have hdescent : baseEnd_5337706 < baseStart_5337706 := by decide
  rcases family_descends (prefixWord ++ tailWord_5337706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5337717 : List Nat := [1, 3, 4, 2, 3, 1, 2, 1, 2, 4]
def baseStart_5337717 : Nat := 118140960795 + 5337717 * 2 ^ 59
def prefixEnd_5337717 : Nat := 4983230072969 + 3 ^ 40 * 5337717 * 2
def baseEnd_5337717 : Nat := 913604806224999297129931

theorem tailTrace_5337717 : CollatzResearch.WordTrace tailWord_5337717 prefixEnd_5337717 913604806224999297129931 := by
  unfold tailWord_5337717
  simp only [CollatzResearch.WordTrace]
  refine ⟨194682532803370393331771405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129788355202246928887847603 194682532803370393331771405)
  ·
    refine ⟨73005949801263897499414277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 194682532803370393331771405 73005949801263897499414277)
    ·
      refine ⟨13688615587736980781140177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 73005949801263897499414277 13688615587736980781140177)
      ·
        refine ⟨10266461690802735585855133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13688615587736980781140177 10266461690802735585855133)
        ·
          refine ⟨3849923134051025844695675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10266461690802735585855133 3849923134051025844695675)
          ·
            refine ⟨5774884701076538767043513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3849923134051025844695675 5774884701076538767043513)
            ·
              refine ⟨4331163525807404075282635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5774884701076538767043513 4331163525807404075282635)
              ·
                refine ⟨6496745288711106112923953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4331163525807404075282635 6496745288711106112923953)
                ·
                  refine ⟨4872558966533329584692965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6496745288711106112923953 4872558966533329584692965)
                  ·
                    refine ⟨913604806224999297129931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4872558966533329584692965 913604806224999297129931)
                    ·
                      rfl

theorem cell23_5337717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 3, 1, 2, 1, 2, 4].length) (baseStart_5337717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5337717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5337717 prefixEnd_5337717 := by exact prefixLift 5337717
  have htrace : WordTrace (prefixWord ++ tailWord_5337717) baseStart_5337717 baseEnd_5337717 := by
    simpa [prefixWord, tailWord_5337717, baseEnd_5337717] using wordTrace_append hprefix tailTrace_5337717
  have hstable : (prefixWord ++ tailWord_5337717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5337717).length < 2 ^ (prefixWord ++ tailWord_5337717).sum := by decide
  have hdescent : baseEnd_5337717 < baseStart_5337717 := by decide
  rcases family_descends (prefixWord ++ tailWord_5337717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5337722 : List Nat := [3, 1, 1, 1, 1, 1, 1, 2, 6, 6]
def baseStart_5337722 : Nat := 118140960795 + 5337722 * 2 ^ 59
def prefixEnd_5337722 : Nat := 4983230072969 + 3 ^ 40 * 5337722 * 2
def baseEnd_5337722 : Nat := 913605662026090123942423

theorem tailTrace_5337722 : CollatzResearch.WordTrace tailWord_5337722 prefixEnd_5337722 913605662026090123942423 := by
  unfold tailWord_5337722
  simp only [CollatzResearch.WordTrace]
  refine ⟨48670678792088069796425855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129788476778901519457135613 48670678792088069796425855)
  ·
    refine ⟨73006018188132104694638783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48670678792088069796425855 73006018188132104694638783)
    ·
      refine ⟨109509027282198157041958175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73006018188132104694638783 109509027282198157041958175)
      ·
        refine ⟨164263540923297235562937263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109509027282198157041958175 164263540923297235562937263)
        ·
          refine ⟨246395311384945853344405895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 164263540923297235562937263 246395311384945853344405895)
          ·
            refine ⟨369592967077418780016608843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 246395311384945853344405895 369592967077418780016608843)
            ·
              refine ⟨554389450616128170024913265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 369592967077418780016608843 554389450616128170024913265)
              ·
                refine ⟨415792087962096127518684949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 554389450616128170024913265 415792087962096127518684949)
                ·
                  refine ⟨19490254123223255977438357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 415792087962096127518684949 19490254123223255977438357)
                  ·
                    refine ⟨913605662026090123942423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19490254123223255977438357 913605662026090123942423)
                    ·
                      rfl

theorem cell23_5337722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 2, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 2, 6, 6].length) (baseStart_5337722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5337722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5337722 prefixEnd_5337722 := by exact prefixLift 5337722
  have htrace : WordTrace (prefixWord ++ tailWord_5337722) baseStart_5337722 baseEnd_5337722 := by
    simpa [prefixWord, tailWord_5337722, baseEnd_5337722] using wordTrace_append hprefix tailTrace_5337722
  have hstable : (prefixWord ++ tailWord_5337722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5337722).length < 2 ^ (prefixWord ++ tailWord_5337722).sum := by decide
  have hdescent : baseEnd_5337722 < baseStart_5337722 := by decide
  rcases family_descends (prefixWord ++ tailWord_5337722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5337733 : List Nat := [1, 3, 1, 1, 4, 2, 3, 2, 1, 3, 2]
def baseStart_5337733 : Nat := 118140960795 + 5337733 * 2 ^ 59
def prefixEnd_5337733 : Nat := 4983230072969 + 3 ^ 40 * 5337733 * 2
def baseEnd_5337733 : Nat := 2740822634365469828789719

theorem tailTrace_5337733 : CollatzResearch.WordTrace tailWord_5337733 prefixEnd_5337733 2740822634365469828789719 := by
  unfold tailWord_5337733
  simp only [CollatzResearch.WordTrace]
  refine ⟨194683116371312428064353853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129788744247541618709569235 194683116371312428064353853)
  ·
    refine ⟨73006168639242160524132695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 194683116371312428064353853 73006168639242160524132695)
    ·
      refine ⟨109509252958863240786199043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73006168639242160524132695 109509252958863240786199043)
      ·
        refine ⟨164263879438294861179298565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109509252958863240786199043 164263879438294861179298565)
        ·
          refine ⟨30799477394680286471118481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 164263879438294861179298565 30799477394680286471118481)
          ·
            refine ⟨23099608046010214853338861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30799477394680286471118481 23099608046010214853338861)
            ·
              refine ⟨8662353017253830570002073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23099608046010214853338861 8662353017253830570002073)
              ·
                refine ⟨6496764762940372927501555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8662353017253830570002073 6496764762940372927501555)
                ·
                  refine ⟨9745147144410559391252333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6496764762940372927501555 9745147144410559391252333)
                  ·
                    refine ⟨3654430179153959771719625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9745147144410559391252333 3654430179153959771719625)
                    ·
                      refine ⟨2740822634365469828789719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3654430179153959771719625 2740822634365469828789719)
                      ·
                        rfl

theorem cell23_5337733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 3, 2, 1, 3, 2].length) (baseStart_5337733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5337733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5337733 prefixEnd_5337733 := by exact prefixLift 5337733
  have htrace : WordTrace (prefixWord ++ tailWord_5337733) baseStart_5337733 baseEnd_5337733 := by
    simpa [prefixWord, tailWord_5337733, baseEnd_5337733] using wordTrace_append hprefix tailTrace_5337733
  have hstable : (prefixWord ++ tailWord_5337733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5337733).length < 2 ^ (prefixWord ++ tailWord_5337733).sum := by decide
  have hdescent : baseEnd_5337733 < baseStart_5337733 := by decide
  rcases family_descends (prefixWord ++ tailWord_5337733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5337779 : List Nat := [1, 1, 1, 2, 3, 4, 1, 1, 1, 5, 3]
def baseStart_5337779 : Nat := 118140960795 + 5337779 * 2 ^ 59
def prefixEnd_5337779 : Nat := 4983230072969 + 3 ^ 40 * 5337779 * 2
def baseEnd_5337779 : Nat := 2740846254475576648814507

theorem tailTrace_5337779 : CollatzResearch.WordTrace tailWord_5337779 prefixEnd_5337779 2740846254475576648814507 := by
  unfold tailWord_5337779
  simp only [CollatzResearch.WordTrace]
  refine ⟨194684794129145777920528391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129789862752763851947018927 194684794129145777920528391)
  ·
    refine ⟨292027191193718666880792587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194684794129145777920528391 292027191193718666880792587)
    ·
      refine ⟨438040786790578000321188881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 292027191193718666880792587 438040786790578000321188881)
      ·
        refine ⟨328530590092933500240891661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 438040786790578000321188881 328530590092933500240891661)
        ·
          refine ⟨123198971284850062590334373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 328530590092933500240891661 123198971284850062590334373)
          ·
            refine ⟨23099807115909386735687695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 123198971284850062590334373 23099807115909386735687695)
            ·
              refine ⟨34649710673864080103531543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23099807115909386735687695 34649710673864080103531543)
              ·
                refine ⟨51974566010796120155297315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34649710673864080103531543 51974566010796120155297315)
                ·
                  refine ⟨77961849016194180232945973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51974566010796120155297315 77961849016194180232945973)
                  ·
                    refine ⟨7308923345268204396838685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 77961849016194180232945973 7308923345268204396838685)
                    ·
                      refine ⟨2740846254475576648814507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7308923345268204396838685 2740846254475576648814507)
                      ·
                        rfl

theorem cell23_5337779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 1, 1, 1, 5, 3].length) (baseStart_5337779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5337779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5337779 prefixEnd_5337779 := by exact prefixLift 5337779
  have htrace : WordTrace (prefixWord ++ tailWord_5337779) baseStart_5337779 baseEnd_5337779 := by
    simpa [prefixWord, tailWord_5337779, baseEnd_5337779] using wordTrace_append hprefix tailTrace_5337779
  have hstable : (prefixWord ++ tailWord_5337779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5337779).length < 2 ^ (prefixWord ++ tailWord_5337779).sum := by decide
  have hdescent : baseEnd_5337779 < baseStart_5337779 := by decide
  rcases family_descends (prefixWord ++ tailWord_5337779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5337799 : List Nat := [1, 1, 4, 1, 1, 1, 2, 5, 2, 5]
def baseStart_5337799 : Nat := 118140960795 + 5337799 * 2 ^ 59
def prefixEnd_5337799 : Nat := 4983230072969 + 3 ^ 40 * 5337799 * 2
def baseEnd_5337799 : Nat := 913618841362888856854805

theorem tailTrace_5337799 : CollatzResearch.WordTrace tailWord_5337799 prefixEnd_5337799 913618841362888856854805 := by
  unfold tailWord_5337799
  simp only [CollatzResearch.WordTrace]
  refine ⟨194685523589073321336256451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129790349059382214224170967 194685523589073321336256451)
  ·
    refine ⟨292028285383609982004384677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194685523589073321336256451 292028285383609982004384677)
    ·
      refine ⟨54755303509426871625822127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 292028285383609982004384677 54755303509426871625822127)
      ·
        refine ⟨82132955264140307438733191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54755303509426871625822127 82132955264140307438733191)
        ·
          refine ⟨123199432896210461158099787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82132955264140307438733191 123199432896210461158099787)
          ·
            refine ⟨184799149344315691737149681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 123199432896210461158099787 184799149344315691737149681)
            ·
              refine ⟨138599362008236768802862261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 184799149344315691737149681 138599362008236768802862261)
              ·
                refine ⟨12993690188272197075268337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 138599362008236768802862261 12993690188272197075268337)
                ·
                  refine ⟨9745267641204147806451253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12993690188272197075268337 9745267641204147806451253)
                  ·
                    refine ⟨913618841362888856854805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9745267641204147806451253 913618841362888856854805)
                    ·
                      rfl

theorem cell23_5337799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 5, 2, 5].length) (baseStart_5337799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5337799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5337799 prefixEnd_5337799 := by exact prefixLift 5337799
  have htrace : WordTrace (prefixWord ++ tailWord_5337799) baseStart_5337799 baseEnd_5337799 := by
    simpa [prefixWord, tailWord_5337799, baseEnd_5337799] using wordTrace_append hprefix tailTrace_5337799
  have hstable : (prefixWord ++ tailWord_5337799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5337799).length < 2 ^ (prefixWord ++ tailWord_5337799).sum := by decide
  have hdescent : baseEnd_5337799 < baseStart_5337799 := by decide
  rcases family_descends (prefixWord ++ tailWord_5337799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5337906 : List Nat := [3, 2, 1, 1, 3, 1, 3, 1, 3, 5]
def baseStart_5337906 : Nat := 118140960795 + 5337906 * 2 ^ 59
def prefixEnd_5337906 : Nat := 4983230072969 + 3 ^ 40 * 5337906 * 2
def baseEnd_5337906 : Nat := 913637155506232550642141

theorem tailTrace_5337906 : CollatzResearch.WordTrace tailWord_5337906 prefixEnd_5337906 913637155506232550642141 := by
  unfold tailWord_5337906
  simp only [CollatzResearch.WordTrace]
  refine ⟨48672356549921419652600393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129792950799790452406934381 48672356549921419652600393)
  ·
    refine ⟨36504267412441064739450295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48672356549921419652600393 36504267412441064739450295)
    ·
      refine ⟨54756401118661597109175443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36504267412441064739450295 54756401118661597109175443)
      ·
        refine ⟨82134601677992395663763165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54756401118661597109175443 82134601677992395663763165)
        ·
          refine ⟨30800475629247148373911187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 82134601677992395663763165 30800475629247148373911187)
          ·
            refine ⟨46200713443870722560866781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30800475629247148373911187 46200713443870722560866781)
            ·
              refine ⟨17325267541451520960325043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46200713443870722560866781 17325267541451520960325043)
              ·
                refine ⟨25987901312177281440487565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17325267541451520960325043 25987901312177281440487565)
                ·
                  refine ⟨9745462992066480540182837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25987901312177281440487565 9745462992066480540182837)
                  ·
                    refine ⟨913637155506232550642141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9745462992066480540182837 913637155506232550642141)
                    ·
                      rfl

theorem cell23_5337906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 3, 1, 3, 5].length) (baseStart_5337906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5337906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5337906 prefixEnd_5337906 := by exact prefixLift 5337906
  have htrace : WordTrace (prefixWord ++ tailWord_5337906) baseStart_5337906 baseEnd_5337906 := by
    simpa [prefixWord, tailWord_5337906, baseEnd_5337906] using wordTrace_append hprefix tailTrace_5337906
  have hstable : (prefixWord ++ tailWord_5337906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5337906).length < 2 ^ (prefixWord ++ tailWord_5337906).sum := by decide
  have hdescent : baseEnd_5337906 < baseStart_5337906 := by decide
  rcases family_descends (prefixWord ++ tailWord_5337906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5337923 : List Nat := [1, 1, 1, 3, 1, 4, 5, 1, 1, 5]
def baseStart_5337923 : Nat := 118140960795 + 5337923 * 2 ^ 59
def prefixEnd_5337923 : Nat := 4983230072969 + 3 ^ 40 * 5337923 * 2
def baseEnd_5337923 : Nat := 913640065229941361804615

theorem tailTrace_5337923 : CollatzResearch.WordTrace tailWord_5337923 prefixEnd_5337923 913640065229941361804615 := by
  unfold tailWord_5337923
  simp only [CollatzResearch.WordTrace]
  refine ⟨194690046240624090513770423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129793364160416060342513615 194690046240624090513770423)
  ·
    refine ⟨292035069360936135770655635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194690046240624090513770423 292035069360936135770655635)
    ·
      refine ⟨438052604041404203655983453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 292035069360936135770655635 438052604041404203655983453)
      ·
        refine ⟨164269726515526576370993795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 438052604041404203655983453 164269726515526576370993795)
        ·
          refine ⟨246404589773289864556490693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 164269726515526576370993795 246404589773289864556490693)
          ·
            refine ⟨46200860582491849604342005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 246404589773289864556490693 46200860582491849604342005)
            ·
              refine ⟨4331330679608610900407063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 46200860582491849604342005 4331330679608610900407063)
              ·
                refine ⟨6496996019412916350610595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4331330679608610900407063 6496996019412916350610595)
                ·
                  refine ⟨9745494029119374525915893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6496996019412916350610595 9745494029119374525915893)
                  ·
                    refine ⟨913640065229941361804615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9745494029119374525915893 913640065229941361804615)
                    ·
                      rfl

theorem cell23_5337923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 5, 1, 1, 5].length) (baseStart_5337923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5337923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5337923 prefixEnd_5337923 := by exact prefixLift 5337923
  have htrace : WordTrace (prefixWord ++ tailWord_5337923) baseStart_5337923 baseEnd_5337923 := by
    simpa [prefixWord, tailWord_5337923, baseEnd_5337923] using wordTrace_append hprefix tailTrace_5337923
  have hstable : (prefixWord ++ tailWord_5337923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5337923).length < 2 ^ (prefixWord ++ tailWord_5337923).sum := by decide
  have hdescent : baseEnd_5337923 < baseStart_5337923 := by decide
  rcases family_descends (prefixWord ++ tailWord_5337923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5337936 : List Nat := [2, 1, 1, 1, 1, 4, 2, 3, 4, 4]
def baseStart_5337936 : Nat := 118140960795 + 5337936 * 2 ^ 59
def prefixEnd_5337936 : Nat := 4983230072969 + 3 ^ 40 * 5337936 * 2
def baseEnd_5337936 : Nat := 913642290312777511517095

theorem tailTrace_5337936 : CollatzResearch.WordTrace tailWord_5337936 prefixEnd_5337936 913642290312777511517095 := by
  unfold tailWord_5337936
  simp only [CollatzResearch.WordTrace]
  refine ⟨97345260194788496866996831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129793680259717995822662441 97345260194788496866996831)
  ·
    refine ⟨146017890292182745300495247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97345260194788496866996831 146017890292182745300495247)
    ·
      refine ⟨219026835438274117950742871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146017890292182745300495247 219026835438274117950742871)
      ·
        refine ⟨328540253157411176926114307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 219026835438274117950742871 328540253157411176926114307)
        ·
          refine ⟨492810379736116765389171461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 328540253157411176926114307 492810379736116765389171461)
          ·
            refine ⟨92401946200521893510469649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 492810379736116765389171461 92401946200521893510469649)
            ·
              refine ⟨69301459650391420132852237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 92401946200521893510469649 69301459650391420132852237)
              ·
                refine ⟨25988047368896782549819589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 69301459650391420132852237 25988047368896782549819589)
                ·
                  refine ⟨4872758881668146728091173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25988047368896782549819589 4872758881668146728091173)
                  ·
                    refine ⟨913642290312777511517095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4872758881668146728091173 913642290312777511517095)
                    ·
                      rfl

theorem cell23_5337936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 3, 4, 4].length) (baseStart_5337936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5337936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5337936 prefixEnd_5337936 := by exact prefixLift 5337936
  have htrace : WordTrace (prefixWord ++ tailWord_5337936) baseStart_5337936 baseEnd_5337936 := by
    simpa [prefixWord, tailWord_5337936, baseEnd_5337936] using wordTrace_append hprefix tailTrace_5337936
  have hstable : (prefixWord ++ tailWord_5337936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5337936).length < 2 ^ (prefixWord ++ tailWord_5337936).sum := by decide
  have hdescent : baseEnd_5337936 < baseStart_5337936 := by decide
  rcases family_descends (prefixWord ++ tailWord_5337936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5337937 : List Nat := [1, 2, 2, 1, 6, 1, 1, 4, 1, 1, 3]
def baseStart_5337937 : Nat := 118140960795 + 5337937 * 2 ^ 59
def prefixEnd_5337937 : Nat := 4983230072969 + 3 ^ 40 * 5337937 * 2
def baseEnd_5337937 : Nat := 2740927384418987030638781

theorem tailTrace_5337937 : CollatzResearch.WordTrace tailWord_5337937 prefixEnd_5337937 2740927384418987030638781 := by
  unfold tailWord_5337937
  simp only [CollatzResearch.WordTrace]
  refine ⟨194690556862573370904780065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129793704575048913936520043 194690556862573370904780065)
  ·
    refine ⟨146017917646930028178585049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 194690556862573370904780065 146017917646930028178585049)
    ·
      refine ⟨109513438235197521133938787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 146017917646930028178585049 109513438235197521133938787)
      ·
        refine ⟨164270157352796281700908181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109513438235197521133938787 164270157352796281700908181)
        ·
          refine ⟨7700163625912325704730071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 164270157352796281700908181 7700163625912325704730071)
          ·
            refine ⟨11550245438868488557095107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7700163625912325704730071 11550245438868488557095107)
            ·
              refine ⟨17325368158302732835642661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11550245438868488557095107 17325368158302732835642661)
              ·
                refine ⟨3248506529681762406682999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17325368158302732835642661 3248506529681762406682999)
                ·
                  refine ⟨4872759794522643610024499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3248506529681762406682999 4872759794522643610024499)
                  ·
                    refine ⟨7309139691783965415036749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4872759794522643610024499 7309139691783965415036749)
                    ·
                      refine ⟨2740927384418987030638781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7309139691783965415036749 2740927384418987030638781)
                      ·
                        rfl

theorem cell23_5337937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 1, 4, 1, 1, 3].length) (baseStart_5337937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5337937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5337937 prefixEnd_5337937 := by exact prefixLift 5337937
  have htrace : WordTrace (prefixWord ++ tailWord_5337937) baseStart_5337937 baseEnd_5337937 := by
    simpa [prefixWord, tailWord_5337937, baseEnd_5337937] using wordTrace_append hprefix tailTrace_5337937
  have hstable : (prefixWord ++ tailWord_5337937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5337937).length < 2 ^ (prefixWord ++ tailWord_5337937).sum := by decide
  have hdescent : baseEnd_5337937 < baseStart_5337937 := by decide
  rcases family_descends (prefixWord ++ tailWord_5337937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5337939 : List Nat := [1, 1, 1, 2, 1, 1, 3, 3, 3, 1, 6]
def baseStart_5337939 : Nat := 118140960795 + 5337939 * 2 ^ 59
def prefixEnd_5337939 : Nat := 4983230072969 + 3 ^ 40 * 5337939 * 2
def baseEnd_5337939 : Nat := 2740928411380296022813771

theorem tailTrace_5337939 : CollatzResearch.WordTrace tailWord_5337939 prefixEnd_5337939 2740928411380296022813771 := by
  unfold tailWord_5337939
  simp only [CollatzResearch.WordTrace]
  refine ⟨194690629808566125246352871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129793753205710750164235247 194690629808566125246352871)
  ·
    refine ⟨292035944712849187869529307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194690629808566125246352871 292035944712849187869529307)
    ·
      refine ⟨438053917069273781804293961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 292035944712849187869529307 438053917069273781804293961)
      ·
        refine ⟨328540437801955336353220471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 438053917069273781804293961 328540437801955336353220471)
        ·
          refine ⟨492810656702933004529830707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 328540437801955336353220471 492810656702933004529830707)
          ·
            refine ⟨739215985054399506794746061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 492810656702933004529830707 739215985054399506794746061)
            ·
              refine ⟨277205994395399815048029773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 739215985054399506794746061 277205994395399815048029773)
              ·
                refine ⟨103952247898274930643011165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 277205994395399815048029773 103952247898274930643011165)
                ·
                  refine ⟨38982092961853098991129187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 103952247898274930643011165 38982092961853098991129187)
                  ·
                    refine ⟨58473139442779648486693781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 38982092961853098991129187 58473139442779648486693781)
                    ·
                      refine ⟨2740928411380296022813771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 58473139442779648486693781 2740928411380296022813771)
                      ·
                        rfl

theorem cell23_5337939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 3, 3, 1, 6].length) (baseStart_5337939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5337939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5337939 prefixEnd_5337939 := by exact prefixLift 5337939
  have htrace : WordTrace (prefixWord ++ tailWord_5337939) baseStart_5337939 baseEnd_5337939 := by
    simpa [prefixWord, tailWord_5337939, baseEnd_5337939] using wordTrace_append hprefix tailTrace_5337939
  have hstable : (prefixWord ++ tailWord_5337939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5337939).length < 2 ^ (prefixWord ++ tailWord_5337939).sum := by decide
  have hdescent : baseEnd_5337939 < baseStart_5337939 := by decide
  rcases family_descends (prefixWord ++ tailWord_5337939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5337960 : List Nat := [2, 1, 4, 2, 1, 2, 1, 1, 5, 2, 2]
def baseStart_5337960 : Nat := 118140960795 + 5337960 * 2 ^ 59
def prefixEnd_5337960 : Nat := 4983230072969 + 3 ^ 40 * 5337960 * 2
def baseEnd_5337960 : Nat := 2740939194474040440651175

theorem tailTrace_5337960 : CollatzResearch.WordTrace tailWord_5337960 prefixEnd_5337960 2740939194474040440651175 := by
  unfold tailWord_5337960
  simp only [CollatzResearch.WordTrace]
  refine ⟨97345697870745022916433667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129794263827660030555244889 97345697870745022916433667)
  ·
    refine ⟨146018546806117534374650501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97345697870745022916433667 146018546806117534374650501)
    ·
      refine ⟨27378477526147037695246969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 146018546806117534374650501 27378477526147037695246969)
      ·
        refine ⟨20533858144610278271435227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27378477526147037695246969 20533858144610278271435227)
        ·
          refine ⟨30800787216915417407152841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20533858144610278271435227 30800787216915417407152841)
          ·
            refine ⟨23100590412686563055364631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30800787216915417407152841 23100590412686563055364631)
            ·
              refine ⟨34650885619029844583046947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23100590412686563055364631 34650885619029844583046947)
              ·
                refine ⟨51976328428544766874570421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34650885619029844583046947 51976328428544766874570421)
                ·
                  refine ⟨4872780790176071894490977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 51976328428544766874570421 4872780790176071894490977)
                  ·
                    refine ⟨3654585592632053920868233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4872780790176071894490977 3654585592632053920868233)
                    ·
                      refine ⟨2740939194474040440651175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3654585592632053920868233 2740939194474040440651175)
                      ·
                        rfl

theorem cell23_5337960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 1, 1, 5, 2, 2].length) (baseStart_5337960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5337960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5337960 prefixEnd_5337960 := by exact prefixLift 5337960
  have htrace : WordTrace (prefixWord ++ tailWord_5337960) baseStart_5337960 baseEnd_5337960 := by
    simpa [prefixWord, tailWord_5337960, baseEnd_5337960] using wordTrace_append hprefix tailTrace_5337960
  have hstable : (prefixWord ++ tailWord_5337960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5337960).length < 2 ^ (prefixWord ++ tailWord_5337960).sum := by decide
  have hdescent : baseEnd_5337960 < baseStart_5337960 := by decide
  rcases family_descends (prefixWord ++ tailWord_5337960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5337973 : List Nat := [1, 3, 4, 1, 1, 2, 2, 2, 1, 2, 4]
def baseStart_5337973 : Nat := 118140960795 + 5337973 * 2 ^ 59
def prefixEnd_5337973 : Nat := 4983230072969 + 3 ^ 40 * 5337973 * 2
def baseEnd_5337973 : Nat := 2740945869722548889788615

theorem tailTrace_5337973 : CollatzResearch.WordTrace tailWord_5337973 prefixEnd_5337973 2740945869722548889788615 := by
  unfold tailWord_5337973
  simp only [CollatzResearch.WordTrace]
  refine ⟨194691869890442949053090573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129794579926961966035393715 194691869890442949053090573)
  ·
    refine ⟨73009451208916105894908965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 194691869890442949053090573 73009451208916105894908965)
    ·
      refine ⟨13689272101671769855295431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 73009451208916105894908965 13689272101671769855295431)
      ·
        refine ⟨20533908152507654782943147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13689272101671769855295431 20533908152507654782943147)
        ·
          refine ⟨30800862228761482174414721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20533908152507654782943147 30800862228761482174414721)
          ·
            refine ⟨23100646671571111630811041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30800862228761482174414721 23100646671571111630811041)
            ·
              refine ⟨17325485003678333723108281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23100646671571111630811041 17325485003678333723108281)
              ·
                refine ⟨12994113752758750292331211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17325485003678333723108281 12994113752758750292331211)
                ·
                  refine ⟨19491170629138125438496817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12994113752758750292331211 19491170629138125438496817)
                  ·
                    refine ⟨14618377971853594078872613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19491170629138125438496817 14618377971853594078872613)
                    ·
                      refine ⟨2740945869722548889788615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14618377971853594078872613 2740945869722548889788615)
                      ·
                        rfl

theorem cell23_5337973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 2, 2, 1, 2, 4].length) (baseStart_5337973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5337973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5337973 prefixEnd_5337973 := by exact prefixLift 5337973
  have htrace : WordTrace (prefixWord ++ tailWord_5337973) baseStart_5337973 baseEnd_5337973 := by
    simpa [prefixWord, tailWord_5337973, baseEnd_5337973] using wordTrace_append hprefix tailTrace_5337973
  have hstable : (prefixWord ++ tailWord_5337973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5337973).length < 2 ^ (prefixWord ++ tailWord_5337973).sum := by decide
  have hdescent : baseEnd_5337973 < baseStart_5337973 := by decide
  rcases family_descends (prefixWord ++ tailWord_5337973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5337976 : List Nat := [2, 1, 2, 1, 1, 1, 1, 5, 3, 3, 3]
def baseStart_5337976 : Nat := 118140960795 + 5337976 * 2 ^ 59
def prefixEnd_5337976 : Nat := 4983230072969 + 3 ^ 40 * 5337976 * 2
def baseEnd_5337976 : Nat := 2740947410164512378051101

theorem tailTrace_5337976 : CollatzResearch.WordTrace tailWord_5337976 prefixEnd_5337976 2740947410164512378051101 := by
  unfold tailWord_5337976
  simp only [CollatzResearch.WordTrace]
  refine ⟨97345989654716040282724891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129794652872954720376966521 97345989654716040282724891)
  ·
    refine ⟨146018984482074060424087337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97345989654716040282724891 146018984482074060424087337)
    ·
      refine ⟨109514238361555545318065503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 146018984482074060424087337 109514238361555545318065503)
      ·
        refine ⟨164271357542333317977098255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109514238361555545318065503 164271357542333317977098255)
        ·
          refine ⟨246407036313499976965647383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 164271357542333317977098255 246407036313499976965647383)
          ·
            refine ⟨369610554470249965448471075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 246407036313499976965647383 369610554470249965448471075)
            ·
              refine ⟨554415831705374948172706613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 369610554470249965448471075 554415831705374948172706613)
              ·
                refine ⟨51976484222378901391191245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 554415831705374948172706613 51976484222378901391191245)
                ·
                  refine ⟨19491181583392088021696717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 51976484222378901391191245 19491181583392088021696717)
                  ·
                    refine ⟨7309193093772033008136269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19491181583392088021696717 7309193093772033008136269)
                    ·
                      refine ⟨2740947410164512378051101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7309193093772033008136269 2740947410164512378051101)
                      ·
                        rfl

theorem cell23_5337976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 5, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 5, 3, 3, 3].length) (baseStart_5337976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5337976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5337976 prefixEnd_5337976 := by exact prefixLift 5337976
  have htrace : WordTrace (prefixWord ++ tailWord_5337976) baseStart_5337976 baseEnd_5337976 := by
    simpa [prefixWord, tailWord_5337976, baseEnd_5337976] using wordTrace_append hprefix tailTrace_5337976
  have hstable : (prefixWord ++ tailWord_5337976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5337976).length < 2 ^ (prefixWord ++ tailWord_5337976).sum := by decide
  have hdescent : baseEnd_5337976 < baseStart_5337976 := by decide
  rcases family_descends (prefixWord ++ tailWord_5337976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5337977 : List Nat := [1, 2, 1, 3, 2, 3, 1, 5, 1, 2, 2]
def baseStart_5337977 : Nat := 118140960795 + 5337977 * 2 ^ 59
def prefixEnd_5337977 : Nat := 4983230072969 + 3 ^ 40 * 5337977 * 2
def baseEnd_5337977 : Nat := 2740947923645166874138597

theorem tailTrace_5337977 : CollatzResearch.WordTrace tailWord_5337977 prefixEnd_5337977 2740947923645166874138597 := by
  unfold tailWord_5337977
  simp only [CollatzResearch.WordTrace]
  refine ⟨194692015782428457736236185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129794677188285638490824123 194692015782428457736236185)
  ·
    refine ⟨146019011836821343302177139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 194692015782428457736236185 146019011836821343302177139)
    ·
      refine ⟨219028517755232014953265709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146019011836821343302177139 219028517755232014953265709)
      ·
        refine ⟨82135694158212005607474641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 219028517755232014953265709 82135694158212005607474641)
        ·
          refine ⟨61601770618659004205605981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82135694158212005607474641 61601770618659004205605981)
          ·
            refine ⟨23100663981997126577102243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 61601770618659004205605981 23100663981997126577102243)
            ·
              refine ⟨34650995972995689865653365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23100663981997126577102243 34650995972995689865653365)
              ·
                refine ⟨3248530872468345924905003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 34650995972995689865653365 3248530872468345924905003)
                ·
                  refine ⟨4872796308702518887357505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3248530872468345924905003 4872796308702518887357505)
                  ·
                    refine ⟨3654597231526889165518129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4872796308702518887357505 3654597231526889165518129)
                    ·
                      refine ⟨2740947923645166874138597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3654597231526889165518129 2740947923645166874138597)
                      ·
                        rfl

theorem cell23_5337977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 1, 5, 1, 2, 2].length) (baseStart_5337977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5337977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5337977 prefixEnd_5337977 := by exact prefixLift 5337977
  have htrace : WordTrace (prefixWord ++ tailWord_5337977) baseStart_5337977 baseEnd_5337977 := by
    simpa [prefixWord, tailWord_5337977, baseEnd_5337977] using wordTrace_append hprefix tailTrace_5337977
  have hstable : (prefixWord ++ tailWord_5337977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5337977).length < 2 ^ (prefixWord ++ tailWord_5337977).sum := by decide
  have hdescent : baseEnd_5337977 < baseStart_5337977 := by decide
  rcases family_descends (prefixWord ++ tailWord_5337977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5337994 : List Nat := [3, 1, 2, 4, 1, 1, 2, 4, 1, 2, 2]
def baseStart_5337994 : Nat := 118140960795 + 5337994 * 2 ^ 59
def prefixEnd_5337994 : Nat := 4983230072969 + 3 ^ 40 * 5337994 * 2
def baseEnd_5337994 : Nat := 2740956652816293307626019

theorem tailTrace_5337994 : CollatzResearch.WordTrace tailWord_5337994 prefixEnd_5337994 2740956652816293307626019 := by
  unfold tailWord_5337994
  simp only [CollatzResearch.WordTrace]
  refine ⟨48673158955841717409901259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129795090548911246426403357 48673158955841717409901259)
  ·
    refine ⟨73009738433762576114851889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48673158955841717409901259 73009738433762576114851889)
    ·
      refine ⟨54757303825321932086138917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73009738433762576114851889 54757303825321932086138917)
      ·
        refine ⟨10266994467247862266151047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 54757303825321932086138917 10266994467247862266151047)
        ·
          refine ⟨15400491700871793399226571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10266994467247862266151047 15400491700871793399226571)
          ·
            refine ⟨23100737551307690098839857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15400491700871793399226571 23100737551307690098839857)
            ·
              refine ⟨17325553163480767574129893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23100737551307690098839857 17325553163480767574129893)
              ·
                refine ⟨3248541218152643920149355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17325553163480767574129893 3248541218152643920149355)
                ·
                  refine ⟨4872811827228965880224033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3248541218152643920149355 4872811827228965880224033)
                  ·
                    refine ⟨3654608870421724410168025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4872811827228965880224033 3654608870421724410168025)
                    ·
                      refine ⟨2740956652816293307626019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3654608870421724410168025 2740956652816293307626019)
                      ·
                        rfl

theorem cell23_5337994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 2, 4, 1, 2, 2].length) (baseStart_5337994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5337994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5337994 prefixEnd_5337994 := by exact prefixLift 5337994
  have htrace : WordTrace (prefixWord ++ tailWord_5337994) baseStart_5337994 baseEnd_5337994 := by
    simpa [prefixWord, tailWord_5337994, baseEnd_5337994] using wordTrace_append hprefix tailTrace_5337994
  have hstable : (prefixWord ++ tailWord_5337994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5337994).length < 2 ^ (prefixWord ++ tailWord_5337994).sum := by decide
  have hdescent : baseEnd_5337994 < baseStart_5337994 := by decide
  rcases family_descends (prefixWord ++ tailWord_5337994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5338003 : List Nat := [1, 1, 1, 2, 1, 2, 1, 6, 3, 3, 2]
def baseStart_5338003 : Nat := 118140960795 + 5338003 * 2 ^ 59
def prefixEnd_5338003 : Nat := 4983230072969 + 3 ^ 40 * 5338003 * 2
def baseEnd_5338003 : Nat := 2740961274142183772413477

theorem tailTrace_5338003 : CollatzResearch.WordTrace tailWord_5338003 prefixEnd_5338003 2740961274142183772413477 := by
  unfold tailWord_5338003
  simp only [CollatzResearch.WordTrace]
  refine ⟨194692964080334264176682663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129795309386889509451121775 194692964080334264176682663)
  ·
    refine ⟨292039446120501396265023995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194692964080334264176682663 292039446120501396265023995)
    ·
      refine ⟨438059169180752094397535993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 292039446120501396265023995 438059169180752094397535993)
      ·
        refine ⟨328544376885564070798151995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 438059169180752094397535993 328544376885564070798151995)
        ·
          refine ⟨492816565328346106197227993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 328544376885564070798151995 492816565328346106197227993)
          ·
            refine ⟨369612423996259579647920995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 492816565328346106197227993 369612423996259579647920995)
            ·
              refine ⟨554418635994389369471881493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 369612423996259579647920995 554418635994389369471881493)
              ·
                refine ⟨25988373562237001693994445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 554418635994389369471881493 25988373562237001693994445)
                ·
                  refine ⟨9745640085838875635247917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25988373562237001693994445 9745640085838875635247917)
                  ·
                    refine ⟨3654615032189578363217969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9745640085838875635247917 3654615032189578363217969)
                    ·
                      refine ⟨2740961274142183772413477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3654615032189578363217969 2740961274142183772413477)
                      ·
                        rfl

theorem cell23_5338003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 6, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 6, 3, 3, 2].length) (baseStart_5338003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5338003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5338003 prefixEnd_5338003 := by exact prefixLift 5338003
  have htrace : WordTrace (prefixWord ++ tailWord_5338003) baseStart_5338003 baseEnd_5338003 := by
    simpa [prefixWord, tailWord_5338003, baseEnd_5338003] using wordTrace_append hprefix tailTrace_5338003
  have hstable : (prefixWord ++ tailWord_5338003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5338003).length < 2 ^ (prefixWord ++ tailWord_5338003).sum := by decide
  have hdescent : baseEnd_5338003 < baseStart_5338003 := by decide
  rcases family_descends (prefixWord ++ tailWord_5338003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5338016 : List Nat := [2, 1, 1, 4, 1, 1, 2, 2, 2, 3, 4]
def baseStart_5338016 : Nat := 118140960795 + 5338016 * 2 ^ 59
def prefixEnd_5338016 : Nat := 4983230072969 + 3 ^ 40 * 5338016 * 2
def baseEnd_5338016 : Nat := 2740967949390692221550917

theorem tailTrace_5338016 : CollatzResearch.WordTrace tailWord_5338016 prefixEnd_5338016 2740967949390692221550917 := by
  unfold tailWord_5338016
  simp only [CollatzResearch.WordTrace]
  refine ⟨97346719114643583698452951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129795625486191444931270601 97346719114643583698452951)
  ·
    refine ⟨146020078671965375547679427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97346719114643583698452951 146020078671965375547679427)
    ·
      refine ⟨219030118007948063321519141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146020078671965375547679427 219030118007948063321519141)
      ·
        refine ⟨41068147126490261872784839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 219030118007948063321519141 41068147126490261872784839)
        ·
          refine ⟨61602220689735392809177259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41068147126490261872784839 61602220689735392809177259)
          ·
            refine ⟨92403331034603089213765889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61602220689735392809177259 92403331034603089213765889)
            ·
              refine ⟨69302498275952316910324417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 92403331034603089213765889 69302498275952316910324417)
              ·
                refine ⟨51976873706964237682743313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 69302498275952316910324417 51976873706964237682743313)
                ·
                  refine ⟨38982655280223178262057485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 51976873706964237682743313 38982655280223178262057485)
                  ·
                    refine ⟨14618495730083691848271557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 38982655280223178262057485 14618495730083691848271557)
                    ·
                      refine ⟨2740967949390692221550917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14618495730083691848271557 2740967949390692221550917)
                      ·
                        rfl

theorem cell23_5338016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 2, 2, 3, 4].length) (baseStart_5338016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5338016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5338016 prefixEnd_5338016 := by exact prefixLift 5338016
  have htrace : WordTrace (prefixWord ++ tailWord_5338016) baseStart_5338016 baseEnd_5338016 := by
    simpa [prefixWord, tailWord_5338016, baseEnd_5338016] using wordTrace_append hprefix tailTrace_5338016
  have hstable : (prefixWord ++ tailWord_5338016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5338016).length < 2 ^ (prefixWord ++ tailWord_5338016).sum := by decide
  have hdescent : baseEnd_5338016 < baseStart_5338016 := by decide
  rcases family_descends (prefixWord ++ tailWord_5338016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5338070 : List Nat := [5, 2, 1, 1, 2, 1, 1, 2, 2, 1, 5]
def baseStart_5338070 : Nat := 118140960795 + 5338070 * 2 ^ 59
def prefixEnd_5338070 : Nat := 4983230072969 + 3 ^ 40 * 5338070 * 2
def baseEnd_5338070 : Nat := 2740995677346035010275669

theorem tailTrace_5338070 : CollatzResearch.WordTrace tailWord_5338070 prefixEnd_5338070 2740995677346035010275669 := by
  unfold tailWord_5338070
  simp only [CollatzResearch.WordTrace]
  refine ⟨12168462985693220913710729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 129796938514061023079581109 12168462985693220913710729)
  ·
    refine ⟨9126347239269915685283047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12168462985693220913710729 9126347239269915685283047)
    ·
      refine ⟨13689520858904873527924571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9126347239269915685283047 13689520858904873527924571)
      ·
        refine ⟨20534281288357310291886857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13689520858904873527924571 20534281288357310291886857)
        ·
          refine ⟨15400710966267982718915143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20534281288357310291886857 15400710966267982718915143)
          ·
            refine ⟨23101066449401974078372715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15400710966267982718915143 23101066449401974078372715)
            ·
              refine ⟨34651599674102961117559073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23101066449401974078372715 34651599674102961117559073)
              ·
                refine ⟨25988699755577220838169305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34651599674102961117559073 25988699755577220838169305)
                ·
                  refine ⟨19491524816682915628626979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25988699755577220838169305 19491524816682915628626979)
                  ·
                    refine ⟨29237287225024373442940469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19491524816682915628626979 29237287225024373442940469)
                    ·
                      refine ⟨2740995677346035010275669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29237287225024373442940469 2740995677346035010275669)
                      ·
                        rfl

theorem cell23_5338070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 1, 2, 2, 1, 5].length) (baseStart_5338070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5338070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5338070 prefixEnd_5338070 := by exact prefixLift 5338070
  have htrace : WordTrace (prefixWord ++ tailWord_5338070) baseStart_5338070 baseEnd_5338070 := by
    simpa [prefixWord, tailWord_5338070, baseEnd_5338070] using wordTrace_append hprefix tailTrace_5338070
  have hstable : (prefixWord ++ tailWord_5338070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5338070).length < 2 ^ (prefixWord ++ tailWord_5338070).sum := by decide
  have hdescent : baseEnd_5338070 < baseStart_5338070 := by decide
  rcases family_descends (prefixWord ++ tailWord_5338070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5338113 : List Nat := [1, 2, 4, 1, 2, 2, 2, 1, 1, 2, 5]
def baseStart_5338113 : Nat := 118140960795 + 5338113 * 2 ^ 59
def prefixEnd_5338113 : Nat := 4983230072969 + 3 ^ 40 * 5338113 * 2
def baseEnd_5338113 : Nat := 2741017757014178342037971

theorem tailTrace_5338113 : CollatzResearch.WordTrace tailWord_5338113 prefixEnd_5338113 2741017757014178342037971 := by
  unfold tailWord_5338113
  simp only [CollatzResearch.WordTrace]
  refine ⟨194696976109935752963186993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129797984073290501975457995 194696976109935752963186993)
  ·
    refine ⟨146022732082451814722390245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 194696976109935752963186993 146022732082451814722390245)
    ·
      refine ⟨27379262265459715260448171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 146022732082451814722390245 27379262265459715260448171)
      ·
        refine ⟨41068893398189572890672257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27379262265459715260448171 41068893398189572890672257)
        ·
          refine ⟨30801670048642179668004193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41068893398189572890672257 30801670048642179668004193)
          ·
            refine ⟨23101252536481634751003145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30801670048642179668004193 23101252536481634751003145)
            ·
              refine ⟨17325939402361226063252359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23101252536481634751003145 17325939402361226063252359)
              ·
                refine ⟨25988909103541839094878539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17325939402361226063252359 25988909103541839094878539)
                ·
                  refine ⟨38983363655312758642317809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25988909103541839094878539 38983363655312758642317809)
                  ·
                    refine ⟨29237522741484568981738357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 38983363655312758642317809 29237522741484568981738357)
                    ·
                      refine ⟨2741017757014178342037971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29237522741484568981738357 2741017757014178342037971)
                      ·
                        rfl

theorem cell23_5338113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 2, 1, 1, 2, 5].length) (baseStart_5338113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5338113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5338113 prefixEnd_5338113 := by exact prefixLift 5338113
  have htrace : WordTrace (prefixWord ++ tailWord_5338113) baseStart_5338113 baseEnd_5338113 := by
    simpa [prefixWord, tailWord_5338113, baseEnd_5338113] using wordTrace_append hprefix tailTrace_5338113
  have hstable : (prefixWord ++ tailWord_5338113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5338113).length < 2 ^ (prefixWord ++ tailWord_5338113).sum := by decide
  have hdescent : baseEnd_5338113 < baseStart_5338113 := by decide
  rcases family_descends (prefixWord ++ tailWord_5338113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5338140 : List Nat := [2, 2, 3, 1, 4, 1, 1, 1, 1, 3, 4]
def baseStart_5338140 : Nat := 118140960795 + 5338140 * 2 ^ 59
def prefixEnd_5338140 : Nat := 4983230072969 + 3 ^ 40 * 5338140 * 2
def baseEnd_5338140 : Nat := 2741031620991849736400347

theorem tailTrace_5338140 : CollatzResearch.WordTrace tailWord_5338140 prefixEnd_5338140 2741031620991849736400347 := by
  unfold tailWord_5338140
  simp only [CollatzResearch.WordTrace]
  refine ⟨97348980440418968287209937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129798640587225291049613249 97348980440418968287209937)
  ·
    refine ⟨73011735330314226215407453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97348980440418968287209937 73011735330314226215407453)
    ·
      refine ⟨27379400748867834830777795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73011735330314226215407453 27379400748867834830777795)
      ·
        refine ⟨41069101123301752246166693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27379400748867834830777795 41069101123301752246166693)
        ·
          refine ⟨7700456460619078546156255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 41069101123301752246166693 7700456460619078546156255)
          ·
            refine ⟨11550684690928617819234383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7700456460619078546156255 11550684690928617819234383)
            ·
              refine ⟨17326027036392926728851575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11550684690928617819234383 17326027036392926728851575)
              ·
                refine ⟨25989040554589390093277363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17326027036392926728851575 25989040554589390093277363)
                ·
                  refine ⟨38983560831884085139916045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25989040554589390093277363 38983560831884085139916045)
                  ·
                    refine ⟨14618835311956531927468517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 38983560831884085139916045 14618835311956531927468517)
                    ·
                      refine ⟨2741031620991849736400347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14618835311956531927468517 2741031620991849736400347)
                      ·
                        rfl

theorem cell23_5338140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 1, 1, 1, 3, 4].length) (baseStart_5338140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5338140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5338140 prefixEnd_5338140 := by exact prefixLift 5338140
  have htrace : WordTrace (prefixWord ++ tailWord_5338140) baseStart_5338140 baseEnd_5338140 := by
    simpa [prefixWord, tailWord_5338140, baseEnd_5338140] using wordTrace_append hprefix tailTrace_5338140
  have hstable : (prefixWord ++ tailWord_5338140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5338140).length < 2 ^ (prefixWord ++ tailWord_5338140).sum := by decide
  have hdescent : baseEnd_5338140 < baseStart_5338140 := by decide
  rcases family_descends (prefixWord ++ tailWord_5338140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5338193 : List Nat := [1, 2, 2, 1, 3, 1, 2, 3, 3, 5]
def baseStart_5338193 : Nat := 118140960795 + 5338193 * 2 ^ 59
def prefixEnd_5338193 : Nat := 4983230072969 + 3 ^ 40 * 5338193 * 2
def baseEnd_5338193 : Nat := 913686278488846009679201

theorem tailTrace_5338193 : CollatzResearch.WordTrace tailWord_5338193 prefixEnd_5338193 913686278488846009679201 := by
  unfold tailWord_5338193
  simp only [CollatzResearch.WordTrace]
  refine ⟨194699893949645926626099233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129799929299763951084066155 194699893949645926626099233)
  ·
    refine ⟨146024920462234444969574425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 194699893949645926626099233 146024920462234444969574425)
    ·
      refine ⟨109518690346675833727180819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 146024920462234444969574425 109518690346675833727180819)
      ·
        refine ⟨164278035520013750590771229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109518690346675833727180819 164278035520013750590771229)
        ·
          refine ⟨61604263320005156471539211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 164278035520013750590771229 61604263320005156471539211)
          ·
            refine ⟨92406394980007734707308817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61604263320005156471539211 92406394980007734707308817)
            ·
              refine ⟨69304796235005801030481613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 92406394980007734707308817 69304796235005801030481613)
              ·
                refine ⟨25989298588127175386430605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 69304796235005801030481613 25989298588127175386430605)
                ·
                  refine ⟨9745986970547690769911477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25989298588127175386430605 9745986970547690769911477)
                  ·
                    refine ⟨913686278488846009679201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9745986970547690769911477 913686278488846009679201)
                    ·
                      rfl

theorem cell23_5338193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 3, 3, 5].length) (baseStart_5338193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5338193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5338193 prefixEnd_5338193 := by exact prefixLift 5338193
  have htrace : WordTrace (prefixWord ++ tailWord_5338193) baseStart_5338193 baseEnd_5338193 := by
    simpa [prefixWord, tailWord_5338193, baseEnd_5338193] using wordTrace_append hprefix tailTrace_5338193
  have hstable : (prefixWord ++ tailWord_5338193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5338193).length < 2 ^ (prefixWord ++ tailWord_5338193).sum := by decide
  have hdescent : baseEnd_5338193 < baseStart_5338193 := by decide
  rcases family_descends (prefixWord ++ tailWord_5338193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5338200 : List Nat := [2, 1, 2, 2, 1, 3, 1, 3, 1, 5, 2]
def baseStart_5338200 : Nat := 118140960795 + 5338200 * 2 ^ 59
def prefixEnd_5338200 : Nat := 4983230072969 + 3 ^ 40 * 5338200 * 2
def baseEnd_5338200 : Nat := 2741062429831119501650071

theorem tailTrace_5338200 : CollatzResearch.WordTrace tailWord_5338200 prefixEnd_5338200 2741062429831119501650071 := by
  unfold tailWord_5338200
  simp only [CollatzResearch.WordTrace]
  refine ⟨97350074630310283410802027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129800099507080377881069369 97350074630310283410802027)
  ·
    refine ⟨146025111945465425116203041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97350074630310283410802027 146025111945465425116203041)
    ·
      refine ⟨109518833959099068837152281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 146025111945465425116203041 109518833959099068837152281)
      ·
        refine ⟨82139125469324301627864211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 109518833959099068837152281 82139125469324301627864211)
        ·
          refine ⟨123208688203986452441796317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82139125469324301627864211 123208688203986452441796317)
          ·
            refine ⟨46203258076494919665673619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 123208688203986452441796317 46203258076494919665673619)
            ·
              refine ⟨69304887114742379498510429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46203258076494919665673619 69304887114742379498510429)
              ·
                refine ⟨25989332668028392311941411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 69304887114742379498510429 25989332668028392311941411)
                ·
                  refine ⟨38983999002042588467912117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25989332668028392311941411 38983999002042588467912117)
                  ·
                    refine ⟨3654749906441492668866761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 38983999002042588467912117 3654749906441492668866761)
                    ·
                      refine ⟨2741062429831119501650071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3654749906441492668866761 2741062429831119501650071)
                      ·
                        rfl

theorem cell23_5338200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 3, 1, 5, 2].length) (baseStart_5338200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5338200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5338200 prefixEnd_5338200 := by exact prefixLift 5338200
  have htrace : WordTrace (prefixWord ++ tailWord_5338200) baseStart_5338200 baseEnd_5338200 := by
    simpa [prefixWord, tailWord_5338200, baseEnd_5338200] using wordTrace_append hprefix tailTrace_5338200
  have hstable : (prefixWord ++ tailWord_5338200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5338200).length < 2 ^ (prefixWord ++ tailWord_5338200).sum := by decide
  have hdescent : baseEnd_5338200 < baseStart_5338200 := by decide
  rcases family_descends (prefixWord ++ tailWord_5338200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5338217 : List Nat := [1, 2, 1, 1, 1, 7, 1, 2, 2, 3, 2]
def baseStart_5338217 : Nat := 118140960795 + 5338217 * 2 ^ 59
def prefixEnd_5338217 : Nat := 4983230072969 + 3 ^ 40 * 5338217 * 2
def baseEnd_5338217 : Nat := 2741071159002245935137493

theorem tailTrace_5338217 : CollatzResearch.WordTrace tailWord_5338217 prefixEnd_5338217 2741071159002245935137493 := by
  unfold tailWord_5338217
  simp only [CollatzResearch.WordTrace]
  refine ⟨194700769301558978724972905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129800512867705985816648603 194700769301558978724972905)
  ·
    refine ⟨146025576976169234043729679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 194700769301558978724972905 146025576976169234043729679)
    ·
      refine ⟨219038365464253851065594519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146025576976169234043729679 219038365464253851065594519)
      ·
        refine ⟨328557548196380776598391779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 219038365464253851065594519 328557548196380776598391779)
        ·
          refine ⟨492836322294571164897587669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 328557548196380776598391779 492836322294571164897587669)
          ·
            refine ⟨11550851303779011677287211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 492836322294571164897587669 11550851303779011677287211)
            ·
              refine ⟨17326276955668517515930817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11550851303779011677287211 17326276955668517515930817)
              ·
                refine ⟨12994707716751388136948113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17326276955668517515930817 12994707716751388136948113)
                ·
                  refine ⟨9746030787563541102711085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12994707716751388136948113 9746030787563541102711085)
                  ·
                    refine ⟨3654761545336327913516657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9746030787563541102711085 3654761545336327913516657)
                    ·
                      refine ⟨2741071159002245935137493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3654761545336327913516657 2741071159002245935137493)
                      ·
                        rfl

theorem cell23_5338217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 1, 2, 2, 3, 2].length) (baseStart_5338217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5338217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5338217 prefixEnd_5338217 := by exact prefixLift 5338217
  have htrace : WordTrace (prefixWord ++ tailWord_5338217) baseStart_5338217 baseEnd_5338217 := by
    simpa [prefixWord, tailWord_5338217, baseEnd_5338217] using wordTrace_append hprefix tailTrace_5338217
  have hstable : (prefixWord ++ tailWord_5338217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5338217).length < 2 ^ (prefixWord ++ tailWord_5338217).sum := by decide
  have hdescent : baseEnd_5338217 < baseStart_5338217 := by decide
  rcases family_descends (prefixWord ++ tailWord_5338217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5338243 : List Nat := [1, 1, 1, 3, 3, 2, 1, 3, 1, 1, 6]
def baseStart_5338243 : Nat := 118140960795 + 5338243 * 2 ^ 59
def prefixEnd_5338243 : Nat := 4983230072969 + 3 ^ 40 * 5338243 * 2
def baseEnd_5338243 : Nat := 2741084509499262833412373

theorem tailTrace_5338243 : CollatzResearch.WordTrace tailWord_5338243 prefixEnd_5338243 2741084509499262833412373 := by
  unfold tailWord_5338243
  simp only [CollatzResearch.WordTrace]
  refine ⟨194701717599464785165419383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129801145066309856776946255 194701717599464785165419383)
  ·
    refine ⟨292052576399197177748129075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194701717599464785165419383 292052576399197177748129075)
    ·
      refine ⟨438078864598795766622193613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 292052576399197177748129075 438078864598795766622193613)
      ·
        refine ⟨164279574224548412483322605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 438078864598795766622193613 164279574224548412483322605)
        ·
          refine ⟨61604840334205654681245977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 164279574224548412483322605 61604840334205654681245977)
          ·
            refine ⟨46203630250654241010934483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61604840334205654681245977 46203630250654241010934483)
            ·
              refine ⟨69305445375981361516401725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46203630250654241010934483 69305445375981361516401725)
              ·
                refine ⟨25989542015993010568650647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 69305445375981361516401725 25989542015993010568650647)
                ·
                  refine ⟨38984313023989515852975971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25989542015993010568650647 38984313023989515852975971)
                  ·
                    refine ⟨58476469535984273779463957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 38984313023989515852975971 58476469535984273779463957)
                    ·
                      refine ⟨2741084509499262833412373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 58476469535984273779463957 2741084509499262833412373)
                      ·
                        rfl

theorem cell23_5338243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 3, 1, 1, 6].length) (baseStart_5338243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5338243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5338243 prefixEnd_5338243 := by exact prefixLift 5338243
  have htrace : WordTrace (prefixWord ++ tailWord_5338243) baseStart_5338243 baseEnd_5338243 := by
    simpa [prefixWord, tailWord_5338243, baseEnd_5338243] using wordTrace_append hprefix tailTrace_5338243
  have hstable : (prefixWord ++ tailWord_5338243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5338243).length < 2 ^ (prefixWord ++ tailWord_5338243).sum := by decide
  have hdescent : baseEnd_5338243 < baseStart_5338243 := by decide
  rcases family_descends (prefixWord ++ tailWord_5338243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
