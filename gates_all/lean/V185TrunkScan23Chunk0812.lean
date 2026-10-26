import V185TrunkScan23Chunk0811

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_4803384 : List Nat := [2, 1, 2, 1, 3, 2, 1, 2, 2, 5, 2]
def baseStart_4803384 : Nat := 118140960795 + 4803384 * 2 ^ 59
def prefixEnd_4803384 : Nat := 4983230072969 + 3 ^ 40 * 4803384 * 2
def baseEnd_4803384 : Nat := 2466444760116139971709645

theorem tailTrace_4803384 : CollatzResearch.WordTrace tailWord_4803384 prefixEnd_4803384 2466444760116139971709645 := by
  unfold tailWord_4803384
  simp only [CollatzResearch.WordTrace]
  refine ⟨87596903615083797760348603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116795871486778397013798137 87596903615083797760348603)
  ·
    refine ⟨131395355422625696640522905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87596903615083797760348603 131395355422625696640522905)
    ·
      refine ⟨98546516566969272480392179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 131395355422625696640522905 98546516566969272480392179)
      ·
        refine ⟨147819774850453908720588269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98546516566969272480392179 147819774850453908720588269)
        ·
          refine ⟨55432415568920215770220601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 147819774850453908720588269 55432415568920215770220601)
          ·
            refine ⟨41574311676690161827665451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55432415568920215770220601 41574311676690161827665451)
            ·
              refine ⟨62361467515035242741498177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41574311676690161827665451 62361467515035242741498177)
              ·
                refine ⟨46771100636276432056123633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 62361467515035242741498177 46771100636276432056123633)
                ·
                  refine ⟨35078325477207324042092725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 46771100636276432056123633 35078325477207324042092725)
                  ·
                    refine ⟨3288593013488186628946193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 35078325477207324042092725 3288593013488186628946193)
                    ·
                      refine ⟨2466444760116139971709645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3288593013488186628946193 2466444760116139971709645)
                      ·
                        rfl

theorem cell23_4803384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 2, 2, 5, 2].length) (baseStart_4803384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4803384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4803384 prefixEnd_4803384 := by exact prefixLift 4803384
  have htrace : WordTrace (prefixWord ++ tailWord_4803384) baseStart_4803384 baseEnd_4803384 := by
    simpa [prefixWord, tailWord_4803384, baseEnd_4803384] using wordTrace_append hprefix tailTrace_4803384
  have hstable : (prefixWord ++ tailWord_4803384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4803384).length < 2 ^ (prefixWord ++ tailWord_4803384).sum := by decide
  have hdescent : baseEnd_4803384 < baseStart_4803384 := by decide
  rcases family_descends (prefixWord ++ tailWord_4803384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4803431 : List Nat := [1, 1, 5, 1, 2, 2, 2, 1, 2, 4, 2]
def baseStart_4803431 : Nat := 118140960795 + 4803431 * 2 ^ 59
def prefixEnd_4803431 : Nat := 4983230072969 + 3 ^ 40 * 4803431 * 2
def baseEnd_4803431 : Nat := 2466468893706901287821929

theorem tailTrace_4803431 : CollatzResearch.WordTrace tailWord_4803431 prefixEnd_4803431 2466468893706901287821929 := by
  unfold tailWord_4803431
  simp only [CollatzResearch.WordTrace]
  refine ⟨175195521460997322547658147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116797014307331548365105431 175195521460997322547658147)
  ·
    refine ⟨262793282191495983821487221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175195521460997322547658147 262793282191495983821487221)
    ·
      refine ⟨24636870205452748483264427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 262793282191495983821487221 24636870205452748483264427)
      ·
        refine ⟨36955305308179122724896641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24636870205452748483264427 36955305308179122724896641)
        ·
          refine ⟨27716478981134342043672481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36955305308179122724896641 27716478981134342043672481)
          ·
            refine ⟨20787359235850756532754361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27716478981134342043672481 20787359235850756532754361)
            ·
              refine ⟨15590519426888067399565771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20787359235850756532754361 15590519426888067399565771)
              ·
                refine ⟨23385779140332101099348657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15590519426888067399565771 23385779140332101099348657)
                ·
                  refine ⟨17539334355249075824511493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23385779140332101099348657 17539334355249075824511493)
                  ·
                    refine ⟨3288625191609201717095905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17539334355249075824511493 3288625191609201717095905)
                    ·
                      refine ⟨2466468893706901287821929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3288625191609201717095905 2466468893706901287821929)
                      ·
                        rfl

theorem cell23_4803431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 2, 1, 2, 4, 2].length) (baseStart_4803431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4803431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4803431 prefixEnd_4803431 := by exact prefixLift 4803431
  have htrace : WordTrace (prefixWord ++ tailWord_4803431) baseStart_4803431 baseEnd_4803431 := by
    simpa [prefixWord, tailWord_4803431, baseEnd_4803431] using wordTrace_append hprefix tailTrace_4803431
  have hstable : (prefixWord ++ tailWord_4803431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4803431).length < 2 ^ (prefixWord ++ tailWord_4803431).sum := by decide
  have hdescent : baseEnd_4803431 < baseStart_4803431 := by decide
  rcases family_descends (prefixWord ++ tailWord_4803431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4803514 : List Nat := [3, 1, 1, 1, 2, 1, 5, 2, 1, 6]
def baseStart_4803514 : Nat := 118140960795 + 4803514 * 2 ^ 59
def prefixEnd_4803514 : Nat := 4983230072969 + 3 ^ 40 * 4803514 * 2
def baseEnd_4803514 : Nat := 822170504200408154361349

theorem tailTrace_4803514 : CollatzResearch.WordTrace tailWord_4803514 prefixEnd_4803514 822170504200408154361349 := by
  unfold tailWord_4803514
  simp only [CollatzResearch.WordTrace]
  refine ⟨43799637179924156930732399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 116799032479797751815286397 43799637179924156930732399)
  ·
    refine ⟨65699455769886235396098599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43799637179924156930732399 65699455769886235396098599)
    ·
      refine ⟨98549183654829353094147899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65699455769886235396098599 98549183654829353094147899)
      ·
        refine ⟨147823775482244029641221849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98549183654829353094147899 147823775482244029641221849)
        ·
          refine ⟨110867831611683022230916387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 147823775482244029641221849 110867831611683022230916387)
          ·
            refine ⟨166301747417524533346374581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 110867831611683022230916387 166301747417524533346374581)
            ·
              refine ⟨15590788820392925001222617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 166301747417524533346374581 15590788820392925001222617)
              ·
                refine ⟨11693091615294693750916963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15590788820392925001222617 11693091615294693750916963)
                ·
                  refine ⟨17539637422942040626375445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11693091615294693750916963 17539637422942040626375445)
                  ·
                    refine ⟨822170504200408154361349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17539637422942040626375445 822170504200408154361349)
                    ·
                      rfl

theorem cell23_4803514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 5, 2, 1, 6].length) (baseStart_4803514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4803514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4803514 prefixEnd_4803514 := by exact prefixLift 4803514
  have htrace : WordTrace (prefixWord ++ tailWord_4803514) baseStart_4803514 baseEnd_4803514 := by
    simpa [prefixWord, tailWord_4803514, baseEnd_4803514] using wordTrace_append hprefix tailTrace_4803514
  have hstable : (prefixWord ++ tailWord_4803514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4803514).length < 2 ^ (prefixWord ++ tailWord_4803514).sum := by decide
  have hdescent : baseEnd_4803514 < baseStart_4803514 := by decide
  rcases family_descends (prefixWord ++ tailWord_4803514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4803518 : List Nat := [4, 2, 1, 1, 1, 2, 5, 1, 1, 5]
def baseStart_4803518 : Nat := 118140960795 + 4803518 * 2 ^ 59
def prefixEnd_4803518 : Nat := 4983230072969 + 3 ^ 40 * 4803518 * 2
def baseEnd_4803518 : Nat := 822171188841280815811343

theorem tailTrace_4803518 : CollatzResearch.WordTrace tailWord_4803518 prefixEnd_4803518 822171188841280815811343 := by
  unfold tailWord_4803518
  simp only [CollatzResearch.WordTrace]
  refine ⟨21899836826460267050759401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 116799129741121424270716805 21899836826460267050759401)
  ·
    refine ⟨16424877619845200288069551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21899836826460267050759401 16424877619845200288069551)
    ·
      refine ⟨24637316429767800432104327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16424877619845200288069551 24637316429767800432104327)
      ·
        refine ⟨36955974644651700648156491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24637316429767800432104327 36955974644651700648156491)
        ·
          refine ⟨55433961966977550972234737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36955974644651700648156491 55433961966977550972234737)
          ·
            refine ⟨41575471475233163229176053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55433961966977550972234737 41575471475233163229176053)
            ·
              refine ⟨3897700450803109052735255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 41575471475233163229176053 3897700450803109052735255)
              ·
                refine ⟨5846550676204663579102883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3897700450803109052735255 5846550676204663579102883)
                ·
                  refine ⟨8769826014306995368654325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5846550676204663579102883 8769826014306995368654325)
                  ·
                    refine ⟨822171188841280815811343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8769826014306995368654325 822171188841280815811343)
                    ·
                      rfl

theorem cell23_4803518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 5, 1, 1, 5].length) (baseStart_4803518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4803518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4803518 prefixEnd_4803518 := by exact prefixLift 4803518
  have htrace : WordTrace (prefixWord ++ tailWord_4803518) baseStart_4803518 baseEnd_4803518 := by
    simpa [prefixWord, tailWord_4803518, baseEnd_4803518] using wordTrace_append hprefix tailTrace_4803518
  have hstable : (prefixWord ++ tailWord_4803518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4803518).length < 2 ^ (prefixWord ++ tailWord_4803518).sum := by decide
  have hdescent : baseEnd_4803518 < baseStart_4803518 := by decide
  rcases family_descends (prefixWord ++ tailWord_4803518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4803526 : List Nat := [6, 1, 3, 1, 1, 1, 1, 4, 1, 4]
def baseStart_4803526 : Nat := 118140960795 + 4803526 * 2 ^ 59
def prefixEnd_4803526 : Nat := 4983230072969 + 3 ^ 40 * 4803526 * 2
def baseEnd_4803526 : Nat := 822172558123026138711331

theorem tailTrace_4803526 : CollatzResearch.WordTrace tailWord_4803526 prefixEnd_4803526 822172558123026138711331 := by
  unfold tailWord_4803526
  simp only [CollatzResearch.WordTrace]
  refine ⟨5474968324864161055386451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 116799324263768769181577621 5474968324864161055386451)
  ·
    refine ⟨8212452487296241583079677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5474968324864161055386451 8212452487296241583079677)
    ·
      refine ⟨3079669682736090593654879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8212452487296241583079677 3079669682736090593654879)
      ·
        refine ⟨4619504524104135890482319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3079669682736090593654879 4619504524104135890482319)
        ·
          refine ⟨6929256786156203835723479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4619504524104135890482319 6929256786156203835723479)
          ·
            refine ⟨10393885179234305753585219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6929256786156203835723479 10393885179234305753585219)
            ·
              refine ⟨15590827768851458630377829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10393885179234305753585219 15590827768851458630377829)
              ·
                refine ⟨2923280206659648493195843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15590827768851458630377829 2923280206659648493195843)
                ·
                  refine ⟨4384920309989472739793765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2923280206659648493195843 4384920309989472739793765)
                  ·
                    refine ⟨822172558123026138711331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4384920309989472739793765 822172558123026138711331)
                    ·
                      rfl

theorem cell23_4803526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 1, 4, 1, 4].length) (baseStart_4803526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4803526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4803526 prefixEnd_4803526 := by exact prefixLift 4803526
  have htrace : WordTrace (prefixWord ++ tailWord_4803526) baseStart_4803526 baseEnd_4803526 := by
    simpa [prefixWord, tailWord_4803526, baseEnd_4803526] using wordTrace_append hprefix tailTrace_4803526
  have hstable : (prefixWord ++ tailWord_4803526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4803526).length < 2 ^ (prefixWord ++ tailWord_4803526).sum := by decide
  have hdescent : baseEnd_4803526 < baseStart_4803526 := by decide
  rcases family_descends (prefixWord ++ tailWord_4803526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4803531 : List Nat := [1, 1, 1, 1, 3, 5, 1, 4, 2, 4]
def baseStart_4803531 : Nat := 118140960795 + 4803531 * 2 ^ 59
def prefixEnd_4803531 : Nat := 4983230072969 + 3 ^ 40 * 4803531 * 2
def baseEnd_4803531 : Nat := 822173413924116965523823

theorem tailTrace_4803531 : CollatzResearch.WordTrace tailWord_4803531 prefixEnd_4803531 822173413924116965523823 := by
  unfold tailWord_4803531
  simp only [CollatzResearch.WordTrace]
  refine ⟨175199168760635039626298447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116799445840423359750865631 175199168760635039626298447)
  ·
    refine ⟨262798753140952559439447671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175199168760635039626298447 262798753140952559439447671)
    ·
      refine ⟨394198129711428839159171507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 262798753140952559439447671 394198129711428839159171507)
      ·
        refine ⟨591297194567143258738757261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 394198129711428839159171507 591297194567143258738757261)
        ·
          refine ⟨221736447962678722027033973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 591297194567143258738757261 221736447962678722027033973)
          ·
            refine ⟨20787791996501130190034435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 221736447962678722027033973 20787791996501130190034435)
            ·
              refine ⟨31181687994751695285051653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20787791996501130190034435 31181687994751695285051653)
              ·
                refine ⟨5846566499015942865947185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31181687994751695285051653 5846566499015942865947185)
                ·
                  refine ⟨4384924874261957149460389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5846566499015942865947185 4384924874261957149460389)
                  ·
                    refine ⟨822173413924116965523823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4384924874261957149460389 822173413924116965523823)
                    ·
                      rfl

theorem cell23_4803531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 1, 4, 2, 4].length) (baseStart_4803531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4803531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4803531 prefixEnd_4803531 := by exact prefixLift 4803531
  have htrace : WordTrace (prefixWord ++ tailWord_4803531) baseStart_4803531 baseEnd_4803531 := by
    simpa [prefixWord, tailWord_4803531, baseEnd_4803531] using wordTrace_append hprefix tailTrace_4803531
  have hstable : (prefixWord ++ tailWord_4803531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4803531).length < 2 ^ (prefixWord ++ tailWord_4803531).sum := by decide
  have hdescent : baseEnd_4803531 < baseStart_4803531 := by decide
  rcases family_descends (prefixWord ++ tailWord_4803531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4803544 : List Nat := [2, 1, 2, 2, 2, 3, 3, 8]
def baseStart_4803544 : Nat := 118140960795 + 4803544 * 2 ^ 59
def prefixEnd_4803544 : Nat := 4983230072969 + 3 ^ 40 * 4803544 * 2
def baseEnd_4803544 : Nat := 91352848778550346137367

theorem tailTrace_4803544 : CollatzResearch.WordTrace tailWord_4803544 prefixEnd_4803544 91352848778550346137367 := by
  unfold tailWord_4803544
  simp only [CollatzResearch.WordTrace]
  refine ⟨87599821454793971423260843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116799761939725295231014457 87599821454793971423260843)
  ·
    refine ⟨131399732182190957134891265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87599821454793971423260843 131399732182190957134891265)
    ·
      refine ⟨98549799136643217851168449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 131399732182190957134891265 98549799136643217851168449)
      ·
        refine ⟨73912349352482413388376337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 98549799136643217851168449 73912349352482413388376337)
        ·
          refine ⟨55434262014361810041282253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73912349352482413388376337 55434262014361810041282253)
          ·
            refine ⟨20787848255385678765480845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55434262014361810041282253 20787848255385678765480845)
            ·
              refine ⟨7795443095769629537055317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20787848255385678765480845 7795443095769629537055317)
              ·
                refine ⟨91352848778550346137367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7795443095769629537055317 91352848778550346137367)
                ·
                  rfl

theorem cell23_4803544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 3, 8].length) (baseStart_4803544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4803544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4803544 prefixEnd_4803544 := by exact prefixLift 4803544
  have htrace : WordTrace (prefixWord ++ tailWord_4803544) baseStart_4803544 baseEnd_4803544 := by
    simpa [prefixWord, tailWord_4803544, baseEnd_4803544] using wordTrace_append hprefix tailTrace_4803544
  have hstable : (prefixWord ++ tailWord_4803544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4803544).length < 2 ^ (prefixWord ++ tailWord_4803544).sum := by decide
  have hdescent : baseEnd_4803544 < baseStart_4803544 := by decide
  rcases family_descends (prefixWord ++ tailWord_4803544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4803582 : List Nat := [4, 2, 2, 2, 2, 2, 1, 2, 2, 4]
def baseStart_4803582 : Nat := 118140960795 + 4803582 * 2 ^ 59
def prefixEnd_4803582 : Nat := 4983230072969 + 3 ^ 40 * 4803582 * 2
def baseEnd_4803582 : Nat := 822182143095243399011245

theorem tailTrace_4803582 : CollatzResearch.WordTrace tailWord_4803582 prefixEnd_4803582 822182143095243399011245 := by
  unfold tailWord_4803582
  simp only [CollatzResearch.WordTrace]
  refine ⟨21900128610431284417050625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 116800685922300183557603333 21900128610431284417050625)
  ·
    refine ⟨16425096457823463312787969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21900128610431284417050625 16425096457823463312787969)
    ·
      refine ⟨12318822343367597484590977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16425096457823463312787969 12318822343367597484590977)
      ·
        refine ⟨9239116757525698113443233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12318822343367597484590977 9239116757525698113443233)
        ·
          refine ⟨6929337568144273585082425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9239116757525698113443233 6929337568144273585082425)
          ·
            refine ⟨5197003176108205188811819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6929337568144273585082425 5197003176108205188811819)
            ·
              refine ⟨7795504764162307783217729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5197003176108205188811819 7795504764162307783217729)
              ·
                refine ⟨5846628573121730837413297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7795504764162307783217729 5846628573121730837413297)
                ·
                  refine ⟨4384971429841298128059973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5846628573121730837413297 4384971429841298128059973)
                  ·
                    refine ⟨822182143095243399011245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4384971429841298128059973 822182143095243399011245)
                    ·
                      rfl

theorem cell23_4803582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 2, 1, 2, 2, 4].length) (baseStart_4803582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4803582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4803582 prefixEnd_4803582 := by exact prefixLift 4803582
  have htrace : WordTrace (prefixWord ++ tailWord_4803582) baseStart_4803582 baseEnd_4803582 := by
    simpa [prefixWord, tailWord_4803582, baseEnd_4803582] using wordTrace_append hprefix tailTrace_4803582
  have hstable : (prefixWord ++ tailWord_4803582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4803582).length < 2 ^ (prefixWord ++ tailWord_4803582).sum := by decide
  have hdescent : baseEnd_4803582 < baseStart_4803582 := by decide
  rcases family_descends (prefixWord ++ tailWord_4803582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4803615 : List Nat := [1, 1, 2, 4, 1, 4, 2, 2, 1, 3, 2]
def baseStart_4803615 : Nat := 118140960795 + 4803615 * 2 ^ 59
def prefixEnd_4803615 : Nat := 4983230072969 + 3 ^ 40 * 4803615 * 2
def baseEnd_4803615 : Nat := 2466563374147328567921083

theorem tailTrace_4803615 : CollatzResearch.WordTrace tailWord_4803615 prefixEnd_4803615 2466563374147328567921083 := by
  unfold tailWord_4803615
  simp only [CollatzResearch.WordTrace]
  refine ⟨175202232492330721972356299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116801488328220481314904199 175202232492330721972356299)
  ·
    refine ⟨262803348738496082958534449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175202232492330721972356299 262803348738496082958534449)
    ·
      refine ⟨197102511553872062218900837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 262803348738496082958534449 197102511553872062218900837)
      ·
        refine ⟨36956720916351011666043907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 197102511553872062218900837 36956720916351011666043907)
        ·
          refine ⟨55435081374526517499065861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36956720916351011666043907 55435081374526517499065861)
          ·
            refine ⟨10394077757723722031074849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 55435081374526517499065861 10394077757723722031074849)
            ·
              refine ⟨7795558318292791523306137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10394077757723722031074849 7795558318292791523306137)
              ·
                refine ⟨5846668738719593642479603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7795558318292791523306137 5846668738719593642479603)
                ·
                  refine ⟨8770003108079390463719405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5846668738719593642479603 8770003108079390463719405)
                  ·
                    refine ⟨3288751165529771423894777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8770003108079390463719405 3288751165529771423894777)
                    ·
                      refine ⟨2466563374147328567921083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3288751165529771423894777 2466563374147328567921083)
                      ·
                        rfl

theorem cell23_4803615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 2, 2, 1, 3, 2].length) (baseStart_4803615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4803615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4803615 prefixEnd_4803615 := by exact prefixLift 4803615
  have htrace : WordTrace (prefixWord ++ tailWord_4803615) baseStart_4803615 baseEnd_4803615 := by
    simpa [prefixWord, tailWord_4803615, baseEnd_4803615] using wordTrace_append hprefix tailTrace_4803615
  have hstable : (prefixWord ++ tailWord_4803615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4803615).length < 2 ^ (prefixWord ++ tailWord_4803615).sum := by decide
  have hdescent : baseEnd_4803615 < baseStart_4803615 := by decide
  rcases family_descends (prefixWord ++ tailWord_4803615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4803628 : List Nat := [2, 2, 1, 1, 1, 2, 3, 1, 6, 2, 2]
def baseStart_4803628 : Nat := 118140960795 + 4803628 * 2 ^ 59
def prefixEnd_4803628 : Nat := 4983230072969 + 3 ^ 40 * 4803628 * 2
def baseEnd_4803628 : Nat := 2466570049395837017058523

theorem tailTrace_4803628 : CollatzResearch.WordTrace tailWord_4803628 prefixEnd_4803628 2466570049395837017058523 := by
  unfold tailWord_4803628
  simp only [CollatzResearch.WordTrace]
  refine ⟨87601353320641812596289769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116801804427522416795053025 87601353320641812596289769)
  ·
    refine ⟨65701014990481359447217327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87601353320641812596289769 65701014990481359447217327)
    ·
      refine ⟨98551522485722039170825991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65701014990481359447217327 98551522485722039170825991)
      ·
        refine ⟨147827283728583058756238987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98551522485722039170825991 147827283728583058756238987)
        ·
          refine ⟨221740925592874588134358481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 147827283728583058756238987 221740925592874588134358481)
          ·
            refine ⟨166305694194655941100768861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 221740925592874588134358481 166305694194655941100768861)
            ·
              refine ⟨62364635322995977912788323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 166305694194655941100768861 62364635322995977912788323)
              ·
                refine ⟨93546952984493966869182485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62364635322995977912788323 93546952984493966869182485)
                ·
                  refine ⟨4385013421148154696992929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 93546952984493966869182485 4385013421148154696992929)
                  ·
                    refine ⟨3288760065861116022744697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4385013421148154696992929 3288760065861116022744697)
                    ·
                      refine ⟨2466570049395837017058523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3288760065861116022744697 2466570049395837017058523)
                      ·
                        rfl

theorem cell23_4803628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 6, 2, 2].length) (baseStart_4803628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4803628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4803628 prefixEnd_4803628 := by exact prefixLift 4803628
  have htrace : WordTrace (prefixWord ++ tailWord_4803628) baseStart_4803628 baseEnd_4803628 := by
    simpa [prefixWord, tailWord_4803628, baseEnd_4803628] using wordTrace_append hprefix tailTrace_4803628
  have hstable : (prefixWord ++ tailWord_4803628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4803628).length < 2 ^ (prefixWord ++ tailWord_4803628).sum := by decide
  have hdescent : baseEnd_4803628 < baseStart_4803628 := by decide
  rcases family_descends (prefixWord ++ tailWord_4803628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4803645 : List Nat := [1, 4, 1, 3, 1, 2, 2, 1, 4, 2, 2]
def baseStart_4803645 : Nat := 118140960795 + 4803645 * 2 ^ 59
def prefixEnd_4803645 : Nat := 4983230072969 + 3 ^ 40 * 4803645 * 2
def baseEnd_4803645 : Nat := 2466578778566963450545945

theorem tailTrace_4803645 : CollatzResearch.WordTrace tailWord_4803645 prefixEnd_4803645 2466578778566963450545945 := by
  unfold tailWord_4803645
  simp only [CollatzResearch.WordTrace]
  refine ⟨175203326682222037095948389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116802217788148024730632259 175203326682222037095948389)
  ·
    refine ⟨32850623752916631955490323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 175203326682222037095948389 32850623752916631955490323)
    ·
      refine ⟨49275935629374947933235485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32850623752916631955490323 49275935629374947933235485)
      ·
        refine ⟨18478475861015605474963307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49275935629374947933235485 18478475861015605474963307)
        ·
          refine ⟨27717713791523408212444961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18478475861015605474963307 27717713791523408212444961)
          ·
            refine ⟨20788285343642556159333721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27717713791523408212444961 20788285343642556159333721)
            ·
              refine ⟨15591214007731917119500291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20788285343642556159333721 15591214007731917119500291)
              ·
                refine ⟨23386821011597875679250437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15591214007731917119500291 23386821011597875679250437)
                ·
                  refine ⟨4385028939674601689859457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23386821011597875679250437 4385028939674601689859457)
                  ·
                    refine ⟨3288771704755951267394593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4385028939674601689859457 3288771704755951267394593)
                    ·
                      refine ⟨2466578778566963450545945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3288771704755951267394593 2466578778566963450545945)
                      ·
                        rfl

theorem cell23_4803645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 2, 1, 4, 2, 2].length) (baseStart_4803645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4803645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4803645 prefixEnd_4803645 := by exact prefixLift 4803645
  have htrace : WordTrace (prefixWord ++ tailWord_4803645) baseStart_4803645 baseEnd_4803645 := by
    simpa [prefixWord, tailWord_4803645, baseEnd_4803645] using wordTrace_append hprefix tailTrace_4803645
  have hstable : (prefixWord ++ tailWord_4803645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4803645).length < 2 ^ (prefixWord ++ tailWord_4803645).sum := by decide
  have hdescent : baseEnd_4803645 < baseStart_4803645 := by decide
  rcases family_descends (prefixWord ++ tailWord_4803645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4803664 : List Nat := [2, 1, 1, 1, 1, 3, 1, 3, 3, 7]
def baseStart_4803664 : Nat := 118140960795 + 4803664 * 2 ^ 59
def prefixEnd_4803664 : Nat := 4983230072969 + 3 ^ 40 * 4803664 * 2
def baseEnd_4803664 : Nat := 822196178233132958736119

theorem tailTrace_4803664 : CollatzResearch.WordTrace tailWord_4803664 prefixEnd_4803664 822196178233132958736119 := by
  unfold tailWord_4803664
  simp only [CollatzResearch.WordTrace]
  refine ⟨87602009834576601670445023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116802679779435468893926697 87602009834576601670445023)
  ·
    refine ⟨131403014751864902505667535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87602009834576601670445023 131403014751864902505667535)
    ·
      refine ⟨197104522127797353758501303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131403014751864902505667535 197104522127797353758501303)
      ·
        refine ⟨295656783191696030637751955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 197104522127797353758501303 295656783191696030637751955)
        ·
          refine ⟨443485174787544045956627933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 295656783191696030637751955 443485174787544045956627933)
          ·
            refine ⟨166306940545329017233735475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 443485174787544045956627933 166306940545329017233735475)
            ·
              refine ⟨249460410817993525850603213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 166306940545329017233735475 249460410817993525850603213)
              ·
                refine ⟨93547654056747572193976205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 249460410817993525850603213 93547654056747572193976205)
                ·
                  refine ⟨35080370271280339572741077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 93547654056747572193976205 35080370271280339572741077)
                  ·
                    refine ⟨822196178233132958736119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 35080370271280339572741077 822196178233132958736119)
                    ·
                      rfl

theorem cell23_4803664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 3, 3, 7].length) (baseStart_4803664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4803664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4803664 prefixEnd_4803664 := by exact prefixLift 4803664
  have htrace : WordTrace (prefixWord ++ tailWord_4803664) baseStart_4803664 baseEnd_4803664 := by
    simpa [prefixWord, tailWord_4803664, baseEnd_4803664] using wordTrace_append hprefix tailTrace_4803664
  have hstable : (prefixWord ++ tailWord_4803664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4803664).length < 2 ^ (prefixWord ++ tailWord_4803664).sum := by decide
  have hdescent : baseEnd_4803664 < baseStart_4803664 := by decide
  rcases family_descends (prefixWord ++ tailWord_4803664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4803681 : List Nat := [1, 2, 3, 1, 1, 2, 3, 3, 2, 5]
def baseStart_4803681 : Nat := 118140960795 + 4803681 * 2 ^ 59
def prefixEnd_4803681 : Nat := 4983230072969 + 3 ^ 40 * 4803681 * 2
def baseEnd_4803681 : Nat := 822199087956841769898593

theorem tailTrace_4803681 : CollatzResearch.WordTrace tailWord_4803681 prefixEnd_4803681 822199087956841769898593 := by
  unfold tailWord_4803681
  simp only [CollatzResearch.WordTrace]
  refine ⟨175204639710091615244258897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116803093140061076829505931 175204639710091615244258897)
  ·
    refine ⟨131403479782568711433194173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 175204639710091615244258897 131403479782568711433194173)
    ·
      refine ⟨49276304918463266787447815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 131403479782568711433194173 49276304918463266787447815)
      ·
        refine ⟨73914457377694900181171723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49276304918463266787447815 73914457377694900181171723)
        ·
          refine ⟨110871686066542350271757585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73914457377694900181171723 110871686066542350271757585)
          ·
            refine ⟨83153764549906762703818189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 110871686066542350271757585 83153764549906762703818189)
            ·
              refine ⟨31182661706215036013931821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 83153764549906762703818189 31182661706215036013931821)
              ·
                refine ⟨11693498139830638505224433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31182661706215036013931821 11693498139830638505224433)
                ·
                  refine ⟨8770123604872978878918325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11693498139830638505224433 8770123604872978878918325)
                  ·
                    refine ⟨822199087956841769898593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8770123604872978878918325 822199087956841769898593)
                    ·
                      rfl

theorem cell23_4803681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 3, 3, 2, 5].length) (baseStart_4803681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4803681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4803681 prefixEnd_4803681 := by exact prefixLift 4803681
  have htrace : WordTrace (prefixWord ++ tailWord_4803681) baseStart_4803681 baseEnd_4803681 := by
    simpa [prefixWord, tailWord_4803681, baseEnd_4803681] using wordTrace_append hprefix tailTrace_4803681
  have hstable : (prefixWord ++ tailWord_4803681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4803681).length < 2 ^ (prefixWord ++ tailWord_4803681).sum := by decide
  have hdescent : baseEnd_4803681 < baseStart_4803681 := by decide
  rcases family_descends (prefixWord ++ tailWord_4803681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4803711 : List Nat := [1, 1, 2, 2, 1, 1, 1, 1, 9, 4]
def baseStart_4803711 : Nat := 118140960795 + 4803711 * 2 ^ 59
def prefixEnd_4803711 : Nat := 4983230072969 + 3 ^ 40 * 4803711 * 2
def baseEnd_4803711 : Nat := 822204222763386730773547

theorem tailTrace_4803711 : CollatzResearch.WordTrace tailWord_4803711 prefixEnd_4803711 822204222763386730773547 := by
  unfold tailWord_4803711
  simp only [CollatzResearch.WordTrace]
  refine ⟨175205733899982930367850987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116803822599988620245233991 175205733899982930367850987)
  ·
    refine ⟨262808600849974395551776481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175205733899982930367850987 262808600849974395551776481)
    ·
      refine ⟨197106450637480796663832361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 262808600849974395551776481 197106450637480796663832361)
      ·
        refine ⟨147829837978110597497874271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 197106450637480796663832361 147829837978110597497874271)
        ·
          refine ⟨221744756967165896246811407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 147829837978110597497874271 221744756967165896246811407)
          ·
            refine ⟨332617135450748844370217111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 221744756967165896246811407 332617135450748844370217111)
            ·
              refine ⟨498925703176123266555325667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 332617135450748844370217111 498925703176123266555325667)
              ·
                refine ⟨748388554764184899832988501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 498925703176123266555325667 748388554764184899832988501)
                ·
                  refine ⟨4385089188071395897458917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 748388554764184899832988501 4385089188071395897458917)
                  ·
                    refine ⟨822204222763386730773547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4385089188071395897458917 822204222763386730773547)
                    ·
                      rfl

theorem cell23_4803711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 1, 9, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 1, 9, 4].length) (baseStart_4803711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4803711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4803711 prefixEnd_4803711 := by exact prefixLift 4803711
  have htrace : WordTrace (prefixWord ++ tailWord_4803711) baseStart_4803711 baseEnd_4803711 := by
    simpa [prefixWord, tailWord_4803711, baseEnd_4803711] using wordTrace_append hprefix tailTrace_4803711
  have hstable : (prefixWord ++ tailWord_4803711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4803711).length < 2 ^ (prefixWord ++ tailWord_4803711).sum := by decide
  have hdescent : baseEnd_4803711 < baseStart_4803711 := by decide
  rcases family_descends (prefixWord ++ tailWord_4803711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4803735 : List Nat := [1, 1, 3, 3, 3, 3, 1, 1, 2, 1, 4]
def baseStart_4803735 : Nat := 118140960795 + 4803735 * 2 ^ 59
def prefixEnd_4803735 : Nat := 4983230072969 + 3 ^ 40 * 4803735 * 2
def baseEnd_4803735 : Nat := 2466624991825868098420531

theorem tailTrace_4803735 : CollatzResearch.WordTrace tailWord_4803735 prefixEnd_4803735 2466624991825868098420531 := by
  unfold tailWord_4803735
  simp only [CollatzResearch.WordTrace]
  refine ⟨175206609251895982466724659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116804406167930654977816439 175206609251895982466724659)
  ·
    refine ⟨262809913877843973700086989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175206609251895982466724659 262809913877843973700086989)
    ·
      refine ⟨98553717704191490137532621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 262809913877843973700086989 98553717704191490137532621)
      ·
        refine ⟨36957644139071808801574733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 98553717704191490137532621 36957644139071808801574733)
        ·
          refine ⟨13859116552151928300590525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36957644139071808801574733 13859116552151928300590525)
          ·
            refine ⟨5197168707056973112721447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13859116552151928300590525 5197168707056973112721447)
            ·
              refine ⟨7795753060585459669082171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5197168707056973112721447 7795753060585459669082171)
              ·
                refine ⟨11693629590878189503623257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7795753060585459669082171 11693629590878189503623257)
                ·
                  refine ⟨8770222193158642127717443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11693629590878189503623257 8770222193158642127717443)
                  ·
                    refine ⟨13155333289737963191576165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8770222193158642127717443 13155333289737963191576165)
                    ·
                      refine ⟨2466624991825868098420531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13155333289737963191576165 2466624991825868098420531)
                      ·
                        rfl

theorem cell23_4803735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 3, 1, 1, 2, 1, 4].length) (baseStart_4803735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4803735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4803735 prefixEnd_4803735 := by exact prefixLift 4803735
  have htrace : WordTrace (prefixWord ++ tailWord_4803735) baseStart_4803735 baseEnd_4803735 := by
    simpa [prefixWord, tailWord_4803735, baseEnd_4803735] using wordTrace_append hprefix tailTrace_4803735
  have hstable : (prefixWord ++ tailWord_4803735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4803735).length < 2 ^ (prefixWord ++ tailWord_4803735).sum := by decide
  have hdescent : baseEnd_4803735 < baseStart_4803735 := by decide
  rcases family_descends (prefixWord ++ tailWord_4803735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4803741 : List Nat := [1, 4, 2, 1, 1, 2, 2, 2, 8]
def baseStart_4803741 : Nat := 118140960795 + 4803741 * 2 ^ 59
def prefixEnd_4803741 : Nat := 4983230072969 + 3 ^ 40 * 4803741 * 2
def baseEnd_4803741 : Nat := 274069785856643897216167

theorem tailTrace_4803741 : CollatzResearch.WordTrace tailWord_4803741 prefixEnd_4803741 274069785856643897216167 := by
  unfold tailWord_4803741
  simp only [CollatzResearch.WordTrace]
  refine ⟨175206828089874245491443077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116804552059916163660962051 175206828089874245491443077)
  ·
    refine ⟨32851280266851421029645577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 175206828089874245491443077 32851280266851421029645577)
    ·
      refine ⟨24638460200138565772234183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32851280266851421029645577 24638460200138565772234183)
      ·
        refine ⟨36957690300207848658351275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24638460200138565772234183 36957690300207848658351275)
        ·
          refine ⟨55436535450311772987526913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36957690300207848658351275 55436535450311772987526913)
          ·
            refine ⟨41577401587733829740645185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55436535450311772987526913 41577401587733829740645185)
            ·
              refine ⟨31183051190800372305483889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41577401587733829740645185 31183051190800372305483889)
              ·
                refine ⟨23387288393100279229112917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31183051190800372305483889 23387288393100279229112917)
                ·
                  refine ⟨274069785856643897216167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 23387288393100279229112917 274069785856643897216167)
                  ·
                    rfl

theorem cell23_4803741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 2, 2, 8].length) (baseStart_4803741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4803741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4803741 prefixEnd_4803741 := by exact prefixLift 4803741
  have htrace : WordTrace (prefixWord ++ tailWord_4803741) baseStart_4803741 baseEnd_4803741 := by
    simpa [prefixWord, tailWord_4803741, baseEnd_4803741] using wordTrace_append hprefix tailTrace_4803741
  have hstable : (prefixWord ++ tailWord_4803741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4803741).length < 2 ^ (prefixWord ++ tailWord_4803741).sum := by decide
  have hdescent : baseEnd_4803741 < baseStart_4803741 := by decide
  rcases family_descends (prefixWord ++ tailWord_4803741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4803771 : List Nat := [1, 1, 1, 1, 1, 2, 4, 4, 3, 5]
def baseStart_4803771 : Nat := 118140960795 + 4803771 * 2 ^ 59
def prefixEnd_4803771 : Nat := 4983230072969 + 3 ^ 40 * 4803771 * 2
def baseEnd_4803771 : Nat := 822214492376476652523455

theorem tailTrace_4803771 : CollatzResearch.WordTrace tailWord_4803771 prefixEnd_4803771 822214492376476652523455 := by
  unfold tailWord_4803771
  simp only [CollatzResearch.WordTrace]
  refine ⟨175207922279765560615035167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116805281519843707076690111 175207922279765560615035167)
  ·
    refine ⟨262811883419648340922552751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175207922279765560615035167 262811883419648340922552751)
    ·
      refine ⟨394217825129472511383829127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 262811883419648340922552751 394217825129472511383829127)
      ·
        refine ⟨591326737694208767075743691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 394217825129472511383829127 591326737694208767075743691)
        ·
          refine ⟨886990106541313150613615537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 591326737694208767075743691 886990106541313150613615537)
          ·
            refine ⟨665242579905984862960211653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 886990106541313150613615537 665242579905984862960211653)
            ·
              refine ⟨124732983732372161805039685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 665242579905984862960211653 124732983732372161805039685)
              ·
                refine ⟨23387434449819780338444941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 124732983732372161805039685 23387434449819780338444941)
                ·
                  refine ⟨8770287918682417626916853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23387434449819780338444941 8770287918682417626916853)
                  ·
                    refine ⟨822214492376476652523455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8770287918682417626916853 822214492376476652523455)
                    ·
                      rfl

theorem cell23_4803771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 4, 3, 5].length) (baseStart_4803771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4803771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4803771 prefixEnd_4803771 := by exact prefixLift 4803771
  have htrace : WordTrace (prefixWord ++ tailWord_4803771) baseStart_4803771 baseEnd_4803771 := by
    simpa [prefixWord, tailWord_4803771, baseEnd_4803771] using wordTrace_append hprefix tailTrace_4803771
  have hstable : (prefixWord ++ tailWord_4803771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4803771).length < 2 ^ (prefixWord ++ tailWord_4803771).sum := by decide
  have hdescent : baseEnd_4803771 < baseStart_4803771 := by decide
  rcases family_descends (prefixWord ++ tailWord_4803771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4803796 : List Nat := [2, 4, 1, 4, 1, 2, 1, 3, 1, 4]
def baseStart_4803796 : Nat := 118140960795 + 4803796 * 2 ^ 59
def prefixEnd_4803796 : Nat := 4983230072969 + 3 ^ 40 * 4803796 * 2
def baseEnd_4803796 : Nat := 822218771381930786585917

theorem tailTrace_4803796 : CollatzResearch.WordTrace tailWord_4803796 prefixEnd_4803796 822218771381930786585917 := by
  unfold tailWord_4803796
  simp only [CollatzResearch.WordTrace]
  refine ⟨87604417052337494942347621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116805889403116659923130161 87604417052337494942347621)
  ·
    refine ⟨16425828197313280301690179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 87604417052337494942347621 16425828197313280301690179)
    ·
      refine ⟨24638742295969920452535269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16425828197313280301690179 24638742295969920452535269)
      ·
        refine ⟨4619764180494360084850363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24638742295969920452535269 4619764180494360084850363)
        ·
          refine ⟨6929646270741540127275545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4619764180494360084850363 6929646270741540127275545)
          ·
            refine ⟨5197234703056155095456659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6929646270741540127275545 5197234703056155095456659)
            ·
              refine ⟨7795852054584232643184989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5197234703056155095456659 7795852054584232643184989)
              ·
                refine ⟨2923444520469087241194371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7795852054584232643184989 2923444520469087241194371)
                ·
                  refine ⟨4385166780703630861791557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2923444520469087241194371 4385166780703630861791557)
                  ·
                    refine ⟨822218771381930786585917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4385166780703630861791557 822218771381930786585917)
                    ·
                      rfl

theorem cell23_4803796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 2, 1, 3, 1, 4].length) (baseStart_4803796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4803796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4803796 prefixEnd_4803796 := by exact prefixLift 4803796
  have htrace : WordTrace (prefixWord ++ tailWord_4803796) baseStart_4803796 baseEnd_4803796 := by
    simpa [prefixWord, tailWord_4803796, baseEnd_4803796] using wordTrace_append hprefix tailTrace_4803796
  have hstable : (prefixWord ++ tailWord_4803796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4803796).length < 2 ^ (prefixWord ++ tailWord_4803796).sum := by decide
  have hdescent : baseEnd_4803796 < baseStart_4803796 := by decide
  rcases family_descends (prefixWord ++ tailWord_4803796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4803801 : List Nat := [1, 2, 1, 2, 3, 1, 1, 3, 3, 6]
def baseStart_4803801 : Nat := 118140960795 + 4803801 * 2 ^ 59
def prefixEnd_4803801 : Nat := 4983230072969 + 3 ^ 40 * 4803801 * 2
def baseEnd_4803801 : Nat := 822219627183021613398409

theorem tailTrace_4803801 : CollatzResearch.WordTrace tailWord_4803801 prefixEnd_4803801 822219627183021613398409 := by
  unfold tailWord_4803801
  simp only [CollatzResearch.WordTrace]
  refine ⟨175209016469656875738627257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116806010979771250492418171 175209016469656875738627257)
  ·
    refine ⟨131406762352242656803970443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 175209016469656875738627257 131406762352242656803970443)
    ·
      refine ⟨197110143528363985205955665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131406762352242656803970443 197110143528363985205955665)
      ·
        refine ⟨147832607646272988904466749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 197110143528363985205955665 147832607646272988904466749)
        ·
          refine ⟨55437227867352370839175031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 147832607646272988904466749 55437227867352370839175031)
          ·
            refine ⟨83155841801028556258762547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55437227867352370839175031 83155841801028556258762547)
            ·
              refine ⟨124733762701542834388143821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83155841801028556258762547 124733762701542834388143821)
              ·
                refine ⟨46775161013078562895553933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 124733762701542834388143821 46775161013078562895553933)
                ·
                  refine ⟨17540685379904461085832725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 46775161013078562895553933 17540685379904461085832725)
                  ·
                    refine ⟨822219627183021613398409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17540685379904461085832725 822219627183021613398409)
                    ·
                      rfl

theorem cell23_4803801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 3, 3, 6].length) (baseStart_4803801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4803801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4803801 prefixEnd_4803801 := by exact prefixLift 4803801
  have htrace : WordTrace (prefixWord ++ tailWord_4803801) baseStart_4803801 baseEnd_4803801 := by
    simpa [prefixWord, tailWord_4803801, baseEnd_4803801] using wordTrace_append hprefix tailTrace_4803801
  have hstable : (prefixWord ++ tailWord_4803801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4803801).length < 2 ^ (prefixWord ++ tailWord_4803801).sum := by decide
  have hdescent : baseEnd_4803801 < baseStart_4803801 := by decide
  rcases family_descends (prefixWord ++ tailWord_4803801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4803819 : List Nat := [1, 1, 1, 1, 2, 7, 3, 2, 1, 1, 3]
def baseStart_4803819 : Nat := 118140960795 + 4803819 * 2 ^ 59
def prefixEnd_4803819 : Nat := 4983230072969 + 3 ^ 40 * 4803819 * 2
def baseEnd_4803819 : Nat := 2466668124200845769770145

theorem tailTrace_4803819 : CollatzResearch.WordTrace tailWord_4803819 prefixEnd_4803819 2466668124200845769770145 := by
  unfold tailWord_4803819
  simp only [CollatzResearch.WordTrace]
  refine ⟨175209672983591664812782511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116806448655727776541855007 175209672983591664812782511)
  ·
    refine ⟨262814509475387497219173767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175209672983591664812782511 262814509475387497219173767)
    ·
      refine ⟨394221764213081245828760651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 262814509475387497219173767 394221764213081245828760651)
      ·
        refine ⟨591332646319621868743140977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 394221764213081245828760651 591332646319621868743140977)
        ·
          refine ⟨443499484739716401557355733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 591332646319621868743140977 443499484739716401557355733)
          ·
            refine ⟨10394519173587103161500525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 443499484739716401557355733 10394519173587103161500525)
            ·
              refine ⟨3897944690095163685562697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10394519173587103161500525 3897944690095163685562697)
              ·
                refine ⟨2923458517571372764172023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3897944690095163685562697 2923458517571372764172023)
                ·
                  refine ⟨4385187776357059146258035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2923458517571372764172023 4385187776357059146258035)
                  ·
                    refine ⟨6577781664535588719387053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4385187776357059146258035 6577781664535588719387053)
                    ·
                      refine ⟨2466668124200845769770145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6577781664535588719387053 2466668124200845769770145)
                      ·
                        rfl

theorem cell23_4803819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 3, 2, 1, 1, 3].length) (baseStart_4803819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4803819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4803819 prefixEnd_4803819 := by exact prefixLift 4803819
  have htrace : WordTrace (prefixWord ++ tailWord_4803819) baseStart_4803819 baseEnd_4803819 := by
    simpa [prefixWord, tailWord_4803819, baseEnd_4803819] using wordTrace_append hprefix tailTrace_4803819
  have hstable : (prefixWord ++ tailWord_4803819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4803819).length < 2 ^ (prefixWord ++ tailWord_4803819).sum := by decide
  have hdescent : baseEnd_4803819 < baseStart_4803819 := by decide
  rcases family_descends (prefixWord ++ tailWord_4803819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4803842 : List Nat := [3, 4, 1, 1, 3, 1, 1, 1, 3, 1, 4]
def baseStart_4803842 : Nat := 118140960795 + 4803842 * 2 ^ 59
def prefixEnd_4803842 : Nat := 4983230072969 + 3 ^ 40 * 4803842 * 2
def baseEnd_4803842 : Nat := 2466679934255899179782539

theorem tailTrace_4803842 : CollatzResearch.WordTrace tailWord_4803842 prefixEnd_4803842 2466679934255899179782539 := by
  unfold tailWord_4803842
  simp only [CollatzResearch.WordTrace]
  refine ⟨43802627965627084935217445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 116807007908338893160579853 43802627965627084935217445)
  ·
    refine ⟨8212992743555078425353271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 43802627965627084935217445 8212992743555078425353271)
    ·
      refine ⟨12319489115332617638029907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8212992743555078425353271 12319489115332617638029907)
      ·
        refine ⟨18479233672998926457044861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12319489115332617638029907 18479233672998926457044861)
        ·
          refine ⟨6929712627374597421391823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18479233672998926457044861 6929712627374597421391823)
          ·
            refine ⟨10394568941061896132087735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6929712627374597421391823 10394568941061896132087735)
            ·
              refine ⟨15591853411592844198131603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10394568941061896132087735 15591853411592844198131603)
              ·
                refine ⟨23387780117389266297197405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15591853411592844198131603 23387780117389266297197405)
                ·
                  refine ⟨8770417544020974861449027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23387780117389266297197405 8770417544020974861449027)
                  ·
                    refine ⟨13155626316031462292173541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8770417544020974861449027 13155626316031462292173541)
                    ·
                      refine ⟨2466679934255899179782539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13155626316031462292173541 2466679934255899179782539)
                      ·
                        rfl

theorem cell23_4803842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 1, 1, 3, 1, 4].length) (baseStart_4803842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4803842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4803842 prefixEnd_4803842 := by exact prefixLift 4803842
  have htrace : WordTrace (prefixWord ++ tailWord_4803842) baseStart_4803842 baseEnd_4803842 := by
    simpa [prefixWord, tailWord_4803842, baseEnd_4803842] using wordTrace_append hprefix tailTrace_4803842
  have hstable : (prefixWord ++ tailWord_4803842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4803842).length < 2 ^ (prefixWord ++ tailWord_4803842).sum := by decide
  have hdescent : baseEnd_4803842 < baseStart_4803842 := by decide
  rcases family_descends (prefixWord ++ tailWord_4803842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4803870 : List Nat := [4, 3, 2, 1, 2, 2, 2, 2, 1, 1, 3]
def baseStart_4803870 : Nat := 118140960795 + 4803870 * 2 ^ 59
def prefixEnd_4803870 : Nat := 4983230072969 + 3 ^ 40 * 4803870 * 2
def baseEnd_4803870 : Nat := 2466694311714225070232411

theorem tailTrace_4803870 : CollatzResearch.WordTrace tailWord_4803870 prefixEnd_4803870 2466694311714225070232411 := by
  unfold tailWord_4803870
  simp only [CollatzResearch.WordTrace]
  refine ⟨21901441638300862565361133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 116807688737604600348592709 21901441638300862565361133)
  ·
    refine ⟨8213040614362823462010425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21901441638300862565361133 8213040614362823462010425)
    ·
      refine ⟨6159780460772117596507819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8213040614362823462010425 6159780460772117596507819)
      ·
        refine ⟨9239670691158176394761729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6159780460772117596507819 9239670691158176394761729)
        ·
          refine ⟨6929753018368632296071297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9239670691158176394761729 6929753018368632296071297)
          ·
            refine ⟨5197314763776474222053473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6929753018368632296071297 5197314763776474222053473)
            ·
              refine ⟨3897986072832355666540105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5197314763776474222053473 3897986072832355666540105)
              ·
                refine ⟨2923489554624266749905079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3897986072832355666540105 2923489554624266749905079)
                ·
                  refine ⟨4385234331936400124857619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2923489554624266749905079 4385234331936400124857619)
                  ·
                    refine ⟨6577851497904600187286429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4385234331936400124857619 6577851497904600187286429)
                    ·
                      refine ⟨2466694311714225070232411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6577851497904600187286429 2466694311714225070232411)
                      ·
                        rfl

theorem cell23_4803870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 2, 2, 2, 1, 1, 3].length) (baseStart_4803870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4803870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4803870 prefixEnd_4803870 := by exact prefixLift 4803870
  have htrace : WordTrace (prefixWord ++ tailWord_4803870) baseStart_4803870 baseEnd_4803870 := by
    simpa [prefixWord, tailWord_4803870, baseEnd_4803870] using wordTrace_append hprefix tailTrace_4803870
  have hstable : (prefixWord ++ tailWord_4803870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4803870).length < 2 ^ (prefixWord ++ tailWord_4803870).sum := by decide
  have hdescent : baseEnd_4803870 < baseStart_4803870 := by decide
  rcases family_descends (prefixWord ++ tailWord_4803870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4803881 : List Nat := [1, 2, 1, 1, 1, 1, 1, 2, 3, 2, 8]
def baseStart_4803881 : Nat := 118140960795 + 4803881 * 2 ^ 59
def prefixEnd_4803881 : Nat := 4983230072969 + 3 ^ 40 * 4803881 * 2
def baseEnd_4803881 : Nat := 2466699960001424527194859

theorem tailTrace_4803881 : CollatzResearch.WordTrace tailWord_4803881 prefixEnd_4803881 2466699960001424527194859 := by
  unfold tailWord_4803881
  simp only [CollatzResearch.WordTrace]
  refine ⟨175211934309367049401539497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116807956206244699601026331 175211934309367049401539497)
  ·
    refine ⟨131408950732025287051154623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 175211934309367049401539497 131408950732025287051154623)
    ·
      refine ⟨197113426098037930576731935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131408950732025287051154623 197113426098037930576731935)
      ·
        refine ⟨295670139147056895865097903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 197113426098037930576731935 295670139147056895865097903)
        ·
          refine ⟨443505208720585343797646855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 295670139147056895865097903 443505208720585343797646855)
          ·
            refine ⟨665257813080878015696470283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 443505208720585343797646855 665257813080878015696470283)
            ·
              refine ⟨997886719621317023544705425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 665257813080878015696470283 997886719621317023544705425)
              ·
                refine ⟨748415039715987767658529069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 997886719621317023544705425 748415039715987767658529069)
                ·
                  refine ⟨280655639893495412871948401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 748415039715987767658529069 280655639893495412871948401)
                  ·
                    refine ⟨210491729920121559653961301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 280655639893495412871948401 210491729920121559653961301)
                    ·
                      refine ⟨2466699960001424527194859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 210491729920121559653961301 2466699960001424527194859)
                      ·
                        rfl

theorem cell23_4803881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 2, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 2, 3, 2, 8].length) (baseStart_4803881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4803881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4803881 prefixEnd_4803881 := by exact prefixLift 4803881
  have htrace : WordTrace (prefixWord ++ tailWord_4803881) baseStart_4803881 baseEnd_4803881 := by
    simpa [prefixWord, tailWord_4803881, baseEnd_4803881] using wordTrace_append hprefix tailTrace_4803881
  have hstable : (prefixWord ++ tailWord_4803881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4803881).length < 2 ^ (prefixWord ++ tailWord_4803881).sum := by decide
  have hdescent : baseEnd_4803881 < baseStart_4803881 := by decide
  rcases family_descends (prefixWord ++ tailWord_4803881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4803892 : List Nat := [2, 5, 1, 1, 1, 1, 4, 1, 1, 3, 3]
def baseStart_4803892 : Nat := 118140960795 + 4803892 * 2 ^ 59
def prefixEnd_4803892 : Nat := 4983230072969 + 3 ^ 40 * 4803892 * 2
def baseEnd_4803892 : Nat := 2466705608288623984157309

theorem tailTrace_4803892 : CollatzResearch.WordTrace tailWord_4803892 prefixEnd_4803892 2466705608288623984157309 := by
  unfold tailWord_4803892
  simp only [CollatzResearch.WordTrace]
  refine ⟨87606167756163599140094965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116808223674884798853459953 87606167756163599140094965)
  ·
    refine ⟨8213078227140337419383903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 87606167756163599140094965 8213078227140337419383903)
    ·
      refine ⟨12319617340710506129075855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8213078227140337419383903 12319617340710506129075855)
      ·
        refine ⟨18479426011065759193613783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12319617340710506129075855 18479426011065759193613783)
        ·
          refine ⟨27719139016598638790420675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18479426011065759193613783 27719139016598638790420675)
          ·
            refine ⟨41578708524897958185631013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27719139016598638790420675 41578708524897958185631013)
            ·
              refine ⟨7796007848418367159805815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 41578708524897958185631013 7796007848418367159805815)
              ·
                refine ⟨11694011772627550739708723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7796007848418367159805815 11694011772627550739708723)
                ·
                  refine ⟨17541017658941326109563085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11694011772627550739708723 17541017658941326109563085)
                  ·
                    refine ⟨6577881622102997291086157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17541017658941326109563085 6577881622102997291086157)
                    ·
                      refine ⟨2466705608288623984157309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6577881622102997291086157 2466705608288623984157309)
                      ·
                        rfl

theorem cell23_4803892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 4, 1, 1, 3, 3].length) (baseStart_4803892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4803892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4803892 prefixEnd_4803892 := by exact prefixLift 4803892
  have htrace : WordTrace (prefixWord ++ tailWord_4803892) baseStart_4803892 baseEnd_4803892 := by
    simpa [prefixWord, tailWord_4803892, baseEnd_4803892] using wordTrace_append hprefix tailTrace_4803892
  have hstable : (prefixWord ++ tailWord_4803892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4803892).length < 2 ^ (prefixWord ++ tailWord_4803892).sum := by decide
  have hdescent : baseEnd_4803892 < baseStart_4803892 := by decide
  rcases family_descends (prefixWord ++ tailWord_4803892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4803898 : List Nat := [3, 1, 1, 1, 4, 1, 1, 2, 2, 3, 4]
def baseStart_4803898 : Nat := 118140960795 + 4803898 * 2 ^ 59
def prefixEnd_4803898 : Nat := 4983230072969 + 3 ^ 40 * 4803898 * 2
def baseEnd_4803898 : Nat := 2466708689172550960682281

theorem tailTrace_4803898 : CollatzResearch.WordTrace tailWord_4803898 prefixEnd_4803898 2466708689172550960682281 := by
  unfold tailWord_4803898
  simp only [CollatzResearch.WordTrace]
  refine ⟨43803138587576365326227087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 116808369566870307536605565 43803138587576365326227087)
  ·
    refine ⟨65704707881364547989340631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43803138587576365326227087 65704707881364547989340631)
    ·
      refine ⟨98557061822046821984010947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65704707881364547989340631 98557061822046821984010947)
      ·
        refine ⟨147835592733070232976016421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98557061822046821984010947 147835592733070232976016421)
        ·
          refine ⟨27719173637450668683003079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 147835592733070232976016421 27719173637450668683003079)
          ·
            refine ⟨41578760456176003024504619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27719173637450668683003079 41578760456176003024504619)
            ·
              refine ⟨62368140684264004536756929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41578760456176003024504619 62368140684264004536756929)
              ·
                refine ⟨46776105513198003402567697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 62368140684264004536756929 46776105513198003402567697)
                ·
                  refine ⟨35082079134898502551925773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 46776105513198003402567697 35082079134898502551925773)
                  ·
                    refine ⟨13155779675586938456972165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 35082079134898502551925773 13155779675586938456972165)
                    ·
                      refine ⟨2466708689172550960682281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13155779675586938456972165 2466708689172550960682281)
                      ·
                        rfl

theorem cell23_4803898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 2, 2, 3, 4].length) (baseStart_4803898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4803898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4803898 prefixEnd_4803898 := by exact prefixLift 4803898
  have htrace : WordTrace (prefixWord ++ tailWord_4803898) baseStart_4803898 baseEnd_4803898 := by
    simpa [prefixWord, tailWord_4803898, baseEnd_4803898] using wordTrace_append hprefix tailTrace_4803898
  have hstable : (prefixWord ++ tailWord_4803898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4803898).length < 2 ^ (prefixWord ++ tailWord_4803898).sum := by decide
  have hdescent : baseEnd_4803898 < baseStart_4803898 := by decide
  rcases family_descends (prefixWord ++ tailWord_4803898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4803902 : List Nat := [4, 2, 1, 2, 1, 1, 1, 3, 3, 3, 2]
def baseStart_4803902 : Nat := 118140960795 + 4803902 * 2 ^ 59
def prefixEnd_4803902 : Nat := 4983230072969 + 3 ^ 40 * 4803902 * 2
def baseEnd_4803902 : Nat := 2466710743095168945032263

theorem tailTrace_4803902 : CollatzResearch.WordTrace tailWord_4803902 prefixEnd_4803902 2466710743095168945032263 := by
  unfold tailWord_4803902
  simp only [CollatzResearch.WordTrace]
  refine ⟨21901587530286371248506745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 116808466828193979992035973 21901587530286371248506745)
  ·
    refine ⟨16426190647714778436380059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21901587530286371248506745 16426190647714778436380059)
    ·
      refine ⟨24639285971572167654570089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16426190647714778436380059 24639285971572167654570089)
      ·
        refine ⟨18479464478679125740927567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24639285971572167654570089 18479464478679125740927567)
        ·
          refine ⟨27719196718018688611391351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18479464478679125740927567 27719196718018688611391351)
          ·
            refine ⟨41578795077028032917087027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27719196718018688611391351 41578795077028032917087027)
            ·
              refine ⟨62368192615542049375630541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41578795077028032917087027 62368192615542049375630541)
              ·
                refine ⟨23388072230828268515861453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 62368192615542049375630541 23388072230828268515861453)
                ·
                  refine ⟨8770527086560600693448045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23388072230828268515861453 8770527086560600693448045)
                  ·
                    refine ⟨3288947657460225260043017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8770527086560600693448045 3288947657460225260043017)
                    ·
                      refine ⟨2466710743095168945032263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3288947657460225260043017 2466710743095168945032263)
                      ·
                        rfl

theorem cell23_4803902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 3, 3, 3, 2].length) (baseStart_4803902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4803902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4803902 prefixEnd_4803902 := by exact prefixLift 4803902
  have htrace : WordTrace (prefixWord ++ tailWord_4803902) baseStart_4803902 baseEnd_4803902 := by
    simpa [prefixWord, tailWord_4803902, baseEnd_4803902] using wordTrace_append hprefix tailTrace_4803902
  have hstable : (prefixWord ++ tailWord_4803902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4803902).length < 2 ^ (prefixWord ++ tailWord_4803902).sum := by decide
  have hdescent : baseEnd_4803902 < baseStart_4803902 := by decide
  rcases family_descends (prefixWord ++ tailWord_4803902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4803910 : List Nat := [6, 1, 1, 3, 2, 1, 2, 1, 1, 1, 4]
def baseStart_4803910 : Nat := 118140960795 + 4803910 * 2 ^ 59
def prefixEnd_4803910 : Nat := 4983230072969 + 3 ^ 40 * 4803910 * 2
def baseEnd_4803910 : Nat := 2466714850940404913732227

theorem tailTrace_4803910 : CollatzResearch.WordTrace tailWord_4803910 prefixEnd_4803910 2466714850940404913732227 := by
  unfold tailWord_4803910
  simp only [CollatzResearch.WordTrace]
  refine ⟨5475406000820687104823287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 116808661350841324902896789 5475406000820687104823287)
  ·
    refine ⟨8213109001231030657234931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5475406000820687104823287 8213109001231030657234931)
    ·
      refine ⟨12319663501846545985852397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8213109001231030657234931 12319663501846545985852397)
      ·
        refine ⟨4619873813192454744694649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12319663501846545985852397 4619873813192454744694649)
        ·
          refine ⟨3464905359894341058520987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4619873813192454744694649 3464905359894341058520987)
          ·
            refine ⟨5197358039841511587781481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3464905359894341058520987 5197358039841511587781481)
            ·
              refine ⟨3898018529881133690836111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5197358039841511587781481 3898018529881133690836111)
              ·
                refine ⟨5847027794821700536254167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3898018529881133690836111 5847027794821700536254167)
                ·
                  refine ⟨8770541692232550804381251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5847027794821700536254167 8770541692232550804381251)
                  ·
                    refine ⟨13155812538348826206571877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8770541692232550804381251 13155812538348826206571877)
                    ·
                      refine ⟨2466714850940404913732227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13155812538348826206571877 2466714850940404913732227)
                      ·
                        rfl

theorem cell23_4803910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 2, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 2, 1, 2, 1, 1, 1, 4].length) (baseStart_4803910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4803910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4803910 prefixEnd_4803910 := by exact prefixLift 4803910
  have htrace : WordTrace (prefixWord ++ tailWord_4803910) baseStart_4803910 baseEnd_4803910 := by
    simpa [prefixWord, tailWord_4803910, baseEnd_4803910] using wordTrace_append hprefix tailTrace_4803910
  have hstable : (prefixWord ++ tailWord_4803910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4803910).length < 2 ^ (prefixWord ++ tailWord_4803910).sum := by decide
  have hdescent : baseEnd_4803910 < baseStart_4803910 := by decide
  rcases family_descends (prefixWord ++ tailWord_4803910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4803918 : List Nat := [4, 1, 1, 1, 1, 1, 4, 1, 1, 3, 5]
def baseStart_4803918 : Nat := 118140960795 + 4803918 * 2 ^ 59
def prefixEnd_4803918 : Nat := 4983230072969 + 3 ^ 40 * 4803918 * 2
def baseEnd_4803918 : Nat := 2466718958785640882432189

theorem tailTrace_4803918 : CollatzResearch.WordTrace tailWord_4803918 prefixEnd_4803918 2466718958785640882432189 := by
  unfold tailWord_4803918
  simp only [CollatzResearch.WordTrace]
  refine ⟨21901660476279125590079551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 116808855873488669813757605 21901660476279125590079551)
  ·
    refine ⟨32852490714418688385119327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21901660476279125590079551 32852490714418688385119327)
    ·
      refine ⟨49278736071628032577678991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32852490714418688385119327 49278736071628032577678991)
      ·
        refine ⟨73918104107442048866518487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49278736071628032577678991 73918104107442048866518487)
        ·
          refine ⟨110877156161163073299777731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73918104107442048866518487 110877156161163073299777731)
          ·
            refine ⟨166315734241744609949666597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 110877156161163073299777731 166315734241744609949666597)
            ·
              refine ⟨31184200170327114365562487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 166315734241744609949666597 31184200170327114365562487)
              ·
                refine ⟨46776300255490671548343731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31184200170327114365562487 46776300255490671548343731)
                ·
                  refine ⟨70164450383236007322515597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 46776300255490671548343731 70164450383236007322515597)
                  ·
                    refine ⟨26311668893713502745943349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 70164450383236007322515597 26311668893713502745943349)
                    ·
                      refine ⟨2466718958785640882432189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26311668893713502745943349 2466718958785640882432189)
                      ·
                        rfl

theorem cell23_4803918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 4, 1, 1, 3, 5].length) (baseStart_4803918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4803918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4803918 prefixEnd_4803918 := by exact prefixLift 4803918
  have htrace : WordTrace (prefixWord ++ tailWord_4803918) baseStart_4803918 baseEnd_4803918 := by
    simpa [prefixWord, tailWord_4803918, baseEnd_4803918] using wordTrace_append hprefix tailTrace_4803918
  have hstable : (prefixWord ++ tailWord_4803918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4803918).length < 2 ^ (prefixWord ++ tailWord_4803918).sum := by decide
  have hdescent : baseEnd_4803918 < baseStart_4803918 := by decide
  rcases family_descends (prefixWord ++ tailWord_4803918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4803928 : List Nat := [2, 1, 2, 2, 1, 1, 3, 1, 4, 2, 4]
def baseStart_4803928 : Nat := 118140960795 + 4803928 * 2 ^ 59
def prefixEnd_4803928 : Nat := 4983230072969 + 3 ^ 40 * 4803928 * 2
def baseEnd_4803928 : Nat := 2466724093592185843307143

theorem tailTrace_4803928 : CollatzResearch.WordTrace tailWord_4803928 prefixEnd_4803928 2466724093592185843307143 := by
  unfold tailWord_4803928
  simp only [CollatzResearch.WordTrace]
  refine ⟨87606824270098388214250219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116809099026797850952333625 87606824270098388214250219)
  ·
    refine ⟨131410236405147582321375329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87606824270098388214250219 131410236405147582321375329)
    ·
      refine ⟨98557677303860686741031497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 131410236405147582321375329 98557677303860686741031497)
      ·
        refine ⟨73918257977895515055773623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 98557677303860686741031497 73918257977895515055773623)
        ·
          refine ⟨110877386966843272583660435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73918257977895515055773623 110877386966843272583660435)
          ·
            refine ⟨166316080450264908875490653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 110877386966843272583660435 166316080450264908875490653)
            ·
              refine ⟨62368530168849340828308995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 166316080450264908875490653 62368530168849340828308995)
              ·
                refine ⟨93552795253274011242463493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62368530168849340828308995 93552795253274011242463493)
                ·
                  refine ⟨17541149109988877107961905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 93552795253274011242463493 17541149109988877107961905)
                  ·
                    refine ⟨13155861832491657830971429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17541149109988877107961905 13155861832491657830971429)
                    ·
                      refine ⟨2466724093592185843307143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13155861832491657830971429 2466724093592185843307143)
                      ·
                        rfl

theorem cell23_4803928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 1, 4, 2, 4].length) (baseStart_4803928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4803928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4803928 prefixEnd_4803928 := by exact prefixLift 4803928
  have htrace : WordTrace (prefixWord ++ tailWord_4803928) baseStart_4803928 baseEnd_4803928 := by
    simpa [prefixWord, tailWord_4803928, baseEnd_4803928] using wordTrace_append hprefix tailTrace_4803928
  have hstable : (prefixWord ++ tailWord_4803928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4803928).length < 2 ^ (prefixWord ++ tailWord_4803928).sum := by decide
  have hdescent : baseEnd_4803928 < baseStart_4803928 := by decide
  rcases family_descends (prefixWord ++ tailWord_4803928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4803949 : List Nat := [1, 5, 1, 1, 1, 5, 1, 1, 1, 4, 2]
def baseStart_4803949 : Nat := 118140960795 + 4803949 * 2 ^ 59
def prefixEnd_4803949 : Nat := 4983230072969 + 3 ^ 40 * 4803949 * 2
def baseEnd_4803949 : Nat := 2466734876685930261144547

theorem tailTrace_4803949 : CollatzResearch.WordTrace tailWord_4803949 prefixEnd_4803949 2466734876685930261144547 := by
  unfold tailWord_4803949
  simp only [CollatzResearch.WordTrace]
  refine ⟨175214414473120697015014901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116809609648747131343343267 175214414473120697015014901)
  ·
    refine ⟨16426351356855065345157647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 175214414473120697015014901 16426351356855065345157647)
    ·
      refine ⟨24639527035282598017736471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16426351356855065345157647 24639527035282598017736471)
      ·
        refine ⟨36959290552923897026604707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24639527035282598017736471 36959290552923897026604707)
        ·
          refine ⟨55438935829385845539907061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36959290552923897026604707 55438935829385845539907061)
          ·
            refine ⟨5197400234004923019366287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 55438935829385845539907061 5197400234004923019366287)
            ·
              refine ⟨7796100351007384529049431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5197400234004923019366287 7796100351007384529049431)
              ·
                refine ⟨11694150526511076793574147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7796100351007384529049431 11694150526511076793574147)
                ·
                  refine ⟨17541225789766615190361221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11694150526511076793574147 17541225789766615190361221)
                  ·
                    refine ⟨3288979835581240348192729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17541225789766615190361221 3288979835581240348192729)
                    ·
                      refine ⟨2466734876685930261144547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3288979835581240348192729 2466734876685930261144547)
                      ·
                        rfl

theorem cell23_4803949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 5, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 5, 1, 1, 1, 4, 2].length) (baseStart_4803949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4803949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4803949 prefixEnd_4803949 := by exact prefixLift 4803949
  have htrace : WordTrace (prefixWord ++ tailWord_4803949) baseStart_4803949 baseEnd_4803949 := by
    simpa [prefixWord, tailWord_4803949, baseEnd_4803949] using wordTrace_append hprefix tailTrace_4803949
  have hstable : (prefixWord ++ tailWord_4803949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4803949).length < 2 ^ (prefixWord ++ tailWord_4803949).sum := by decide
  have hdescent : baseEnd_4803949 < baseStart_4803949 := by decide
  rcases family_descends (prefixWord ++ tailWord_4803949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4803968 : List Nat := [2, 1, 1, 2, 1, 2, 1, 2, 6, 5]
def baseStart_4803968 : Nat := 118140960795 + 4803968 * 2 ^ 59
def prefixEnd_4803968 : Nat := 4983230072969 + 3 ^ 40 * 4803968 * 2
def baseEnd_4803968 : Nat := 822248210939455228935653

theorem tailTrace_4803968 : CollatzResearch.WordTrace tailWord_4803968 prefixEnd_4803968 822248210939455228935653 := by
  unfold tailWord_4803968
  simp only [CollatzResearch.WordTrace]
  refine ⟨87607553730025931629978279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116810071640034575506637705 87607553730025931629978279)
  ·
    refine ⟨131411330595038897444967419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87607553730025931629978279 131411330595038897444967419)
    ·
      refine ⟨197116995892558346167451129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131411330595038897444967419 197116995892558346167451129)
      ·
        refine ⟨147837746919418759625588347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 197116995892558346167451129 147837746919418759625588347)
        ·
          refine ⟨221756620379128139438382521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 147837746919418759625588347 221756620379128139438382521)
          ·
            refine ⟨166317465284346104578786891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 221756620379128139438382521 166317465284346104578786891)
            ·
              refine ⟨249476197926519156868180337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 166317465284346104578786891 249476197926519156868180337)
              ·
                refine ⟨187107148444889367651135253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 249476197926519156868180337 187107148444889367651135253)
                ·
                  refine ⟨8770647583354189108646965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 187107148444889367651135253 8770647583354189108646965)
                  ·
                    refine ⟨822248210939455228935653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8770647583354189108646965 822248210939455228935653)
                    ·
                      rfl

theorem cell23_4803968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 2, 6, 5].length) (baseStart_4803968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4803968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4803968 prefixEnd_4803968 := by exact prefixLift 4803968
  have htrace : WordTrace (prefixWord ++ tailWord_4803968) baseStart_4803968 baseEnd_4803968 := by
    simpa [prefixWord, tailWord_4803968, baseEnd_4803968] using wordTrace_append hprefix tailTrace_4803968
  have hstable : (prefixWord ++ tailWord_4803968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4803968).length < 2 ^ (prefixWord ++ tailWord_4803968).sum := by decide
  have hdescent : baseEnd_4803968 < baseStart_4803968 := by decide
  rcases family_descends (prefixWord ++ tailWord_4803968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4803972 : List Nat := [2, 3, 2, 1, 1, 3, 3, 3, 5]
def baseStart_4803972 : Nat := 118140960795 + 4803972 * 2 ^ 59
def prefixEnd_4803972 : Nat := 4983230072969 + 3 ^ 40 * 4803972 * 2
def baseEnd_4803972 : Nat := 274082965193442630128549

theorem tailTrace_4803972 : CollatzResearch.WordTrace tailWord_4803972 prefixEnd_4803972 274082965193442630128549 := by
  unfold tailWord_4803972
  simp only [CollatzResearch.WordTrace]
  refine ⟨87607626676018685971551085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116810168901358247962068113 87607626676018685971551085)
  ·
    refine ⟨32852860003507007239331657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 87607626676018685971551085 32852860003507007239331657)
    ·
      refine ⟨24639645002630255429498743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32852860003507007239331657 24639645002630255429498743)
      ·
        refine ⟨36959467503945383144248115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24639645002630255429498743 36959467503945383144248115)
        ·
          refine ⟨55439201255918074716372173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36959467503945383144248115 55439201255918074716372173)
          ·
            refine ⟨20789700470969278018639565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55439201255918074716372173 20789700470969278018639565)
            ·
              refine ⟨7796137676613479256989837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20789700470969278018639565 7796137676613479256989837)
              ·
                refine ⟨2923551628730054721371189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7796137676613479256989837 2923551628730054721371189)
                ·
                  refine ⟨274082965193442630128549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2923551628730054721371189 274082965193442630128549)
                  ·
                    rfl

theorem cell23_4803972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 3, 3, 5].length) (baseStart_4803972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4803972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4803972 prefixEnd_4803972 := by exact prefixLift 4803972
  have htrace : WordTrace (prefixWord ++ tailWord_4803972) baseStart_4803972 baseEnd_4803972 := by
    simpa [prefixWord, tailWord_4803972, baseEnd_4803972] using wordTrace_append hprefix tailTrace_4803972
  have hstable : (prefixWord ++ tailWord_4803972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4803972).length < 2 ^ (prefixWord ++ tailWord_4803972).sum := by decide
  have hdescent : baseEnd_4803972 < baseStart_4803972 := by decide
  rcases family_descends (prefixWord ++ tailWord_4803972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4804015 : List Nat := [1, 1, 2, 1, 2, 2, 1, 6, 3, 4]
def baseStart_4804015 : Nat := 118140960795 + 4804015 * 2 ^ 59
def prefixEnd_4804015 : Nat := 4983230072969 + 3 ^ 40 * 4804015 * 2
def baseEnd_4804015 : Nat := 822256255469709000973081

theorem tailTrace_4804015 : CollatzResearch.WordTrace tailWord_4804015 prefixEnd_4804015 822256255469709000973081 := by
  unfold tailWord_4804015
  simp only [CollatzResearch.WordTrace]
  refine ⟨175216821690881590286917499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116811214460587726857944999 175216821690881590286917499)
  ·
    refine ⟨262825232536322385430376249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175216821690881590286917499 262825232536322385430376249)
    ·
      refine ⟨197118924402241789072782187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 262825232536322385430376249 197118924402241789072782187)
      ·
        refine ⟨295678386603362683609173281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 197118924402241789072782187 295678386603362683609173281)
        ·
          refine ⟨221758789952522012706879961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 295678386603362683609173281 221758789952522012706879961)
          ·
            refine ⟨166319092464391509530159971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 221758789952522012706879961 166319092464391509530159971)
            ·
              refine ⟨249478638696587264295239957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 166319092464391509530159971 249478638696587264295239957)
              ·
                refine ⟨11694311188902528013839373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 249478638696587264295239957 11694311188902528013839373)
                ·
                  refine ⟨4385366695838448005189765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11694311188902528013839373 4385366695838448005189765)
                  ·
                    refine ⟨822256255469709000973081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4385366695838448005189765 822256255469709000973081)
                    ·
                      rfl

theorem cell23_4804015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 6, 3, 4].length) (baseStart_4804015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4804015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4804015 prefixEnd_4804015 := by exact prefixLift 4804015
  have htrace : WordTrace (prefixWord ++ tailWord_4804015) baseStart_4804015 baseEnd_4804015 := by
    simpa [prefixWord, tailWord_4804015, baseEnd_4804015] using wordTrace_append hprefix tailTrace_4804015
  have hstable : (prefixWord ++ tailWord_4804015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4804015).length < 2 ^ (prefixWord ++ tailWord_4804015).sum := by decide
  have hdescent : baseEnd_4804015 < baseStart_4804015 := by decide
  rcases family_descends (prefixWord ++ tailWord_4804015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4804042 : List Nat := [3, 1, 2, 1, 2, 3, 2, 2, 2, 2, 3]
def baseStart_4804042 : Nat := 118140960795 + 4804042 * 2 ^ 59
def prefixEnd_4804042 : Nat := 4983230072969 + 3 ^ 40 * 4804042 * 2
def baseEnd_4804042 : Nat := 2466782630386798397281619

theorem tailTrace_4804042 : CollatzResearch.WordTrace tailWord_4804042 prefixEnd_4804042 2466782630386798397281619 := by
  unfold tailWord_4804042
  simp only [CollatzResearch.WordTrace]
  refine ⟨43804451615445943474537595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 116811870974522515932100253 43804451615445943474537595)
  ·
    refine ⟨65706677423168915211806393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43804451615445943474537595 65706677423168915211806393)
    ·
      refine ⟨49280008067376686408854795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65706677423168915211806393 49280008067376686408854795)
      ·
        refine ⟨73920012101065029613282193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49280008067376686408854795 73920012101065029613282193)
        ·
          refine ⟨55440009075798772209961645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73920012101065029613282193 55440009075798772209961645)
          ·
            refine ⟨20790003403424539578735617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55440009075798772209961645 20790003403424539578735617)
            ·
              refine ⟨15592502552568404684051713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20790003403424539578735617 15592502552568404684051713)
              ·
                refine ⟨11694376914426303513038785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15592502552568404684051713 11694376914426303513038785)
                ·
                  refine ⟨8770782685819727634779089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11694376914426303513038785 8770782685819727634779089)
                  ·
                    refine ⟨6578087014364795726084317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8770782685819727634779089 6578087014364795726084317)
                    ·
                      refine ⟨2466782630386798397281619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6578087014364795726084317 2466782630386798397281619)
                      ·
                        rfl

theorem cell23_4804042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 2, 2, 2, 2, 3].length) (baseStart_4804042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4804042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4804042 prefixEnd_4804042 := by exact prefixLift 4804042
  have htrace : WordTrace (prefixWord ++ tailWord_4804042) baseStart_4804042 baseEnd_4804042 := by
    simpa [prefixWord, tailWord_4804042, baseEnd_4804042] using wordTrace_append hprefix tailTrace_4804042
  have hstable : (prefixWord ++ tailWord_4804042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4804042).length < 2 ^ (prefixWord ++ tailWord_4804042).sum := by decide
  have hdescent : baseEnd_4804042 < baseStart_4804042 := by decide
  rcases family_descends (prefixWord ++ tailWord_4804042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4804048 : List Nat := [2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 8]
def baseStart_4804048 : Nat := 118140960795 + 4804048 * 2 ^ 59
def prefixEnd_4804048 : Nat := 4983230072969 + 3 ^ 40 * 4804048 * 2
def baseEnd_4804048 : Nat := 2466785711270725373806591

theorem tailTrace_4804048 : CollatzResearch.WordTrace tailWord_4804048 prefixEnd_4804048 2466785711270725373806591 := by
  unfold tailWord_4804048
  simp only [CollatzResearch.WordTrace]
  refine ⟨87609012649881018461434399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116812016866508024615245865 87609012649881018461434399)
  ·
    refine ⟨131413518974821527692151599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87609012649881018461434399 131413518974821527692151599)
    ·
      refine ⟨197120278462232291538227399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131413518974821527692151599 197120278462232291538227399)
      ·
        refine ⟨295680417693348437307341099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 197120278462232291538227399 295680417693348437307341099)
        ·
          refine ⟨443520626540022655961011649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 295680417693348437307341099 443520626540022655961011649)
          ·
            refine ⟨332640469905016991970758737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 443520626540022655961011649 332640469905016991970758737)
            ·
              refine ⟨249480352428762743978069053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 332640469905016991970758737 249480352428762743978069053)
              ·
                refine ⟨93555132160786028991775895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 249480352428762743978069053 93555132160786028991775895)
                ·
                  refine ⟨140332698241179043487663843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 93555132160786028991775895 140332698241179043487663843)
                  ·
                    refine ⟨210499047361768565231495765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 140332698241179043487663843 210499047361768565231495765)
                    ·
                      refine ⟨2466785711270725373806591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 210499047361768565231495765 2466785711270725373806591)
                      ·
                        rfl

theorem cell23_4804048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 8].length) (baseStart_4804048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4804048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4804048 prefixEnd_4804048 := by exact prefixLift 4804048
  have htrace : WordTrace (prefixWord ++ tailWord_4804048) baseStart_4804048 baseEnd_4804048 := by
    simpa [prefixWord, tailWord_4804048, baseEnd_4804048] using wordTrace_append hprefix tailTrace_4804048
  have hstable : (prefixWord ++ tailWord_4804048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4804048).length < 2 ^ (prefixWord ++ tailWord_4804048).sum := by decide
  have hdescent : baseEnd_4804048 < baseStart_4804048 := by decide
  rcases family_descends (prefixWord ++ tailWord_4804048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4804095 : List Nat := [1, 1, 2, 2, 1, 2, 2, 2, 5, 1, 4]
def baseStart_4804095 : Nat := 118140960795 + 4804095 * 2 ^ 59
def prefixEnd_4804095 : Nat := 4983230072969 + 3 ^ 40 * 4804095 * 2
def baseEnd_4804095 : Nat := 2466809844861486689918875

theorem tailTrace_4804095 : CollatzResearch.WordTrace tailWord_4804095 prefixEnd_4804095 2466809844861486689918875 := by
  unfold tailWord_4804095
  simp only [CollatzResearch.WordTrace]
  refine ⟨175219739530591763949829739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116813159687061175966553159 175219739530591763949829739)
  ·
    refine ⟨262829609295887645924744609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175219739530591763949829739 262829609295887645924744609)
    ·
      refine ⟨197122206971915734443558457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 262829609295887645924744609 197122206971915734443558457)
      ·
        refine ⟨147841655228936800832668843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 197122206971915734443558457 147841655228936800832668843)
        ·
          refine ⟨221762482843405201249003265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 147841655228936800832668843 221762482843405201249003265)
          ·
            refine ⟨166321862132553900936752449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 221762482843405201249003265 166321862132553900936752449)
            ·
              refine ⟨124741396599415425702564337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 166321862132553900936752449 124741396599415425702564337)
              ·
                refine ⟨93556047449561569276923253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 124741396599415425702564337 93556047449561569276923253)
                ·
                  refine ⟨8770879448396397119711555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 93556047449561569276923253 8770879448396397119711555)
                  ·
                    refine ⟨13156319172594595679567333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8770879448396397119711555 13156319172594595679567333)
                    ·
                      refine ⟨2466809844861486689918875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13156319172594595679567333 2466809844861486689918875)
                      ·
                        rfl

theorem cell23_4804095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 2, 5, 1, 4].length) (baseStart_4804095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4804095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4804095 prefixEnd_4804095 := by exact prefixLift 4804095
  have htrace : WordTrace (prefixWord ++ tailWord_4804095) baseStart_4804095 baseEnd_4804095 := by
    simpa [prefixWord, tailWord_4804095, baseEnd_4804095] using wordTrace_append hprefix tailTrace_4804095
  have hstable : (prefixWord ++ tailWord_4804095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4804095).length < 2 ^ (prefixWord ++ tailWord_4804095).sum := by decide
  have hdescent : baseEnd_4804095 < baseStart_4804095 := by decide
  rcases family_descends (prefixWord ++ tailWord_4804095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4804106 : List Nat := [3, 1, 2, 2, 2, 2, 2, 4, 1, 1, 3]
def baseStart_4804106 : Nat := 118140960795 + 4804106 * 2 ^ 59
def prefixEnd_4804106 : Nat := 4983230072969 + 3 ^ 40 * 4804106 * 2
def baseEnd_4804106 : Nat := 2466815493148686146881325

theorem tailTrace_4804106 : CollatzResearch.WordTrace tailWord_4804106 prefixEnd_4804106 2466815493148686146881325 := by
  unfold tailWord_4804106
  simp only [CollatzResearch.WordTrace]
  refine ⟨43805035183387978207120043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 116813427155701275218986781 43805035183387978207120043)
  ·
    refine ⟨65707552775081967310680065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43805035183387978207120043 65707552775081967310680065)
    ·
      refine ⟨49280664581311475483010049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65707552775081967310680065 49280664581311475483010049)
      ·
        refine ⟨36960498435983606612257537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49280664581311475483010049 36960498435983606612257537)
        ·
          refine ⟨27720373826987704959193153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36960498435983606612257537 27720373826987704959193153)
          ·
            refine ⟨20790280370240778719394865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27720373826987704959193153 20790280370240778719394865)
            ·
              refine ⟨15592710277680584039546149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20790280370240778719394865 15592710277680584039546149)
              ·
                refine ⟨2923633177065109507414903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15592710277680584039546149 2923633177065109507414903)
                ·
                  refine ⟨4385449765597664261122355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2923633177065109507414903 4385449765597664261122355)
                  ·
                    refine ⟨6578174648396496391683533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4385449765597664261122355 6578174648396496391683533)
                    ·
                      refine ⟨2466815493148686146881325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6578174648396496391683533 2466815493148686146881325)
                      ·
                        rfl

theorem cell23_4804106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 2, 4, 1, 1, 3].length) (baseStart_4804106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4804106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4804106 prefixEnd_4804106 := by exact prefixLift 4804106
  have htrace : WordTrace (prefixWord ++ tailWord_4804106) baseStart_4804106 baseEnd_4804106 := by
    simpa [prefixWord, tailWord_4804106, baseEnd_4804106] using wordTrace_append hprefix tailTrace_4804106
  have hstable : (prefixWord ++ tailWord_4804106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4804106).length < 2 ^ (prefixWord ++ tailWord_4804106).sum := by decide
  have hdescent : baseEnd_4804106 < baseStart_4804106 := by decide
  rcases family_descends (prefixWord ++ tailWord_4804106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4804115 : List Nat := [1, 1, 1, 2, 1, 6, 1, 1, 3, 1, 5]
def baseStart_4804115 : Nat := 118140960795 + 4804115 * 2 ^ 59
def prefixEnd_4804115 : Nat := 4983230072969 + 3 ^ 40 * 4804115 * 2
def baseEnd_4804115 : Nat := 2466820114474576611668783

theorem tailTrace_4804115 : CollatzResearch.WordTrace tailWord_4804115 prefixEnd_4804115 2466820114474576611668783 := by
  unfold tailWord_4804115
  simp only [CollatzResearch.WordTrace]
  refine ⟨175220468990519307365557799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116813645993679538243705199 175220468990519307365557799)
  ·
    refine ⟨262830703485778961048336699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175220468990519307365557799 262830703485778961048336699)
    ·
      refine ⟨394246055228668441572505049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 262830703485778961048336699 394246055228668441572505049)
      ·
        refine ⟨295684541421501331179378787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 394246055228668441572505049 295684541421501331179378787)
        ·
          refine ⟨443526812132251996769068181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 295684541421501331179378787 443526812132251996769068181)
          ·
            refine ⟨20790319318699312348550071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 443526812132251996769068181 20790319318699312348550071)
            ·
              refine ⟨31185478978048968522825107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20790319318699312348550071 31185478978048968522825107)
              ·
                refine ⟨46778218467073452784237661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31185478978048968522825107 46778218467073452784237661)
                ·
                  refine ⟨17541831925152544794089123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 46778218467073452784237661 17541831925152544794089123)
                  ·
                    refine ⟨26312747887728817191133685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17541831925152544794089123 26312747887728817191133685)
                    ·
                      refine ⟨2466820114474576611668783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26312747887728817191133685 2466820114474576611668783)
                      ·
                        rfl

theorem cell23_4804115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 1, 1, 3, 1, 5].length) (baseStart_4804115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4804115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4804115 prefixEnd_4804115 := by exact prefixLift 4804115
  have htrace : WordTrace (prefixWord ++ tailWord_4804115) baseStart_4804115 baseEnd_4804115 := by
    simpa [prefixWord, tailWord_4804115, baseEnd_4804115] using wordTrace_append hprefix tailTrace_4804115
  have hstable : (prefixWord ++ tailWord_4804115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4804115).length < 2 ^ (prefixWord ++ tailWord_4804115).sum := by decide
  have hdescent : baseEnd_4804115 < baseStart_4804115 := by decide
  rcases family_descends (prefixWord ++ tailWord_4804115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4804129 : List Nat := [1, 2, 3, 2, 2, 3, 2, 2, 1, 1, 4]
def baseStart_4804129 : Nat := 118140960795 + 4804129 * 2 ^ 59
def prefixEnd_4804129 : Nat := 4983230072969 + 3 ^ 40 * 4804129 * 2
def baseEnd_4804129 : Nat := 2466827303203739556893719

theorem tailTrace_4804129 : CollatzResearch.WordTrace tailWord_4804129 prefixEnd_4804129 2466827303203739556893719 := by
  unfold tailWord_4804129
  simp only [CollatzResearch.WordTrace]
  refine ⟨175220979612468587756567441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116813986408312391837711627 175220979612468587756567441)
  ·
    refine ⟨131415734709351440817425581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 175220979612468587756567441 131415734709351440817425581)
    ·
      refine ⟨49280900516006790306534593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 131415734709351440817425581 49280900516006790306534593)
      ·
        refine ⟨36960675387005092729900945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49280900516006790306534593 36960675387005092729900945)
        ·
          refine ⟨27720506540253819547425709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36960675387005092729900945 27720506540253819547425709)
          ·
            refine ⟨10395189952595182330284641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27720506540253819547425709 10395189952595182330284641)
            ·
              refine ⟨7796392464446386747713481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10395189952595182330284641 7796392464446386747713481)
              ·
                refine ⟨5847294348334790060785111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7796392464446386747713481 5847294348334790060785111)
                ·
                  refine ⟨8770941522502185091177667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5847294348334790060785111 8770941522502185091177667)
                  ·
                    refine ⟨13156412283753277636766501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8770941522502185091177667 13156412283753277636766501)
                    ·
                      refine ⟨2466827303203739556893719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13156412283753277636766501 2466827303203739556893719)
                      ·
                        rfl

theorem cell23_4804129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 2, 2, 1, 1, 4].length) (baseStart_4804129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4804129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4804129 prefixEnd_4804129 := by exact prefixLift 4804129
  have htrace : WordTrace (prefixWord ++ tailWord_4804129) baseStart_4804129 baseEnd_4804129 := by
    simpa [prefixWord, tailWord_4804129, baseEnd_4804129] using wordTrace_append hprefix tailTrace_4804129
  have hstable : (prefixWord ++ tailWord_4804129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4804129).length < 2 ^ (prefixWord ++ tailWord_4804129).sum := by decide
  have hdescent : baseEnd_4804129 < baseStart_4804129 := by decide
  rcases family_descends (prefixWord ++ tailWord_4804129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4804149 : List Nat := [1, 3, 3, 1, 1, 3, 2, 3, 1, 2, 3]
def baseStart_4804149 : Nat := 118140960795 + 4804149 * 2 ^ 59
def prefixEnd_4804149 : Nat := 4983230072969 + 3 ^ 40 * 4804149 * 2
def baseEnd_4804149 : Nat := 2466837572816829478643627

theorem tailTrace_4804149 : CollatzResearch.WordTrace tailWord_4804149 prefixEnd_4804149 2466837572816829478643627 := by
  unfold tailWord_4804149
  simp only [CollatzResearch.WordTrace]
  refine ⟨175221709072396131172295501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116814472714930754114863667 175221709072396131172295501)
  ·
    refine ⟨65708140902148549189610813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 175221709072396131172295501 65708140902148549189610813)
    ·
      refine ⟨24640552838305705946104055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65708140902148549189610813 24640552838305705946104055)
      ·
        refine ⟨36960829257458558919156083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24640552838305705946104055 36960829257458558919156083)
        ·
          refine ⟨55441243886187838378734125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36960829257458558919156083 55441243886187838378734125)
          ·
            refine ⟨20790466457320439392025297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55441243886187838378734125 20790466457320439392025297)
            ·
              refine ⟨15592849842990329544018973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20790466457320439392025297 15592849842990329544018973)
              ·
                refine ⟨5847318691121373579007115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15592849842990329544018973 5847318691121373579007115)
                ·
                  refine ⟨8770978036682060368510673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5847318691121373579007115 8770978036682060368510673)
                  ·
                    refine ⟨6578233527511545276383005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8770978036682060368510673 6578233527511545276383005)
                    ·
                      refine ⟨2466837572816829478643627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6578233527511545276383005 2466837572816829478643627)
                      ·
                        rfl

theorem cell23_4804149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 2, 3, 1, 2, 3].length) (baseStart_4804149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4804149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4804149 prefixEnd_4804149 := by exact prefixLift 4804149
  have htrace : WordTrace (prefixWord ++ tailWord_4804149) baseStart_4804149 baseEnd_4804149 := by
    simpa [prefixWord, tailWord_4804149, baseEnd_4804149] using wordTrace_append hprefix tailTrace_4804149
  have hstable : (prefixWord ++ tailWord_4804149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4804149).length < 2 ^ (prefixWord ++ tailWord_4804149).sum := by decide
  have hdescent : baseEnd_4804149 < baseStart_4804149 := by decide
  rcases family_descends (prefixWord ++ tailWord_4804149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4804165 : List Nat := [1, 3, 1, 1, 1, 4, 2, 1, 2, 7]
def baseStart_4804165 : Nat := 118140960795 + 4804165 * 2 ^ 59
def prefixEnd_4804165 : Nat := 4983230072969 + 3 ^ 40 * 4804165 * 2
def baseEnd_4804165 : Nat := 822281929502433805347851

theorem tailTrace_4804165 : CollatzResearch.WordTrace tailWord_4804165 prefixEnd_4804165 822281929502433805347851 := by
  unfold tailWord_4804165
  simp only [CollatzResearch.WordTrace]
  refine ⟨175222292640338165904877949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116814861760225443936585299 175222292640338165904877949)
  ·
    refine ⟨65708359740126812214329231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 175222292640338165904877949 65708359740126812214329231)
    ·
      refine ⟨98562539610190218321493847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65708359740126812214329231 98562539610190218321493847)
      ·
        refine ⟨147843809415285327482240771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98562539610190218321493847 147843809415285327482240771)
        ·
          refine ⟨221765714122927991223361157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 147843809415285327482240771 221765714122927991223361157)
          ·
            refine ⟨41581071398048998354380217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 221765714122927991223361157 41581071398048998354380217)
            ·
              refine ⟨31185803548536748765785163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41581071398048998354380217 31185803548536748765785163)
              ·
                refine ⟨46778705322805123148677745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31185803548536748765785163 46778705322805123148677745)
                ·
                  refine ⟨35084028992103842361508309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 46778705322805123148677745 35084028992103842361508309)
                  ·
                    refine ⟨822281929502433805347851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 35084028992103842361508309 822281929502433805347851)
                    ·
                      rfl

theorem cell23_4804165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 2, 1, 2, 7].length) (baseStart_4804165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4804165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4804165 prefixEnd_4804165 := by exact prefixLift 4804165
  have htrace : WordTrace (prefixWord ++ tailWord_4804165) baseStart_4804165 baseEnd_4804165 := by
    simpa [prefixWord, tailWord_4804165, baseEnd_4804165] using wordTrace_append hprefix tailTrace_4804165
  have hstable : (prefixWord ++ tailWord_4804165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4804165).length < 2 ^ (prefixWord ++ tailWord_4804165).sum := by decide
  have hdescent : baseEnd_4804165 < baseStart_4804165 := by decide
  rcases family_descends (prefixWord ++ tailWord_4804165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4804213 : List Nat := [1, 3, 4, 2, 1, 2, 2, 2, 2, 1, 3]
def baseStart_4804213 : Nat := 118140960795 + 4804213 * 2 ^ 59
def prefixEnd_4804213 : Nat := 4983230072969 + 3 ^ 40 * 4804213 * 2
def baseEnd_4804213 : Nat := 2466870435578717228243333

theorem tailTrace_4804213 : CollatzResearch.WordTrace tailWord_4804213 prefixEnd_4804213 2466870435578717228243333 := by
  unfold tailWord_4804213
  simp only [CollatzResearch.WordTrace]
  refine ⟨175224043344164270102625293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116816028896109513401750195 175224043344164270102625293)
  ·
    refine ⟨65709016254061601288484485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 175224043344164270102625293 65709016254061601288484485)
    ·
      refine ⟨12320440547636550241590841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 65709016254061601288484485 12320440547636550241590841)
      ·
        refine ⟨9240330410727412681193131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12320440547636550241590841 9240330410727412681193131)
        ·
          refine ⟨13860495616091119021789697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9240330410727412681193131 13860495616091119021789697)
          ·
            refine ⟨10395371712068339266342273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13860495616091119021789697 10395371712068339266342273)
            ·
              refine ⟨7796528784051254449756705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10395371712068339266342273 7796528784051254449756705)
              ·
                refine ⟨5847396588038440837317529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7796528784051254449756705 5847396588038440837317529)
                ·
                  refine ⟨4385547441028830627988147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5847396588038440837317529 4385547441028830627988147)
                  ·
                    refine ⟨6578321161543245941982221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4385547441028830627988147 6578321161543245941982221)
                    ·
                      refine ⟨2466870435578717228243333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6578321161543245941982221 2466870435578717228243333)
                      ·
                        rfl

theorem cell23_4804213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 2, 2, 2, 1, 3].length) (baseStart_4804213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4804213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4804213 prefixEnd_4804213 := by exact prefixLift 4804213
  have htrace : WordTrace (prefixWord ++ tailWord_4804213) baseStart_4804213 baseEnd_4804213 := by
    simpa [prefixWord, tailWord_4804213, baseEnd_4804213] using wordTrace_append hprefix tailTrace_4804213
  have hstable : (prefixWord ++ tailWord_4804213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4804213).length < 2 ^ (prefixWord ++ tailWord_4804213).sum := by decide
  have hdescent : baseEnd_4804213 < baseStart_4804213 := by decide
  rcases family_descends (prefixWord ++ tailWord_4804213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4804215 : List Nat := [1, 1, 3, 1, 1, 3, 1, 1, 2, 3, 6]
def baseStart_4804215 : Nat := 118140960795 + 4804215 * 2 ^ 59
def prefixEnd_4804215 : Nat := 4983230072969 + 3 ^ 40 * 4804215 * 2
def baseEnd_4804215 : Nat := 2466871462540026220418323

theorem tailTrace_4804215 : CollatzResearch.WordTrace tailWord_4804215 prefixEnd_4804215 2466871462540026220418323 := by
  unfold tailWord_4804215
  simp only [CollatzResearch.WordTrace]
  refine ⟨175224116290157024444198099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116816077526771349629465399 175224116290157024444198099)
  ·
    refine ⟨262836174435235536666297149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175224116290157024444198099 262836174435235536666297149)
    ·
      refine ⟨98563565413213326249861431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 262836174435235536666297149 98563565413213326249861431)
      ·
        refine ⟨147845348119819989374792147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98563565413213326249861431 147845348119819989374792147)
        ·
          refine ⟨221768022179729984062188221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 147845348119819989374792147 221768022179729984062188221)
          ·
            refine ⟨83163008317398744023320583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 221768022179729984062188221 83163008317398744023320583)
            ·
              refine ⟨124744512476098116034980875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83163008317398744023320583 124744512476098116034980875)
              ·
                refine ⟨187116768714147174052471313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 124744512476098116034980875 187116768714147174052471313)
                ·
                  refine ⟨140337576535610380539353485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 187116768714147174052471313 140337576535610380539353485)
                  ·
                    refine ⟨52626591200853892702257557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 140337576535610380539353485 52626591200853892702257557)
                    ·
                      refine ⟨2466871462540026220418323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 52626591200853892702257557 2466871462540026220418323)
                      ·
                        rfl

theorem cell23_4804215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 1, 2, 3, 6].length) (baseStart_4804215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4804215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4804215 prefixEnd_4804215 := by exact prefixLift 4804215
  have htrace : WordTrace (prefixWord ++ tailWord_4804215) baseStart_4804215 baseEnd_4804215 := by
    simpa [prefixWord, tailWord_4804215, baseEnd_4804215] using wordTrace_append hprefix tailTrace_4804215
  have hstable : (prefixWord ++ tailWord_4804215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4804215).length < 2 ^ (prefixWord ++ tailWord_4804215).sum := by decide
  have hdescent : baseEnd_4804215 < baseStart_4804215 := by decide
  rcases family_descends (prefixWord ++ tailWord_4804215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4804236 : List Nat := [2, 2, 1, 2, 1, 1, 3, 5, 2, 2, 2]
def baseStart_4804236 : Nat := 118140960795 + 4804236 * 2 ^ 59
def prefixEnd_4804236 : Nat := 4983230072969 + 3 ^ 40 * 4804236 * 2
def baseEnd_4804236 : Nat := 2466882245633770638255727

theorem tailTrace_4804236 : CollatzResearch.WordTrace tailWord_4804236 prefixEnd_4804236 2466882245633770638255727 := by
  unfold tailWord_4804236
  simp only [CollatzResearch.WordTrace]
  refine ⟨87612441111540472515356281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116816588148720630020475041 87612441111540472515356281)
  ·
    refine ⟨65709330833655354386517211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87612441111540472515356281 65709330833655354386517211)
    ·
      refine ⟨98563996250483031579775817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65709330833655354386517211 98563996250483031579775817)
      ·
        refine ⟨73922997187862273684831863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 98563996250483031579775817 73922997187862273684831863)
        ·
          refine ⟨110884495781793410527247795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73922997187862273684831863 110884495781793410527247795)
          ·
            refine ⟨166326743672690115790871693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 110884495781793410527247795 166326743672690115790871693)
            ·
              refine ⟨62372528877258793421576885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 166326743672690115790871693 62372528877258793421576885)
              ·
                refine ⟨5847424582243011883272833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 62372528877258793421576885 5847424582243011883272833)
                ·
                  refine ⟨4385568436682258912454625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5847424582243011883272833 4385568436682258912454625)
                  ·
                    refine ⟨3289176327511694184340969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4385568436682258912454625 3289176327511694184340969)
                    ·
                      refine ⟨2466882245633770638255727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3289176327511694184340969 2466882245633770638255727)
                      ·
                        rfl

theorem cell23_4804236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 5, 2, 2, 2].length) (baseStart_4804236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4804236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4804236 prefixEnd_4804236 := by exact prefixLift 4804236
  have htrace : WordTrace (prefixWord ++ tailWord_4804236) baseStart_4804236 baseEnd_4804236 := by
    simpa [prefixWord, tailWord_4804236, baseEnd_4804236] using wordTrace_append hprefix tailTrace_4804236
  have hstable : (prefixWord ++ tailWord_4804236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4804236).length < 2 ^ (prefixWord ++ tailWord_4804236).sum := by decide
  have hdescent : baseEnd_4804236 < baseStart_4804236 := by decide
  rcases family_descends (prefixWord ++ tailWord_4804236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4804259 : List Nat := [1, 1, 1, 4, 1, 1, 6, 3, 5]
def baseStart_4804259 : Nat := 118140960795 + 4804259 * 2 ^ 59
def prefixEnd_4804259 : Nat := 4983230072969 + 3 ^ 40 * 4804259 * 2
def baseEnd_4804259 : Nat := 274099339520980449807569

theorem tailTrace_4804259 : CollatzResearch.WordTrace tailWord_4804259 prefixEnd_4804259 274099339520980449807569 := by
  unfold tailWord_4804259
  simp only [CollatzResearch.WordTrace]
  refine ⟨175225721101997619958799831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116817147401331746639199887 175225721101997619958799831)
  ·
    refine ⟨262838581652996429938199747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175225721101997619958799831 262838581652996429938199747)
    ·
      refine ⟨394257872479494644907299621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 262838581652996429938199747 394257872479494644907299621)
      ·
        refine ⟨73923351089905245920118679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 394257872479494644907299621 73923351089905245920118679)
        ·
          refine ⟨110885026634857868880178019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73923351089905245920118679 110885026634857868880178019)
          ·
            refine ⟨166327539952286803320267029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 110885026634857868880178019 166327539952286803320267029)
            ·
              refine ⟨7796603435263443905637517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 166327539952286803320267029 7796603435263443905637517)
              ·
                refine ⟨2923726288223791464614069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7796603435263443905637517 2923726288223791464614069)
                ·
                  refine ⟨274099339520980449807569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2923726288223791464614069 274099339520980449807569)
                  ·
                    rfl

theorem cell23_4804259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 6, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 6, 3, 5].length) (baseStart_4804259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4804259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4804259 prefixEnd_4804259 := by exact prefixLift 4804259
  have htrace : WordTrace (prefixWord ++ tailWord_4804259) baseStart_4804259 baseEnd_4804259 := by
    simpa [prefixWord, tailWord_4804259, baseEnd_4804259] using wordTrace_append hprefix tailTrace_4804259
  have hstable : (prefixWord ++ tailWord_4804259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4804259).length < 2 ^ (prefixWord ++ tailWord_4804259).sum := by decide
  have hdescent : baseEnd_4804259 < baseStart_4804259 := by decide
  rcases family_descends (prefixWord ++ tailWord_4804259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4804264 : List Nat := [2, 1, 7, 1, 2, 1, 1, 2, 2, 1, 3]
def baseStart_4804264 : Nat := 118140960795 + 4804264 * 2 ^ 59
def prefixEnd_4804264 : Nat := 4983230072969 + 3 ^ 40 * 4804264 * 2
def baseEnd_4804264 : Nat := 2466896623092096528705599

theorem tailTrace_4804264 : CollatzResearch.WordTrace tailWord_4804264 prefixEnd_4804264 2466896623092096528705599 := by
  unfold tailWord_4804264
  simp only [CollatzResearch.WordTrace]
  refine ⟨87612951733489752906365923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116817268977986337208487897 87612951733489752906365923)
  ·
    refine ⟨131419427600234629359548885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87612951733489752906365923 131419427600234629359548885)
    ·
      refine ⟨3080142834380499125614427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 131419427600234629359548885 3080142834380499125614427)
      ·
        refine ⟨4620214251570748688421641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3080142834380499125614427 4620214251570748688421641)
        ·
          refine ⟨3465160688678061516316231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4620214251570748688421641 3465160688678061516316231)
          ·
            refine ⟨5197741033017092274474347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3465160688678061516316231 5197741033017092274474347)
            ·
              refine ⟨7796611549525638411711521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5197741033017092274474347 7796611549525638411711521)
              ·
                refine ⟨5847458662144228808783641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7796611549525638411711521 5847458662144228808783641)
                ·
                  refine ⟨4385593996608171606587731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5847458662144228808783641 4385593996608171606587731)
                  ·
                    refine ⟨6578390994912257409881597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4385593996608171606587731 6578390994912257409881597)
                    ·
                      refine ⟨2466896623092096528705599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6578390994912257409881597 2466896623092096528705599)
                      ·
                        rfl

theorem cell23_4804264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 2, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 2, 1, 1, 2, 2, 1, 3].length) (baseStart_4804264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4804264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4804264 prefixEnd_4804264 := by exact prefixLift 4804264
  have htrace : WordTrace (prefixWord ++ tailWord_4804264) baseStart_4804264 baseEnd_4804264 := by
    simpa [prefixWord, tailWord_4804264, baseEnd_4804264] using wordTrace_append hprefix tailTrace_4804264
  have hstable : (prefixWord ++ tailWord_4804264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4804264).length < 2 ^ (prefixWord ++ tailWord_4804264).sum := by decide
  have hdescent : baseEnd_4804264 < baseStart_4804264 := by decide
  rcases family_descends (prefixWord ++ tailWord_4804264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4804269 : List Nat := [1, 5, 2, 1, 1, 1, 1, 1, 4, 3, 3]
def baseStart_4804269 : Nat := 118140960795 + 4804269 * 2 ^ 59
def prefixEnd_4804269 : Nat := 4983230072969 + 3 ^ 40 * 4804269 * 2
def baseEnd_4804269 : Nat := 2466899190495369009143075

theorem tailTrace_4804269 : CollatzResearch.WordTrace tailWord_4804269 prefixEnd_4804269 2466899190495369009143075 := by
  unfold tailWord_4804269
  simp only [CollatzResearch.WordTrace]
  refine ⟨175226085831961391666663861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116817390554640927777775907 175226085831961391666663861)
  ·
    refine ⟨16427445546746380468749737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 175226085831961391666663861 16427445546746380468749737)
    ·
      refine ⟨12320584160059785351562303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16427445546746380468749737 12320584160059785351562303)
      ·
        refine ⟨18480876240089678027343455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12320584160059785351562303 18480876240089678027343455)
        ·
          refine ⟨27721314360134517041015183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18480876240089678027343455 27721314360134517041015183)
          ·
            refine ⟨41581971540201775561522775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27721314360134517041015183 41581971540201775561522775)
            ·
              refine ⟨62372957310302663342284163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41581971540201775561522775 62372957310302663342284163)
              ·
                refine ⟨93559435965453995013426245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62372957310302663342284163 93559435965453995013426245)
                ·
                  refine ⟨17542394243522624065017421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 93559435965453995013426245 17542394243522624065017421)
                  ·
                    refine ⟨6578397841320984024381533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17542394243522624065017421 6578397841320984024381533)
                    ·
                      refine ⟨2466899190495369009143075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6578397841320984024381533 2466899190495369009143075)
                      ·
                        rfl

theorem cell23_4804269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 1, 4, 3, 3].length) (baseStart_4804269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4804269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4804269 prefixEnd_4804269 := by exact prefixLift 4804269
  have htrace : WordTrace (prefixWord ++ tailWord_4804269) baseStart_4804269 baseEnd_4804269 := by
    simpa [prefixWord, tailWord_4804269, baseEnd_4804269] using wordTrace_append hprefix tailTrace_4804269
  have hstable : (prefixWord ++ tailWord_4804269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4804269).length < 2 ^ (prefixWord ++ tailWord_4804269).sum := by decide
  have hdescent : baseEnd_4804269 < baseStart_4804269 := by decide
  rcases family_descends (prefixWord ++ tailWord_4804269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4804270 : List Nat := [4, 1, 4, 1, 2, 1, 1, 1, 4, 2, 2]
def baseStart_4804270 : Nat := 118140960795 + 4804270 * 2 ^ 59
def prefixEnd_4804270 : Nat := 4983230072969 + 3 ^ 40 * 4804270 * 2
def baseEnd_4804270 : Nat := 2466899703976023505230571

theorem tailTrace_4804270 : CollatzResearch.WordTrace tailWord_4804270 prefixEnd_4804270 2466899703976023505230571 := by
  unfold tailWord_4804270
  simp only [CollatzResearch.WordTrace]
  refine ⟨21903265288119721104681283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 116817414869971845891633509 21903265288119721104681283)
  ·
    refine ⟨32854897932179581657021925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21903265288119721104681283 32854897932179581657021925)
    ·
      refine ⟨6160293362283671560691611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32854897932179581657021925 6160293362283671560691611)
      ·
        refine ⟨9240440043425507341037417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6160293362283671560691611 9240440043425507341037417)
        ·
          refine ⟨6930330032569130505778063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9240440043425507341037417 6930330032569130505778063)
          ·
            refine ⟨10395495048853695758667095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6930330032569130505778063 10395495048853695758667095)
            ·
              refine ⟨15593242573280543638000643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10395495048853695758667095 15593242573280543638000643)
              ·
                refine ⟨23389863859920815457000965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15593242573280543638000643 23389863859920815457000965)
                ·
                  refine ⟨4385599473735152898187681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23389863859920815457000965 4385599473735152898187681)
                  ·
                    refine ⟨3289199605301364673640761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4385599473735152898187681 3289199605301364673640761)
                    ·
                      refine ⟨2466899703976023505230571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3289199605301364673640761 2466899703976023505230571)
                      ·
                        rfl

theorem cell23_4804270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 1, 1, 4, 2, 2].length) (baseStart_4804270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4804270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4804270 prefixEnd_4804270 := by exact prefixLift 4804270
  have htrace : WordTrace (prefixWord ++ tailWord_4804270) baseStart_4804270 baseEnd_4804270 := by
    simpa [prefixWord, tailWord_4804270, baseEnd_4804270] using wordTrace_append hprefix tailTrace_4804270
  have hstable : (prefixWord ++ tailWord_4804270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4804270).length < 2 ^ (prefixWord ++ tailWord_4804270).sum := by decide
  have hdescent : baseEnd_4804270 < baseStart_4804270 := by decide
  rcases family_descends (prefixWord ++ tailWord_4804270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4804272 : List Nat := [2, 1, 1, 1, 2, 1, 4, 4, 2, 5]
def baseStart_4804272 : Nat := 118140960795 + 4804272 * 2 ^ 59
def prefixEnd_4804272 : Nat := 4983230072969 + 3 ^ 40 * 4804272 * 2
def baseEnd_4804272 : Nat := 822300243645777499135187

theorem tailTrace_4804272 : CollatzResearch.WordTrace tailWord_4804272 prefixEnd_4804272 822300243645777499135187 := by
  unfold tailWord_4804272
  simp only [CollatzResearch.WordTrace]
  refine ⟨87613097625475261589511535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116817463500633682119348713 87613097625475261589511535)
  ·
    refine ⟨131419646438212892384267303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87613097625475261589511535 131419646438212892384267303)
    ·
      refine ⟨197129469657319338576400955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131419646438212892384267303 197129469657319338576400955)
      ·
        refine ⟨295694204485979007864601433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 197129469657319338576400955 295694204485979007864601433)
        ·
          refine ⟨221770653364484255898451075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 295694204485979007864601433 221770653364484255898451075)
          ·
            refine ⟨332655980046726383847676613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 221770653364484255898451075 332655980046726383847676613)
            ·
              refine ⟨62372996258761196971439365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 332655980046726383847676613 62372996258761196971439365)
              ·
                refine ⟨11694936798517724432144881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 62372996258761196971439365 11694936798517724432144881)
                ·
                  refine ⟨8771202598888293324108661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11694936798517724432144881 8771202598888293324108661)
                  ·
                    refine ⟨822300243645777499135187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8771202598888293324108661 822300243645777499135187)
                    ·
                      rfl

theorem cell23_4804272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 4, 2, 5].length) (baseStart_4804272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4804272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4804272 prefixEnd_4804272 := by exact prefixLift 4804272
  have htrace : WordTrace (prefixWord ++ tailWord_4804272) baseStart_4804272 baseEnd_4804272 := by
    simpa [prefixWord, tailWord_4804272, baseEnd_4804272] using wordTrace_append hprefix tailTrace_4804272
  have hstable : (prefixWord ++ tailWord_4804272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4804272).length < 2 ^ (prefixWord ++ tailWord_4804272).sum := by decide
  have hdescent : baseEnd_4804272 < baseStart_4804272 := by decide
  rcases family_descends (prefixWord ++ tailWord_4804272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4804302 : List Nat := [4, 1, 1, 1, 3, 1, 1, 1, 2, 8]
def baseStart_4804302 : Nat := 118140960795 + 4804302 * 2 ^ 59
def prefixEnd_4804302 : Nat := 4983230072969 + 3 ^ 40 * 4804302 * 2
def baseEnd_4804302 : Nat := 822305378452322460010141

theorem tailTrace_4804302 : CollatzResearch.WordTrace tailWord_4804302 prefixEnd_4804302 822305378452322460010141 := by
  unfold tailWord_4804302
  simp only [CollatzResearch.WordTrace]
  refine ⟨21903411180105229787826895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 116818192960561225535076773 21903411180105229787826895)
  ·
    refine ⟨32855116770157844681740343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21903411180105229787826895 32855116770157844681740343)
    ·
      refine ⟨49282675155236767022610515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32855116770157844681740343 49282675155236767022610515)
      ·
        refine ⟨73924012732855150533915773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49282675155236767022610515 73924012732855150533915773)
        ·
          refine ⟨27721504774820681450218415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 73924012732855150533915773 27721504774820681450218415)
          ·
            refine ⟨41582257162231022175327623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27721504774820681450218415 41582257162231022175327623)
            ·
              refine ⟨62373385743346533262991435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41582257162231022175327623 62373385743346533262991435)
              ·
                refine ⟨93560078615019799894487153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62373385743346533262991435 93560078615019799894487153)
                ·
                  refine ⟨70170058961264849920865365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 93560078615019799894487153 70170058961264849920865365)
                  ·
                    refine ⟨822305378452322460010141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 70170058961264849920865365 822305378452322460010141)
                    ·
                      rfl

theorem cell23_4804302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 1, 2, 8].length) (baseStart_4804302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4804302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4804302 prefixEnd_4804302 := by exact prefixLift 4804302
  have htrace : WordTrace (prefixWord ++ tailWord_4804302) baseStart_4804302 baseEnd_4804302 := by
    simpa [prefixWord, tailWord_4804302, baseEnd_4804302] using wordTrace_append hprefix tailTrace_4804302
  have hstable : (prefixWord ++ tailWord_4804302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4804302).length < 2 ^ (prefixWord ++ tailWord_4804302).sum := by decide
  have hdescent : baseEnd_4804302 < baseStart_4804302 := by decide
  rcases family_descends (prefixWord ++ tailWord_4804302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4804332 : List Nat := [2, 2, 1, 1, 2, 2, 4, 1, 8]
def baseStart_4804332 : Nat := 118140960795 + 4804332 * 2 ^ 59
def prefixEnd_4804332 : Nat := 4983230072969 + 3 ^ 40 * 4804332 * 2
def baseEnd_4804332 : Nat := 274103504419622473628365

theorem tailTrace_4804332 : CollatzResearch.WordTrace tailWord_4804332 prefixEnd_4804332 274103504419622473628365 := by
  unfold tailWord_4804332
  simp only [CollatzResearch.WordTrace]
  refine ⟨87614191815366576713103625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116818922420488768950804833 87614191815366576713103625)
  ·
    refine ⟨65710643861524932534827719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87614191815366576713103625 65710643861524932534827719)
    ·
      refine ⟨98565965792287398802241579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65710643861524932534827719 98565965792287398802241579)
      ·
        refine ⟨147848948688431098203362369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98565965792287398802241579 147848948688431098203362369)
        ·
          refine ⟨110886711516323323652521777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 147848948688431098203362369 110886711516323323652521777)
          ·
            refine ⟨83165033637242492739391333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 110886711516323323652521777 83165033637242492739391333)
            ·
              refine ⟨15593443806982967388635875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 83165033637242492739391333 15593443806982967388635875)
              ·
                refine ⟨23390165710474451082953813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15593443806982967388635875 23390165710474451082953813)
                ·
                  refine ⟨274103504419622473628365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 23390165710474451082953813 274103504419622473628365)
                  ·
                    rfl

theorem cell23_4804332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 8].length) (baseStart_4804332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4804332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4804332 prefixEnd_4804332 := by exact prefixLift 4804332
  have htrace : WordTrace (prefixWord ++ tailWord_4804332) baseStart_4804332 baseEnd_4804332 := by
    simpa [prefixWord, tailWord_4804332, baseEnd_4804332] using wordTrace_append hprefix tailTrace_4804332
  have hstable : (prefixWord ++ tailWord_4804332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4804332).length < 2 ^ (prefixWord ++ tailWord_4804332).sum := by decide
  have hdescent : baseEnd_4804332 < baseStart_4804332 := by decide
  rcases family_descends (prefixWord ++ tailWord_4804332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4804433 : List Nat := [1, 2, 2, 1, 5, 1, 4, 1, 1, 1, 4]
def baseStart_4804433 : Nat := 118140960795 + 4804433 * 2 ^ 59
def prefixEnd_4804433 : Nat := 4983230072969 + 3 ^ 40 * 4804433 * 2
def baseEnd_4804433 : Nat := 2466983401322706367492321

theorem tailTrace_4804433 : CollatzResearch.WordTrace tailWord_4804433 prefixEnd_4804433 2466983401322706367492321 := by
  unfold tailWord_4804433
  simp only [CollatzResearch.WordTrace]
  refine ⟨175232067403367247675633953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116821378268911498450422635 175232067403367247675633953)
  ·
    refine ⟨131424050552525435756725465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 175232067403367247675633953 131424050552525435756725465)
    ·
      refine ⟨98568037914394076817544099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 131424050552525435756725465 98568037914394076817544099)
      ·
        refine ⟨147852056871591115226316149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98568037914394076817544099 147852056871591115226316149)
        ·
          refine ⟨13861130331711667052467139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 147852056871591115226316149 13861130331711667052467139)
          ·
            refine ⟨20791695497567500578700709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13861130331711667052467139 20791695497567500578700709)
            ·
              refine ⟨3898442905793906358506383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20791695497567500578700709 3898442905793906358506383)
              ·
                refine ⟨5847664358690859537759575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3898442905793906358506383 5847664358690859537759575)
                ·
                  refine ⟨8771496538036289306639363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5847664358690859537759575 8771496538036289306639363)
                  ·
                    refine ⟨13157244807054433959959045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8771496538036289306639363 13157244807054433959959045)
                    ·
                      refine ⟨2466983401322706367492321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13157244807054433959959045 2466983401322706367492321)
                      ·
                        rfl

theorem cell23_4804433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 4, 1, 1, 1, 4].length) (baseStart_4804433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4804433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4804433 prefixEnd_4804433 := by exact prefixLift 4804433
  have htrace : WordTrace (prefixWord ++ tailWord_4804433) baseStart_4804433 baseEnd_4804433 := by
    simpa [prefixWord, tailWord_4804433, baseEnd_4804433] using wordTrace_append hprefix tailTrace_4804433
  have hstable : (prefixWord ++ tailWord_4804433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4804433).length < 2 ^ (prefixWord ++ tailWord_4804433).sum := by decide
  have hdescent : baseEnd_4804433 < baseStart_4804433 := by decide
  rcases family_descends (prefixWord ++ tailWord_4804433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4804439 : List Nat := [1, 1, 3, 2, 5, 1, 10]
def baseStart_4804439 : Nat := 118140960795 + 4804439 * 2 ^ 59
def prefixEnd_4804439 : Nat := 4983230072969 + 3 ^ 40 * 4804439 * 2
def baseEnd_4804439 : Nat := 30456623237118930173053

theorem tailTrace_4804439 : CollatzResearch.WordTrace tailWord_4804439 prefixEnd_4804439 30456623237118930173053 := by
  unfold tailWord_4804439
  simp only [CollatzResearch.WordTrace]
  refine ⟨175232286241345510700352371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116821524160897007133568247 175232286241345510700352371)
  ·
    refine ⟨262848429362018266050528557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175232286241345510700352371 262848429362018266050528557)
    ·
      refine ⟨98568161010756849768948209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 262848429362018266050528557 98568161010756849768948209)
      ·
        refine ⟨73926120758067637326711157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 98568161010756849768948209 73926120758067637326711157)
        ·
          refine ⟨6930573821068840999379171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 73926120758067637326711157 6930573821068840999379171)
          ·
            refine ⟨10395860731603261499068757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6930573821068840999379171 10395860731603261499068757)
            ·
              refine ⟨30456623237118930173053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 10395860731603261499068757 30456623237118930173053)
              ·
                rfl

theorem cell23_4804439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 10].length) (baseStart_4804439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4804439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4804439 prefixEnd_4804439 := by exact prefixLift 4804439
  have htrace : WordTrace (prefixWord ++ tailWord_4804439) baseStart_4804439 baseEnd_4804439 := by
    simpa [prefixWord, tailWord_4804439, baseEnd_4804439] using wordTrace_append hprefix tailTrace_4804439
  have hstable : (prefixWord ++ tailWord_4804439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4804439).length < 2 ^ (prefixWord ++ tailWord_4804439).sum := by decide
  have hdescent : baseEnd_4804439 < baseStart_4804439 := by decide
  rcases family_descends (prefixWord ++ tailWord_4804439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4804450 : List Nat := [3, 3, 2, 1, 2, 1, 1, 3, 3, 2, 2]
def baseStart_4804450 : Nat := 118140960795 + 4804450 * 2 ^ 59
def prefixEnd_4804450 : Nat := 4983230072969 + 3 ^ 40 * 4804450 * 2
def baseEnd_4804450 : Nat := 2466992130493832800979743

theorem tailTrace_4804450 : CollatzResearch.WordTrace tailWord_4804450 prefixEnd_4804450 2466992130493832800979743 := by
  unfold tailWord_4804450
  simp only [CollatzResearch.WordTrace]
  refine ⟨43808171861076414894750701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 116821791629537106386001869 43808171861076414894750701)
  ·
    refine ⟨16428064447903655585531513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43808171861076414894750701 16428064447903655585531513)
    ·
      refine ⟨12321048335927741689148635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16428064447903655585531513 12321048335927741689148635)
      ·
        refine ⟨18481572503891612533722953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12321048335927741689148635 18481572503891612533722953)
        ·
          refine ⟨13861179377918709400292215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18481572503891612533722953 13861179377918709400292215)
          ·
            refine ⟨20791769066878064100438323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13861179377918709400292215 20791769066878064100438323)
            ·
              refine ⟨31187653600317096150657485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20791769066878064100438323 31187653600317096150657485)
              ·
                refine ⟨11695370100118911056496557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31187653600317096150657485 11695370100118911056496557)
                ·
                  refine ⟨4385763787544591646186209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11695370100118911056496557 4385763787544591646186209)
                  ·
                    refine ⟨3289322840658443734639657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4385763787544591646186209 3289322840658443734639657)
                    ·
                      refine ⟨2466992130493832800979743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3289322840658443734639657 2466992130493832800979743)
                      ·
                        rfl

theorem cell23_4804450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 1, 3, 3, 2, 2].length) (baseStart_4804450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4804450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4804450 prefixEnd_4804450 := by exact prefixLift 4804450
  have htrace : WordTrace (prefixWord ++ tailWord_4804450) baseStart_4804450 baseEnd_4804450 := by
    simpa [prefixWord, tailWord_4804450, baseEnd_4804450] using wordTrace_append hprefix tailTrace_4804450
  have hstable : (prefixWord ++ tailWord_4804450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4804450).length < 2 ^ (prefixWord ++ tailWord_4804450).sum := by decide
  have hdescent : baseEnd_4804450 < baseStart_4804450 := by decide
  rcases family_descends (prefixWord ++ tailWord_4804450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4804613 : List Nat := [1, 3, 1, 1, 2, 4, 1, 2, 2, 4, 2]
def baseStart_4804613 : Nat := 118140960795 + 4804613 * 2 ^ 59
def prefixEnd_4804613 : Nat := 4983230072969 + 3 ^ 40 * 4804613 * 2
def baseEnd_4804613 : Nat := 2467075827840515663241493

theorem tailTrace_4804613 : CollatzResearch.WordTrace tailWord_4804613 prefixEnd_4804613 2467075827840515663241493 := by
  unfold tailWord_4804613
  simp only [CollatzResearch.WordTrace]
  refine ⟨175238632542715138417186493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116825755028476758944790995 175238632542715138417186493)
  ·
    refine ⟨65714487203518176906444935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 175238632542715138417186493 65714487203518176906444935)
    ·
      refine ⟨98571730805277265359667403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65714487203518176906444935 98571730805277265359667403)
      ·
        refine ⟨147857596207915898039501105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98571730805277265359667403 147857596207915898039501105)
        ·
          refine ⟨110893197155936923529625829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 147857596207915898039501105 110893197155936923529625829)
          ·
            refine ⟨20792474466738173161804843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 110893197155936923529625829 20792474466738173161804843)
            ·
              refine ⟨31188711700107259742707265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20792474466738173161804843 31188711700107259742707265)
              ·
                refine ⟨23391533775080444807030449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31188711700107259742707265 23391533775080444807030449)
                ·
                  refine ⟨17543650331310333605272837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23391533775080444807030449 17543650331310333605272837)
                  ·
                    refine ⟨3289434437120687550988657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17543650331310333605272837 3289434437120687550988657)
                    ·
                      refine ⟨2467075827840515663241493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3289434437120687550988657 2467075827840515663241493)
                      ·
                        rfl

theorem cell23_4804613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 1, 2, 2, 4, 2].length) (baseStart_4804613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4804613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4804613 prefixEnd_4804613 := by exact prefixLift 4804613
  have htrace : WordTrace (prefixWord ++ tailWord_4804613) baseStart_4804613 baseEnd_4804613 := by
    simpa [prefixWord, tailWord_4804613, baseEnd_4804613] using wordTrace_append hprefix tailTrace_4804613
  have hstable : (prefixWord ++ tailWord_4804613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4804613).length < 2 ^ (prefixWord ++ tailWord_4804613).sum := by decide
  have hdescent : baseEnd_4804613 < baseStart_4804613 := by decide
  rcases family_descends (prefixWord ++ tailWord_4804613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4804614 : List Nat := [6, 2, 1, 2, 1, 1, 2, 1, 7]
def baseStart_4804614 : Nat := 118140960795 + 4804614 * 2 ^ 59
def prefixEnd_4804614 : Nat := 4983230072969 + 3 ^ 40 * 4804614 * 2
def baseEnd_4804614 : Nat := 274119593480130017703221

theorem tailTrace_4804614 : CollatzResearch.WordTrace tailWord_4804614 prefixEnd_4804614 274119593480130017703221 := by
  unfold tailWord_4804614
  simp only [CollatzResearch.WordTrace]
  refine ⟨5476208406740984862124153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 116825779343807677058648597 5476208406740984862124153)
  ·
    refine ⟨4107156305055738646593115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5476208406740984862124153 4107156305055738646593115)
    ·
      refine ⟨6160734457583607969889673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4107156305055738646593115 6160734457583607969889673)
      ·
        refine ⟨4620550843187705977417255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6160734457583607969889673 4620550843187705977417255)
        ·
          refine ⟨6930826264781558966125883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4620550843187705977417255 6930826264781558966125883)
          ·
            refine ⟨10396239397172338449188825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6930826264781558966125883 10396239397172338449188825)
            ·
              refine ⟨7797179547879253836891619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10396239397172338449188825 7797179547879253836891619)
              ·
                refine ⟨11695769321818880755337429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7797179547879253836891619 11695769321818880755337429)
                ·
                  refine ⟨274119593480130017703221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11695769321818880755337429 274119593480130017703221)
                  ·
                    rfl

theorem cell23_4804614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 2, 1, 7].length) (baseStart_4804614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4804614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4804614 prefixEnd_4804614 := by exact prefixLift 4804614
  have htrace : WordTrace (prefixWord ++ tailWord_4804614) baseStart_4804614 baseEnd_4804614 := by
    simpa [prefixWord, tailWord_4804614, baseEnd_4804614] using wordTrace_append hprefix tailTrace_4804614
  have hstable : (prefixWord ++ tailWord_4804614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4804614).length < 2 ^ (prefixWord ++ tailWord_4804614).sum := by decide
  have hdescent : baseEnd_4804614 < baseStart_4804614 := by decide
  rcases family_descends (prefixWord ++ tailWord_4804614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4804657 : List Nat := [1, 2, 2, 3, 1, 5, 1, 3, 1, 4]
def baseStart_4804657 : Nat := 118140960795 + 4804657 * 2 ^ 59
def prefixEnd_4804657 : Nat := 4983230072969 + 3 ^ 40 * 4804657 * 2
def baseEnd_4804657 : Nat := 822366140329771163697097

theorem tailTrace_4804657 : CollatzResearch.WordTrace tailWord_4804657 prefixEnd_4804657 822366140329771163697097 := by
  unfold tailWord_4804657
  simp only [CollatzResearch.WordTrace]
  refine ⟨175240237354555733931788225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116826824903037155954525483 175240237354555733931788225)
  ·
    refine ⟨131430178015916800448841169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 175240237354555733931788225 131430178015916800448841169)
    ·
      refine ⟨98572633511937600336630877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 131430178015916800448841169 98572633511937600336630877)
      ·
        refine ⟨36964737566976600126236579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 98572633511937600336630877 36964737566976600126236579)
        ·
          refine ⟨55447106350464900189354869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36964737566976600126236579 55447106350464900189354869)
          ·
            refine ⟨5198166220356084392752019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 55447106350464900189354869 5198166220356084392752019)
            ·
              refine ⟨7797249330534126589128029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5198166220356084392752019 7797249330534126589128029)
              ·
                refine ⟨2923968498950297470923011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7797249330534126589128029 2923968498950297470923011)
                ·
                  refine ⟨4385952748425446206384517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2923968498950297470923011 4385952748425446206384517)
                  ·
                    refine ⟨822366140329771163697097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4385952748425446206384517 822366140329771163697097)
                    ·
                      rfl

theorem cell23_4804657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 5, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 5, 1, 3, 1, 4].length) (baseStart_4804657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4804657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4804657 prefixEnd_4804657 := by exact prefixLift 4804657
  have htrace : WordTrace (prefixWord ++ tailWord_4804657) baseStart_4804657 baseEnd_4804657 := by
    simpa [prefixWord, tailWord_4804657, baseEnd_4804657] using wordTrace_append hprefix tailTrace_4804657
  have hstable : (prefixWord ++ tailWord_4804657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4804657).length < 2 ^ (prefixWord ++ tailWord_4804657).sum := by decide
  have hdescent : baseEnd_4804657 < baseStart_4804657 := by decide
  rcases family_descends (prefixWord ++ tailWord_4804657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4804663 : List Nat := [1, 1, 3, 1, 2, 2, 2, 2, 5, 1, 3]
def baseStart_4804663 : Nat := 118140960795 + 4804663 * 2 ^ 59
def prefixEnd_4804663 : Nat := 4983230072969 + 3 ^ 40 * 4804663 * 2
def baseEnd_4804663 : Nat := 2467101501873240467616263

theorem tailTrace_4804663 : CollatzResearch.WordTrace tailWord_4804663 prefixEnd_4804663 2467101501873240467616263 := by
  unfold tailWord_4804663
  simp only [CollatzResearch.WordTrace]
  refine ⟨175240456192533996956506643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116826970795022664637671095 175240456192533996956506643)
  ·
    refine ⟨262860684288800995434759965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175240456192533996956506643 262860684288800995434759965)
    ·
      refine ⟨98572756608300373288034987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 262860684288800995434759965 98572756608300373288034987)
      ·
        refine ⟨147859134912450559932052481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98572756608300373288034987 147859134912450559932052481)
        ·
          refine ⟨110894351184337919949039361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 147859134912450559932052481 110894351184337919949039361)
          ·
            refine ⟨83170763388253439961779521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 110894351184337919949039361 83170763388253439961779521)
            ·
              refine ⟨62378072541190079971334641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 83170763388253439961779521 62378072541190079971334641)
              ·
                refine ⟨46783554405892559978500981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 62378072541190079971334641 46783554405892559978500981)
                ·
                  refine ⟨4385958225552427497984467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 46783554405892559978500981 4385958225552427497984467)
                  ·
                    refine ⟨6578937338328641246976701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4385958225552427497984467 6578937338328641246976701)
                    ·
                      refine ⟨2467101501873240467616263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6578937338328641246976701 2467101501873240467616263)
                      ·
                        rfl

theorem cell23_4804663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 2, 5, 1, 3].length) (baseStart_4804663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4804663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4804663 prefixEnd_4804663 := by exact prefixLift 4804663
  have htrace : WordTrace (prefixWord ++ tailWord_4804663) baseStart_4804663 baseEnd_4804663 := by
    simpa [prefixWord, tailWord_4804663, baseEnd_4804663] using wordTrace_append hprefix tailTrace_4804663
  have hstable : (prefixWord ++ tailWord_4804663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4804663).length < 2 ^ (prefixWord ++ tailWord_4804663).sum := by decide
  have hdescent : baseEnd_4804663 < baseStart_4804663 := by decide
  rcases family_descends (prefixWord ++ tailWord_4804663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4804666 : List Nat := [3, 1, 1, 1, 3, 1, 1, 2, 5, 5]
def baseStart_4804666 : Nat := 118140960795 + 4804666 * 2 ^ 59
def prefixEnd_4804666 : Nat := 4983230072969 + 3 ^ 40 * 4804666 * 2
def baseEnd_4804666 : Nat := 822367680771734651959583

theorem tailTrace_4804666 : CollatzResearch.WordTrace tailWord_4804666 prefixEnd_4804666 822367680771734651959583 := by
  unfold tailWord_4804666
  simp only [CollatzResearch.WordTrace]
  refine ⟨43810141402880782117216463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 116827043741015418979243901 43810141402880782117216463)
  ·
    refine ⟨65715212104321173175824695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43810141402880782117216463 65715212104321173175824695)
    ·
      refine ⟨98572818156481759763737043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65715212104321173175824695 98572818156481759763737043)
      ·
        refine ⟨147859227234722639645605565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98572818156481759763737043 147859227234722639645605565)
        ·
          refine ⟨55447210213020989867102087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 147859227234722639645605565 55447210213020989867102087)
          ·
            refine ⟨83170815319531484800653131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55447210213020989867102087 83170815319531484800653131)
            ·
              refine ⟨124756222979297227200979697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83170815319531484800653131 124756222979297227200979697)
              ·
                refine ⟨93567167234472920400734773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 124756222979297227200979697 93567167234472920400734773)
                ·
                  refine ⟨8771921928231836287568885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 93567167234472920400734773 8771921928231836287568885)
                  ·
                    refine ⟨822367680771734651959583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8771921928231836287568885 822367680771734651959583)
                    ·
                      rfl

theorem cell23_4804666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 2, 5, 5].length) (baseStart_4804666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4804666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4804666 prefixEnd_4804666 := by exact prefixLift 4804666
  have htrace : WordTrace (prefixWord ++ tailWord_4804666) baseStart_4804666 baseEnd_4804666 := by
    simpa [prefixWord, tailWord_4804666, baseEnd_4804666] using wordTrace_append hprefix tailTrace_4804666
  have hstable : (prefixWord ++ tailWord_4804666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4804666).length < 2 ^ (prefixWord ++ tailWord_4804666).sum := by decide
  have hdescent : baseEnd_4804666 < baseStart_4804666 := by decide
  rcases family_descends (prefixWord ++ tailWord_4804666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4804700 : List Nat := [2, 2, 4, 1, 1, 2, 3, 2, 1, 5]
def baseStart_4804700 : Nat := 118140960795 + 4804700 * 2 ^ 59
def prefixEnd_4804700 : Nat := 4983230072969 + 3 ^ 40 * 4804700 * 2
def baseEnd_4804700 : Nat := 822373500219152274284531

theorem tailTrace_4804700 : CollatzResearch.WordTrace tailWord_4804700 prefixEnd_4804700 822373500219152274284531 := by
  unfold tailWord_4804700
  simp only [CollatzResearch.WordTrace]
  refine ⟨87620902846699976137801777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116827870462266634850402369 87620902846699976137801777)
  ·
    refine ⟨65715677135024982103351333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87620902846699976137801777 65715677135024982103351333)
    ·
      refine ⟨12321689462817184144378375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 65715677135024982103351333 12321689462817184144378375)
      ·
        refine ⟨18482534194225776216567563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12321689462817184144378375 18482534194225776216567563)
        ·
          refine ⟨27723801291338664324851345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18482534194225776216567563 27723801291338664324851345)
          ·
            refine ⟨20792850968503998243638509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27723801291338664324851345 20792850968503998243638509)
            ·
              refine ⟨7797319113188999341364441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20792850968503998243638509 7797319113188999341364441)
              ·
                refine ⟨5847989334891749506023331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7797319113188999341364441 5847989334891749506023331)
                ·
                  refine ⟨8771984002337624259034997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5847989334891749506023331 8771984002337624259034997)
                  ·
                    refine ⟨822373500219152274284531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8771984002337624259034997 822373500219152274284531)
                    ·
                      rfl

theorem cell23_4804700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 3, 2, 1, 5].length) (baseStart_4804700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4804700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4804700 prefixEnd_4804700 := by exact prefixLift 4804700
  have htrace : WordTrace (prefixWord ++ tailWord_4804700) baseStart_4804700 baseEnd_4804700 := by
    simpa [prefixWord, tailWord_4804700, baseEnd_4804700] using wordTrace_append hprefix tailTrace_4804700
  have hstable : (prefixWord ++ tailWord_4804700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4804700).length < 2 ^ (prefixWord ++ tailWord_4804700).sum := by decide
  have hdescent : baseEnd_4804700 < baseStart_4804700 := by decide
  rcases family_descends (prefixWord ++ tailWord_4804700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4804703 : List Nat := [1, 1, 2, 3, 1, 1, 2, 6, 1, 1, 4]
def baseStart_4804703 : Nat := 118140960795 + 4804703 * 2 ^ 59
def prefixEnd_4804703 : Nat := 4983230072969 + 3 ^ 40 * 4804703 * 2
def baseEnd_4804703 : Nat := 2467122041099420311116079

theorem tailTrace_4804703 : CollatzResearch.WordTrace tailWord_4804703 prefixEnd_4804703 2467122041099420311116079 := by
  unfold tailWord_4804703
  simp only [CollatzResearch.WordTrace]
  refine ⟨175241915112389083787962763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116827943408259389191975175 175241915112389083787962763)
  ·
    refine ⟨262862872668583625681944145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175241915112389083787962763 262862872668583625681944145)
    ·
      refine ⟨197147154501437719261458109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 262862872668583625681944145 197147154501437719261458109)
      ·
        refine ⟨73930182938039144723046791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 197147154501437719261458109 73930182938039144723046791)
        ·
          refine ⟨110895274407058717084570187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73930182938039144723046791 110895274407058717084570187)
          ·
            refine ⟨166342911610588075626855281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 110895274407058717084570187 166342911610588075626855281)
            ·
              refine ⟨124757183707941056720141461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 166342911610588075626855281 124757183707941056720141461)
              ·
                refine ⟨5847992986309737033756631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 124757183707941056720141461 5847992986309737033756631)
                ·
                  refine ⟨8771989479464605550634947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5847992986309737033756631 8771989479464605550634947)
                  ·
                    refine ⟨13157984219196908325952421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8771989479464605550634947 13157984219196908325952421)
                    ·
                      refine ⟨2467122041099420311116079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13157984219196908325952421 2467122041099420311116079)
                      ·
                        rfl

theorem cell23_4804703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 6, 1, 1, 4].length) (baseStart_4804703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4804703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4804703 prefixEnd_4804703 := by exact prefixLift 4804703
  have htrace : WordTrace (prefixWord ++ tailWord_4804703) baseStart_4804703 baseEnd_4804703 := by
    simpa [prefixWord, tailWord_4804703, baseEnd_4804703] using wordTrace_append hprefix tailTrace_4804703
  have hstable : (prefixWord ++ tailWord_4804703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4804703).length < 2 ^ (prefixWord ++ tailWord_4804703).sum := by decide
  have hdescent : baseEnd_4804703 < baseStart_4804703 := by decide
  rcases family_descends (prefixWord ++ tailWord_4804703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4804758 : List Nat := [5, 3, 2, 1, 1, 1, 1, 1, 1, 5, 2]
def baseStart_4804758 : Nat := 118140960795 + 4804758 * 2 ^ 59
def prefixEnd_4804758 : Nat := 4983230072969 + 3 ^ 40 * 4804758 * 2
def baseEnd_4804758 : Nat := 2467150282535417595928327

theorem tailTrace_4804758 : CollatzResearch.WordTrace tailWord_4804758 prefixEnd_4804758 2467150282535417595928327 := by
  unfold tailWord_4804758
  simp only [CollatzResearch.WordTrace]
  refine ⟨10952745070449364261325933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 116829280751459885454143285 10952745070449364261325933)
  ·
    refine ⟨4107279401418511597997225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10952745070449364261325933 4107279401418511597997225)
    ·
      refine ⟨3080459551063883698497919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4107279401418511597997225 3080459551063883698497919)
      ·
        refine ⟨4620689326595825547746879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3080459551063883698497919 4620689326595825547746879)
        ·
          refine ⟨6931033989893738321620319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4620689326595825547746879 6931033989893738321620319)
          ·
            refine ⟨10396550984840607482430479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6931033989893738321620319 10396550984840607482430479)
            ·
              refine ⟨15594826477260911223645719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10396550984840607482430479 15594826477260911223645719)
              ·
                refine ⟨23392239715891366835468579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15594826477260911223645719 23392239715891366835468579)
                ·
                  refine ⟨35088359573837050253202869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23392239715891366835468579 35088359573837050253202869)
                  ·
                    refine ⟨3289533710047223461237769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 35088359573837050253202869 3289533710047223461237769)
                    ·
                      refine ⟨2467150282535417595928327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3289533710047223461237769 2467150282535417595928327)
                      ·
                        rfl

theorem cell23_4804758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 1, 1, 1, 5, 2].length) (baseStart_4804758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4804758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4804758 prefixEnd_4804758 := by exact prefixLift 4804758
  have htrace : WordTrace (prefixWord ++ tailWord_4804758) baseStart_4804758 baseEnd_4804758 := by
    simpa [prefixWord, tailWord_4804758, baseEnd_4804758] using wordTrace_append hprefix tailTrace_4804758
  have hstable : (prefixWord ++ tailWord_4804758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4804758).length < 2 ^ (prefixWord ++ tailWord_4804758).sum := by decide
  have hdescent : baseEnd_4804758 < baseStart_4804758 := by decide
  rcases family_descends (prefixWord ++ tailWord_4804758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4804760 : List Nat := [2, 1, 2, 4, 3, 1, 3, 7]
def baseStart_4804760 : Nat := 118140960795 + 4804760 * 2 ^ 59
def prefixEnd_4804760 : Nat := 4983230072969 + 3 ^ 40 * 4804760 * 2
def baseEnd_4804760 : Nat := 91375974425804688448271

theorem tailTrace_4804760 : CollatzResearch.WordTrace tailWord_4804760 prefixEnd_4804760 91375974425804688448271 := by
  unfold tailWord_4804760
  simp only [CollatzResearch.WordTrace]
  refine ⟨87621997036591291261393867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116829329382121721681858489 87621997036591291261393867)
  ·
    refine ⟨131432995554886936892090801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87621997036591291261393867 131432995554886936892090801)
    ·
      refine ⟨98574746666165202669068101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 131432995554886936892090801 98574746666165202669068101)
      ·
        refine ⟨18482764999905975500450269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 98574746666165202669068101 18482764999905975500450269)
        ·
          refine ⟨6931036874964740812668851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18482764999905975500450269 6931036874964740812668851)
          ·
            refine ⟨10396555312447111219003277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6931036874964740812668851 10396555312447111219003277)
            ·
              refine ⟨3898708242167666707126229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10396555312447111219003277 3898708242167666707126229)
              ·
                refine ⟨91375974425804688448271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3898708242167666707126229 91375974425804688448271)
                ·
                  rfl

theorem cell23_4804760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 3, 7].length) (baseStart_4804760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4804760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4804760 prefixEnd_4804760 := by exact prefixLift 4804760
  have htrace : WordTrace (prefixWord ++ tailWord_4804760) baseStart_4804760 baseEnd_4804760 := by
    simpa [prefixWord, tailWord_4804760, baseEnd_4804760] using wordTrace_append hprefix tailTrace_4804760
  have hstable : (prefixWord ++ tailWord_4804760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4804760).length < 2 ^ (prefixWord ++ tailWord_4804760).sum := by decide
  have hdescent : baseEnd_4804760 < baseStart_4804760 := by decide
  rcases family_descends (prefixWord ++ tailWord_4804760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4804763 : List Nat := [1, 1, 1, 1, 1, 1, 2, 4, 2, 7, 2]
def baseStart_4804763 : Nat := 118140960795 + 4804763 * 2 ^ 59
def prefixEnd_4804763 : Nat := 4983230072969 + 3 ^ 40 * 4804763 * 2
def baseEnd_4804763 : Nat := 2467152849938690076365803

theorem tailTrace_4804763 : CollatzResearch.WordTrace tailWord_4804763 prefixEnd_4804763 2467152849938690076365803 := by
  unfold tailWord_4804763
  simp only [CollatzResearch.WordTrace]
  refine ⟨175244103492171714035146943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116829402328114476023431295 175244103492171714035146943)
  ·
    refine ⟨262866155238257571052720415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175244103492171714035146943 262866155238257571052720415)
    ·
      refine ⟨394299232857386356579080623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 262866155238257571052720415 394299232857386356579080623)
      ·
        refine ⟨591448849286079534868620935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 394299232857386356579080623 591448849286079534868620935)
        ·
          refine ⟨887173273929119302302931403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 591448849286079534868620935 887173273929119302302931403)
          ·
            refine ⟨1330759910893678953454397105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 887173273929119302302931403 1330759910893678953454397105)
            ·
              refine ⟨998069933170259215090797829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1330759910893678953454397105 998069933170259215090797829)
              ·
                refine ⟨187138112469423602829524593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 998069933170259215090797829 187138112469423602829524593)
                ·
                  refine ⟨140353584352067702122143445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 187138112469423602829524593 140353584352067702122143445)
                  ·
                    refine ⟨3289537133251586768487737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 140353584352067702122143445 3289537133251586768487737)
                    ·
                      refine ⟨2467152849938690076365803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3289537133251586768487737 2467152849938690076365803)
                      ·
                        rfl

theorem cell23_4804763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4, 2, 7, 2].length) (baseStart_4804763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4804763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4804763 prefixEnd_4804763 := by exact prefixLift 4804763
  have htrace : WordTrace (prefixWord ++ tailWord_4804763) baseStart_4804763 baseEnd_4804763 := by
    simpa [prefixWord, tailWord_4804763, baseEnd_4804763] using wordTrace_append hprefix tailTrace_4804763
  have hstable : (prefixWord ++ tailWord_4804763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4804763).length < 2 ^ (prefixWord ++ tailWord_4804763).sum := by decide
  have hdescent : baseEnd_4804763 < baseStart_4804763 := by decide
  rcases family_descends (prefixWord ++ tailWord_4804763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4804814 : List Nat := [4, 1, 1, 1, 4, 2, 2, 2, 1, 3, 2]
def baseStart_4804814 : Nat := 118140960795 + 4804814 * 2 ^ 59
def prefixEnd_4804814 : Nat := 4983230072969 + 3 ^ 40 * 4804814 * 2
def baseEnd_4804814 : Nat := 2467179037452069376828069

theorem tailTrace_4804814 : CollatzResearch.WordTrace tailWord_4804814 prefixEnd_4804814 2467179037452069376828069 := by
  unfold tailWord_4804814
  simp only [CollatzResearch.WordTrace]
  refine ⟨21905745451873368718156687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 116830642409991299830168997 21905745451873368718156687)
  ·
    refine ⟨32858618177810053077235031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21905745451873368718156687 32858618177810053077235031)
    ·
      refine ⟨49287927266715079615852547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32858618177810053077235031 49287927266715079615852547)
      ·
        refine ⟨73931890900072619423778821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49287927266715079615852547 73931890900072619423778821)
        ·
          refine ⟨13862229543763616141958529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 73931890900072619423778821 13862229543763616141958529)
          ·
            refine ⟨10396672157822712106468897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13862229543763616141958529 10396672157822712106468897)
            ·
              refine ⟨7797504118367034079851673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10396672157822712106468897 7797504118367034079851673)
              ·
                refine ⟨5848128088775275559888755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7797504118367034079851673 5848128088775275559888755)
                ·
                  refine ⟨8772192133162913339833133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5848128088775275559888755 8772192133162913339833133)
                  ·
                    refine ⟨3289572049936092502437425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8772192133162913339833133 3289572049936092502437425)
                    ·
                      refine ⟨2467179037452069376828069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3289572049936092502437425 2467179037452069376828069)
                      ·
                        rfl

theorem cell23_4804814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 2, 2, 1, 3, 2].length) (baseStart_4804814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4804814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4804814 prefixEnd_4804814 := by exact prefixLift 4804814
  have htrace : WordTrace (prefixWord ++ tailWord_4804814) baseStart_4804814 baseEnd_4804814 := by
    simpa [prefixWord, tailWord_4804814, baseEnd_4804814] using wordTrace_append hprefix tailTrace_4804814
  have hstable : (prefixWord ++ tailWord_4804814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4804814).length < 2 ^ (prefixWord ++ tailWord_4804814).sum := by decide
  have hdescent : baseEnd_4804814 < baseStart_4804814 := by decide
  rcases family_descends (prefixWord ++ tailWord_4804814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4804850 : List Nat := [3, 2, 1, 3, 2, 1, 3, 1, 7]
def baseStart_4804850 : Nat := 118140960795 + 4804850 * 2 ^ 59
def prefixEnd_4804850 : Nat := 4983230072969 + 3 ^ 40 * 4804850 * 2
def baseEnd_4804850 : Nat := 274133058083959026219767

theorem tailTrace_4804850 : CollatzResearch.WordTrace tailWord_4804850 prefixEnd_4804850 274133058083959026219767 := by
  unfold tailWord_4804850
  simp only [CollatzResearch.WordTrace]
  refine ⟨43811819160714131973391001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 116831517761904351929042669 43811819160714131973391001)
  ·
    refine ⟨32858864370535598980043251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43811819160714131973391001 32858864370535598980043251)
    ·
      refine ⟨49288296555803398470064877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32858864370535598980043251 49288296555803398470064877)
      ·
        refine ⟨18483111208426274426274329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49288296555803398470064877 18483111208426274426274329)
        ·
          refine ⟨13862333406319705819705747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18483111208426274426274329 13862333406319705819705747)
          ·
            refine ⟨20793500109479558729558621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13862333406319705819705747 20793500109479558729558621)
            ·
              refine ⟨7797562541054834523584483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20793500109479558729558621 7797562541054834523584483)
              ·
                refine ⟨11696343811582251785376725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7797562541054834523584483 11696343811582251785376725)
                ·
                  refine ⟨274133058083959026219767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11696343811582251785376725 274133058083959026219767)
                  ·
                    rfl

theorem cell23_4804850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 3, 1, 7].length) (baseStart_4804850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4804850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4804850 prefixEnd_4804850 := by exact prefixLift 4804850
  have htrace : WordTrace (prefixWord ++ tailWord_4804850) baseStart_4804850 baseEnd_4804850 := by
    simpa [prefixWord, tailWord_4804850, baseEnd_4804850] using wordTrace_append hprefix tailTrace_4804850
  have hstable : (prefixWord ++ tailWord_4804850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4804850).length < 2 ^ (prefixWord ++ tailWord_4804850).sum := by decide
  have hdescent : baseEnd_4804850 < baseStart_4804850 := by decide
  rcases family_descends (prefixWord ++ tailWord_4804850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4804863 : List Nat := [1, 1, 2, 2, 1, 4, 1, 2, 4, 5]
def baseStart_4804863 : Nat := 118140960795 + 4804863 * 2 ^ 59
def prefixEnd_4804863 : Nat := 4983230072969 + 3 ^ 40 * 4804863 * 2
def baseEnd_4804863 : Nat := 822401399334713228371781

theorem tailTrace_4804863 : CollatzResearch.WordTrace tailWord_4804863 prefixEnd_4804863 822401399334713228371781 := by
  unfold tailWord_4804863
  simp only [CollatzResearch.WordTrace]
  refine ⟨175247750791809431113787243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116831833861206287409191495 175247750791809431113787243)
  ·
    refine ⟨262871626187714146670680865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175247750791809431113787243 262871626187714146670680865)
    ·
      refine ⟨197153719640785610003010649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 262871626187714146670680865 197153719640785610003010649)
      ·
        refine ⟨147865289730589207502257987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 197153719640785610003010649 147865289730589207502257987)
        ·
          refine ⟨221797934595883811253386981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 147865289730589207502257987 221797934595883811253386981)
          ·
            refine ⟨41587112736728214610010059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 221797934595883811253386981 41587112736728214610010059)
            ·
              refine ⟨62380669105092321915015089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41587112736728214610010059 62380669105092321915015089)
              ·
                refine ⟨46785501828819241436261317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 62380669105092321915015089 46785501828819241436261317)
                ·
                  refine ⟨8772281592903607769298997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 46785501828819241436261317 8772281592903607769298997)
                  ·
                    refine ⟨822401399334713228371781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8772281592903607769298997 822401399334713228371781)
                    ·
                      rfl

theorem cell23_4804863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 2, 4, 5].length) (baseStart_4804863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4804863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4804863 prefixEnd_4804863 := by exact prefixLift 4804863
  have htrace : WordTrace (prefixWord ++ tailWord_4804863) baseStart_4804863 baseEnd_4804863 := by
    simpa [prefixWord, tailWord_4804863, baseEnd_4804863] using wordTrace_append hprefix tailTrace_4804863
  have hstable : (prefixWord ++ tailWord_4804863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4804863).length < 2 ^ (prefixWord ++ tailWord_4804863).sum := by decide
  have hdescent : baseEnd_4804863 < baseStart_4804863 := by decide
  rcases family_descends (prefixWord ++ tailWord_4804863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4804883 : List Nat := [1, 1, 1, 2, 1, 3, 1, 5, 1, 3, 4]
def baseStart_4804883 : Nat := 118140960795 + 4804883 * 2 ^ 59
def prefixEnd_4804883 : Nat := 4983230072969 + 3 ^ 40 * 4804883 * 2
def baseEnd_4804883 : Nat := 2467214467617229606865251

theorem tailTrace_4804883 : CollatzResearch.WordTrace tailWord_4804883 prefixEnd_4804883 2467214467617229606865251 := by
  unfold tailWord_4804883
  simp only [CollatzResearch.WordTrace]
  refine ⟨175248480251736974529515303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116832320167824649686343535 175248480251736974529515303)
  ·
    refine ⟨262872720377605461794272955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175248480251736974529515303 262872720377605461794272955)
    ·
      refine ⟨394309080566408192691409433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 262872720377605461794272955 394309080566408192691409433)
      ·
        refine ⟨295731810424806144518557075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 394309080566408192691409433 295731810424806144518557075)
        ·
          refine ⟨443597715637209216777835613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 295731810424806144518557075 443597715637209216777835613)
          ·
            refine ⟨166349143363953456291688355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 443597715637209216777835613 166349143363953456291688355)
            ·
              refine ⟨249523715045930184437532533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 166349143363953456291688355 249523715045930184437532533)
              ·
                refine ⟨23392848285555954791018675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 249523715045930184437532533 23392848285555954791018675)
                ·
                  refine ⟨35089272428333932186528013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23392848285555954791018675 35089272428333932186528013)
                  ·
                    refine ⟨13158477160625224569948005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 35089272428333932186528013 13158477160625224569948005)
                    ·
                      refine ⟨2467214467617229606865251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13158477160625224569948005 2467214467617229606865251)
                      ·
                        rfl

theorem cell23_4804883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 5, 1, 3, 4].length) (baseStart_4804883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4804883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4804883 prefixEnd_4804883 := by exact prefixLift 4804883
  have htrace : WordTrace (prefixWord ++ tailWord_4804883) baseStart_4804883 baseEnd_4804883 := by
    simpa [prefixWord, tailWord_4804883, baseEnd_4804883] using wordTrace_append hprefix tailTrace_4804883
  have hstable : (prefixWord ++ tailWord_4804883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4804883).length < 2 ^ (prefixWord ++ tailWord_4804883).sum := by decide
  have hdescent : baseEnd_4804883 < baseStart_4804883 := by decide
  rcases family_descends (prefixWord ++ tailWord_4804883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4804901 : List Nat := [1, 3, 1, 2, 6, 1, 2, 2, 5]
def baseStart_4804901 : Nat := 118140960795 + 4804901 * 2 ^ 59
def prefixEnd_4804901 : Nat := 4983230072969 + 3 ^ 40 * 4804901 * 2
def baseEnd_4804901 : Nat := 274135967807667837382241

theorem tailTrace_4804901 : CollatzResearch.WordTrace tailWord_4804901 prefixEnd_4804901 274135967807667837382241 := by
  unfold tailWord_4804901
  simp only [CollatzResearch.WordTrace]
  refine ⟨175249136765671763603670557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116832757843781175735780371 175249136765671763603670557)
  ·
    refine ⟨65718426287126911351376459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 175249136765671763603670557 65718426287126911351376459)
    ·
      refine ⟨98577639430690367027064689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65718426287126911351376459 98577639430690367027064689)
      ·
        refine ⟨73933229573017775270298517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 98577639430690367027064689 73933229573017775270298517)
        ·
          refine ⟨3465620136235208215795243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 73933229573017775270298517 3465620136235208215795243)
          ·
            refine ⟨5198430204352812323692865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3465620136235208215795243 5198430204352812323692865)
            ·
              refine ⟨3898822653264609242769649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5198430204352812323692865 3898822653264609242769649)
              ·
                refine ⟨2924116989948456932077237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3898822653264609242769649 2924116989948456932077237)
                ·
                  refine ⟨274135967807667837382241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2924116989948456932077237 274135967807667837382241)
                  ·
                    rfl

theorem cell23_4804901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 6, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 6, 1, 2, 2, 5].length) (baseStart_4804901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4804901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4804901 prefixEnd_4804901 := by exact prefixLift 4804901
  have htrace : WordTrace (prefixWord ++ tailWord_4804901) baseStart_4804901 baseEnd_4804901 := by
    simpa [prefixWord, tailWord_4804901, baseEnd_4804901] using wordTrace_append hprefix tailTrace_4804901
  have hstable : (prefixWord ++ tailWord_4804901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4804901).length < 2 ^ (prefixWord ++ tailWord_4804901).sum := by decide
  have hdescent : baseEnd_4804901 < baseStart_4804901 := by decide
  rcases family_descends (prefixWord ++ tailWord_4804901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4804917 : List Nat := [1, 3, 3, 1, 2, 1, 3, 1, 2, 4, 2]
def baseStart_4804917 : Nat := 118140960795 + 4804917 * 2 ^ 59
def prefixEnd_4804917 : Nat := 4983230072969 + 3 ^ 40 * 4804917 * 2
def baseEnd_4804917 : Nat := 2467231925959482473840095

theorem tailTrace_4804917 : CollatzResearch.WordTrace tailWord_4804917 prefixEnd_4804917 2467231925959482473840095 := by
  unfold tailWord_4804917
  simp only [CollatzResearch.WordTrace]
  refine ⟨175249720333613798336253005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116833146889075865557502003 175249720333613798336253005)
  ·
    refine ⟨65718645125105174376094877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 175249720333613798336253005 65718645125105174376094877)
    ·
      refine ⟨24644491921914440391035579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65718645125105174376094877 24644491921914440391035579)
      ·
        refine ⟨36966737882871660586553369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24644491921914440391035579 36966737882871660586553369)
        ·
          refine ⟨27725053412153745439915027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36966737882871660586553369 27725053412153745439915027)
          ·
            refine ⟨41587580118230618159872541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27725053412153745439915027 41587580118230618159872541)
            ·
              refine ⟨15595342544336481809952203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41587580118230618159872541 15595342544336481809952203)
              ·
                refine ⟨23393013816504722714928305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15595342544336481809952203 23393013816504722714928305)
                ·
                  refine ⟨17544760362378542036196229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23393013816504722714928305 17544760362378542036196229)
                  ·
                    refine ⟨3289642567945976631786793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17544760362378542036196229 3289642567945976631786793)
                    ·
                      refine ⟨2467231925959482473840095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3289642567945976631786793 2467231925959482473840095)
                      ·
                        rfl

theorem cell23_4804917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 3, 1, 2, 4, 2].length) (baseStart_4804917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4804917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4804917 prefixEnd_4804917 := by exact prefixLift 4804917
  have htrace : WordTrace (prefixWord ++ tailWord_4804917) baseStart_4804917 baseEnd_4804917 := by
    simpa [prefixWord, tailWord_4804917, baseEnd_4804917] using wordTrace_append hprefix tailTrace_4804917
  have hstable : (prefixWord ++ tailWord_4804917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4804917).length < 2 ^ (prefixWord ++ tailWord_4804917).sum := by decide
  have hdescent : baseEnd_4804917 < baseStart_4804917 := by decide
  rcases family_descends (prefixWord ++ tailWord_4804917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4804920 : List Nat := [2, 1, 2, 1, 3, 1, 2, 2, 4, 2, 3]
def baseStart_4804920 : Nat := 118140960795 + 4804920 * 2 ^ 59
def prefixEnd_4804920 : Nat := 4983230072969 + 3 ^ 40 * 4804920 * 2
def baseEnd_4804920 : Nat := 2467233466401445962102581

theorem tailTrace_4804920 : CollatzResearch.WordTrace tailWord_4804920 prefixEnd_4804920 2467233466401445962102581 := by
  unfold tailWord_4804920
  simp only [CollatzResearch.WordTrace]
  refine ⟨87624914876301464924306107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116833219835068619899074809 87624914876301464924306107)
  ·
    refine ⟨131437372314452197386459161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87624914876301464924306107 131437372314452197386459161)
    ·
      refine ⟨98578029235839148039844371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 131437372314452197386459161 98578029235839148039844371)
      ·
        refine ⟨147867043853758722059766557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98578029235839148039844371 147867043853758722059766557)
        ·
          refine ⟨55450141445159520772412459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 147867043853758722059766557 55450141445159520772412459)
          ·
            refine ⟨83175212167739281158618689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55450141445159520772412459 83175212167739281158618689)
            ·
              refine ⟨62381409125804460868964017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 83175212167739281158618689 62381409125804460868964017)
              ·
                refine ⟨46786056844353345651723013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 62381409125804460868964017 46786056844353345651723013)
                ·
                  refine ⟨8772385658316252309698065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 46786056844353345651723013 8772385658316252309698065)
                  ·
                    refine ⟨6579289243737189232273549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8772385658316252309698065 6579289243737189232273549)
                    ·
                      refine ⟨2467233466401445962102581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6579289243737189232273549 2467233466401445962102581)
                      ·
                        rfl

theorem cell23_4804920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 2, 4, 2, 3].length) (baseStart_4804920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4804920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4804920 prefixEnd_4804920 := by exact prefixLift 4804920
  have htrace : WordTrace (prefixWord ++ tailWord_4804920) baseStart_4804920 baseEnd_4804920 := by
    simpa [prefixWord, tailWord_4804920, baseEnd_4804920] using wordTrace_append hprefix tailTrace_4804920
  have hstable : (prefixWord ++ tailWord_4804920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4804920).length < 2 ^ (prefixWord ++ tailWord_4804920).sum := by decide
  have hdescent : baseEnd_4804920 < baseStart_4804920 := by decide
  rcases family_descends (prefixWord ++ tailWord_4804920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4804944 : List Nat := [2, 1, 1, 1, 1, 7, 2, 3, 1, 4]
def baseStart_4804944 : Nat := 118140960795 + 4804944 * 2 ^ 59
def prefixEnd_4804944 : Nat := 4983230072969 + 3 ^ 40 * 4804944 * 2
def baseEnd_4804944 : Nat := 822415263312384622734157

theorem tailTrace_4804944 : CollatzResearch.WordTrace tailWord_4804944 prefixEnd_4804944 822415263312384622734157 := by
  unfold tailWord_4804944
  simp only [CollatzResearch.WordTrace]
  refine ⟨87625352552257990973742943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116833803403010654631657257 87625352552257990973742943)
  ·
    refine ⟨131438028828386986460614415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87625352552257990973742943 131438028828386986460614415)
    ·
      refine ⟨197157043242580479690921623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131438028828386986460614415 197157043242580479690921623)
      ·
        refine ⟨295735564863870719536382435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 197157043242580479690921623 295735564863870719536382435)
        ·
          refine ⟨443603347295806079304573653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 295735564863870719536382435 443603347295806079304573653)
          ·
            refine ⟨10396953452245454983700945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 443603347295806079304573653 10396953452245454983700945)
            ·
              refine ⟨7797715089184091237775709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10396953452245454983700945 7797715089184091237775709)
              ·
                refine ⟨2924143158444034214165891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7797715089184091237775709 2924143158444034214165891)
                ·
                  refine ⟨4386214737666051321248837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2924143158444034214165891 4386214737666051321248837)
                  ·
                    refine ⟨822415263312384622734157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4386214737666051321248837 822415263312384622734157)
                    ·
                      rfl

theorem cell23_4804944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 2, 3, 1, 4].length) (baseStart_4804944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4804944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4804944 prefixEnd_4804944 := by exact prefixLift 4804944
  have htrace : WordTrace (prefixWord ++ tailWord_4804944) baseStart_4804944 baseEnd_4804944 := by
    simpa [prefixWord, tailWord_4804944, baseEnd_4804944] using wordTrace_append hprefix tailTrace_4804944
  have hstable : (prefixWord ++ tailWord_4804944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4804944).length < 2 ^ (prefixWord ++ tailWord_4804944).sum := by decide
  have hdescent : baseEnd_4804944 < baseStart_4804944 := by decide
  rcases family_descends (prefixWord ++ tailWord_4804944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4804987 : List Nat := [1, 1, 1, 1, 1, 8, 2, 2, 1, 5]
def baseStart_4804987 : Nat := 118140960795 + 4804987 * 2 ^ 59
def prefixEnd_4804987 : Nat := 4983230072969 + 3 ^ 40 * 4804987 * 2
def baseEnd_4804987 : Nat := 822422623201765733321591

theorem tailTrace_4804987 : CollatzResearch.WordTrace tailWord_4804987 prefixEnd_4804987 822422623201765733321591 := by
  unfold tailWord_4804987
  simp only [CollatzResearch.WordTrace]
  refine ⟨175252273443360200291301215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116834848962240133527534143 175252273443360200291301215)
  ·
    refine ⟨262878410165040300436951823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175252273443360200291301215 262878410165040300436951823)
    ·
      refine ⟨394317615247560450655427735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 262878410165040300436951823 394317615247560450655427735)
      ·
        refine ⟨591476422871340675983141603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 394317615247560450655427735 591476422871340675983141603)
        ·
          refine ⟨887214634307011013974712405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 591476422871340675983141603 887214634307011013974712405)
          ·
            refine ⟨10397046495785285320016161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 887214634307011013974712405 10397046495785285320016161)
            ·
              refine ⟨7797784871838963990012121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10397046495785285320016161 7797784871838963990012121)
              ·
                refine ⟨5848338653879222992509091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7797784871838963990012121 5848338653879222992509091)
                ·
                  refine ⟨8772507980818834488763637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5848338653879222992509091 8772507980818834488763637)
                  ·
                    refine ⟨822422623201765733321591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8772507980818834488763637 822422623201765733321591)
                    ·
                      rfl

theorem cell23_4804987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 2, 2, 1, 5].length) (baseStart_4804987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4804987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4804987 prefixEnd_4804987 := by exact prefixLift 4804987
  have htrace : WordTrace (prefixWord ++ tailWord_4804987) baseStart_4804987 baseEnd_4804987 := by
    simpa [prefixWord, tailWord_4804987, baseEnd_4804987] using wordTrace_append hprefix tailTrace_4804987
  have hstable : (prefixWord ++ tailWord_4804987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4804987).length < 2 ^ (prefixWord ++ tailWord_4804987).sum := by decide
  have hdescent : baseEnd_4804987 < baseStart_4804987 := by decide
  rcases family_descends (prefixWord ++ tailWord_4804987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4805000 : List Nat := [2, 1, 3, 3, 1, 1, 2, 1, 3, 6]
def baseStart_4805000 : Nat := 118140960795 + 4805000 * 2 ^ 59
def prefixEnd_4805000 : Nat := 4983230072969 + 3 ^ 40 * 4805000 * 2
def baseEnd_4805000 : Nat := 822424848284601883034071

theorem tailTrace_4805000 : CollatzResearch.WordTrace tailWord_4805000 prefixEnd_4805000 822424848284601883034071 := by
  unfold tailWord_4805000
  simp only [CollatzResearch.WordTrace]
  refine ⟨87626373796156551755762227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116835165061542069007682969 87626373796156551755762227)
  ·
    refine ⟨131439560694234827633643341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87626373796156551755762227 131439560694234827633643341)
    ·
      refine ⟨49289835260338060362616253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 131439560694234827633643341 49289835260338060362616253)
      ·
        refine ⟨18483688222626772635981095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49289835260338060362616253 18483688222626772635981095)
        ·
          refine ⟨27725532333940158953971643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18483688222626772635981095 27725532333940158953971643)
          ·
            refine ⟨41588298500910238430957465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27725532333940158953971643 41588298500910238430957465)
            ·
              refine ⟨31191223875682678823218099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41588298500910238430957465 31191223875682678823218099)
              ·
                refine ⟨46786835813524018234827149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31191223875682678823218099 46786835813524018234827149)
                ·
                  refine ⟨17545063430071506838060181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 46786835813524018234827149 17545063430071506838060181)
                  ·
                    refine ⟨822424848284601883034071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17545063430071506838060181 822424848284601883034071)
                    ·
                      rfl

theorem cell23_4805000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 2, 1, 3, 6].length) (baseStart_4805000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4805000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4805000 prefixEnd_4805000 := by exact prefixLift 4805000
  have htrace : WordTrace (prefixWord ++ tailWord_4805000) baseStart_4805000 baseEnd_4805000 := by
    simpa [prefixWord, tailWord_4805000, baseEnd_4805000] using wordTrace_append hprefix tailTrace_4805000
  have hstable : (prefixWord ++ tailWord_4805000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4805000).length < 2 ^ (prefixWord ++ tailWord_4805000).sum := by decide
  have hdescent : baseEnd_4805000 < baseStart_4805000 := by decide
  rcases family_descends (prefixWord ++ tailWord_4805000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4805001 : List Nat := [1, 2, 1, 1, 6, 1, 3, 3, 1, 1, 3]
def baseStart_4805001 : Nat := 118140960795 + 4805001 * 2 ^ 59
def prefixEnd_4805001 : Nat := 4983230072969 + 3 ^ 40 * 4805001 * 2
def baseEnd_4805001 : Nat := 2467275058334460145189709

theorem tailTrace_4805001 : CollatzResearch.WordTrace tailWord_4805001 prefixEnd_4805001 2467275058334460145189709 := by
  unfold tailWord_4805001
  simp only [CollatzResearch.WordTrace]
  refine ⟨175252784065309480682310857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116835189376872987121540571 175252784065309480682310857)
  ·
    refine ⟨131439588048982110511733143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 175252784065309480682310857 131439588048982110511733143)
    ·
      refine ⟨197159382073473165767599715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131439588048982110511733143 197159382073473165767599715)
      ·
        refine ⟨295739073110209748651399573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 197159382073473165767599715 295739073110209748651399573)
        ·
          refine ⟨13862769052041081968034355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 295739073110209748651399573 13862769052041081968034355)
          ·
            refine ⟨20794153578061622952051533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13862769052041081968034355 20794153578061622952051533)
            ·
              refine ⟨7797807591773108607019325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20794153578061622952051533 7797807591773108607019325)
              ·
                refine ⟨2924177846914915727632247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7797807591773108607019325 2924177846914915727632247)
                ·
                  refine ⟨4386266770372373591448371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2924177846914915727632247 4386266770372373591448371)
                  ·
                    refine ⟨6579400155558560387172557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4386266770372373591448371 6579400155558560387172557)
                    ·
                      refine ⟨2467275058334460145189709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6579400155558560387172557 2467275058334460145189709)
                      ·
                        rfl

theorem cell23_4805001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 3, 3, 1, 1, 3].length) (baseStart_4805001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4805001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4805001 prefixEnd_4805001 := by exact prefixLift 4805001
  have htrace : WordTrace (prefixWord ++ tailWord_4805001) baseStart_4805001 baseEnd_4805001 := by
    simpa [prefixWord, tailWord_4805001, baseEnd_4805001] using wordTrace_append hprefix tailTrace_4805001
  have hstable : (prefixWord ++ tailWord_4805001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4805001).length < 2 ^ (prefixWord ++ tailWord_4805001).sum := by decide
  have hdescent : baseEnd_4805001 < baseStart_4805001 := by decide
  rcases family_descends (prefixWord ++ tailWord_4805001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4805017 : List Nat := [1, 2, 1, 2, 1, 4, 2, 4, 2, 4]
def baseStart_4805017 : Nat := 118140960795 + 4805017 * 2 ^ 59
def prefixEnd_4805017 : Nat := 4983230072969 + 3 ^ 40 * 4805017 * 2
def baseEnd_4805017 : Nat := 822427758008310694196545

theorem tailTrace_4805017 : CollatzResearch.WordTrace tailWord_4805017 prefixEnd_4805017 822427758008310694196545 := by
  unfold tailWord_4805017
  simp only [CollatzResearch.WordTrace]
  refine ⟨175253367633251515414893305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116835578422167676943262203 175253367633251515414893305)
  ·
    refine ⟨131440025724938636561169979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 175253367633251515414893305 131440025724938636561169979)
    ·
      refine ⟨197160038587407954841754969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131440025724938636561169979 197160038587407954841754969)
      ·
        refine ⟨147870028940555966131316227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 197160038587407954841754969 147870028940555966131316227)
        ·
          refine ⟨221805043410833949196974341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 147870028940555966131316227 221805043410833949196974341)
          ·
            refine ⟨41588445639531365474432689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 221805043410833949196974341 41588445639531365474432689)
            ·
              refine ⟨31191334229648524105824517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41588445639531365474432689 31191334229648524105824517)
              ·
                refine ⟨5848375168059098269842097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31191334229648524105824517 5848375168059098269842097)
                ·
                  refine ⟨4386281376044323702381573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5848375168059098269842097 4386281376044323702381573)
                  ·
                    refine ⟨822427758008310694196545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4386281376044323702381573 822427758008310694196545)
                    ·
                      rfl

theorem cell23_4805017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 2, 4, 2, 4].length) (baseStart_4805017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4805017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4805017 prefixEnd_4805017 := by exact prefixLift 4805017
  have htrace : WordTrace (prefixWord ++ tailWord_4805017) baseStart_4805017 baseEnd_4805017 := by
    simpa [prefixWord, tailWord_4805017, baseEnd_4805017] using wordTrace_append hprefix tailTrace_4805017
  have hstable : (prefixWord ++ tailWord_4805017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4805017).length < 2 ^ (prefixWord ++ tailWord_4805017).sum := by decide
  have hdescent : baseEnd_4805017 < baseStart_4805017 := by decide
  rcases family_descends (prefixWord ++ tailWord_4805017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4805018 : List Nat := [3, 1, 1, 4, 1, 3, 3, 2, 1, 1, 3]
def baseStart_4805018 : Nat := 118140960795 + 4805018 * 2 ^ 59
def prefixEnd_4805018 : Nat := 4983230072969 + 3 ^ 40 * 4805018 * 2
def baseEnd_4805018 : Nat := 2467283787505586578677131

theorem tailTrace_4805018 : CollatzResearch.WordTrace tailWord_4805018 prefixEnd_4805018 2467283787505586578677131 := by
  unfold tailWord_4805018
  simp only [CollatzResearch.WordTrace]
  refine ⟨43813351026561973146419927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 116835602737498595057119805 43813351026561973146419927)
  ·
    refine ⟨65720026539842959719629891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43813351026561973146419927 65720026539842959719629891)
    ·
      refine ⟨98580039809764439579444837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65720026539842959719629891 98580039809764439579444837)
      ·
        refine ⟨18483757464330832421145907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 98580039809764439579444837 18483757464330832421145907)
        ·
          refine ⟨27725636196496248631718861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18483757464330832421145907 27725636196496248631718861)
          ·
            refine ⟨10397113573686093236894573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27725636196496248631718861 10397113573686093236894573)
            ·
              refine ⟨3898917590132284963835465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10397113573686093236894573 3898917590132284963835465)
              ·
                refine ⟨2924188192599213722876599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3898917590132284963835465 2924188192599213722876599)
                ·
                  refine ⟨4386282288898820584314899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2924188192599213722876599 4386282288898820584314899)
                  ·
                    refine ⟨6579423433348230876472349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4386282288898820584314899 6579423433348230876472349)
                    ·
                      refine ⟨2467283787505586578677131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6579423433348230876472349 2467283787505586578677131)
                      ·
                        rfl

theorem cell23_4805018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 3, 2, 1, 1, 3].length) (baseStart_4805018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4805018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4805018 prefixEnd_4805018 := by exact prefixLift 4805018
  have htrace : WordTrace (prefixWord ++ tailWord_4805018) baseStart_4805018 baseEnd_4805018 := by
    simpa [prefixWord, tailWord_4805018, baseEnd_4805018] using wordTrace_append hprefix tailTrace_4805018
  have hstable : (prefixWord ++ tailWord_4805018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4805018).length < 2 ^ (prefixWord ++ tailWord_4805018).sum := by decide
  have hdescent : baseEnd_4805018 < baseStart_4805018 := by decide
  rcases family_descends (prefixWord ++ tailWord_4805018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4805101 : List Nat := [1, 5, 1, 3, 1, 1, 2, 1, 3, 3, 2]
def baseStart_4805101 : Nat := 118140960795 + 4805101 * 2 ^ 59
def prefixEnd_4805101 : Nat := 4983230072969 + 3 ^ 40 * 4805101 * 2
def baseEnd_4805101 : Nat := 2467326406399909753939249

theorem tailTrace_4805101 : CollatzResearch.WordTrace tailWord_4805101 prefixEnd_4805101 2467326406399909753939249 := by
  unfold tailWord_4805101
  simp only [CollatzResearch.WordTrace]
  refine ⟨175256431364947197760951157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116837620909964798507300771 175256431364947197760951157)
  ·
    refine ⟨16430290440463799790089171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 175256431364947197760951157 16430290440463799790089171)
    ·
      refine ⟨24645435660695699685133757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16430290440463799790089171 24645435660695699685133757)
      ·
        refine ⟨9242038372760887381925159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24645435660695699685133757 9242038372760887381925159)
        ·
          refine ⟨13863057559141331072887739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9242038372760887381925159 13863057559141331072887739)
          ·
            refine ⟨20794586338711996609331609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13863057559141331072887739 20794586338711996609331609)
            ·
              refine ⟨15595939754033997456998707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20794586338711996609331609 15595939754033997456998707)
              ·
                refine ⟨23393909631050996185498061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15595939754033997456998707 23393909631050996185498061)
                ·
                  refine ⟨8772716111644123569561773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23393909631050996185498061 8772716111644123569561773)
                  ·
                    refine ⟨3289768541866546338585665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8772716111644123569561773 3289768541866546338585665)
                    ·
                      refine ⟨2467326406399909753939249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3289768541866546338585665 2467326406399909753939249)
                      ·
                        rfl

theorem cell23_4805101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 2, 1, 3, 3, 2].length) (baseStart_4805101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4805101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4805101 prefixEnd_4805101 := by exact prefixLift 4805101
  have htrace : WordTrace (prefixWord ++ tailWord_4805101) baseStart_4805101 baseEnd_4805101 := by
    simpa [prefixWord, tailWord_4805101, baseEnd_4805101] using wordTrace_append hprefix tailTrace_4805101
  have hstable : (prefixWord ++ tailWord_4805101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4805101).length < 2 ^ (prefixWord ++ tailWord_4805101).sum := by decide
  have hdescent : baseEnd_4805101 < baseStart_4805101 := by decide
  rcases family_descends (prefixWord ++ tailWord_4805101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4805131 : List Nat := [1, 1, 1, 1, 7, 2, 1, 1, 4, 2, 2]
def baseStart_4805131 : Nat := 118140960795 + 4805131 * 2 ^ 59
def prefixEnd_4805131 : Nat := 4983230072969 + 3 ^ 40 * 4805131 * 2
def baseEnd_4805131 : Nat := 2467341810819544636564111

theorem tailTrace_4805131 : CollatzResearch.WordTrace tailWord_4805131 prefixEnd_4805131 2467341810819544636564111 := by
  unfold tailWord_4805131
  simp only [CollatzResearch.WordTrace]
  refine ⟨175257525554838512884543247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116838350369892341923028831 175257525554838512884543247)
  ·
    refine ⟨262886288332257769326814871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175257525554838512884543247 262886288332257769326814871)
    ·
      refine ⟨394329432498386653990222307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 262886288332257769326814871 394329432498386653990222307)
      ·
        refine ⟨591494148747579980985333461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 394329432498386653990222307 591494148747579980985333461)
        ·
          refine ⟨13863144111271405804343753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 591494148747579980985333461 13863144111271405804343753)
          ·
            refine ⟨10397358083453554353257815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13863144111271405804343753 10397358083453554353257815)
            ·
              refine ⟨15596037125180331529886723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10397358083453554353257815 15596037125180331529886723)
              ·
                refine ⟨23394055687770497294830085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15596037125180331529886723 23394055687770497294830085)
                ·
                  refine ⟨4386385441456968242780641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23394055687770497294830085 4386385441456968242780641)
                  ·
                    refine ⟨3289789081092726182085481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4386385441456968242780641 3289789081092726182085481)
                    ·
                      refine ⟨2467341810819544636564111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3289789081092726182085481 2467341810819544636564111)
                      ·
                        rfl

theorem cell23_4805131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 1, 1, 4, 2, 2].length) (baseStart_4805131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4805131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4805131 prefixEnd_4805131 := by exact prefixLift 4805131
  have htrace : WordTrace (prefixWord ++ tailWord_4805131) baseStart_4805131 baseEnd_4805131 := by
    simpa [prefixWord, tailWord_4805131, baseEnd_4805131] using wordTrace_append hprefix tailTrace_4805131
  have hstable : (prefixWord ++ tailWord_4805131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4805131).length < 2 ^ (prefixWord ++ tailWord_4805131).sum := by decide
  have hdescent : baseEnd_4805131 < baseStart_4805131 := by decide
  rcases family_descends (prefixWord ++ tailWord_4805131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4805177 : List Nat := [1, 2, 1, 5, 1, 1, 2, 2, 1, 2, 5]
def baseStart_4805177 : Nat := 118140960795 + 4805177 * 2 ^ 59
def prefixEnd_4805177 : Nat := 4983230072969 + 3 ^ 40 * 4805177 * 2
def baseEnd_4805177 : Nat := 2467365430929651456588899

theorem tailTrace_4805177 : CollatzResearch.WordTrace tailWord_4805177 prefixEnd_4805177 2467365430929651456588899 := by
  unfold tailWord_4805177
  simp only [CollatzResearch.WordTrace]
  refine ⟨175259203312671862740717785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116839468875114575160478523 175259203312671862740717785)
  ·
    refine ⟨131444402484503897055538339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 175259203312671862740717785 131444402484503897055538339)
    ·
      refine ⟨197166603726755845583307509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131444402484503897055538339 197166603726755845583307509)
      ·
        refine ⟨18484369099383360523435079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 197166603726755845583307509 18484369099383360523435079)
        ·
          refine ⟨27726553649075040785152619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18484369099383360523435079 27726553649075040785152619)
          ·
            refine ⟨41589830473612561177728929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27726553649075040785152619 41589830473612561177728929)
            ·
              refine ⟨31192372855209420883296697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41589830473612561177728929 31192372855209420883296697)
              ·
                refine ⟨23394279641407065662472523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31192372855209420883296697 23394279641407065662472523)
                ·
                  refine ⟨35091419462110598493708785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23394279641407065662472523 35091419462110598493708785)
                  ·
                    refine ⟨26318564596582948870281589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 35091419462110598493708785 26318564596582948870281589)
                    ·
                      refine ⟨2467365430929651456588899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26318564596582948870281589 2467365430929651456588899)
                      ·
                        rfl

theorem cell23_4805177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 2, 2, 1, 2, 5].length) (baseStart_4805177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4805177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4805177 prefixEnd_4805177 := by exact prefixLift 4805177
  have htrace : WordTrace (prefixWord ++ tailWord_4805177) baseStart_4805177 baseEnd_4805177 := by
    simpa [prefixWord, tailWord_4805177, baseEnd_4805177] using wordTrace_append hprefix tailTrace_4805177
  have hstable : (prefixWord ++ tailWord_4805177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4805177).length < 2 ^ (prefixWord ++ tailWord_4805177).sum := by decide
  have hdescent : baseEnd_4805177 < baseStart_4805177 := by decide
  rcases family_descends (prefixWord ++ tailWord_4805177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4805218 : List Nat := [3, 3, 2, 3, 1, 1, 2, 1, 2, 5]
def baseStart_4805218 : Nat := 118140960795 + 4805218 * 2 ^ 59
def prefixEnd_4805218 : Nat := 4983230072969 + 3 ^ 40 * 4805218 * 2
def baseEnd_4805218 : Nat := 822462161212161932058737

theorem tailTrace_4805218 : CollatzResearch.WordTrace tailWord_4805218 prefixEnd_4805218 822462161212161932058737 := by
  unfold tailWord_4805218
  simp only [CollatzResearch.WordTrace]
  refine ⟨43815174676380831685740077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 116840465803682217828640205 43815174676380831685740077)
  ·
    refine ⟨16430690503642811882152529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43815174676380831685740077 16430690503642811882152529)
    ·
      refine ⟨12323017877732108911614397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16430690503642811882152529 12323017877732108911614397)
      ·
        refine ⟨4621131704149540841855399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12323017877732108911614397 4621131704149540841855399)
        ·
          refine ⟨6931697556224311262783099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4621131704149540841855399 6931697556224311262783099)
          ·
            refine ⟨10397546334336466894174649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6931697556224311262783099 10397546334336466894174649)
            ·
              refine ⟨7798159750752350170630987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10397546334336466894174649 7798159750752350170630987)
              ·
                refine ⟨11697239626128525255946481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7798159750752350170630987 11697239626128525255946481)
                ·
                  refine ⟨8772929719596393941959861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11697239626128525255946481 8772929719596393941959861)
                  ·
                    refine ⟨822462161212161932058737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8772929719596393941959861 822462161212161932058737)
                    ·
                      rfl

theorem cell23_4805218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 2, 1, 2, 5].length) (baseStart_4805218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4805218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4805218 prefixEnd_4805218 := by exact prefixLift 4805218
  have htrace : WordTrace (prefixWord ++ tailWord_4805218) baseStart_4805218 baseEnd_4805218 := by
    simpa [prefixWord, tailWord_4805218, baseEnd_4805218] using wordTrace_append hprefix tailTrace_4805218
  have hstable : (prefixWord ++ tailWord_4805218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4805218).length < 2 ^ (prefixWord ++ tailWord_4805218).sum := by decide
  have hdescent : baseEnd_4805218 < baseStart_4805218 := by decide
  rcases family_descends (prefixWord ++ tailWord_4805218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4805221 : List Nat := [1, 3, 1, 3, 4, 1, 2, 1, 2, 1, 4]
def baseStart_4805221 : Nat := 118140960795 + 4805221 * 2 ^ 59
def prefixEnd_4805221 : Nat := 4983230072969 + 3 ^ 40 * 4805221 * 2
def baseEnd_4805221 : Nat := 2467388024078449284438697

theorem tailTrace_4805221 : CollatzResearch.WordTrace tailWord_4805221 prefixEnd_4805221 2467388024078449284438697 := by
  unfold tailWord_4805221
  simp only [CollatzResearch.WordTrace]
  refine ⟨175260808124512458255319517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116840538749674972170213011 175260808124512458255319517)
  ·
    refine ⟨65722803046692171845744819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 175260808124512458255319517 65722803046692171845744819)
    ·
      refine ⟨98584204570038257768617229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65722803046692171845744819 98584204570038257768617229)
      ·
        refine ⟨36969076713764346663231461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 98584204570038257768617229 36969076713764346663231461)
        ·
          refine ⟨6931701883830814999355899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 36969076713764346663231461 6931701883830814999355899)
          ·
            refine ⟨10397552825746222499033849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6931701883830814999355899 10397552825746222499033849)
            ·
              refine ⟨7798164619309666874275387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10397552825746222499033849 7798164619309666874275387)
              ·
                refine ⟨11697246928964500311413081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7798164619309666874275387 11697246928964500311413081)
                ·
                  refine ⟨8772935196723375233559811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11697246928964500311413081 8772935196723375233559811)
                  ·
                    refine ⟨13159402795085062850339717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8772935196723375233559811 13159402795085062850339717)
                    ·
                      refine ⟨2467388024078449284438697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13159402795085062850339717 2467388024078449284438697)
                      ·
                        rfl

theorem cell23_4805221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 2, 1, 2, 1, 4].length) (baseStart_4805221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4805221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4805221 prefixEnd_4805221 := by exact prefixLift 4805221
  have htrace : WordTrace (prefixWord ++ tailWord_4805221) baseStart_4805221 baseEnd_4805221 := by
    simpa [prefixWord, tailWord_4805221, baseEnd_4805221] using wordTrace_append hprefix tailTrace_4805221
  have hstable : (prefixWord ++ tailWord_4805221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4805221).length < 2 ^ (prefixWord ++ tailWord_4805221).sum := by decide
  have hdescent : baseEnd_4805221 < baseStart_4805221 := by decide
  rcases family_descends (prefixWord ++ tailWord_4805221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4805248 : List Nat := [2, 1, 1, 2, 1, 5, 4, 2, 1, 4]
def baseStart_4805248 : Nat := 118140960795 + 4805248 * 2 ^ 59
def prefixEnd_4805248 : Nat := 4983230072969 + 3 ^ 40 * 4805248 * 2
def baseEnd_4805248 : Nat := 822467296018706892933691

theorem tailTrace_4805248 : CollatzResearch.WordTrace tailWord_4805248 prefixEnd_4805248 822467296018706892933691 := by
  unfold tailWord_4805248
  simp only [CollatzResearch.WordTrace]
  refine ⟨87630896447707320933276199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116841195263609761244368265 87630896447707320933276199)
  ·
    refine ⟨131446344671560981399914299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87630896447707320933276199 131446344671560981399914299)
    ·
      refine ⟨197169517007341472099871449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131446344671560981399914299 197169517007341472099871449)
      ·
        refine ⟨147877137755506104074903587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 197169517007341472099871449 147877137755506104074903587)
        ·
          refine ⟨221815706633259156112355381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 147877137755506104074903587 221815706633259156112355381)
          ·
            refine ⟨20795222496868045885533317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 221815706633259156112355381 20795222496868045885533317)
            ·
              refine ⟨3899104218162758603537497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20795222496868045885533317 3899104218162758603537497)
              ·
                refine ⟨2924328163622068952653123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3899104218162758603537497 2924328163622068952653123)
                ·
                  refine ⟨4386492245433103428979685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2924328163622068952653123 4386492245433103428979685)
                  ·
                    refine ⟨822467296018706892933691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4386492245433103428979685 822467296018706892933691)
                    ·
                      rfl

theorem cell23_4805248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 4, 2, 1, 4].length) (baseStart_4805248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4805248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4805248 prefixEnd_4805248 := by exact prefixLift 4805248
  have htrace : WordTrace (prefixWord ++ tailWord_4805248) baseStart_4805248 baseEnd_4805248 := by
    simpa [prefixWord, tailWord_4805248, baseEnd_4805248] using wordTrace_append hprefix tailTrace_4805248
  have hstable : (prefixWord ++ tailWord_4805248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4805248).length < 2 ^ (prefixWord ++ tailWord_4805248).sum := by decide
  have hdescent : baseEnd_4805248 < baseStart_4805248 := by decide
  rcases family_descends (prefixWord ++ tailWord_4805248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4805271 : List Nat := [1, 1, 3, 3, 2, 1, 3, 2, 3, 1, 3]
def baseStart_4805271 : Nat := 118140960795 + 4805271 * 2 ^ 59
def prefixEnd_4805271 : Nat := 4983230072969 + 3 ^ 40 * 4805271 * 2
def baseEnd_4805271 : Nat := 2467413698111174088813467

theorem tailTrace_4805271 : CollatzResearch.WordTrace tailWord_4805271 prefixEnd_4805271 2467413698111174088813467 := by
  unfold tailWord_4805271
  simp only [CollatzResearch.WordTrace]
  refine ⟨175262631774331316794639667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116841754516220877863093111 175262631774331316794639667)
  ·
    refine ⟨262893947661496975191959501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175262631774331316794639667 262893947661496975191959501)
    ·
      refine ⟨98585230373061365696984813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 262893947661496975191959501 98585230373061365696984813)
      ·
        refine ⟨36969461389898012136369305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 98585230373061365696984813 36969461389898012136369305)
        ·
          refine ⟨27727096042423509102276979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36969461389898012136369305 27727096042423509102276979)
          ·
            refine ⟨41590644063635263653415469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27727096042423509102276979 41590644063635263653415469)
            ·
              refine ⟨15596491523863223870030801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41590644063635263653415469 15596491523863223870030801)
              ·
                refine ⟨11697368642897417902523101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15596491523863223870030801 11697368642897417902523101)
                ·
                  refine ⟨4386513241086531713446163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11697368642897417902523101 4386513241086531713446163)
                  ·
                    refine ⟨6579769861629797570169245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4386513241086531713446163 6579769861629797570169245)
                    ·
                      refine ⟨2467413698111174088813467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6579769861629797570169245 2467413698111174088813467)
                      ·
                        rfl

theorem cell23_4805271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 3, 2, 3, 1, 3].length) (baseStart_4805271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4805271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4805271 prefixEnd_4805271 := by exact prefixLift 4805271
  have htrace : WordTrace (prefixWord ++ tailWord_4805271) baseStart_4805271 baseEnd_4805271 := by
    simpa [prefixWord, tailWord_4805271, baseEnd_4805271] using wordTrace_append hprefix tailTrace_4805271
  have hstable : (prefixWord ++ tailWord_4805271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4805271).length < 2 ^ (prefixWord ++ tailWord_4805271).sum := by decide
  have hdescent : baseEnd_4805271 < baseStart_4805271 := by decide
  rcases family_descends (prefixWord ++ tailWord_4805271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4805307 : List Nat := [1, 1, 1, 1, 1, 2, 3, 1, 2, 6, 4]
def baseStart_4805307 : Nat := 118140960795 + 4805307 * 2 ^ 59
def prefixEnd_4805307 : Nat := 4983230072969 + 3 ^ 40 * 4805307 * 2
def baseEnd_4805307 : Nat := 2467432183414735947963301

theorem tailTrace_4805307 : CollatzResearch.WordTrace tailWord_4805307 prefixEnd_4805307 2467432183414735947963301 := by
  unfold tailWord_4805307
  simp only [CollatzResearch.WordTrace]
  refine ⟨175263944802200894942950175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116842629868133929961966783 175263944802200894942950175)
  ·
    refine ⟨262895917203301342414425263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175263944802200894942950175 262895917203301342414425263)
    ·
      refine ⟨394343875804952013621637895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 262895917203301342414425263 394343875804952013621637895)
      ·
        refine ⟨591515813707428020432456843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 394343875804952013621637895 591515813707428020432456843)
        ·
          refine ⟨887273720561142030648685265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 591515813707428020432456843 887273720561142030648685265)
          ·
            refine ⟨665455290420856522986513949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 887273720561142030648685265 665455290420856522986513949)
            ·
              refine ⟨249545733907821196119942731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 665455290420856522986513949 249545733907821196119942731)
              ·
                refine ⟨374318600861731794179914097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 249545733907821196119942731 374318600861731794179914097)
                ·
                  refine ⟨280738950646298845634935573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 374318600861731794179914097 280738950646298845634935573)
                  ·
                    refine ⟨13159638311545258389137605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 280738950646298845634935573 13159638311545258389137605)
                    ·
                      refine ⟨2467432183414735947963301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13159638311545258389137605 2467432183414735947963301)
                      ·
                        rfl

theorem cell23_4805307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 1, 2, 6, 4].length) (baseStart_4805307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4805307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4805307 prefixEnd_4805307 := by exact prefixLift 4805307
  have htrace : WordTrace (prefixWord ++ tailWord_4805307) baseStart_4805307 baseEnd_4805307 := by
    simpa [prefixWord, tailWord_4805307, baseEnd_4805307] using wordTrace_append hprefix tailTrace_4805307
  have hstable : (prefixWord ++ tailWord_4805307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4805307).length < 2 ^ (prefixWord ++ tailWord_4805307).sum := by decide
  have hdescent : baseEnd_4805307 < baseStart_4805307 := by decide
  rcases family_descends (prefixWord ++ tailWord_4805307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4805325 : List Nat := [1, 6, 2, 1, 2, 1, 2, 2, 1, 5]
def baseStart_4805325 : Nat := 118140960795 + 4805325 * 2 ^ 59
def prefixEnd_4805325 : Nat := 4983230072969 + 3 ^ 40 * 4805325 * 2
def baseEnd_4805325 : Nat := 822480475355505625846073

theorem tailTrace_4805325 : CollatzResearch.WordTrace tailWord_4805325 prefixEnd_4805325 822480475355505625846073 := by
  unfold tailWord_4805325
  simp only [CollatzResearch.WordTrace]
  refine ⟨175264601316135684017105429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116843067544090456011403619 175264601316135684017105429)
  ·
    refine ⟨8215528186693860188301817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 175264601316135684017105429 8215528186693860188301817)
    ·
      refine ⟨6161646140020395141226363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8215528186693860188301817 6161646140020395141226363)
      ·
        refine ⟨9242469210030592711839545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6161646140020395141226363 9242469210030592711839545)
        ·
          refine ⟨6931851907522944533879659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9242469210030592711839545 6931851907522944533879659)
          ·
            refine ⟨10397777861284416800819489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6931851907522944533879659 10397777861284416800819489)
            ·
              refine ⟨7798333395963312600614617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10397777861284416800819489 7798333395963312600614617)
              ·
                refine ⟨5848750046972484450460963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7798333395963312600614617 5848750046972484450460963)
                ·
                  refine ⟨8773125070458726675691445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5848750046972484450460963 8773125070458726675691445)
                  ·
                    refine ⟨822480475355505625846073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8773125070458726675691445 822480475355505625846073)
                    ·
                      rfl

theorem cell23_4805325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 2, 2, 1, 5].length) (baseStart_4805325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4805325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4805325 prefixEnd_4805325 := by exact prefixLift 4805325
  have htrace : WordTrace (prefixWord ++ tailWord_4805325) baseStart_4805325 baseEnd_4805325 := by
    simpa [prefixWord, tailWord_4805325, baseEnd_4805325] using wordTrace_append hprefix tailTrace_4805325
  have hstable : (prefixWord ++ tailWord_4805325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4805325).length < 2 ^ (prefixWord ++ tailWord_4805325).sum := by decide
  have hdescent : baseEnd_4805325 < baseStart_4805325 := by decide
  rcases family_descends (prefixWord ++ tailWord_4805325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4805344 : List Nat := [2, 1, 1, 3, 1, 2, 1, 3, 3, 3, 3]
def baseStart_4805344 : Nat := 118140960795 + 4805344 * 2 ^ 59
def prefixEnd_4805344 : Nat := 4983230072969 + 3 ^ 40 * 4805344 * 2
def baseEnd_4805344 : Nat := 2467451182198952303200631

theorem tailTrace_4805344 : CollatzResearch.WordTrace tailWord_4805344 prefixEnd_4805344 2467451182198952303200631 := by
  unfold tailWord_4805344
  simp only [CollatzResearch.WordTrace]
  refine ⟨87632647151533425131023543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116843529535377900174698057 87632647151533425131023543)
  ·
    refine ⟨131448970727300137696535315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87632647151533425131023543 131448970727300137696535315)
    ·
      refine ⟨197173456090950206544802973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131448970727300137696535315 197173456090950206544802973)
      ·
        refine ⟨73940046034106327454301115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 197173456090950206544802973 73940046034106327454301115)
        ·
          refine ⟨110910069051159491181451673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73940046034106327454301115 110910069051159491181451673)
          ·
            refine ⟨83182551788369618386088755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 110910069051159491181451673 83182551788369618386088755)
            ·
              refine ⟨124773827682554427579133133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83182551788369618386088755 124773827682554427579133133)
              ·
                refine ⟨46790185380957910342174925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 124773827682554427579133133 46790185380957910342174925)
                ·
                  refine ⟨17546319517859216378315597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 46790185380957910342174925 17546319517859216378315597)
                  ·
                    refine ⟨6579869819197206141868349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17546319517859216378315597 6579869819197206141868349)
                    ·
                      refine ⟨2467451182198952303200631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6579869819197206141868349 2467451182198952303200631)
                      ·
                        rfl

theorem cell23_4805344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 3, 3, 3, 3].length) (baseStart_4805344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4805344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4805344 prefixEnd_4805344 := by exact prefixLift 4805344
  have htrace : WordTrace (prefixWord ++ tailWord_4805344) baseStart_4805344 baseEnd_4805344 := by
    simpa [prefixWord, tailWord_4805344, baseEnd_4805344] using wordTrace_append hprefix tailTrace_4805344
  have hstable : (prefixWord ++ tailWord_4805344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4805344).length < 2 ^ (prefixWord ++ tailWord_4805344).sum := by decide
  have hdescent : baseEnd_4805344 < baseStart_4805344 := by decide
  rcases family_descends (prefixWord ++ tailWord_4805344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4805361 : List Nat := [1, 2, 2, 2, 2, 2, 1, 3, 4, 1, 3]
def baseStart_4805361 : Nat := 118140960795 + 4805361 * 2 ^ 59
def prefixEnd_4805361 : Nat := 4983230072969 + 3 ^ 40 * 4805361 * 2
def baseEnd_4805361 : Nat := 2467459911370078736688053

theorem tailTrace_4805361 : CollatzResearch.WordTrace tailWord_4805361 prefixEnd_4805361 2467459911370078736688053 := by
  unfold tailWord_4805361
  simp only [CollatzResearch.WordTrace]
  refine ⟨175265914344005262165415937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116843942896003508110277291 175265914344005262165415937)
  ·
    refine ⟨131449435758003946624061953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 175265914344005262165415937 131449435758003946624061953)
    ·
      refine ⟨98587076818502959968046465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 131449435758003946624061953 98587076818502959968046465)
      ·
        refine ⟨73940307613877219976034849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 98587076818502959968046465 73940307613877219976034849)
        ·
          refine ⟨55455230710407914982026137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73940307613877219976034849 55455230710407914982026137)
          ·
            refine ⟨41591423032805936236519603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55455230710407914982026137 41591423032805936236519603)
            ·
              refine ⟨62387134549208904354779405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41591423032805936236519603 62387134549208904354779405)
              ·
                refine ⟨23395175455953339133042277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 62387134549208904354779405 23395175455953339133042277)
                ·
                  refine ⟨4386595397991251087445427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23395175455953339133042277 4386595397991251087445427)
                  ·
                    refine ⟨6579893096986876631168141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4386595397991251087445427 6579893096986876631168141)
                    ·
                      refine ⟨2467459911370078736688053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6579893096986876631168141 2467459911370078736688053)
                      ·
                        rfl

theorem cell23_4805361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 3, 4, 1, 3].length) (baseStart_4805361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4805361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4805361 prefixEnd_4805361 := by exact prefixLift 4805361
  have htrace : WordTrace (prefixWord ++ tailWord_4805361) baseStart_4805361 baseEnd_4805361 := by
    simpa [prefixWord, tailWord_4805361, baseEnd_4805361] using wordTrace_append hprefix tailTrace_4805361
  have hstable : (prefixWord ++ tailWord_4805361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4805361).length < 2 ^ (prefixWord ++ tailWord_4805361).sum := by decide
  have hdescent : baseEnd_4805361 < baseStart_4805361 := by decide
  rcases family_descends (prefixWord ++ tailWord_4805361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4805428 : List Nat := [2, 5, 1, 1, 3, 1, 1, 1, 2, 6]
def baseStart_4805428 : Nat := 118140960795 + 4805428 * 2 ^ 59
def prefixEnd_4805428 : Nat := 4983230072969 + 3 ^ 40 * 4805428 * 2
def baseEnd_4805428 : Nat := 822498104857976658183415

theorem tailTrace_4805428 : CollatzResearch.WordTrace tailWord_4805428 prefixEnd_4805428 822498104857976658183415 := by
  unfold tailWord_4805428
  simp only [CollatzResearch.WordTrace]
  refine ⟨87634179017381266304052469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116845572023175021738736625 87634179017381266304052469)
  ·
    refine ⟨8215704282879493716004919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 87634179017381266304052469 8215704282879493716004919)
    ·
      refine ⟨12323556424319240574007379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8215704282879493716004919 12323556424319240574007379)
      ·
        refine ⟨18485334636478860861011069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12323556424319240574007379 18485334636478860861011069)
        ·
          refine ⟨6932000488679572822879151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18485334636478860861011069 6932000488679572822879151)
          ·
            refine ⟨10398000733019359234318727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6932000488679572822879151 10398000733019359234318727)
            ·
              refine ⟨15597001099529038851478091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10398000733019359234318727 15597001099529038851478091)
              ·
                refine ⟨23395501649293558277217137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15597001099529038851478091 23395501649293558277217137)
                ·
                  refine ⟨17546626236970168707912853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23395501649293558277217137 17546626236970168707912853)
                  ·
                    refine ⟨822498104857976658183415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17546626236970168707912853 822498104857976658183415)
                    ·
                      rfl

theorem cell23_4805428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 1, 1, 2, 6].length) (baseStart_4805428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4805428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4805428 prefixEnd_4805428 := by exact prefixLift 4805428
  have htrace : WordTrace (prefixWord ++ tailWord_4805428) baseStart_4805428 baseEnd_4805428 := by
    simpa [prefixWord, tailWord_4805428, baseEnd_4805428] using wordTrace_append hprefix tailTrace_4805428
  have hstable : (prefixWord ++ tailWord_4805428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4805428).length < 2 ^ (prefixWord ++ tailWord_4805428).sum := by decide
  have hdescent : baseEnd_4805428 < baseStart_4805428 := by decide
  rcases family_descends (prefixWord ++ tailWord_4805428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4805458 : List Nat := [3, 2, 2, 1, 1, 2, 4, 3, 5]
def baseStart_4805458 : Nat := 118140960795 + 4805458 * 2 ^ 59
def prefixEnd_4805458 : Nat := 4983230072969 + 3 ^ 40 * 4805458 * 2
def baseEnd_4805458 : Nat := 274167746554840539686123

theorem tailTrace_4805458 : CollatzResearch.WordTrace tailWord_4805458 prefixEnd_4805458 274167746554840539686123 := by
  unfold tailWord_4805458
  simp only [CollatzResearch.WordTrace]
  refine ⟨43817363056163461932924257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 116846301483102565154464685 43817363056163461932924257)
  ·
    refine ⟨32863022292122596449693193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43817363056163461932924257 32863022292122596449693193)
    ·
      refine ⟨24647266719091947337269895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32863022292122596449693193 24647266719091947337269895)
      ·
        refine ⟨36970900078637921005904843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24647266719091947337269895 36970900078637921005904843)
        ·
          refine ⟨55456350117956881508857265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36970900078637921005904843 55456350117956881508857265)
          ·
            refine ⟨41592262588467661131642949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55456350117956881508857265 41592262588467661131642949)
            ·
              refine ⟨7798549235337686462183053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 41592262588467661131642949 7798549235337686462183053)
              ·
                refine ⟨2924455963251632423318645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7798549235337686462183053 2924455963251632423318645)
                ·
                  refine ⟨274167746554840539686123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2924455963251632423318645 274167746554840539686123)
                  ·
                    rfl

theorem cell23_4805458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 4, 3, 5].length) (baseStart_4805458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4805458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4805458 prefixEnd_4805458 := by exact prefixLift 4805458
  have htrace : WordTrace (prefixWord ++ tailWord_4805458) baseStart_4805458 baseEnd_4805458 := by
    simpa [prefixWord, tailWord_4805458, baseEnd_4805458] using wordTrace_append hprefix tailTrace_4805458
  have hstable : (prefixWord ++ tailWord_4805458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4805458).length < 2 ^ (prefixWord ++ tailWord_4805458).sum := by decide
  have hdescent : baseEnd_4805458 < baseStart_4805458 := by decide
  rcases family_descends (prefixWord ++ tailWord_4805458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4805464 : List Nat := [2, 1, 2, 2, 1, 1, 1, 3, 3, 2, 5]
def baseStart_4805464 : Nat := 118140960795 + 4805464 * 2 ^ 59
def prefixEnd_4805464 : Nat := 4983230072969 + 3 ^ 40 * 4805464 * 2
def baseEnd_4805464 : Nat := 2467512799877491833700079

theorem tailTrace_4805464 : CollatzResearch.WordTrace tailWord_4805464 prefixEnd_4805464 2467512799877491833700079 := by
  unfold tailWord_4805464
  simp only [CollatzResearch.WordTrace]
  refine ⟨87634835531316055378207723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116846447375088073837610297 87634835531316055378207723)
  ·
    refine ⟨131452253296974083067311585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87634835531316055378207723 131452253296974083067311585)
    ·
      refine ⟨98589189972730562300483689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 131452253296974083067311585 98589189972730562300483689)
      ·
        refine ⟨73941892479547921725362767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 98589189972730562300483689 73941892479547921725362767)
        ·
          refine ⟨110912838719321882588044151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73941892479547921725362767 110912838719321882588044151)
          ·
            refine ⟨166369258078982823882066227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 110912838719321882588044151 166369258078982823882066227)
            ·
              refine ⟨249553887118474235823099341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 166369258078982823882066227 249553887118474235823099341)
              ·
                refine ⟨93582707669427838433662253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 249553887118474235823099341 93582707669427838433662253)
                ·
                  refine ⟨35093515376035439412623345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 93582707669427838433662253 35093515376035439412623345)
                  ·
                    refine ⟨26320136532026579559467509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 35093515376035439412623345 26320136532026579559467509)
                    ·
                      refine ⟨2467512799877491833700079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26320136532026579559467509 2467512799877491833700079)
                      ·
                        rfl

theorem cell23_4805464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 3, 3, 2, 5].length) (baseStart_4805464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4805464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4805464 prefixEnd_4805464 := by exact prefixLift 4805464
  have htrace : WordTrace (prefixWord ++ tailWord_4805464) baseStart_4805464 baseEnd_4805464 := by
    simpa [prefixWord, tailWord_4805464, baseEnd_4805464] using wordTrace_append hprefix tailTrace_4805464
  have hstable : (prefixWord ++ tailWord_4805464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4805464).length < 2 ^ (prefixWord ++ tailWord_4805464).sum := by decide
  have hdescent : baseEnd_4805464 < baseStart_4805464 := by decide
  rcases family_descends (prefixWord ++ tailWord_4805464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4805468 : List Nat := [2, 2, 4, 2, 1, 1, 1, 2, 2, 3, 3]
def baseStart_4805468 : Nat := 118140960795 + 4805468 * 2 ^ 59
def prefixEnd_4805468 : Nat := 4983230072969 + 3 ^ 40 * 4805468 * 2
def baseEnd_4805468 : Nat := 2467514853800109818050061

theorem tailTrace_4805468 : CollatzResearch.WordTrace tailWord_4805468 prefixEnd_4805468 2467514853800109818050061 := by
  unfold tailWord_4805468
  simp only [CollatzResearch.WordTrace]
  refine ⟨87634908477308809719780529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116846544636411746293040705 87634908477308809719780529)
  ·
    refine ⟨65726181357981607289835397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87634908477308809719780529 65726181357981607289835397)
    ·
      refine ⟨12323659004621551366844137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 65726181357981607289835397 12323659004621551366844137)
      ·
        refine ⟨9242744253466163525133103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12323659004621551366844137 9242744253466163525133103)
        ·
          refine ⟨13864116380199245287699655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9242744253466163525133103 13864116380199245287699655)
          ·
            refine ⟨20796174570298867931549483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13864116380199245287699655 20796174570298867931549483)
            ·
              refine ⟨31194261855448301897324225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20796174570298867931549483 31194261855448301897324225)
              ·
                refine ⟨23395696391586226422993169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31194261855448301897324225 23395696391586226422993169)
                ·
                  refine ⟨17546772293689669817244877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23395696391586226422993169 17546772293689669817244877)
                  ·
                    refine ⟨6580039610133626181466829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17546772293689669817244877 6580039610133626181466829)
                    ·
                      refine ⟨2467514853800109818050061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6580039610133626181466829 2467514853800109818050061)
                      ·
                        rfl

theorem cell23_4805468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 1, 2, 2, 3, 3].length) (baseStart_4805468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4805468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4805468 prefixEnd_4805468 := by exact prefixLift 4805468
  have htrace : WordTrace (prefixWord ++ tailWord_4805468) baseStart_4805468 baseEnd_4805468 := by
    simpa [prefixWord, tailWord_4805468, baseEnd_4805468] using wordTrace_append hprefix tailTrace_4805468
  have hstable : (prefixWord ++ tailWord_4805468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4805468).length < 2 ^ (prefixWord ++ tailWord_4805468).sum := by decide
  have hdescent : baseEnd_4805468 < baseStart_4805468 := by decide
  rcases family_descends (prefixWord ++ tailWord_4805468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4805504 : List Nat := [2, 1, 1, 2, 1, 2, 2, 2, 1, 3, 6]
def baseStart_4805504 : Nat := 118140960795 + 4805504 * 2 ^ 59
def prefixEnd_4805504 : Nat := 4983230072969 + 3 ^ 40 * 4805504 * 2
def baseEnd_4805504 : Nat := 2467533339103671677199895

theorem tailTrace_4805504 : CollatzResearch.WordTrace tailWord_4805504 prefixEnd_4805504 2467533339103671677199895 := by
  unfold tailWord_4805504
  simp only [CollatzResearch.WordTrace]
  refine ⟨87635564991243598793935783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116847419988324798391914377 87635564991243598793935783)
  ·
    refine ⟨131453347486865398190903675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87635564991243598793935783 131453347486865398190903675)
    ·
      refine ⟨197180021230298097286355513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131453347486865398190903675 197180021230298097286355513)
      ·
        refine ⟨147885015922723572964766635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 197180021230298097286355513 147885015922723572964766635)
        ·
          refine ⟨221827523884085359447149953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 147885015922723572964766635 221827523884085359447149953)
          ·
            refine ⟨166370642913064019585362465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 221827523884085359447149953 166370642913064019585362465)
            ·
              refine ⟨124777982184798014689021849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 166370642913064019585362465 124777982184798014689021849)
              ·
                refine ⟨93583486638598511016766387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 124777982184798014689021849 93583486638598511016766387)
                ·
                  refine ⟨140375229957897766525149581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 93583486638598511016766387 140375229957897766525149581)
                  ·
                    refine ⟨52640711234211662446931093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 140375229957897766525149581 52640711234211662446931093)
                    ·
                      refine ⟨2467533339103671677199895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 52640711234211662446931093 2467533339103671677199895)
                      ·
                        rfl

theorem cell23_4805504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 2, 1, 3, 6].length) (baseStart_4805504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4805504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4805504 prefixEnd_4805504 := by exact prefixLift 4805504
  have htrace : WordTrace (prefixWord ++ tailWord_4805504) baseStart_4805504 baseEnd_4805504 := by
    simpa [prefixWord, tailWord_4805504, baseEnd_4805504] using wordTrace_append hprefix tailTrace_4805504
  have hstable : (prefixWord ++ tailWord_4805504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4805504).length < 2 ^ (prefixWord ++ tailWord_4805504).sum := by decide
  have hdescent : baseEnd_4805504 < baseStart_4805504 := by decide
  rcases family_descends (prefixWord ++ tailWord_4805504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4805535 : List Nat := [1, 1, 2, 5, 2, 3, 1, 1, 3, 4]
def baseStart_4805535 : Nat := 118140960795 + 4805535 * 2 ^ 59
def prefixEnd_4805535 : Nat := 4983230072969 + 3 ^ 40 * 4805535 * 2
def baseEnd_4805535 : Nat := 822516419001320351970751

theorem tailTrace_4805535 : CollatzResearch.WordTrace tailWord_4805535 prefixEnd_4805535 822516419001320351970751 := by
  unfold tailWord_4805535
  simp only [CollatzResearch.WordTrace]
  refine ⟨175272260645374889882250059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116848173763583259921500039 175272260645374889882250059)
  ·
    refine ⟨262908390968062334823375089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175272260645374889882250059 262908390968062334823375089)
    ·
      refine ⟨197181293226046751117531317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 262908390968062334823375089 197181293226046751117531317)
      ·
        refine ⟨18485746239941882917268561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 197181293226046751117531317 18485746239941882917268561)
        ·
          refine ⟨13864309679956412187951421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18485746239941882917268561 13864309679956412187951421)
          ·
            refine ⟨5199116129983654570481783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13864309679956412187951421 5199116129983654570481783)
            ·
              refine ⟨7798674194975481855722675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5199116129983654570481783 7798674194975481855722675)
              ·
                refine ⟨11698011292463222783584013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7798674194975481855722675 11698011292463222783584013)
                ·
                  refine ⟨4386754234673708543844005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11698011292463222783584013 4386754234673708543844005)
                  ·
                    refine ⟨822516419001320351970751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4386754234673708543844005 822516419001320351970751)
                    ·
                      rfl

theorem cell23_4805535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 3, 1, 1, 3, 4].length) (baseStart_4805535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4805535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4805535 prefixEnd_4805535 := by exact prefixLift 4805535
  have htrace : WordTrace (prefixWord ++ tailWord_4805535) baseStart_4805535 baseEnd_4805535 := by
    simpa [prefixWord, tailWord_4805535, baseEnd_4805535] using wordTrace_append hprefix tailTrace_4805535
  have hstable : (prefixWord ++ tailWord_4805535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4805535).length < 2 ^ (prefixWord ++ tailWord_4805535).sum := by decide
  have hdescent : baseEnd_4805535 < baseStart_4805535 := by decide
  rcases family_descends (prefixWord ++ tailWord_4805535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4805592 : List Nat := [2, 1, 2, 2, 2, 4, 1, 4, 1, 1, 3]
def baseStart_4805592 : Nat := 118140960795 + 4805592 * 2 ^ 59
def prefixEnd_4805592 : Nat := 4983230072969 + 3 ^ 40 * 4805592 * 2
def baseEnd_4805592 : Nat := 2467578525401267332899491

theorem tailTrace_4805592 : CollatzResearch.WordTrace tailWord_4805592 prefixEnd_4805592 2467578525401267332899491 := by
  unfold tailWord_4805592
  simp only [CollatzResearch.WordTrace]
  refine ⟨87637169803084194308537515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116849559737445592411383353 87637169803084194308537515)
  ·
    refine ⟨131455754704626291462806273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87637169803084194308537515 131455754704626291462806273)
    ·
      refine ⟨98591816028469718597104705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 131455754704626291462806273 98591816028469718597104705)
      ·
        refine ⟨73943862021352288947828529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 98591816028469718597104705 73943862021352288947828529)
        ·
          refine ⟨55457896516014216710871397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73943862021352288947828529 55457896516014216710871397)
          ·
            refine ⟨10398355596752665633288387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 55457896516014216710871397 10398355596752665633288387)
            ·
              refine ⟨15597533395128998449932581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10398355596752665633288387 15597533395128998449932581)
              ·
                refine ⟨2924537511586687209362359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15597533395128998449932581 2924537511586687209362359)
                ·
                  refine ⟨4386806267380030814043539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2924537511586687209362359 4386806267380030814043539)
                  ·
                    refine ⟨6580209401070046221065309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4386806267380030814043539 6580209401070046221065309)
                    ·
                      refine ⟨2467578525401267332899491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6580209401070046221065309 2467578525401267332899491)
                      ·
                        rfl

theorem cell23_4805592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 1, 4, 1, 1, 3].length) (baseStart_4805592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4805592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4805592 prefixEnd_4805592 := by exact prefixLift 4805592
  have htrace : WordTrace (prefixWord ++ tailWord_4805592) baseStart_4805592 baseEnd_4805592 := by
    simpa [prefixWord, tailWord_4805592, baseEnd_4805592] using wordTrace_append hprefix tailTrace_4805592
  have hstable : (prefixWord ++ tailWord_4805592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4805592).length < 2 ^ (prefixWord ++ tailWord_4805592).sum := by decide
  have hdescent : baseEnd_4805592 < baseStart_4805592 := by decide
  rcases family_descends (prefixWord ++ tailWord_4805592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4805601 : List Nat := [1, 2, 3, 1, 2, 1, 1, 3, 3, 1, 5]
def baseStart_4805601 : Nat := 118140960795 + 4805601 * 2 ^ 59
def prefixEnd_4805601 : Nat := 4983230072969 + 3 ^ 40 * 4805601 * 2
def baseEnd_4805601 : Nat := 2467583146727157797686949

theorem tailTrace_4805601 : CollatzResearch.WordTrace tailWord_4805601 prefixEnd_4805601 2467583146727157797686949 := by
  unfold tailWord_4805601
  simp only [CollatzResearch.WordTrace]
  refine ⟨175274667863135783154152657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116849778575423855436101771 175274667863135783154152657)
  ·
    refine ⟨131456000897351837365614493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 175274667863135783154152657 131456000897351837365614493)
    ·
      refine ⟨49296000336506939012105435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 131456000897351837365614493 49296000336506939012105435)
      ·
        refine ⟨73944000504760408518158153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49296000336506939012105435 73944000504760408518158153)
        ·
          refine ⟨55458000378570306388618615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73944000504760408518158153 55458000378570306388618615)
          ·
            refine ⟨83187000567855459582927923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55458000378570306388618615 83187000567855459582927923)
            ·
              refine ⟨124780500851783189374391885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83187000567855459582927923 124780500851783189374391885)
              ·
                refine ⟨46792687819418696015396957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 124780500851783189374391885 46792687819418696015396957)
                ·
                  refine ⟨17547257932282011005773859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 46792687819418696015396957 17547257932282011005773859)
                  ·
                    refine ⟨26320886898423016508660789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17547257932282011005773859 26320886898423016508660789)
                    ·
                      refine ⟨2467583146727157797686949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26320886898423016508660789 2467583146727157797686949)
                      ·
                        rfl

theorem cell23_4805601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 3, 3, 1, 5].length) (baseStart_4805601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4805601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4805601 prefixEnd_4805601 := by exact prefixLift 4805601
  have htrace : WordTrace (prefixWord ++ tailWord_4805601) baseStart_4805601 baseEnd_4805601 := by
    simpa [prefixWord, tailWord_4805601, baseEnd_4805601] using wordTrace_append hprefix tailTrace_4805601
  have hstable : (prefixWord ++ tailWord_4805601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4805601).length < 2 ^ (prefixWord ++ tailWord_4805601).sum := by decide
  have hdescent : baseEnd_4805601 < baseStart_4805601 := by decide
  rcases family_descends (prefixWord ++ tailWord_4805601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4805615 : List Nat := [1, 1, 2, 1, 4, 3, 1, 1, 5, 2, 2]
def baseStart_4805615 : Nat := 118140960795 + 4805615 * 2 ^ 59
def prefixEnd_4805615 : Nat := 4983230072969 + 3 ^ 40 * 4805615 * 2
def baseEnd_4805615 : Nat := 2467590335456320742911885

theorem tailTrace_4805615 : CollatzResearch.WordTrace tailWord_4805615 prefixEnd_4805615 2467590335456320742911885 := by
  unfold tailWord_4805615
  simp only [CollatzResearch.WordTrace]
  refine ⟨175275178485085063545162299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116850118990056709030108199 175275178485085063545162299)
  ·
    refine ⟨262912767727627595317743449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175275178485085063545162299 262912767727627595317743449)
    ·
      refine ⟨197184575795720696488307587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 262912767727627595317743449 197184575795720696488307587)
      ·
        refine ⟨295776863693581044732461381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 197184575795720696488307587 295776863693581044732461381)
        ·
          refine ⟨55458161942546445887336509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 295776863693581044732461381 55458161942546445887336509)
          ·
            refine ⟨20796810728454917207751191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55458161942546445887336509 20796810728454917207751191)
            ·
              refine ⟨31195216092682375811626787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20796810728454917207751191 31195216092682375811626787)
              ·
                refine ⟨46792824139023563717440181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31195216092682375811626787 46792824139023563717440181)
                ·
                  refine ⟨4386827263033459098510017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 46792824139023563717440181 4386827263033459098510017)
                  ·
                    refine ⟨3290120447275094323882513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4386827263033459098510017 3290120447275094323882513)
                    ·
                      refine ⟨2467590335456320742911885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3290120447275094323882513 2467590335456320742911885)
                      ·
                        rfl

theorem cell23_4805615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 1, 1, 5, 2, 2].length) (baseStart_4805615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4805615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4805615 prefixEnd_4805615 := by exact prefixLift 4805615
  have htrace : WordTrace (prefixWord ++ tailWord_4805615) baseStart_4805615 baseEnd_4805615 := by
    simpa [prefixWord, tailWord_4805615, baseEnd_4805615] using wordTrace_append hprefix tailTrace_4805615
  have hstable : (prefixWord ++ tailWord_4805615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4805615).length < 2 ^ (prefixWord ++ tailWord_4805615).sum := by decide
  have hdescent : baseEnd_4805615 < baseStart_4805615 := by decide
  rcases family_descends (prefixWord ++ tailWord_4805615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4805628 : List Nat := [2, 2, 2, 1, 2, 3, 2, 2, 1, 2, 4]
def baseStart_4805628 : Nat := 118140960795 + 4805628 * 2 ^ 59
def prefixEnd_4805628 : Nat := 4983230072969 + 3 ^ 40 * 4805628 * 2
def baseEnd_4805628 : Nat := 2467597010704829192049325

theorem tailTrace_4805628 : CollatzResearch.WordTrace tailWord_4805628 prefixEnd_4805628 2467597010704829192049325 := by
  unfold tailWord_4805628
  simp only [CollatzResearch.WordTrace]
  refine ⟨87637826317018983382692769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116850435089358644510257025 87637826317018983382692769)
  ·
    refine ⟨65728369737764237537019577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87637826317018983382692769 65728369737764237537019577)
    ·
      refine ⟨49296277303323178152764683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65728369737764237537019577 49296277303323178152764683)
      ·
        refine ⟨73944415954984767229147025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49296277303323178152764683 73944415954984767229147025)
        ·
          refine ⟨55458311966238575421860269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73944415954984767229147025 55458311966238575421860269)
          ·
            refine ⟨20796866987339465783197601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55458311966238575421860269 20796866987339465783197601)
            ·
              refine ⟨15597650240504599337398201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20796866987339465783197601 15597650240504599337398201)
              ·
                refine ⟨11698237680378449503048651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15597650240504599337398201 11698237680378449503048651)
                ·
                  refine ⟨17547356520567674254572977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11698237680378449503048651 17547356520567674254572977)
                  ·
                    refine ⟨13160517390425755690929733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17547356520567674254572977 13160517390425755690929733)
                    ·
                      refine ⟨2467597010704829192049325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13160517390425755690929733 2467597010704829192049325)
                      ·
                        rfl

theorem cell23_4805628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 2, 2, 1, 2, 4].length) (baseStart_4805628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4805628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4805628 prefixEnd_4805628 := by exact prefixLift 4805628
  have htrace : WordTrace (prefixWord ++ tailWord_4805628) baseStart_4805628 baseEnd_4805628 := by
    simpa [prefixWord, tailWord_4805628, baseEnd_4805628] using wordTrace_append hprefix tailTrace_4805628
  have hstable : (prefixWord ++ tailWord_4805628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4805628).length < 2 ^ (prefixWord ++ tailWord_4805628).sum := by decide
  have hdescent : baseEnd_4805628 < baseStart_4805628 := by decide
  rcases family_descends (prefixWord ++ tailWord_4805628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4805642 : List Nat := [3, 1, 2, 2, 3, 3, 1, 2, 2, 4]
def baseStart_4805642 : Nat := 118140960795 + 4805642 * 2 ^ 59
def prefixEnd_4805642 : Nat := 4983230072969 + 3 ^ 40 * 4805642 * 2
def baseEnd_4805642 : Nat := 822534733144664045758087

theorem tailTrace_4805642 : CollatzResearch.WordTrace tailWord_4805642 prefixEnd_4805642 822534733144664045758087 := by
  unfold tailWord_4805642
  simp only [CollatzResearch.WordTrace]
  refine ⟨43819040813996811789098795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 116850775503991498104263453 43819040813996811789098795)
  ·
    refine ⟨65728561220995217683648193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43819040813996811789098795 65728561220995217683648193)
    ·
      refine ⟨49296420915746413262736145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65728561220995217683648193 49296420915746413262736145)
      ·
        refine ⟨36972315686809809947052109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49296420915746413262736145 36972315686809809947052109)
        ·
          refine ⟨13864618382553678730144541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36972315686809809947052109 13864618382553678730144541)
          ·
            refine ⟨5199231893457629523804203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13864618382553678730144541 5199231893457629523804203)
            ·
              refine ⟨7798847840186444285706305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5199231893457629523804203 7798847840186444285706305)
              ·
                refine ⟨5849135880139833214279729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7798847840186444285706305 5849135880139833214279729)
                ·
                  refine ⟨4386851910104874910709797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5849135880139833214279729 4386851910104874910709797)
                  ·
                    refine ⟨822534733144664045758087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4386851910104874910709797 822534733144664045758087)
                    ·
                      rfl

theorem cell23_4805642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 3, 1, 2, 2, 4].length) (baseStart_4805642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4805642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4805642 prefixEnd_4805642 := by exact prefixLift 4805642
  have htrace : WordTrace (prefixWord ++ tailWord_4805642) baseStart_4805642 baseEnd_4805642 := by
    simpa [prefixWord, tailWord_4805642, baseEnd_4805642] using wordTrace_append hprefix tailTrace_4805642
  have hstable : (prefixWord ++ tailWord_4805642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4805642).length < 2 ^ (prefixWord ++ tailWord_4805642).sum := by decide
  have hdescent : baseEnd_4805642 < baseStart_4805642 := by decide
  rcases family_descends (prefixWord ++ tailWord_4805642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4805665 : List Nat := [1, 2, 3, 2, 3, 1, 3, 1, 1, 3, 3]
def baseStart_4805665 : Nat := 118140960795 + 4805665 * 2 ^ 59
def prefixEnd_4805665 : Nat := 4983230072969 + 3 ^ 40 * 4805665 * 2
def baseEnd_4805665 : Nat := 2467616009489045547286655

theorem tailTrace_4805665 : CollatzResearch.WordTrace tailWord_4805665 prefixEnd_4805665 2467616009489045547286655 := by
  unfold tailWord_4805665
  simp only [CollatzResearch.WordTrace]
  refine ⟨175277002134903922084482449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116851334756602614722988299 175277002134903922084482449)
  ·
    refine ⟨131457751601177941563361837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 175277002134903922084482449 131457751601177941563361837)
    ·
      refine ⟨49296656850441728086260689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 131457751601177941563361837 49296656850441728086260689)
      ·
        refine ⟨36972492637831296064695517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49296656850441728086260689 36972492637831296064695517)
        ·
          refine ⟨13864684739186736024260819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36972492637831296064695517 13864684739186736024260819)
          ·
            refine ⟨20797027108780104036391229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13864684739186736024260819 20797027108780104036391229)
            ·
              refine ⟨7798885165792539013646711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20797027108780104036391229 7798885165792539013646711)
              ·
                refine ⟨11698327748688808520470067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7798885165792539013646711 11698327748688808520470067)
                ·
                  refine ⟨17547491623033212780705101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11698327748688808520470067 17547491623033212780705101)
                  ·
                    refine ⟨6580309358637454792764413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17547491623033212780705101 6580309358637454792764413)
                    ·
                      refine ⟨2467616009489045547286655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6580309358637454792764413 2467616009489045547286655)
                      ·
                        rfl

theorem cell23_4805665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 3, 1, 1, 3, 3].length) (baseStart_4805665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4805665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4805665 prefixEnd_4805665 := by exact prefixLift 4805665
  have htrace : WordTrace (prefixWord ++ tailWord_4805665) baseStart_4805665 baseEnd_4805665 := by
    simpa [prefixWord, tailWord_4805665, baseEnd_4805665] using wordTrace_append hprefix tailTrace_4805665
  have hstable : (prefixWord ++ tailWord_4805665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4805665).length < 2 ^ (prefixWord ++ tailWord_4805665).sum := by decide
  have hdescent : baseEnd_4805665 < baseStart_4805665 := by decide
  rcases family_descends (prefixWord ++ tailWord_4805665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4805678 : List Nat := [4, 1, 3, 1, 1, 1, 1, 1, 1, 4, 5]
def baseStart_4805678 : Nat := 118140960795 + 4805678 * 2 ^ 59
def prefixEnd_4805678 : Nat := 4983230072969 + 3 ^ 40 * 4805678 * 2
def baseEnd_4805678 : Nat := 2467622684737553996424095

theorem tailTrace_4805678 : CollatzResearch.WordTrace tailWord_4805678 prefixEnd_4805678 2467622684737553996424095 := by
  unfold tailWord_4805678
  simp only [CollatzResearch.WordTrace]
  refine ⟨21909684535482103163088211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 116851650855904550203137125 21909684535482103163088211)
  ·
    refine ⟨32864526803223154744632317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21909684535482103163088211 32864526803223154744632317)
    ·
      refine ⟨12324197551208683029237119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32864526803223154744632317 12324197551208683029237119)
      ·
        refine ⟨18486296326813024543855679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12324197551208683029237119 18486296326813024543855679)
        ·
          refine ⟨27729444490219536815783519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18486296326813024543855679 27729444490219536815783519)
          ·
            refine ⟨41594166735329305223675279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27729444490219536815783519 41594166735329305223675279)
            ·
              refine ⟨62391250102993957835512919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41594166735329305223675279 62391250102993957835512919)
              ·
                refine ⟨93586875154490936753269379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62391250102993957835512919 93586875154490936753269379)
                ·
                  refine ⟨140380312731736405129904069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 93586875154490936753269379 140380312731736405129904069)
                  ·
                    refine ⟨26321308637200575961857013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 140380312731736405129904069 26321308637200575961857013)
                    ·
                      refine ⟨2467622684737553996424095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26321308637200575961857013 2467622684737553996424095)
                      ·
                        rfl

theorem cell23_4805678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 1, 1, 4, 5].length) (baseStart_4805678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4805678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4805678 prefixEnd_4805678 := by exact prefixLift 4805678
  have htrace : WordTrace (prefixWord ++ tailWord_4805678) baseStart_4805678 baseEnd_4805678 := by
    simpa [prefixWord, tailWord_4805678, baseEnd_4805678] using wordTrace_append hprefix tailTrace_4805678
  have hstable : (prefixWord ++ tailWord_4805678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4805678).length < 2 ^ (prefixWord ++ tailWord_4805678).sum := by decide
  have hdescent : baseEnd_4805678 < baseStart_4805678 := by decide
  rcases family_descends (prefixWord ++ tailWord_4805678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4805692 : List Nat := [2, 2, 2, 2, 2, 2, 2, 3, 1, 3, 2]
def baseStart_4805692 : Nat := 118140960795 + 4805692 * 2 ^ 59
def prefixEnd_4805692 : Nat := 4983230072969 + 3 ^ 40 * 4805692 * 2
def baseEnd_4805692 : Nat := 2467629873466716941649031

theorem tailTrace_4805692 : CollatzResearch.WordTrace tailWord_4805692 prefixEnd_4805692 2467629873466716941649031 := by
  unfold tailWord_4805692
  simp only [CollatzResearch.WordTrace]
  refine ⟨87638993452903052847857665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116851991270537403797143553 87638993452903052847857665)
  ·
    refine ⟨65729245089677289635893249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87638993452903052847857665 65729245089677289635893249)
    ·
      refine ⟨49296933817257967226919937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65729245089677289635893249 49296933817257967226919937)
      ·
        refine ⟨36972700362943475420189953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49296933817257967226919937 36972700362943475420189953)
        ·
          refine ⟨27729525272207606565142465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36972700362943475420189953 27729525272207606565142465)
          ·
            refine ⟨20797143954155704923856849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27729525272207606565142465 20797143954155704923856849)
            ·
              refine ⟨15597857965616778692892637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20797143954155704923856849 15597857965616778692892637)
              ·
                refine ⟨5849196737106292009834739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15597857965616778692892637 5849196737106292009834739)
                ·
                  refine ⟨8773795105659438014752109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5849196737106292009834739 8773795105659438014752109)
                  ·
                    refine ⟨3290173164622289255532041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8773795105659438014752109 3290173164622289255532041)
                    ·
                      refine ⟨2467629873466716941649031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3290173164622289255532041 2467629873466716941649031)
                      ·
                        rfl

theorem cell23_4805692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 2, 3, 1, 3, 2].length) (baseStart_4805692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4805692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4805692 prefixEnd_4805692 := by exact prefixLift 4805692
  have htrace : WordTrace (prefixWord ++ tailWord_4805692) baseStart_4805692 baseEnd_4805692 := by
    simpa [prefixWord, tailWord_4805692, baseEnd_4805692] using wordTrace_append hprefix tailTrace_4805692
  have hstable : (prefixWord ++ tailWord_4805692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4805692).length < 2 ^ (prefixWord ++ tailWord_4805692).sum := by decide
  have hdescent : baseEnd_4805692 < baseStart_4805692 := by decide
  rcases family_descends (prefixWord ++ tailWord_4805692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4805708 : List Nat := [2, 2, 1, 3, 1, 1, 1, 3, 2, 4, 3]
def baseStart_4805708 : Nat := 118140960795 + 4805708 * 2 ^ 59
def prefixEnd_4805708 : Nat := 4983230072969 + 3 ^ 40 * 4805708 * 2
def baseEnd_4805708 : Nat := 2467638089157188879048957

theorem tailTrace_4805708 : CollatzResearch.WordTrace tailWord_4805708 prefixEnd_4805708 2467638089157188879048957 := by
  unfold tailWord_4805708
  simp only [CollatzResearch.WordTrace]
  refine ⟨87639285236874070214148889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116852380315832093618865185 87639285236874070214148889)
  ·
    refine ⟨65729463927655552660611667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87639285236874070214148889 65729463927655552660611667)
    ·
      refine ⟨98594195891483328990917501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65729463927655552660611667 98594195891483328990917501)
      ·
        refine ⟨36972823459306248371594063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 98594195891483328990917501 36972823459306248371594063)
        ·
          refine ⟨55459235188959372557391095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36972823459306248371594063 55459235188959372557391095)
          ·
            refine ⟨83188852783439058836086643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55459235188959372557391095 83188852783439058836086643)
            ·
              refine ⟨124783279175158588254129965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83188852783439058836086643 124783279175158588254129965)
              ·
                refine ⟨46793729690684470595298737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 124783279175158588254129965 46793729690684470595298737)
                ·
                  refine ⟨35095297268013352946474053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 46793729690684470595298737 35095297268013352946474053)
                  ·
                    refine ⟨6580368237752503677463885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 35095297268013352946474053 6580368237752503677463885)
                    ·
                      refine ⟨2467638089157188879048957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6580368237752503677463885 2467638089157188879048957)
                      ·
                        rfl

theorem cell23_4805708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 3, 2, 4, 3].length) (baseStart_4805708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4805708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4805708 prefixEnd_4805708 := by exact prefixLift 4805708
  have htrace : WordTrace (prefixWord ++ tailWord_4805708) baseStart_4805708 baseEnd_4805708 := by
    simpa [prefixWord, tailWord_4805708, baseEnd_4805708] using wordTrace_append hprefix tailTrace_4805708
  have hstable : (prefixWord ++ tailWord_4805708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4805708).length < 2 ^ (prefixWord ++ tailWord_4805708).sum := by decide
  have hdescent : baseEnd_4805708 < baseStart_4805708 := by decide
  rcases family_descends (prefixWord ++ tailWord_4805708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4805726 : List Nat := [4, 4, 1, 1, 1, 2, 1, 1, 3, 3, 2]
def baseStart_4805726 : Nat := 118140960795 + 4805726 * 2 ^ 59
def prefixEnd_4805726 : Nat := 4983230072969 + 3 ^ 40 * 4805726 * 2
def baseEnd_4805726 : Nat := 2467647331808969808623875

theorem tailTrace_4805726 : CollatzResearch.WordTrace tailWord_4805726 prefixEnd_4805726 2467647331808969808623875 := by
  unfold tailWord_4805726
  simp only [CollatzResearch.WordTrace]
  refine ⟨21909903373460366187806629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 116852817991788619668302021 21909903373460366187806629)
  ·
    refine ⟨4108106882523818660213743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21909903373460366187806629 4108106882523818660213743)
    ·
      refine ⟨6162160323785727990320615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4108106882523818660213743 6162160323785727990320615)
      ·
        refine ⟨9243240485678591985480923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6162160323785727990320615 9243240485678591985480923)
        ·
          refine ⟨13864860728517887978221385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9243240485678591985480923 13864860728517887978221385)
          ·
            refine ⟨10398645546388415983666039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13864860728517887978221385 10398645546388415983666039)
            ·
              refine ⟨15597968319582623975499059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10398645546388415983666039 15597968319582623975499059)
              ·
                refine ⟨23396952479373935963248589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15597968319582623975499059 23396952479373935963248589)
                ·
                  refine ⟨8773857179765225986218221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23396952479373935963248589 8773857179765225986218221)
                  ·
                    refine ⟨3290196442411959744831833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8773857179765225986218221 3290196442411959744831833)
                    ·
                      refine ⟨2467647331808969808623875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3290196442411959744831833 2467647331808969808623875)
                      ·
                        rfl

theorem cell23_4805726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 1, 1, 3, 3, 2].length) (baseStart_4805726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4805726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4805726 prefixEnd_4805726 := by exact prefixLift 4805726
  have htrace : WordTrace (prefixWord ++ tailWord_4805726) baseStart_4805726 baseEnd_4805726 := by
    simpa [prefixWord, tailWord_4805726, baseEnd_4805726] using wordTrace_append hprefix tailTrace_4805726
  have hstable : (prefixWord ++ tailWord_4805726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4805726).length < 2 ^ (prefixWord ++ tailWord_4805726).sum := by decide
  have hdescent : baseEnd_4805726 < baseStart_4805726 := by decide
  rcases family_descends (prefixWord ++ tailWord_4805726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4805815 : List Nat := [1, 1, 3, 1, 4, 1, 2, 1, 4, 2, 3]
def baseStart_4805815 : Nat := 118140960795 + 4805815 * 2 ^ 59
def prefixEnd_4805815 : Nat := 4983230072969 + 3 ^ 40 * 4805815 * 2
def baseEnd_4805815 : Nat := 2467693031587219960410965

theorem tailTrace_4805815 : CollatzResearch.WordTrace tailWord_4805815 prefixEnd_4805815 2467693031587219960410965 := by
  unfold tailWord_4805815
  simp only [CollatzResearch.WordTrace]
  refine ⟨175282473084360497702442899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116854982056240331801628599 175282473084360497702442899)
  ·
    refine ⟨262923709626540746553664349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175282473084360497702442899 262923709626540746553664349)
    ·
      refine ⟨98596391109952779957624131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 262923709626540746553664349 98596391109952779957624131)
      ·
        refine ⟨147894586664929169936436197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98596391109952779957624131 147894586664929169936436197)
        ·
          refine ⟨27730234999674219363081787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 147894586664929169936436197 27730234999674219363081787)
          ·
            refine ⟨41595352499511329044622681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27730234999674219363081787 41595352499511329044622681)
            ·
              refine ⟨31196514374633496783467011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41595352499511329044622681 31196514374633496783467011)
              ·
                refine ⟨46794771561950245175200517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31196514374633496783467011 46794771561950245175200517)
                ·
                  refine ⟨8774019667865670970350097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 46794771561950245175200517 8774019667865670970350097)
                  ·
                    refine ⟨6580514750899253227762573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8774019667865670970350097 6580514750899253227762573)
                    ·
                      refine ⟨2467693031587219960410965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6580514750899253227762573 2467693031587219960410965)
                      ·
                        rfl

theorem cell23_4805815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 2, 1, 4, 2, 3].length) (baseStart_4805815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4805815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4805815 prefixEnd_4805815 := by exact prefixLift 4805815
  have htrace : WordTrace (prefixWord ++ tailWord_4805815) baseStart_4805815 baseEnd_4805815 := by
    simpa [prefixWord, tailWord_4805815, baseEnd_4805815] using wordTrace_append hprefix tailTrace_4805815
  have hstable : (prefixWord ++ tailWord_4805815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4805815).length < 2 ^ (prefixWord ++ tailWord_4805815).sum := by decide
  have hdescent : baseEnd_4805815 < baseStart_4805815 := by decide
  rcases family_descends (prefixWord ++ tailWord_4805815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4805822 : List Nat := [4, 2, 1, 1, 3, 1, 1, 3, 3, 4]
def baseStart_4805822 : Nat := 118140960795 + 4805822 * 2 ^ 59
def prefixEnd_4805822 : Nat := 4983230072969 + 3 ^ 40 * 4805822 * 2
def baseEnd_4805822 : Nat := 822565541983933811007811

theorem tailTrace_4805822 : CollatzResearch.WordTrace tailWord_4805822 prefixEnd_4805822 822565541983933811007811 := by
  unfold tailWord_4805822
  simp only [CollatzResearch.WordTrace]
  refine ⟨21910341049416892237243465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 116855152263556758598631813 21910341049416892237243465)
  ·
    refine ⟨16432755787062669177932599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21910341049416892237243465 16432755787062669177932599)
    ·
      refine ⟨24649133680594003766898899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16432755787062669177932599 24649133680594003766898899)
      ·
        refine ⟨36973700520891005650348349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24649133680594003766898899 36973700520891005650348349)
        ·
          refine ⟨13865137695334127118880631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36973700520891005650348349 13865137695334127118880631)
          ·
            refine ⟨20797706543001190678320947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13865137695334127118880631 20797706543001190678320947)
            ·
              refine ⟨31196559814501786017481421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20797706543001190678320947 31196559814501786017481421)
              ·
                refine ⟨11698709930438169756555533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31196559814501786017481421 11698709930438169756555533)
                ·
                  refine ⟨4387016223914313658708325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11698709930438169756555533 4387016223914313658708325)
                  ·
                    refine ⟨822565541983933811007811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4387016223914313658708325 822565541983933811007811)
                    ·
                      rfl

theorem cell23_4805822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 1, 3, 3, 4].length) (baseStart_4805822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4805822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4805822 prefixEnd_4805822 := by exact prefixLift 4805822
  have htrace : WordTrace (prefixWord ++ tailWord_4805822) baseStart_4805822 baseEnd_4805822 := by
    simpa [prefixWord, tailWord_4805822, baseEnd_4805822] using wordTrace_append hprefix tailTrace_4805822
  have hstable : (prefixWord ++ tailWord_4805822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4805822).length < 2 ^ (prefixWord ++ tailWord_4805822).sum := by decide
  have hdescent : baseEnd_4805822 < baseStart_4805822 := by decide
  rcases family_descends (prefixWord ++ tailWord_4805822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4805902 : List Nat := [4, 1, 1, 2, 1, 4, 1, 1, 3, 1, 4]
def baseStart_4805902 : Nat := 118140960795 + 4805902 * 2 ^ 59
def prefixEnd_4805902 : Nat := 4983230072969 + 3 ^ 40 * 4805902 * 2
def baseEnd_4805902 : Nat := 2467737704404161120023065

theorem tailTrace_4805902 : CollatzResearch.WordTrace tailWord_4805902 prefixEnd_4805902 2467737704404161120023065 := by
  unfold tailWord_4805902
  simp only [CollatzResearch.WordTrace]
  refine ⟨21910705779380663945107495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 116857097490030207707239973 21910705779380663945107495)
  ·
    refine ⟨32866058669070995917661243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21910705779380663945107495 32866058669070995917661243)
    ·
      refine ⟨49299088003606493876491865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32866058669070995917661243 49299088003606493876491865)
      ·
        refine ⟨36974316002704870407368899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49299088003606493876491865 36974316002704870407368899)
        ·
          refine ⟨55461474004057305611053349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36974316002704870407368899 55461474004057305611053349)
          ·
            refine ⟨10399026375760744802072503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 55461474004057305611053349 10399026375760744802072503)
            ·
              refine ⟨15598539563641117203108755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10399026375760744802072503 15598539563641117203108755)
              ·
                refine ⟨23397809345461675804663133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15598539563641117203108755 23397809345461675804663133)
                ·
                  refine ⟨8774178504548128426748675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23397809345461675804663133 8774178504548128426748675)
                  ·
                    refine ⟨13161267756822192640123013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8774178504548128426748675 13161267756822192640123013)
                    ·
                      refine ⟨2467737704404161120023065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13161267756822192640123013 2467737704404161120023065)
                      ·
                        rfl

theorem cell23_4805902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 1, 1, 3, 1, 4].length) (baseStart_4805902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4805902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4805902 prefixEnd_4805902 := by exact prefixLift 4805902
  have htrace : WordTrace (prefixWord ++ tailWord_4805902) baseStart_4805902 baseEnd_4805902 := by
    simpa [prefixWord, tailWord_4805902, baseEnd_4805902] using wordTrace_append hprefix tailTrace_4805902
  have hstable : (prefixWord ++ tailWord_4805902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4805902).length < 2 ^ (prefixWord ++ tailWord_4805902).sum := by decide
  have hdescent : baseEnd_4805902 < baseStart_4805902 := by decide
  rcases family_descends (prefixWord ++ tailWord_4805902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4805930 : List Nat := [3, 1, 4, 2, 1, 3, 2, 2, 1, 1, 3]
def baseStart_4805930 : Nat := 118140960795 + 4805930 * 2 ^ 59
def prefixEnd_4805930 : Nat := 4983230072969 + 3 ^ 40 * 4805930 * 2
def baseEnd_4805930 : Nat := 2467752081862487010472937

theorem tailTrace_4805930 : CollatzResearch.WordTrace tailWord_4805930 prefixEnd_4805930 2467752081862487010472937 := by
  unfold tailWord_4805930
  simp only [CollatzResearch.WordTrace]
  refine ⟨43821666869735968085719811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 116857778319295914895252829 43821666869735968085719811)
  ·
    refine ⟨65732500304603952128579717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43821666869735968085719811 65732500304603952128579717)
    ·
      refine ⟨12324843807113241024108697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 65732500304603952128579717 12324843807113241024108697)
      ·
        refine ⟨9243632855334930768081523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12324843807113241024108697 9243632855334930768081523)
        ·
          refine ⟨13865449283002396152122285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9243632855334930768081523 13865449283002396152122285)
          ·
            refine ⟨5199543481125898557045857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13865449283002396152122285 5199543481125898557045857)
            ·
              refine ⟨3899657610844423917784393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5199543481125898557045857 3899657610844423917784393)
              ·
                refine ⟨2924743208133317938338295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3899657610844423917784393 2924743208133317938338295)
                ·
                  refine ⟨4387114812199976907507443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2924743208133317938338295 4387114812199976907507443)
                  ·
                    refine ⟨6580672218299965361261165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4387114812199976907507443 6580672218299965361261165)
                    ·
                      refine ⟨2467752081862487010472937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6580672218299965361261165 2467752081862487010472937)
                      ·
                        rfl

theorem cell23_4805930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 3, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 3, 2, 2, 1, 1, 3].length) (baseStart_4805930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4805930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4805930 prefixEnd_4805930 := by exact prefixLift 4805930
  have htrace : WordTrace (prefixWord ++ tailWord_4805930) baseStart_4805930 baseEnd_4805930 := by
    simpa [prefixWord, tailWord_4805930, baseEnd_4805930] using wordTrace_append hprefix tailTrace_4805930
  have hstable : (prefixWord ++ tailWord_4805930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4805930).length < 2 ^ (prefixWord ++ tailWord_4805930).sum := by decide
  have hdescent : baseEnd_4805930 < baseStart_4805930 := by decide
  rcases family_descends (prefixWord ++ tailWord_4805930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4805935 : List Nat := [1, 1, 2, 1, 2, 1, 3, 1, 5, 3, 3]
def baseStart_4805935 : Nat := 118140960795 + 4805935 * 2 ^ 59
def prefixEnd_4805935 : Nat := 4983230072969 + 3 ^ 40 * 4805935 * 2
def baseEnd_4805935 : Nat := 2467754649265759490910413

theorem tailTrace_4805935 : CollatzResearch.WordTrace tailWord_4805935 prefixEnd_4805935 2467754649265759490910413 := by
  unfold tailWord_4805935
  simp only [CollatzResearch.WordTrace]
  refine ⟨175286849843925758196811259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116857899895950505464540839 175286849843925758196811259)
  ·
    refine ⟨262930274765888637295216889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175286849843925758196811259 262930274765888637295216889)
    ·
      refine ⟨197197706074416477971412667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 262930274765888637295216889 197197706074416477971412667)
      ·
        refine ⟨295796559111624716957119001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 197197706074416477971412667 295796559111624716957119001)
        ·
          refine ⟨221847419333718537717839251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 295796559111624716957119001 221847419333718537717839251)
          ·
            refine ⟨332771129000577806576758877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 221847419333718537717839251 332771129000577806576758877)
            ·
              refine ⟨124789173375216677466284579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 332771129000577806576758877 124789173375216677466284579)
              ·
                refine ⟨187183760062825016199426869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 124789173375216677466284579 187183760062825016199426869)
                ·
                  refine ⟨17548477505889845268696269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 187183760062825016199426869 17548477505889845268696269)
                  ·
                    refine ⟨6580679064708691975761101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17548477505889845268696269 6580679064708691975761101)
                    ·
                      refine ⟨2467754649265759490910413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6580679064708691975761101 2467754649265759490910413)
                      ·
                        rfl

theorem cell23_4805935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 1, 5, 3, 3].length) (baseStart_4805935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4805935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4805935 prefixEnd_4805935 := by exact prefixLift 4805935
  have htrace : WordTrace (prefixWord ++ tailWord_4805935) baseStart_4805935 baseEnd_4805935 := by
    simpa [prefixWord, tailWord_4805935, baseEnd_4805935] using wordTrace_append hprefix tailTrace_4805935
  have hstable : (prefixWord ++ tailWord_4805935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4805935).length < 2 ^ (prefixWord ++ tailWord_4805935).sum := by decide
  have hdescent : baseEnd_4805935 < baseStart_4805935 := by decide
  rcases family_descends (prefixWord ++ tailWord_4805935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4805936 : List Nat := [2, 1, 1, 1, 2, 2, 5, 4, 1, 2, 2]
def baseStart_4805936 : Nat := 118140960795 + 4805936 * 2 ^ 59
def prefixEnd_4805936 : Nat := 4983230072969 + 3 ^ 40 * 4805936 * 2
def baseEnd_4805936 : Nat := 2467755162746413986997909

theorem tailTrace_4805936 : CollatzResearch.WordTrace tailWord_4805936 prefixEnd_4805936 2467755162746413986997909 := by
  unfold tailWord_4805936
  simp only [CollatzResearch.WordTrace]
  refine ⟨87643443158461067683798831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116857924211281423578398441 87643443158461067683798831)
  ·
    refine ⟨131465164737691601525698247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87643443158461067683798831 131465164737691601525698247)
    ·
      refine ⟨197197747106537402288547371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131465164737691601525698247 197197747106537402288547371)
      ·
        refine ⟨295796620659806103432821057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 197197747106537402288547371 295796620659806103432821057)
        ·
          refine ⟨221847465494854577574615793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 295796620659806103432821057 221847465494854577574615793)
          ·
            refine ⟨166385599121140933180961845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 221847465494854577574615793 166385599121140933180961845)
            ·
              refine ⟨15598649917606962485715173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 166385599121140933180961845 15598649917606962485715173)
              ·
                refine ⟨2924746859551305466071595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15598649917606962485715173 2924746859551305466071595)
                ·
                  refine ⟨4387120289326958199107393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2924746859551305466071595 4387120289326958199107393)
                  ·
                    refine ⟨3290340216995218649330545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4387120289326958199107393 3290340216995218649330545)
                    ·
                      refine ⟨2467755162746413986997909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3290340216995218649330545 2467755162746413986997909)
                      ·
                        rfl

theorem cell23_4805936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 5, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 5, 4, 1, 2, 2].length) (baseStart_4805936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4805936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4805936 prefixEnd_4805936 := by exact prefixLift 4805936
  have htrace : WordTrace (prefixWord ++ tailWord_4805936) baseStart_4805936 baseEnd_4805936 := by
    simpa [prefixWord, tailWord_4805936, baseEnd_4805936] using wordTrace_append hprefix tailTrace_4805936
  have hstable : (prefixWord ++ tailWord_4805936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4805936).length < 2 ^ (prefixWord ++ tailWord_4805936).sum := by decide
  have hdescent : baseEnd_4805936 < baseStart_4805936 := by decide
  rcases family_descends (prefixWord ++ tailWord_4805936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4805952 : List Nat := [2, 1, 1, 2, 2, 1, 6, 1, 1, 3, 3]
def baseStart_4805952 : Nat := 118140960795 + 4805952 * 2 ^ 59
def prefixEnd_4805952 : Nat := 4983230072969 + 3 ^ 40 * 4805952 * 2
def baseEnd_4805952 : Nat := 2467763378436885924397835

theorem tailTrace_4805952 : CollatzResearch.WordTrace tailWord_4805952 prefixEnd_4805952 2467763378436885924397835 := by
  unfold tailWord_4805952
  simp only [CollatzResearch.WordTrace]
  refine ⟨87643734942432085050090055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116858313256576113400120073 87643734942432085050090055)
  ·
    refine ⟨131465602413648127575135083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87643734942432085050090055 131465602413648127575135083)
    ·
      refine ⟨197198403620472191362702625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131465602413648127575135083 197198403620472191362702625)
      ·
        refine ⟨147898802715354143522026969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 197198403620472191362702625 147898802715354143522026969)
        ·
          refine ⟨110924102036515607641520227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 147898802715354143522026969 110924102036515607641520227)
          ·
            refine ⟨166386153054773411462280341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 110924102036515607641520227 166386153054773411462280341)
            ·
              refine ⟨7799350924442503662294391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 166386153054773411462280341 7799350924442503662294391)
              ·
                refine ⟨11699026386663755493441587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7799350924442503662294391 11699026386663755493441587)
                ·
                  refine ⟨17548539579995633240162381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11699026386663755493441587 17548539579995633240162381)
                  ·
                    refine ⟨6580702342498362465060893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17548539579995633240162381 6580702342498362465060893)
                    ·
                      refine ⟨2467763378436885924397835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6580702342498362465060893 2467763378436885924397835)
                      ·
                        rfl

theorem cell23_4805952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 6, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 6, 1, 1, 3, 3].length) (baseStart_4805952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4805952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4805952 prefixEnd_4805952 := by exact prefixLift 4805952
  have htrace : WordTrace (prefixWord ++ tailWord_4805952) baseStart_4805952 baseEnd_4805952 := by
    simpa [prefixWord, tailWord_4805952, baseEnd_4805952] using wordTrace_append hprefix tailTrace_4805952
  have hstable : (prefixWord ++ tailWord_4805952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4805952).length < 2 ^ (prefixWord ++ tailWord_4805952).sum := by decide
  have hdescent : baseEnd_4805952 < baseStart_4805952 := by decide
  rcases family_descends (prefixWord ++ tailWord_4805952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4806009 : List Nat := [1, 2, 1, 3, 2, 1, 5, 1, 1, 4, 2]
def baseStart_4806009 : Nat := 118140960795 + 4806009 * 2 ^ 59
def prefixEnd_4806009 : Nat := 4983230072969 + 3 ^ 40 * 4806009 * 2
def baseEnd_4806009 : Nat := 2467792646834192201385073

theorem tailTrace_4806009 : CollatzResearch.WordTrace tailWord_4806009 prefixEnd_4806009 2467792646834192201385073 := by
  unfold tailWord_4806009
  simp only [CollatzResearch.WordTrace]
  refine ⟨175289548845657668835005081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116859699230438445890003387 175289548845657668835005081)
  ·
    refine ⟨131467161634243251626253811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 175289548845657668835005081 131467161634243251626253811)
    ·
      refine ⟨197200742451364877439380717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131467161634243251626253811 197200742451364877439380717)
      ·
        refine ⟨73950278419261829039767769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 197200742451364877439380717 73950278419261829039767769)
        ·
          refine ⟨55462708814446371779825827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73950278419261829039767769 55462708814446371779825827)
          ·
            refine ⟨83194063221669557669738741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55462708814446371779825827 83194063221669557669738741)
            ·
              refine ⟨7799443427031521031538007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 83194063221669557669738741 7799443427031521031538007)
              ·
                refine ⟨11699165140547281547307011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7799443427031521031538007 11699165140547281547307011)
                ·
                  refine ⟨17548747710820922320960517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11699165140547281547307011 17548747710820922320960517)
                  ·
                    refine ⟨3290390195778922935180097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17548747710820922320960517 3290390195778922935180097)
                    ·
                      refine ⟨2467792646834192201385073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3290390195778922935180097 2467792646834192201385073)
                      ·
                        rfl

theorem cell23_4806009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 5, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 5, 1, 1, 4, 2].length) (baseStart_4806009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4806009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4806009 prefixEnd_4806009 := by exact prefixLift 4806009
  have htrace : WordTrace (prefixWord ++ tailWord_4806009) baseStart_4806009 baseEnd_4806009 := by
    simpa [prefixWord, tailWord_4806009, baseEnd_4806009] using wordTrace_append hprefix tailTrace_4806009
  have hstable : (prefixWord ++ tailWord_4806009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4806009).length < 2 ^ (prefixWord ++ tailWord_4806009).sum := by decide
  have hdescent : baseEnd_4806009 < baseStart_4806009 := by decide
  rcases family_descends (prefixWord ++ tailWord_4806009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4806085 : List Nat := [1, 3, 1, 1, 1, 1, 1, 1, 1, 1, 11]
def baseStart_4806085 : Nat := 118140960795 + 4806085 * 2 ^ 59
def prefixEnd_4806085 : Nat := 4983230072969 + 3 ^ 40 * 4806085 * 2
def baseEnd_4806085 : Nat := 2467831671363933904034723

theorem tailTrace_4806085 : CollatzResearch.WordTrace tailWord_4806085 prefixEnd_4806085 2467831671363933904034723 := by
  unfold tailWord_4806085
  simp only [CollatzResearch.WordTrace]
  refine ⟨175292320793382333814771709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116861547195588222543181139 175292320793382333814771709)
  ·
    refine ⟨65734620297518375180539391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 175292320793382333814771709 65734620297518375180539391)
    ·
      refine ⟨98601930446277562770809087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65734620297518375180539391 98601930446277562770809087)
      ·
        refine ⟨147902895669416344156213631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98601930446277562770809087 147902895669416344156213631)
        ·
          refine ⟨221854343504124516234320447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 147902895669416344156213631 221854343504124516234320447)
          ·
            refine ⟨332781515256186774351480671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 221854343504124516234320447 332781515256186774351480671)
            ·
              refine ⟨499172272884280161527221007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 332781515256186774351480671 499172272884280161527221007)
              ·
                refine ⟨748758409326420242290831511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 499172272884280161527221007 748758409326420242290831511)
                ·
                  refine ⟨1123137613989630363436247267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 748758409326420242290831511 1123137613989630363436247267)
                  ·
                    refine ⟨1684706420984445545154370901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1123137613989630363436247267 1684706420984445545154370901)
                    ·
                      refine ⟨2467831671363933904034723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 11 1684706420984445545154370901 2467831671363933904034723)
                      ·
                        rfl

theorem cell23_4806085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 1, 11].length) (baseStart_4806085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4806085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4806085 prefixEnd_4806085 := by exact prefixLift 4806085
  have htrace : WordTrace (prefixWord ++ tailWord_4806085) baseStart_4806085 baseEnd_4806085 := by
    simpa [prefixWord, tailWord_4806085, baseEnd_4806085] using wordTrace_append hprefix tailTrace_4806085
  have hstable : (prefixWord ++ tailWord_4806085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4806085).length < 2 ^ (prefixWord ++ tailWord_4806085).sum := by decide
  have hdescent : baseEnd_4806085 < baseStart_4806085 := by decide
  rcases family_descends (prefixWord ++ tailWord_4806085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4806100 : List Nat := [2, 4, 1, 2, 4, 1, 2, 2, 5]
def baseStart_4806100 : Nat := 118140960795 + 4806100 * 2 ^ 59
def prefixEnd_4806100 : Nat := 4983230072969 + 3 ^ 40 * 4806100 * 2
def baseEnd_4806100 : Nat := 274204374841527927260795

theorem tailTrace_4806100 : CollatzResearch.WordTrace tailWord_4806100 prefixEnd_4806100 274204374841527927260795 := by
  unfold tailWord_4806100
  simp only [CollatzResearch.WordTrace]
  refine ⟨87646433944163995688283877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116861911925551994251045169 87646433944163995688283877)
  ·
    refine ⟨16433706364530749191553227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 87646433944163995688283877 16433706364530749191553227)
    ·
      refine ⟨24650559546796123787329841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16433706364530749191553227 24650559546796123787329841)
      ·
        refine ⟨18487919660097092840497381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24650559546796123787329841 18487919660097092840497381)
        ·
          refine ⟨3466484936268204907593259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18487919660097092840497381 3466484936268204907593259)
          ·
            refine ⟨5199727404402307361389889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3466484936268204907593259 5199727404402307361389889)
            ·
              refine ⟨3899795553301730521042417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5199727404402307361389889 3899795553301730521042417)
              ·
                refine ⟨2924846664976297890781813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3899795553301730521042417 2924846664976297890781813)
                ·
                  refine ⟨274204374841527927260795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2924846664976297890781813 274204374841527927260795)
                  ·
                    rfl

theorem cell23_4806100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 4, 1, 2, 2, 5].length) (baseStart_4806100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4806100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4806100 prefixEnd_4806100 := by exact prefixLift 4806100
  have htrace : WordTrace (prefixWord ++ tailWord_4806100) baseStart_4806100 baseEnd_4806100 := by
    simpa [prefixWord, tailWord_4806100, baseEnd_4806100] using wordTrace_append hprefix tailTrace_4806100
  have hstable : (prefixWord ++ tailWord_4806100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4806100).length < 2 ^ (prefixWord ++ tailWord_4806100).sum := by decide
  have hdescent : baseEnd_4806100 < baseStart_4806100 := by decide
  rcases family_descends (prefixWord ++ tailWord_4806100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4806133 : List Nat := [1, 3, 5, 1, 1, 3, 1, 1, 2, 1, 4]
def baseStart_4806133 : Nat := 118140960795 + 4806133 * 2 ^ 59
def prefixEnd_4806133 : Nat := 4983230072969 + 3 ^ 40 * 4806133 * 2
def baseEnd_4806133 : Nat := 2467856318435349716234503

theorem tailTrace_4806133 : CollatzResearch.WordTrace tailWord_4806133 prefixEnd_4806133 2467856318435349716234503 := by
  unfold tailWord_4806133
  simp only [CollatzResearch.WordTrace]
  refine ⟨175294071497208438012519053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116862714331472292008346035 175294071497208438012519053)
  ·
    refine ⟨65735276811453164254694645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 175294071497208438012519053 65735276811453164254694645)
    ·
      refine ⟨6162682201073734148877623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 65735276811453164254694645 6162682201073734148877623)
      ·
        refine ⟨9244023301610601223316435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6162682201073734148877623 9244023301610601223316435)
        ·
          refine ⟨13866034952415901834974653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9244023301610601223316435 13866034952415901834974653)
          ·
            refine ⟨5199763107155963188115495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13866034952415901834974653 5199763107155963188115495)
            ·
              refine ⟨7799644660733944782173243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5199763107155963188115495 7799644660733944782173243)
              ·
                refine ⟨11699466991100917173259865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7799644660733944782173243 11699466991100917173259865)
                ·
                  refine ⟨8774600243325687879944899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11699466991100917173259865 8774600243325687879944899)
                  ·
                    refine ⟨13161900364988531819917349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8774600243325687879944899 13161900364988531819917349)
                    ·
                      refine ⟨2467856318435349716234503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13161900364988531819917349 2467856318435349716234503)
                      ·
                        rfl

theorem cell23_4806133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 3, 1, 1, 2, 1, 4].length) (baseStart_4806133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4806133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4806133 prefixEnd_4806133 := by exact prefixLift 4806133
  have htrace : WordTrace (prefixWord ++ tailWord_4806133) baseStart_4806133 baseEnd_4806133 := by
    simpa [prefixWord, tailWord_4806133, baseEnd_4806133] using wordTrace_append hprefix tailTrace_4806133
  have hstable : (prefixWord ++ tailWord_4806133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4806133).length < 2 ^ (prefixWord ++ tailWord_4806133).sum := by decide
  have hdescent : baseEnd_4806133 < baseStart_4806133 := by decide
  rcases family_descends (prefixWord ++ tailWord_4806133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4806136 : List Nat := [2, 1, 2, 1, 1, 7, 1, 1, 2, 2, 3]
def baseStart_4806136 : Nat := 118140960795 + 4806136 * 2 ^ 59
def prefixEnd_4806136 : Nat := 4983230072969 + 3 ^ 40 * 4806136 * 2
def baseEnd_4806136 : Nat := 2467857858877313204496989

theorem tailTrace_4806136 : CollatzResearch.WordTrace tailWord_4806136 prefixEnd_4806136 2467857858877313204496989 := by
  unfold tailWord_4806136
  simp only [CollatzResearch.WordTrace]
  refine ⟨87647090458098784762439131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116862787277465046349918841 87647090458098784762439131)
  ·
    refine ⟨131470635687148177143658697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87647090458098784762439131 131470635687148177143658697)
    ·
      refine ⟨98602976765361132857744023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 131470635687148177143658697 98602976765361132857744023)
      ·
        refine ⟨147904465148041699286616035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98602976765361132857744023 147904465148041699286616035)
        ·
          refine ⟨221856697722062548929924053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 147904465148041699286616035 221856697722062548929924053)
          ·
            refine ⟨5199766352860840990545095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 221856697722062548929924053 5199766352860840990545095)
            ·
              refine ⟨7799649529291261485817643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5199766352860840990545095 7799649529291261485817643)
              ·
                refine ⟨11699474293936892228726465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7799649529291261485817643 11699474293936892228726465)
                ·
                  refine ⟨8774605720452669171544849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11699474293936892228726465 8774605720452669171544849)
                  ·
                    refine ⟨6580954290339501878658637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8774605720452669171544849 6580954290339501878658637)
                    ·
                      refine ⟨2467857858877313204496989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6580954290339501878658637 2467857858877313204496989)
                      ·
                        rfl

theorem cell23_4806136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 7, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 7, 1, 1, 2, 2, 3].length) (baseStart_4806136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4806136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4806136 prefixEnd_4806136 := by exact prefixLift 4806136
  have htrace : WordTrace (prefixWord ++ tailWord_4806136) baseStart_4806136 baseEnd_4806136 := by
    simpa [prefixWord, tailWord_4806136, baseEnd_4806136] using wordTrace_append hprefix tailTrace_4806136
  have hstable : (prefixWord ++ tailWord_4806136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4806136).length < 2 ^ (prefixWord ++ tailWord_4806136).sum := by decide
  have hdescent : baseEnd_4806136 < baseStart_4806136 := by decide
  rcases family_descends (prefixWord ++ tailWord_4806136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4806149 : List Nat := [1, 3, 1, 1, 2, 2, 1, 1, 7, 1, 3]
def baseStart_4806149 : Nat := 118140960795 + 4806149 * 2 ^ 59
def prefixEnd_4806149 : Nat := 4983230072969 + 3 ^ 40 * 4806149 * 2
def baseEnd_4806149 : Nat := 2467864534125821653634429

theorem tailTrace_4806149 : CollatzResearch.WordTrace tailWord_4806149 prefixEnd_4806149 2467864534125821653634429 := by
  unfold tailWord_4806149
  simp only [CollatzResearch.WordTrace]
  refine ⟨175294655065150472745101501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116863103376766981830067667 175294655065150472745101501)
  ·
    refine ⟨65735495649431427279413063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 175294655065150472745101501 65735495649431427279413063)
    ·
      refine ⟨98603243474147140919119595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65735495649431427279413063 98603243474147140919119595)
      ·
        refine ⟨147904865211220711378679393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98603243474147140919119595 147904865211220711378679393)
        ·
          refine ⟨110928648908415533534009545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 147904865211220711378679393 110928648908415533534009545)
          ·
            refine ⟨83196486681311650150507159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 110928648908415533534009545 83196486681311650150507159)
            ·
              refine ⟨124794730021967475225760739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83196486681311650150507159 124794730021967475225760739)
              ·
                refine ⟨187192095032951212838641109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 124794730021967475225760739 187192095032951212838641109)
                ·
                  refine ⟨4387314727334794050905651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 187192095032951212838641109 4387314727334794050905651)
                  ·
                    refine ⟨6580972091002191076358477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4387314727334794050905651 6580972091002191076358477)
                    ·
                      refine ⟨2467864534125821653634429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6580972091002191076358477 2467864534125821653634429)
                      ·
                        rfl

theorem cell23_4806149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 1, 7, 1, 3].length) (baseStart_4806149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4806149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4806149 prefixEnd_4806149 := by exact prefixLift 4806149
  have htrace : WordTrace (prefixWord ++ tailWord_4806149) baseStart_4806149 baseEnd_4806149 := by
    simpa [prefixWord, tailWord_4806149, baseEnd_4806149] using wordTrace_append hprefix tailTrace_4806149
  have hstable : (prefixWord ++ tailWord_4806149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4806149).length < 2 ^ (prefixWord ++ tailWord_4806149).sum := by decide
  have hdescent : baseEnd_4806149 < baseStart_4806149 := by decide
  rcases family_descends (prefixWord ++ tailWord_4806149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4806156 : List Nat := [2, 2, 1, 2, 5, 2, 1, 2, 6]
def baseStart_4806156 : Nat := 118140960795 + 4806156 * 2 ^ 59
def prefixEnd_4806156 : Nat := 4983230072969 + 3 ^ 40 * 4806156 * 2
def baseEnd_4806156 : Nat := 274207569832267014027433

theorem tailTrace_4806156 : CollatzResearch.WordTrace tailWord_4806156 prefixEnd_4806156 274207569832267014027433 := by
  unfold tailWord_4806156
  simp only [CollatzResearch.WordTrace]
  refine ⟨87647455188062556470303161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116863273584083408627070881 87647455188062556470303161)
  ·
    refine ⟨65735591391046917352727371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87647455188062556470303161 65735591391046917352727371)
    ·
      refine ⟨98603387086570376029091057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65735591391046917352727371 98603387086570376029091057)
      ·
        refine ⟨73952540314927782021818293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 98603387086570376029091057 73952540314927782021818293)
        ·
          refine ⟨6933050654524479564545465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 73952540314927782021818293 6933050654524479564545465)
          ·
            refine ⟨5199787990893359673409099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6933050654524479564545465 5199787990893359673409099)
            ·
              refine ⟨7799681986340039510113649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5199787990893359673409099 7799681986340039510113649)
              ·
                refine ⟨5849761489755029632585237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7799681986340039510113649 5849761489755029632585237)
                ·
                  refine ⟨274207569832267014027433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5849761489755029632585237 274207569832267014027433)
                  ·
                    rfl

theorem cell23_4806156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 2, 1, 2, 6].length) (baseStart_4806156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4806156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4806156 prefixEnd_4806156 := by exact prefixLift 4806156
  have htrace : WordTrace (prefixWord ++ tailWord_4806156) baseStart_4806156 baseEnd_4806156 := by
    simpa [prefixWord, tailWord_4806156, baseEnd_4806156] using wordTrace_append hprefix tailTrace_4806156
  have hstable : (prefixWord ++ tailWord_4806156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4806156).length < 2 ^ (prefixWord ++ tailWord_4806156).sum := by decide
  have hdescent : baseEnd_4806156 < baseStart_4806156 := by decide
  rcases family_descends (prefixWord ++ tailWord_4806156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4806176 : List Nat := [2, 1, 1, 6, 1, 1, 1, 2, 1, 5, 2]
def baseStart_4806176 : Nat := 118140960795 + 4806176 * 2 ^ 59
def prefixEnd_4806176 : Nat := 4983230072969 + 3 ^ 40 * 4806176 * 2
def baseEnd_4806176 : Nat := 2467878398103493047996805

theorem tailTrace_4806176 : CollatzResearch.WordTrace tailWord_4806176 prefixEnd_4806176 2467878398103493047996805 := by
  unfold tailWord_4806176
  simp only [CollatzResearch.WordTrace]
  refine ⟨87647819918026328178167191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116863759890701770904222921 87647819918026328178167191)
  ·
    refine ⟨131471729877039492267250787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87647819918026328178167191 131471729877039492267250787)
    ·
      refine ⟨197207594815559238400876181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131471729877039492267250787 197207594815559238400876181)
      ·
        refine ⟨9244106006979339300041071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 197207594815559238400876181 9244106006979339300041071)
        ·
          refine ⟨13866159010469008950061607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9244106006979339300041071 13866159010469008950061607)
          ·
            refine ⟨20799238515703513425092411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13866159010469008950061607 20799238515703513425092411)
            ·
              refine ⟨31198857773555270137638617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20799238515703513425092411 31198857773555270137638617)
              ·
                refine ⟨23399143330166452603228963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31198857773555270137638617 23399143330166452603228963)
                ·
                  refine ⟨35098714995249678904843445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23399143330166452603228963 35098714995249678904843445)
                  ·
                    refine ⟨3290504530804657397329073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 35098714995249678904843445 3290504530804657397329073)
                    ·
                      refine ⟨2467878398103493047996805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3290504530804657397329073 2467878398103493047996805)
                      ·
                        rfl

theorem cell23_4806176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 1, 2, 1, 5, 2].length) (baseStart_4806176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4806176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4806176 prefixEnd_4806176 := by exact prefixLift 4806176
  have htrace : WordTrace (prefixWord ++ tailWord_4806176) baseStart_4806176 baseEnd_4806176 := by
    simpa [prefixWord, tailWord_4806176, baseEnd_4806176] using wordTrace_append hprefix tailTrace_4806176
  have hstable : (prefixWord ++ tailWord_4806176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4806176).length < 2 ^ (prefixWord ++ tailWord_4806176).sum := by decide
  have hdescent : baseEnd_4806176 < baseStart_4806176 := by decide
  rcases family_descends (prefixWord ++ tailWord_4806176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4806186 : List Nat := [3, 1, 4, 1, 1, 1, 4, 2, 1, 5]
def baseStart_4806186 : Nat := 118140960795 + 4806186 * 2 ^ 59
def prefixEnd_4806186 : Nat := 4983230072969 + 3 ^ 40 * 4806186 * 2
def baseEnd_4806186 : Nat := 822627844303346002957253

theorem tailTrace_4806186 : CollatzResearch.WordTrace tailWord_4806186 prefixEnd_4806186 822627844303346002957253 := by
  unfold tailWord_4806186
  simp only [CollatzResearch.WordTrace]
  refine ⟨43824001141504107016049603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 116864003044010952042798941 43824001141504107016049603)
  ·
    refine ⟨65736001712256160524074405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43824001141504107016049603 65736001712256160524074405)
    ·
      refine ⟨12325500321048030098263951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 65736001712256160524074405 12325500321048030098263951)
      ·
        refine ⟨18488250481572045147395927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12325500321048030098263951 18488250481572045147395927)
        ·
          refine ⟨27732375722358067721093891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18488250481572045147395927 27732375722358067721093891)
          ·
            refine ⟨41598563583537101581640837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27732375722358067721093891 41598563583537101581640837)
            ·
              refine ⟨7799730671913206546557657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 41598563583537101581640837 7799730671913206546557657)
              ·
                refine ⟨5849798003934904909918243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7799730671913206546557657 5849798003934904909918243)
                ·
                  refine ⟨8774697005902357364877365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5849798003934904909918243 8774697005902357364877365)
                  ·
                    refine ⟨822627844303346002957253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8774697005902357364877365 822627844303346002957253)
                    ·
                      rfl

theorem cell23_4806186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 4, 2, 1, 5].length) (baseStart_4806186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4806186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4806186 prefixEnd_4806186 := by exact prefixLift 4806186
  have htrace : WordTrace (prefixWord ++ tailWord_4806186) baseStart_4806186 baseEnd_4806186 := by
    simpa [prefixWord, tailWord_4806186, baseEnd_4806186] using wordTrace_append hprefix tailTrace_4806186
  have hstable : (prefixWord ++ tailWord_4806186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4806186).length < 2 ^ (prefixWord ++ tailWord_4806186).sum := by decide
  have hdescent : baseEnd_4806186 < baseStart_4806186 := by decide
  rcases family_descends (prefixWord ++ tailWord_4806186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4806192 : List Nat := [2, 1, 1, 1, 2, 3, 1, 1, 5, 1, 5]
def baseStart_4806192 : Nat := 118140960795 + 4806192 * 2 ^ 59
def prefixEnd_4806192 : Nat := 4983230072969 + 3 ^ 40 * 4806192 * 2
def baseEnd_4806192 : Nat := 2467886613793964985396731

theorem tailTrace_4806192 : CollatzResearch.WordTrace tailWord_4806192 prefixEnd_4806192 2467886613793964985396731 := by
  unfold tailWord_4806192
  simp only [CollatzResearch.WordTrace]
  refine ⟨87648111701997345544458415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116864148935996460725944553 87648111701997345544458415)
  ·
    refine ⟨131472167552996018316687623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87648111701997345544458415 131472167552996018316687623)
    ·
      refine ⟨197208251329494027475031435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131472167552996018316687623 197208251329494027475031435)
      ·
        refine ⟨295812376994241041212547153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 197208251329494027475031435 295812376994241041212547153)
        ·
          refine ⟨221859282745680780909410365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 295812376994241041212547153 221859282745680780909410365)
          ·
            refine ⟨83197231029630292841028887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 221859282745680780909410365 83197231029630292841028887)
            ·
              refine ⟨124795846544445439261543331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83197231029630292841028887 124795846544445439261543331)
              ·
                refine ⟨187193769816668158892314997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 124795846544445439261543331 187193769816668158892314997)
                ·
                  refine ⟨17549415920312639896154531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 187193769816668158892314997 17549415920312639896154531)
                  ·
                    refine ⟨26324123880468959844231797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17549415920312639896154531 26324123880468959844231797)
                    ·
                      refine ⟨2467886613793964985396731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26324123880468959844231797 2467886613793964985396731)
                      ·
                        rfl

theorem cell23_4806192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 1, 5, 1, 5].length) (baseStart_4806192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4806192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4806192 prefixEnd_4806192 := by exact prefixLift 4806192
  have htrace : WordTrace (prefixWord ++ tailWord_4806192) baseStart_4806192 baseEnd_4806192 := by
    simpa [prefixWord, tailWord_4806192, baseEnd_4806192] using wordTrace_append hprefix tailTrace_4806192
  have hstable : (prefixWord ++ tailWord_4806192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4806192).length < 2 ^ (prefixWord ++ tailWord_4806192).sum := by decide
  have hdescent : baseEnd_4806192 < baseStart_4806192 := by decide
  rcases family_descends (prefixWord ++ tailWord_4806192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4806199 : List Nat := [1, 1, 3, 1, 2, 4, 1, 2, 4, 4]
def baseStart_4806199 : Nat := 118140960795 + 4806199 * 2 ^ 59
def prefixEnd_4806199 : Nat := 4983230072969 + 3 ^ 40 * 4806199 * 2
def baseEnd_4806199 : Nat := 822630069386182152669733

theorem tailTrace_4806199 : CollatzResearch.WordTrace tailWord_4806199 prefixEnd_4806199 822630069386182152669733 := by
  unfold tailWord_4806199
  simp only [CollatzResearch.WordTrace]
  refine ⟨175296478714969331284421651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116864319143312887522947767 175296478714969331284421651)
  ·
    refine ⟨262944718072453996926632477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175296478714969331284421651 262944718072453996926632477)
    ·
      refine ⟨98604269277170248847487179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 262944718072453996926632477 98604269277170248847487179)
      ·
        refine ⟨147906403915755373271230769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98604269277170248847487179 147906403915755373271230769)
        ·
          refine ⟨110929802936816529953423077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 147906403915755373271230769 110929802936816529953423077)
          ·
            refine ⟨20799338050653099366266827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 110929802936816529953423077 20799338050653099366266827)
            ·
              refine ⟨31199007075979649049400241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20799338050653099366266827 31199007075979649049400241)
              ·
                refine ⟨23399255306984736787050181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31199007075979649049400241 23399255306984736787050181)
                ·
                  refine ⟨4387360370059638147571909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23399255306984736787050181 4387360370059638147571909)
                  ·
                    refine ⟨822630069386182152669733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4387360370059638147571909 822630069386182152669733)
                    ·
                      rfl

theorem cell23_4806199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 1, 2, 4, 4].length) (baseStart_4806199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4806199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4806199 prefixEnd_4806199 := by exact prefixLift 4806199
  have htrace : WordTrace (prefixWord ++ tailWord_4806199) baseStart_4806199 baseEnd_4806199 := by
    simpa [prefixWord, tailWord_4806199, baseEnd_4806199] using wordTrace_append hprefix tailTrace_4806199
  have hstable : (prefixWord ++ tailWord_4806199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4806199).length < 2 ^ (prefixWord ++ tailWord_4806199).sum := by decide
  have hdescent : baseEnd_4806199 < baseStart_4806199 := by decide
  rcases family_descends (prefixWord ++ tailWord_4806199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4806200 : List Nat := [2, 1, 2, 1, 4, 4, 1, 3, 1, 1, 3]
def baseStart_4806200 : Nat := 118140960795 + 4806200 * 2 ^ 59
def prefixEnd_4806200 : Nat := 4983230072969 + 3 ^ 40 * 4806200 * 2
def baseEnd_4806200 : Nat := 2467890721639200954096695

theorem tailTrace_4806200 : CollatzResearch.WordTrace tailWord_4806200 prefixEnd_4806200 2467890721639200954096695 := by
  unfold tailWord_4806200
  simp only [CollatzResearch.WordTrace]
  refine ⟨87648257593982854227604027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116864343458643805636805369 87648257593982854227604027)
  ·
    refine ⟨131472386390974281341406041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87648257593982854227604027 131472386390974281341406041)
    ·
      refine ⟨98604289793230711006054531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 131472386390974281341406041 98604289793230711006054531)
      ·
        refine ⟨147906434689846066509081797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98604289793230711006054531 147906434689846066509081797)
        ·
          refine ⟨27732456504346137470452837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 147906434689846066509081797 27732456504346137470452837)
          ·
            refine ⟨5199835594564900775709907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27732456504346137470452837 5199835594564900775709907)
            ·
              refine ⟨7799753391847351163564861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5199835594564900775709907 7799753391847351163564861)
              ·
                refine ⟨2924907521942756686336823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7799753391847351163564861 2924907521942756686336823)
                ·
                  refine ⟨4387361282914135029505235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2924907521942756686336823 4387361282914135029505235)
                  ·
                    refine ⟨6581041924371202544257853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4387361282914135029505235 6581041924371202544257853)
                    ·
                      refine ⟨2467890721639200954096695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6581041924371202544257853 2467890721639200954096695)
                      ·
                        rfl

theorem cell23_4806200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 4, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 4, 1, 3, 1, 1, 3].length) (baseStart_4806200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4806200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4806200 prefixEnd_4806200 := by exact prefixLift 4806200
  have htrace : WordTrace (prefixWord ++ tailWord_4806200) baseStart_4806200 baseEnd_4806200 := by
    simpa [prefixWord, tailWord_4806200, baseEnd_4806200] using wordTrace_append hprefix tailTrace_4806200
  have hstable : (prefixWord ++ tailWord_4806200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4806200).length < 2 ^ (prefixWord ++ tailWord_4806200).sum := by decide
  have hdescent : baseEnd_4806200 < baseStart_4806200 := by decide
  rcases family_descends (prefixWord ++ tailWord_4806200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4806232 : List Nat := [2, 1, 2, 2, 1, 2, 1, 1, 1, 4, 6]
def baseStart_4806232 : Nat := 118140960795 + 4806232 * 2 ^ 59
def prefixEnd_4806232 : Nat := 4983230072969 + 3 ^ 40 * 4806232 * 2
def baseEnd_4806232 : Nat := 2467907153020144828896547

theorem tailTrace_4806232 : CollatzResearch.WordTrace tailWord_4806232 prefixEnd_4806232 2467907153020144828896547 := by
  unfold tailWord_4806232
  simp only [CollatzResearch.WordTrace]
  refine ⟨87648841161924888960186475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116865121549233185280248633 87648841161924888960186475)
  ·
    refine ⟨131473261742887333440279713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87648841161924888960186475 131473261742887333440279713)
    ·
      refine ⟨98604946307165500080209785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 131473261742887333440279713 98604946307165500080209785)
      ·
        refine ⟨73953709730374125060157339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 98604946307165500080209785 73953709730374125060157339)
        ·
          refine ⟨110930564595561187590236009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73953709730374125060157339 110930564595561187590236009)
          ·
            refine ⟨83197923446670890692677007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 110930564595561187590236009 83197923446670890692677007)
            ·
              refine ⟨124796885170006336039015511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83197923446670890692677007 124796885170006336039015511)
              ·
                refine ⟨187195327755009504058523267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 124796885170006336039015511 187195327755009504058523267)
                ·
                  refine ⟨280792991632514256087784901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 187195327755009504058523267 280792991632514256087784901)
                  ·
                    refine ⟨52648685931096423016459669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 280792991632514256087784901 52648685931096423016459669)
                    ·
                      refine ⟨2467907153020144828896547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 52648685931096423016459669 2467907153020144828896547)
                      ·
                        rfl

theorem cell23_4806232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 1, 1, 4, 6].length) (baseStart_4806232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4806232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4806232 prefixEnd_4806232 := by exact prefixLift 4806232
  have htrace : WordTrace (prefixWord ++ tailWord_4806232) baseStart_4806232 baseEnd_4806232 := by
    simpa [prefixWord, tailWord_4806232, baseEnd_4806232] using wordTrace_append hprefix tailTrace_4806232
  have hstable : (prefixWord ++ tailWord_4806232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4806232).length < 2 ^ (prefixWord ++ tailWord_4806232).sum := by decide
  have hdescent : baseEnd_4806232 < baseStart_4806232 := by decide
  rcases family_descends (prefixWord ++ tailWord_4806232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4806237 : List Nat := [1, 4, 4, 2, 2, 1, 1, 2, 1, 5]
def baseStart_4806237 : Nat := 118140960795 + 4806237 * 2 ^ 59
def prefixEnd_4806237 : Nat := 4983230072969 + 3 ^ 40 * 4806237 * 2
def baseEnd_4806237 : Nat := 822636573474472436444675

theorem tailTrace_4806237 : CollatzResearch.WordTrace tailWord_4806237 prefixEnd_4806237 822636573474472436444675 := by
  unfold tailWord_4806237
  simp only [CollatzResearch.WordTrace]
  refine ⟨175297864688831663774304965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116865243125887775849536643 175297864688831663774304965)
  ·
    refine ⟨32868349629155936957682181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 175297864688831663774304965 32868349629155936957682181)
    ·
      refine ⟨6162815555466738179565409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32868349629155936957682181 6162815555466738179565409)
      ·
        refine ⟨4622111666600053634674057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6162815555466738179565409 4622111666600053634674057)
        ·
          refine ⟨3466583749950040226005543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4622111666600053634674057 3466583749950040226005543)
          ·
            refine ⟨5199875624925060339008315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3466583749950040226005543 5199875624925060339008315)
            ·
              refine ⟨7799813437387590508512473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5199875624925060339008315 7799813437387590508512473)
              ·
                refine ⟨5849860078040692881384355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7799813437387590508512473 5849860078040692881384355)
                ·
                  refine ⟨8774790117061039322076533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5849860078040692881384355 8774790117061039322076533)
                  ·
                    refine ⟨822636573474472436444675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8774790117061039322076533 822636573474472436444675)
                    ·
                      rfl

theorem cell23_4806237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 2, 1, 1, 2, 1, 5].length) (baseStart_4806237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4806237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4806237 prefixEnd_4806237 := by exact prefixLift 4806237
  have htrace : WordTrace (prefixWord ++ tailWord_4806237) baseStart_4806237 baseEnd_4806237 := by
    simpa [prefixWord, tailWord_4806237, baseEnd_4806237] using wordTrace_append hprefix tailTrace_4806237
  have hstable : (prefixWord ++ tailWord_4806237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4806237).length < 2 ^ (prefixWord ++ tailWord_4806237).sum := by decide
  have hdescent : baseEnd_4806237 < baseStart_4806237 := by decide
  rcases family_descends (prefixWord ++ tailWord_4806237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4806243 : List Nat := [1, 1, 1, 5, 1, 5, 1, 2, 1, 2, 3]
def baseStart_4806243 : Nat := 118140960795 + 4806243 * 2 ^ 59
def prefixEnd_4806243 : Nat := 4983230072969 + 3 ^ 40 * 4806243 * 2
def baseEnd_4806243 : Nat := 2467912801307344285858997

theorem tailTrace_4806243 : CollatzResearch.WordTrace tailWord_4806243 prefixEnd_4806243 2467912801307344285858997 := by
  unfold tailWord_4806243
  simp only [CollatzResearch.WordTrace]
  refine ⟨175298083526809926799023383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116865389017873284532682255 175298083526809926799023383)
  ·
    refine ⟨262947125290214890198535075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175298083526809926799023383 262947125290214890198535075)
    ·
      refine ⟨394420687935322335297802613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 262947125290214890198535075 394420687935322335297802613)
      ·
        refine ⟨36976939493936468934168995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 394420687935322335297802613 36976939493936468934168995)
        ·
          refine ⟨55465409240904703401253493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36976939493936468934168995 55465409240904703401253493)
          ·
            refine ⟨5199882116334815943867515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 55465409240904703401253493 5199882116334815943867515)
            ·
              refine ⟨7799823174502223915801273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5199882116334815943867515 7799823174502223915801273)
              ·
                refine ⟨5849867380876667936850955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7799823174502223915801273 5849867380876667936850955)
                ·
                  refine ⟨8774801071315001905276433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5849867380876667936850955 8774801071315001905276433)
                  ·
                    refine ⟨6581100803486251428957325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8774801071315001905276433 6581100803486251428957325)
                    ·
                      refine ⟨2467912801307344285858997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6581100803486251428957325 2467912801307344285858997)
                      ·
                        rfl

theorem cell23_4806243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 5, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 5, 1, 2, 1, 2, 3].length) (baseStart_4806243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4806243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4806243 prefixEnd_4806243 := by exact prefixLift 4806243
  have htrace : WordTrace (prefixWord ++ tailWord_4806243) baseStart_4806243 baseEnd_4806243 := by
    simpa [prefixWord, tailWord_4806243, baseEnd_4806243] using wordTrace_append hprefix tailTrace_4806243
  have hstable : (prefixWord ++ tailWord_4806243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4806243).length < 2 ^ (prefixWord ++ tailWord_4806243).sum := by decide
  have hdescent : baseEnd_4806243 < baseStart_4806243 := by decide
  rcases family_descends (prefixWord ++ tailWord_4806243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4806256 : List Nat := [2, 1, 1, 1, 6, 2, 1, 2, 1, 3, 3]
def baseStart_4806256 : Nat := 118140960795 + 4806256 * 2 ^ 59
def prefixEnd_4806256 : Nat := 4983230072969 + 3 ^ 40 * 4806256 * 2
def baseEnd_4806256 : Nat := 2467919476555852734996437

theorem tailTrace_4806256 : CollatzResearch.WordTrace tailWord_4806256 prefixEnd_4806256 2467919476555852734996437 := by
  unfold tailWord_4806256
  simp only [CollatzResearch.WordTrace]
  refine ⟨87649278837881415009623311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116865705117175220012831081 87649278837881415009623311)
  ·
    refine ⟨131473918256822122514434967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87649278837881415009623311 131473918256822122514434967)
    ·
      refine ⟨197210877385233183771652451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131473918256822122514434967 197210877385233183771652451)
      ·
        refine ⟨295816316077849775657478677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 197210877385233183771652451 295816316077849775657478677)
        ·
          refine ⟨13866389816149208233944313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 295816316077849775657478677 13866389816149208233944313)
          ·
            refine ⟨10399792362111906175458235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13866389816149208233944313 10399792362111906175458235)
            ·
              refine ⟨15599688543167859263187353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10399792362111906175458235 15599688543167859263187353)
              ·
                refine ⟨11699766407375894447390515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15599688543167859263187353 11699766407375894447390515)
                ·
                  refine ⟨17549649611063841671085773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11699766407375894447390515 17549649611063841671085773)
                  ·
                    refine ⟨6581118604148940626657165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17549649611063841671085773 6581118604148940626657165)
                    ·
                      refine ⟨2467919476555852734996437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6581118604148940626657165 2467919476555852734996437)
                      ·
                        rfl

theorem cell23_4806256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 1, 2, 1, 3, 3].length) (baseStart_4806256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4806256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4806256 prefixEnd_4806256 := by exact prefixLift 4806256
  have htrace : WordTrace (prefixWord ++ tailWord_4806256) baseStart_4806256 baseEnd_4806256 := by
    simpa [prefixWord, tailWord_4806256, baseEnd_4806256] using wordTrace_append hprefix tailTrace_4806256
  have hstable : (prefixWord ++ tailWord_4806256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4806256).length < 2 ^ (prefixWord ++ tailWord_4806256).sum := by decide
  have hdescent : baseEnd_4806256 < baseStart_4806256 := by decide
  rcases family_descends (prefixWord ++ tailWord_4806256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4806273 : List Nat := [1, 2, 4, 2, 1, 2, 1, 4, 2, 1, 3]
def baseStart_4806273 : Nat := 118140960795 + 4806273 * 2 ^ 59
def prefixEnd_4806273 : Nat := 4983230072969 + 3 ^ 40 * 4806273 * 2
def baseEnd_4806273 : Nat := 2467928205726979168483859

theorem tailTrace_4806273 : CollatzResearch.WordTrace tailWord_4806273 prefixEnd_4806273 2467928205726979168483859 := by
  unfold tailWord_4806273
  simp only [CollatzResearch.WordTrace]
  refine ⟨175299177716701241922615473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116866118477800827948410315 175299177716701241922615473)
  ·
    refine ⟨131474383287525931441961605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 175299177716701241922615473 131474383287525931441961605)
    ·
      refine ⟨24651446866411112145367801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 131474383287525931441961605 24651446866411112145367801)
      ·
        refine ⟨18488585149808334109025851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24651446866411112145367801 18488585149808334109025851)
        ·
          refine ⟨27732877724712501163538777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18488585149808334109025851 27732877724712501163538777)
          ·
            refine ⟨20799658293534375872654083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27732877724712501163538777 20799658293534375872654083)
            ·
              refine ⟨31199487440301563808981125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20799658293534375872654083 31199487440301563808981125)
              ·
                refine ⟨5849903895056543214183961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31199487440301563808981125 5849903895056543214183961)
                ·
                  refine ⟨4387427921292407410637971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5849903895056543214183961 4387427921292407410637971)
                  ·
                    refine ⟨6581141881938611115956957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4387427921292407410637971 6581141881938611115956957)
                    ·
                      refine ⟨2467928205726979168483859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6581141881938611115956957 2467928205726979168483859)
                      ·
                        rfl

theorem cell23_4806273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 1, 4, 2, 1, 3].length) (baseStart_4806273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4806273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4806273 prefixEnd_4806273 := by exact prefixLift 4806273
  have htrace : WordTrace (prefixWord ++ tailWord_4806273) baseStart_4806273 baseEnd_4806273 := by
    simpa [prefixWord, tailWord_4806273, baseEnd_4806273] using wordTrace_append hprefix tailTrace_4806273
  have hstable : (prefixWord ++ tailWord_4806273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4806273).length < 2 ^ (prefixWord ++ tailWord_4806273).sum := by decide
  have hdescent : baseEnd_4806273 < baseStart_4806273 := by decide
  rcases family_descends (prefixWord ++ tailWord_4806273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4806279 : List Nat := [1, 1, 4, 2, 1, 3, 1, 1, 2, 3, 4]
def baseStart_4806279 : Nat := 118140960795 + 4806279 * 2 ^ 59
def prefixEnd_4806279 : Nat := 4983230072969 + 3 ^ 40 * 4806279 * 2
def baseEnd_4806279 : Nat := 2467931286610906145008831

theorem tailTrace_4806279 : CollatzResearch.WordTrace tailWord_4806279 prefixEnd_4806279 2467931286610906145008831 := by
  unfold tailWord_4806279
  simp only [CollatzResearch.WordTrace]
  refine ⟨175299396554679504947333891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116866264369786336631555927 175299396554679504947333891)
  ·
    refine ⟨262949094832019257421000837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175299396554679504947333891 262949094832019257421000837)
    ·
      refine ⟨49302955281003610766437657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 262949094832019257421000837 49302955281003610766437657)
      ·
        refine ⟨36977216460752708074828243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49302955281003610766437657 36977216460752708074828243)
        ·
          refine ⟨55465824691129062112242365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36977216460752708074828243 55465824691129062112242365)
          ·
            refine ⟨20799684259173398292090887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55465824691129062112242365 20799684259173398292090887)
            ·
              refine ⟨31199526388760097438136331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20799684259173398292090887 31199526388760097438136331)
              ·
                refine ⟨46799289583140146157204497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31199526388760097438136331 46799289583140146157204497)
                ·
                  refine ⟨35099467187355109617903373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 46799289583140146157204497 35099467187355109617903373)
                  ·
                    refine ⟨13162300195258166106713765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 35099467187355109617903373 13162300195258166106713765)
                    ·
                      refine ⟨2467931286610906145008831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13162300195258166106713765 2467931286610906145008831)
                      ·
                        rfl

theorem cell23_4806279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 1, 1, 2, 3, 4].length) (baseStart_4806279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4806279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4806279 prefixEnd_4806279 := by exact prefixLift 4806279
  have htrace : WordTrace (prefixWord ++ tailWord_4806279) baseStart_4806279 baseEnd_4806279 := by
    simpa [prefixWord, tailWord_4806279, baseEnd_4806279] using wordTrace_append hprefix tailTrace_4806279
  have hstable : (prefixWord ++ tailWord_4806279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4806279).length < 2 ^ (prefixWord ++ tailWord_4806279).sum := by decide
  have hdescent : baseEnd_4806279 < baseStart_4806279 := by decide
  rcases family_descends (prefixWord ++ tailWord_4806279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4806330 : List Nat := [3, 1, 1, 1, 2, 4, 3, 2, 2, 2, 2]
def baseStart_4806330 : Nat := 118140960795 + 4806330 * 2 ^ 59
def prefixEnd_4806330 : Nat := 4983230072969 + 3 ^ 40 * 4806330 * 2
def baseEnd_4806330 : Nat := 2467957474124285445471097

theorem tailTrace_4806330 : CollatzResearch.WordTrace tailWord_4806330 prefixEnd_4806330 2467957474124285445471097 := by
  unfold tailWord_4806330
  simp only [CollatzResearch.WordTrace]
  refine ⟨43825314169373685164360111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 116867504451663160438293629 43825314169373685164360111)
  ·
    refine ⟨65737971254060527746540167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43825314169373685164360111 65737971254060527746540167)
    ·
      refine ⟨98606956881090791619810251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65737971254060527746540167 98606956881090791619810251)
      ·
        refine ⟨147910435321636187429715377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98606956881090791619810251 147910435321636187429715377)
        ·
          refine ⟨110932826491227140572286533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 147910435321636187429715377 110932826491227140572286533)
          ·
            refine ⟨20799904967105088857303725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 110932826491227140572286533 20799904967105088857303725)
            ·
              refine ⟨7799964362664408321488897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20799904967105088857303725 7799964362664408321488897)
              ·
                refine ⟨5849973271998306241116673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7799964362664408321488897 5849973271998306241116673)
                ·
                  refine ⟨4387479953998729680837505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5849973271998306241116673 4387479953998729680837505)
                  ·
                    refine ⟨3290609965499047260628129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4387479953998729680837505 3290609965499047260628129)
                    ·
                      refine ⟨2467957474124285445471097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3290609965499047260628129 2467957474124285445471097)
                      ·
                        rfl

theorem cell23_4806330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 3, 2, 2, 2, 2].length) (baseStart_4806330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4806330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4806330 prefixEnd_4806330 := by exact prefixLift 4806330
  have htrace : WordTrace (prefixWord ++ tailWord_4806330) baseStart_4806330 baseEnd_4806330 := by
    simpa [prefixWord, tailWord_4806330, baseEnd_4806330] using wordTrace_append hprefix tailTrace_4806330
  have hstable : (prefixWord ++ tailWord_4806330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4806330).length < 2 ^ (prefixWord ++ tailWord_4806330).sum := by decide
  have hdescent : baseEnd_4806330 < baseStart_4806330 := by decide
  rcases family_descends (prefixWord ++ tailWord_4806330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4806336 : List Nat := [2, 1, 1, 2, 4, 1, 1, 6, 5]
def baseStart_4806336 : Nat := 118140960795 + 4806336 * 2 ^ 59
def prefixEnd_4806336 : Nat := 4983230072969 + 3 ^ 40 * 4806336 * 2
def baseEnd_4806336 : Nat := 274217839445356935777341

theorem tailTrace_4806336 : CollatzResearch.WordTrace tailWord_4806336 prefixEnd_4806336 274217839445356935777341 := by
  unfold tailWord_4806336
  simp only [CollatzResearch.WordTrace]
  refine ⟨87650737757736501841079431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116867650343648669121439241 87650737757736501841079431)
  ·
    refine ⟨131476106636604752761619147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87650737757736501841079431 131476106636604752761619147)
    ·
      refine ⟨197214159954907129142428721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131476106636604752761619147 197214159954907129142428721)
      ·
        refine ⟨147910619966180346856821541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 197214159954907129142428721 147910619966180346856821541)
        ·
          refine ⟨27733241243658815035654039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 147910619966180346856821541 27733241243658815035654039)
          ·
            refine ⟨41599861865488222553481059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27733241243658815035654039 41599861865488222553481059)
            ·
              refine ⟨62399792798232333830221589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41599861865488222553481059 62399792798232333830221589)
              ·
                refine ⟨2924990287417140648291637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 62399792798232333830221589 2924990287417140648291637)
                ·
                  refine ⟨274217839445356935777341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2924990287417140648291637 274217839445356935777341)
                  ·
                    rfl

theorem cell23_4806336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 6, 5].length) (baseStart_4806336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4806336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4806336 prefixEnd_4806336 := by exact prefixLift 4806336
  have htrace : WordTrace (prefixWord ++ tailWord_4806336) baseStart_4806336 baseEnd_4806336 := by
    simpa [prefixWord, tailWord_4806336, baseEnd_4806336] using wordTrace_append hprefix tailTrace_4806336
  have hstable : (prefixWord ++ tailWord_4806336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4806336).length < 2 ^ (prefixWord ++ tailWord_4806336).sum := by decide
  have hdescent : baseEnd_4806336 < baseStart_4806336 := by decide
  rcases family_descends (prefixWord ++ tailWord_4806336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4806399 : List Nat := [1, 1, 2, 2, 1, 3, 2, 2, 2, 1, 6]
def baseStart_4806399 : Nat := 118140960795 + 4806399 * 2 ^ 59
def prefixEnd_4806399 : Nat := 4983230072969 + 3 ^ 40 * 4806399 * 2
def baseEnd_4806399 : Nat := 2467992904289445675508279

theorem tailTrace_4806399 : CollatzResearch.WordTrace tailWord_4806399 prefixEnd_4806399 2467992904289445675508279 := by
  unfold tailWord_4806399
  simp only [CollatzResearch.WordTrace]
  refine ⟨175303773314244765441702251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116869182209496510294468167 175303773314244765441702251)
  ·
    refine ⟨262955659971367148162553377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175303773314244765441702251 262955659971367148162553377)
    ·
      refine ⟨197216744978525361121915033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 262955659971367148162553377 197216744978525361121915033)
      ·
        refine ⟨147912558733894020841436275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 197216744978525361121915033 147912558733894020841436275)
        ·
          refine ⟨221868838100841031262154413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 147912558733894020841436275 221868838100841031262154413)
          ·
            refine ⟨83200814287815386723307905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 221868838100841031262154413 83200814287815386723307905)
            ·
              refine ⟨62400610715861540042480929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 83200814287815386723307905 62400610715861540042480929)
              ·
                refine ⟨46800458036896155031860697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 62400610715861540042480929 46800458036896155031860697)
                ·
                  refine ⟨35100343527672116273895523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 46800458036896155031860697 35100343527672116273895523)
                  ·
                    refine ⟨52650515291508174410843285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 35100343527672116273895523 52650515291508174410843285)
                    ·
                      refine ⟨2467992904289445675508279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 52650515291508174410843285 2467992904289445675508279)
                      ·
                        rfl

theorem cell23_4806399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 2, 2, 1, 6].length) (baseStart_4806399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4806399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4806399 prefixEnd_4806399 := by exact prefixLift 4806399
  have htrace : WordTrace (prefixWord ++ tailWord_4806399) baseStart_4806399 baseEnd_4806399 := by
    simpa [prefixWord, tailWord_4806399, baseEnd_4806399] using wordTrace_append hprefix tailTrace_4806399
  have hstable : (prefixWord ++ tailWord_4806399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4806399).length < 2 ^ (prefixWord ++ tailWord_4806399).sum := by decide
  have hdescent : baseEnd_4806399 < baseStart_4806399 := by decide
  rcases family_descends (prefixWord ++ tailWord_4806399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4806423 : List Nat := [1, 1, 3, 4, 2, 1, 1, 3, 2, 2, 3]
def baseStart_4806423 : Nat := 118140960795 + 4806423 * 2 ^ 59
def prefixEnd_4806423 : Nat := 4983230072969 + 3 ^ 40 * 4806423 * 2
def baseEnd_4806423 : Nat := 2468005227825153581608169

theorem tailTrace_4806423 : CollatzResearch.WordTrace tailWord_4806423 prefixEnd_4806423 2468005227825153581608169 := by
  unfold tailWord_4806423
  simp only [CollatzResearch.WordTrace]
  refine ⟨175304648666157817540575923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116869765777438545027050615 175304648666157817540575923)
  ·
    refine ⟨262956972999236726310863885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175304648666157817540575923 262956972999236726310863885)
    ·
      refine ⟨98608864874713772366573957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 262956972999236726310863885 98608864874713772366573957)
      ·
        refine ⟨18489162164008832318732617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 98608864874713772366573957 18489162164008832318732617)
        ·
          refine ⟨13866871623006624239049463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18489162164008832318732617 13866871623006624239049463)
          ·
            refine ⟨20800307434509936358574195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13866871623006624239049463 20800307434509936358574195)
            ·
              refine ⟨31200461151764904537861293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20800307434509936358574195 31200461151764904537861293)
              ·
                refine ⟨11700172931911839201697985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31200461151764904537861293 11700172931911839201697985)
                ·
                  refine ⟨8775129698933879401273489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11700172931911839201697985 8775129698933879401273489)
                  ·
                    refine ⟨6581347274200409550955117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8775129698933879401273489 6581347274200409550955117)
                    ·
                      refine ⟨2468005227825153581608169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6581347274200409550955117 2468005227825153581608169)
                      ·
                        rfl

theorem cell23_4806423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 1, 3, 2, 2, 3].length) (baseStart_4806423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4806423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4806423 prefixEnd_4806423 := by exact prefixLift 4806423
  have htrace : WordTrace (prefixWord ++ tailWord_4806423) baseStart_4806423 baseEnd_4806423 := by
    simpa [prefixWord, tailWord_4806423, baseEnd_4806423] using wordTrace_append hprefix tailTrace_4806423
  have hstable : (prefixWord ++ tailWord_4806423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4806423).length < 2 ^ (prefixWord ++ tailWord_4806423).sum := by decide
  have hdescent : baseEnd_4806423 < baseStart_4806423 := by decide
  rcases family_descends (prefixWord ++ tailWord_4806423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4806456 : List Nat := [2, 1, 2, 1, 3, 3, 1, 2, 3, 5]
def baseStart_4806456 : Nat := 118140960795 + 4806456 * 2 ^ 59
def prefixEnd_4806456 : Nat := 4983230072969 + 3 ^ 40 * 4806456 * 2
def baseEnd_4806456 : Nat := 822674057562250650831839

theorem tailTrace_4806456 : CollatzResearch.WordTrace tailWord_4806456 prefixEnd_4806456 822674057562250650831839 := by
  unfold tailWord_4806456
  simp only [CollatzResearch.WordTrace]
  refine ⟨87652926137519132088263611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116870568183358842784351481 87652926137519132088263611)
  ·
    refine ⟨131479389206278698132395417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87652926137519132088263611 131479389206278698132395417)
    ·
      refine ⟨98609541904709023599296563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 131479389206278698132395417 98609541904709023599296563)
      ·
        refine ⟨147914312857063535398944845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98609541904709023599296563 147914312857063535398944845)
        ·
          refine ⟨55467867321398825774604317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 147914312857063535398944845 55467867321398825774604317)
          ·
            refine ⟨20800450245524559665476619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55467867321398825774604317 20800450245524559665476619)
            ·
              refine ⟨31200675368286839498214929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20800450245524559665476619 31200675368286839498214929)
              ·
                refine ⟨23400506526215129623661197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31200675368286839498214929 23400506526215129623661197)
                ·
                  refine ⟨8775189947330673608872949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23400506526215129623661197 8775189947330673608872949)
                  ·
                    refine ⟨822674057562250650831839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8775189947330673608872949 822674057562250650831839)
                    ·
                      rfl

theorem cell23_4806456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 1, 2, 3, 5].length) (baseStart_4806456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4806456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4806456 prefixEnd_4806456 := by exact prefixLift 4806456
  have htrace : WordTrace (prefixWord ++ tailWord_4806456) baseStart_4806456 baseEnd_4806456 := by
    simpa [prefixWord, tailWord_4806456, baseEnd_4806456] using wordTrace_append hprefix tailTrace_4806456
  have hstable : (prefixWord ++ tailWord_4806456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4806456).length < 2 ^ (prefixWord ++ tailWord_4806456).sum := by decide
  have hdescent : baseEnd_4806456 < baseStart_4806456 := by decide
  rcases family_descends (prefixWord ++ tailWord_4806456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4806503 : List Nat := [1, 1, 5, 1, 2, 1, 3, 1, 4, 4]
def baseStart_4806503 : Nat := 118140960795 + 4806503 * 2 ^ 59
def prefixEnd_4806503 : Nat := 4983230072969 + 3 ^ 40 * 4806503 * 2
def baseEnd_4806503 : Nat := 822682102092504422869267

theorem tailTrace_4806503 : CollatzResearch.WordTrace tailWord_4806503 prefixEnd_4806503 822682102092504422869267 := by
  unfold tailWord_4806503
  simp only [CollatzResearch.WordTrace]
  refine ⟨175307566505867991203488163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116871711003911994135658775 175307566505867991203488163)
  ·
    refine ⟨262961349758801986805232245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175307566505867991203488163 262961349758801986805232245)
    ·
      refine ⟨24652626539887686262990523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 262961349758801986805232245 24652626539887686262990523)
      ·
        refine ⟨36978939809831529394485785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24652626539887686262990523 36978939809831529394485785)
        ·
          refine ⟨27734204857373647045864339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36978939809831529394485785 27734204857373647045864339)
          ·
            refine ⟨41601307286060470568796509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27734204857373647045864339 41601307286060470568796509)
            ·
              refine ⟨15600490232272676463298691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41601307286060470568796509 15600490232272676463298691)
              ·
                refine ⟨23400735348409014694948037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15600490232272676463298691 23400735348409014694948037)
                ·
                  refine ⟨4387637877826690255302757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23400735348409014694948037 4387637877826690255302757)
                  ·
                    refine ⟨822682102092504422869267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4387637877826690255302757 822682102092504422869267)
                    ·
                      rfl

theorem cell23_4806503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 3, 1, 4, 4].length) (baseStart_4806503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4806503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4806503 prefixEnd_4806503 := by exact prefixLift 4806503
  have htrace : WordTrace (prefixWord ++ tailWord_4806503) baseStart_4806503 baseEnd_4806503 := by
    simpa [prefixWord, tailWord_4806503, baseEnd_4806503] using wordTrace_append hprefix tailTrace_4806503
  have hstable : (prefixWord ++ tailWord_4806503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4806503).length < 2 ^ (prefixWord ++ tailWord_4806503).sum := by decide
  have hdescent : baseEnd_4806503 < baseStart_4806503 := by decide
  rcases family_descends (prefixWord ++ tailWord_4806503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4806560 : List Nat := [2, 1, 1, 4, 1, 1, 1, 6, 2, 1, 3]
def baseStart_4806560 : Nat := 118140960795 + 4806560 * 2 ^ 59
def prefixEnd_4806560 : Nat := 4983230072969 + 3 ^ 40 * 4806560 * 2
def baseEnd_4806560 : Nat := 2468075574674819545595039

theorem tailTrace_4806560 : CollatzResearch.WordTrace tailWord_4806560 prefixEnd_4806560 2468075574674819545595039 := by
  unfold tailWord_4806560
  simp only [CollatzResearch.WordTrace]
  refine ⟨87654822733330744969156567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116873096977774326625542089 87654822733330744969156567)
  ·
    refine ⟨131482234099996117453734851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87654822733330744969156567 131482234099996117453734851)
    ·
      refine ⟨197223351149994176180602277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131482234099996117453734851 197223351149994176180602277)
      ·
        refine ⟨36979378340623908033862927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 197223351149994176180602277 36979378340623908033862927)
        ·
          refine ⟨55469067510935862050794391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36979378340623908033862927 55469067510935862050794391)
          ·
            refine ⟨83203601266403793076191587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55469067510935862050794391 83203601266403793076191587)
            ·
              refine ⟨124805401899605689614287381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83203601266403793076191587 124805401899605689614287381)
              ·
                refine ⟨5850253214044016700669721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 124805401899605689614287381 5850253214044016700669721)
                ·
                  refine ⟨4387689910533012525502291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5850253214044016700669721 4387689910533012525502291)
                  ·
                    refine ⟨6581534865799518788253437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4387689910533012525502291 6581534865799518788253437)
                    ·
                      refine ⟨2468075574674819545595039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6581534865799518788253437 2468075574674819545595039)
                      ·
                        rfl

theorem cell23_4806560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 6, 2, 1, 3].length) (baseStart_4806560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4806560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4806560 prefixEnd_4806560 := by exact prefixLift 4806560
  have htrace : WordTrace (prefixWord ++ tailWord_4806560) baseStart_4806560 baseEnd_4806560 := by
    simpa [prefixWord, tailWord_4806560, baseEnd_4806560] using wordTrace_append hprefix tailTrace_4806560
  have hstable : (prefixWord ++ tailWord_4806560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4806560).length < 2 ^ (prefixWord ++ tailWord_4806560).sum := by decide
  have hdescent : baseEnd_4806560 < baseStart_4806560 := by decide
  rcases family_descends (prefixWord ++ tailWord_4806560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4806561 : List Nat := [1, 2, 3, 4, 3, 1, 1, 1, 3, 2, 2]
def baseStart_4806561 : Nat := 118140960795 + 4806561 * 2 ^ 59
def prefixEnd_4806561 : Nat := 4983230072969 + 3 ^ 40 * 4806561 * 2
def baseEnd_4806561 : Nat := 2468076088155474041682535

theorem tailTrace_4806561 : CollatzResearch.WordTrace tailWord_4806561 prefixEnd_4806561 2468076088155474041682535 := by
  unfold tailWord_4806561
  simp only [CollatzResearch.WordTrace]
  refine ⟨175309681939657867109099537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116873121293105244739399691 175309681939657867109099537)
  ·
    refine ⟨131482261454743400331824653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 175309681939657867109099537 131482261454743400331824653)
    ·
      refine ⟨49305848045528775124434245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 131482261454743400331824653 49305848045528775124434245)
      ·
        refine ⟨9244846508536645335831421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 49305848045528775124434245 9244846508536645335831421)
        ·
          refine ⟨3466817440701242000936783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9244846508536645335831421 3466817440701242000936783)
          ·
            refine ⟨5200226161051863001405175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3466817440701242000936783 5200226161051863001405175)
            ·
              refine ⟨7800339241577794502107763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5200226161051863001405175 7800339241577794502107763)
              ·
                refine ⟨11700508862366691753161645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7800339241577794502107763 11700508862366691753161645)
                ·
                  refine ⟨4387690823387509407435617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11700508862366691753161645 4387690823387509407435617)
                  ·
                    refine ⟨3290768117540632055576713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4387690823387509407435617 3290768117540632055576713)
                    ·
                      refine ⟨2468076088155474041682535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3290768117540632055576713 2468076088155474041682535)
                      ·
                        rfl

theorem cell23_4806561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 3, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 3, 1, 1, 1, 3, 2, 2].length) (baseStart_4806561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4806561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4806561 prefixEnd_4806561 := by exact prefixLift 4806561
  have htrace : WordTrace (prefixWord ++ tailWord_4806561) baseStart_4806561 baseEnd_4806561 := by
    simpa [prefixWord, tailWord_4806561, baseEnd_4806561] using wordTrace_append hprefix tailTrace_4806561
  have hstable : (prefixWord ++ tailWord_4806561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4806561).length < 2 ^ (prefixWord ++ tailWord_4806561).sum := by decide
  have hdescent : baseEnd_4806561 < baseStart_4806561 := by decide
  rcases family_descends (prefixWord ++ tailWord_4806561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4806577 : List Nat := [1, 2, 2, 4, 2, 2, 1, 3, 2, 1, 3]
def baseStart_4806577 : Nat := 118140960795 + 4806577 * 2 ^ 59
def prefixEnd_4806577 : Nat := 4983230072969 + 3 ^ 40 * 4806577 * 2
def baseEnd_4806577 : Nat := 2468084303845945979082461

theorem tailTrace_4806577 : CollatzResearch.WordTrace tailWord_4806577 prefixEnd_4806577 2468084303845945979082461 := by
  unfold tailWord_4806577
  simp only [CollatzResearch.WordTrace]
  refine ⟨175310265507599901841681985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116873510338399934561121323 175310265507599901841681985)
  ·
    refine ⟨131482699130699926381261489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 175310265507599901841681985 131482699130699926381261489)
    ·
      refine ⟨98612024348024944785946117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 131482699130699926381261489 98612024348024944785946117)
      ·
        refine ⟨18489754565254677147364897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 98612024348024944785946117 18489754565254677147364897)
        ·
          refine ⟨13867315923941007860523673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18489754565254677147364897 13867315923941007860523673)
          ·
            refine ⟨10400486942955755895392755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13867315923941007860523673 10400486942955755895392755)
            ·
              refine ⟨15600730414433633843089133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10400486942955755895392755 15600730414433633843089133)
              ·
                refine ⟨5850273905412612691158425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15600730414433633843089133 5850273905412612691158425)
                ·
                  refine ⟨4387705429059459518368819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5850273905412612691158425 4387705429059459518368819)
                  ·
                    refine ⟨6581558143589189277553229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4387705429059459518368819 6581558143589189277553229)
                    ·
                      refine ⟨2468084303845945979082461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6581558143589189277553229 2468084303845945979082461)
                      ·
                        rfl

theorem cell23_4806577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 1, 3, 2, 1, 3].length) (baseStart_4806577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4806577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4806577 prefixEnd_4806577 := by exact prefixLift 4806577
  have htrace : WordTrace (prefixWord ++ tailWord_4806577) baseStart_4806577 baseEnd_4806577 := by
    simpa [prefixWord, tailWord_4806577, baseEnd_4806577] using wordTrace_append hprefix tailTrace_4806577
  have hstable : (prefixWord ++ tailWord_4806577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4806577).length < 2 ^ (prefixWord ++ tailWord_4806577).sum := by decide
  have hdescent : baseEnd_4806577 < baseStart_4806577 := by decide
  rcases family_descends (prefixWord ++ tailWord_4806577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4806600 : List Nat := [2, 1, 3, 1, 4, 1, 1, 1, 3, 4, 2]
def baseStart_4806600 : Nat := 118140960795 + 4806600 * 2 ^ 59
def prefixEnd_4806600 : Nat := 4983230072969 + 3 ^ 40 * 4806600 * 2
def baseEnd_4806600 : Nat := 2468096113900999389094855

theorem tailTrace_4806600 : CollatzResearch.WordTrace tailWord_4806600 prefixEnd_4806600 2468096113900999389094855 := by
  unfold tailWord_4806600
  simp only [CollatzResearch.WordTrace]
  refine ⟨87655552193258288384884627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116874069591011051179846169 87655552193258288384884627)
  ·
    refine ⟨131483328289887432577326941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87655552193258288384884627 131483328289887432577326941)
    ·
      refine ⟨49306248108707787216497603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 131483328289887432577326941 49306248108707787216497603)
      ·
        refine ⟨73959372163061680824746405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49306248108707787216497603 73959372163061680824746405)
        ·
          refine ⟨13867382280574065154639951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 73959372163061680824746405 13867382280574065154639951)
          ·
            refine ⟨20801073420861097731959927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13867382280574065154639951 20801073420861097731959927)
            ·
              refine ⟨31201610131291646597939891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20801073420861097731959927 31201610131291646597939891)
              ·
                refine ⟨46802415196937469896909837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31201610131291646597939891 46802415196937469896909837)
                ·
                  refine ⟨17550905698851551211341189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 46802415196937469896909837 17550905698851551211341189)
                  ·
                    refine ⟨3290794818534665852126473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17550905698851551211341189 3290794818534665852126473)
                    ·
                      refine ⟨2468096113900999389094855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3290794818534665852126473 2468096113900999389094855)
                      ·
                        rfl

theorem cell23_4806600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 1, 1, 3, 4, 2].length) (baseStart_4806600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4806600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4806600 prefixEnd_4806600 := by exact prefixLift 4806600
  have htrace : WordTrace (prefixWord ++ tailWord_4806600) baseStart_4806600 baseEnd_4806600 := by
    simpa [prefixWord, tailWord_4806600, baseEnd_4806600] using wordTrace_append hprefix tailTrace_4806600
  have hstable : (prefixWord ++ tailWord_4806600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4806600).length < 2 ^ (prefixWord ++ tailWord_4806600).sum := by decide
  have hdescent : baseEnd_4806600 < baseStart_4806600 := by decide
  rcases family_descends (prefixWord ++ tailWord_4806600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4806604 : List Nat := [2, 2, 1, 4, 1, 3, 3, 1, 1, 3, 2]
def baseStart_4806604 : Nat := 118140960795 + 4806604 * 2 ^ 59
def prefixEnd_4806604 : Nat := 4983230072969 + 3 ^ 40 * 4806604 * 2
def baseEnd_4806604 : Nat := 2468098167823617373444837

theorem tailTrace_4806604 : CollatzResearch.WordTrace tailWord_4806604 prefixEnd_4806604 2468098167823617373444837 := by
  unfold tailWord_4806604
  simp only [CollatzResearch.WordTrace]
  refine ⟨87655625139251042726457433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116874166852334723635276577 87655625139251042726457433)
  ·
    refine ⟨65741718854438282044843075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87655625139251042726457433 65741718854438282044843075)
    ·
      refine ⟨98612578281657423067264613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65741718854438282044843075 98612578281657423067264613)
      ·
        refine ⟨18489858427810766825112115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 98612578281657423067264613 18489858427810766825112115)
        ·
          refine ⟨27734787641716150237668173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18489858427810766825112115 27734787641716150237668173)
          ·
            refine ⟨10400545365643556339125565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27734787641716150237668173 10400545365643556339125565)
            ·
              refine ⟨3900204512116333627172087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10400545365643556339125565 3900204512116333627172087)
              ·
                refine ⟨5850306768174500440758131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3900204512116333627172087 5850306768174500440758131)
                ·
                  refine ⟨8775460152261750661137197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5850306768174500440758131 8775460152261750661137197)
                  ·
                    refine ⟨3290797557098156497926449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8775460152261750661137197 3290797557098156497926449)
                    ·
                      refine ⟨2468098167823617373444837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3290797557098156497926449 2468098167823617373444837)
                      ·
                        rfl

theorem cell23_4806604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 3, 1, 1, 3, 2].length) (baseStart_4806604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4806604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4806604 prefixEnd_4806604 := by exact prefixLift 4806604
  have htrace : WordTrace (prefixWord ++ tailWord_4806604) baseStart_4806604 baseEnd_4806604 := by
    simpa [prefixWord, tailWord_4806604, baseEnd_4806604] using wordTrace_append hprefix tailTrace_4806604
  have hstable : (prefixWord ++ tailWord_4806604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4806604).length < 2 ^ (prefixWord ++ tailWord_4806604).sum := by decide
  have hdescent : baseEnd_4806604 < baseStart_4806604 := by decide
  rcases family_descends (prefixWord ++ tailWord_4806604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4806662 : List Nat := [6, 2, 1, 2, 2, 1, 1, 2, 2, 1, 3]
def baseStart_4806662 : Nat := 118140960795 + 4806662 * 2 ^ 59
def prefixEnd_4806662 : Nat := 4983230072969 + 3 ^ 40 * 4806662 * 2
def baseEnd_4806662 : Nat := 2468127949701578146519571

theorem tailTrace_4806662 : CollatzResearch.WordTrace tailWord_4806662 prefixEnd_4806662 2468127949701578146519571 := by
  unfold tailWord_4806662
  simp only [CollatzResearch.WordTrace]
  refine ⟨5478542678509123792453945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 116875577141527974239017493 5478542678509123792453945)
  ·
    refine ⟨4108907008881842844340459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5478542678509123792453945 4108907008881842844340459)
    ·
      refine ⟨6163360513322764266510689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4108907008881842844340459 6163360513322764266510689)
      ·
        refine ⟨4622520384992073199883017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6163360513322764266510689 4622520384992073199883017)
        ·
          refine ⟨3466890288744054899912263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4622520384992073199883017 3466890288744054899912263)
          ·
            refine ⟨5200335433116082349868395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3466890288744054899912263 5200335433116082349868395)
            ·
              refine ⟨7800503149674123524802593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5200335433116082349868395 7800503149674123524802593)
              ·
                refine ⟨5850377362255592643601945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7800503149674123524802593 5850377362255592643601945)
                ·
                  refine ⟨4387783021691694482701459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5850377362255592643601945 4387783021691694482701459)
                  ·
                    refine ⟨6581674532537541724052189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4387783021691694482701459 6581674532537541724052189)
                    ·
                      refine ⟨2468127949701578146519571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6581674532537541724052189 2468127949701578146519571)
                      ·
                        rfl

theorem cell23_4806662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 2, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 2, 1, 1, 2, 2, 1, 3].length) (baseStart_4806662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4806662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4806662 prefixEnd_4806662 := by exact prefixLift 4806662
  have htrace : WordTrace (prefixWord ++ tailWord_4806662) baseStart_4806662 baseEnd_4806662 := by
    simpa [prefixWord, tailWord_4806662, baseEnd_4806662] using wordTrace_append hprefix tailTrace_4806662
  have hstable : (prefixWord ++ tailWord_4806662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4806662).length < 2 ^ (prefixWord ++ tailWord_4806662).sum := by decide
  have hdescent : baseEnd_4806662 < baseStart_4806662 := by decide
  rcases family_descends (prefixWord ++ tailWord_4806662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4806767 : List Nat := [1, 1, 2, 1, 3, 4, 1, 3, 2, 3, 2]
def baseStart_4806767 : Nat := 118140960795 + 4806767 * 2 ^ 59
def prefixEnd_4806767 : Nat := 4983230072969 + 3 ^ 40 * 4806767 * 2
def baseEnd_4806767 : Nat := 2468181865170300235706587

theorem tailTrace_4806767 : CollatzResearch.WordTrace tailWord_4806767 prefixEnd_4806767 2468181865170300235706587 := by
  unfold tailWord_4806767
  simp only [CollatzResearch.WordTrace]
  refine ⟨175317195376911564291098555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116878130251274376194065703 175317195376911564291098555)
  ·
    refine ⟨262975793065367346436647833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175317195376911564291098555 262975793065367346436647833)
    ·
      refine ⟨197231844799025509827485875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 262975793065367346436647833 197231844799025509827485875)
      ·
        refine ⟨295847767198538264741228813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 197231844799025509827485875 295847767198538264741228813)
        ·
          refine ⟨110942912699451849277960805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 295847767198538264741228813 110942912699451849277960805)
          ·
            refine ⟨20801796131147221739617651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 110942912699451849277960805 20801796131147221739617651)
            ·
              refine ⟨31202694196720832609426477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20801796131147221739617651 31202694196720832609426477)
              ·
                refine ⟨11701010323770312228534929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31202694196720832609426477 11701010323770312228534929)
                ·
                  refine ⟨8775757742827734171401197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11701010323770312228534929 8775757742827734171401197)
                  ·
                    refine ⟨3290909153560400314275449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8775757742827734171401197 3290909153560400314275449)
                    ·
                      refine ⟨2468181865170300235706587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3290909153560400314275449 2468181865170300235706587)
                      ·
                        rfl

theorem cell23_4806767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 1, 3, 2, 3, 2].length) (baseStart_4806767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4806767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4806767 prefixEnd_4806767 := by exact prefixLift 4806767
  have htrace : WordTrace (prefixWord ++ tailWord_4806767) baseStart_4806767 baseEnd_4806767 := by
    simpa [prefixWord, tailWord_4806767, baseEnd_4806767] using wordTrace_append hprefix tailTrace_4806767
  have hstable : (prefixWord ++ tailWord_4806767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4806767).length < 2 ^ (prefixWord ++ tailWord_4806767).sum := by decide
  have hdescent : baseEnd_4806767 < baseStart_4806767 := by decide
  rcases family_descends (prefixWord ++ tailWord_4806767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4806791 : List Nat := [1, 1, 4, 2, 1, 1, 6, 2, 1, 1, 3]
def baseStart_4806791 : Nat := 118140960795 + 4806791 * 2 ^ 59
def prefixEnd_4806791 : Nat := 4983230072969 + 3 ^ 40 * 4806791 * 2
def baseEnd_4806791 : Nat := 2468194188706008141806477

theorem tailTrace_4806791 : CollatzResearch.WordTrace tailWord_4806791 prefixEnd_4806791 2468194188706008141806477 := by
  unfold tailWord_4806791
  simp only [CollatzResearch.WordTrace]
  refine ⟨175318070728824616389972227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116878713819216410926648151 175318070728824616389972227)
  ·
    refine ⟨262977106093236924584958341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175318070728824616389972227 262977106093236924584958341)
    ·
      refine ⟨49308207392481923359679689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 262977106093236924584958341 49308207392481923359679689)
      ·
        refine ⟨36981155544361442519759767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49308207392481923359679689 36981155544361442519759767)
        ·
          refine ⟨55471733316542163779639651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36981155544361442519759767 55471733316542163779639651)
          ·
            refine ⟨83207599974813245669459477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55471733316542163779639651 83207599974813245669459477)
            ·
              refine ⟨3900356248819370890755913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 83207599974813245669459477 3900356248819370890755913)
              ·
                refine ⟨2925267186614528168066935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3900356248819370890755913 2925267186614528168066935)
                ·
                  refine ⟨4387900779921792252100403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2925267186614528168066935 4387900779921792252100403)
                  ·
                    refine ⟨6581851169882688378150605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4387900779921792252100403 6581851169882688378150605)
                    ·
                      refine ⟨2468194188706008141806477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6581851169882688378150605 2468194188706008141806477)
                      ·
                        rfl

theorem cell23_4806791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 6, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 6, 2, 1, 1, 3].length) (baseStart_4806791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4806791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4806791 prefixEnd_4806791 := by exact prefixLift 4806791
  have htrace : WordTrace (prefixWord ++ tailWord_4806791) baseStart_4806791 baseEnd_4806791 := by
    simpa [prefixWord, tailWord_4806791, baseEnd_4806791] using wordTrace_append hprefix tailTrace_4806791
  have hstable : (prefixWord ++ tailWord_4806791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4806791).length < 2 ^ (prefixWord ++ tailWord_4806791).sum := by decide
  have hdescent : baseEnd_4806791 < baseStart_4806791 := by decide
  rcases family_descends (prefixWord ++ tailWord_4806791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4806800 : List Nat := [2, 1, 1, 1, 1, 1, 5, 1, 5, 2, 3]
def baseStart_4806800 : Nat := 118140960795 + 4806800 * 2 ^ 59
def prefixEnd_4806800 : Nat := 4983230072969 + 3 ^ 40 * 4806800 * 2
def baseEnd_4806800 : Nat := 2468198810031898606593935

theorem tailTrace_4806800 : CollatzResearch.WordTrace tailWord_4806800 prefixEnd_4806800 2468198810031898606593935 := by
  unfold tailWord_4806800
  simp only [CollatzResearch.WordTrace]
  refine ⟨87659199492896005463524927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116878932657194673951366569 87659199492896005463524927)
  ·
    refine ⟨131488799239344008195287391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87659199492896005463524927 131488799239344008195287391)
    ·
      refine ⟨197233198859016012292931087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131488799239344008195287391 197233198859016012292931087)
      ·
        refine ⟨295849798288524018439396631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 197233198859016012292931087 295849798288524018439396631)
        ·
          refine ⟨443774697432786027659094947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 295849798288524018439396631 443774697432786027659094947)
          ·
            refine ⟨665662046149179041488642421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 443774697432786027659094947 665662046149179041488642421)
            ·
              refine ⟨62405816826485535139560227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 665662046149179041488642421 62405816826485535139560227)
              ·
                refine ⟨93608725239728302709340341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62405816826485535139560227 93608725239728302709340341)
                ·
                  refine ⟨8775817991224528379000657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 93608725239728302709340341 8775817991224528379000657)
                  ·
                    refine ⟨6581863493418396284250493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8775817991224528379000657 6581863493418396284250493)
                    ·
                      refine ⟨2468198810031898606593935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6581863493418396284250493 2468198810031898606593935)
                      ·
                        rfl

theorem cell23_4806800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 1, 5, 2, 3].length) (baseStart_4806800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4806800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4806800 prefixEnd_4806800 := by exact prefixLift 4806800
  have htrace : WordTrace (prefixWord ++ tailWord_4806800) baseStart_4806800 baseEnd_4806800 := by
    simpa [prefixWord, tailWord_4806800, baseEnd_4806800] using wordTrace_append hprefix tailTrace_4806800
  have hstable : (prefixWord ++ tailWord_4806800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4806800).length < 2 ^ (prefixWord ++ tailWord_4806800).sum := by decide
  have hdescent : baseEnd_4806800 < baseStart_4806800 := by decide
  rcases family_descends (prefixWord ++ tailWord_4806800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4806807 : List Nat := [1, 1, 3, 3, 4, 1, 2, 1, 1, 6]
def baseStart_4806807 : Nat := 118140960795 + 4806807 * 2 ^ 59
def prefixEnd_4806807 : Nat := 4983230072969 + 3 ^ 40 * 4806807 * 2
def baseEnd_4806807 : Nat := 822734134798826693068801

theorem tailTrace_4806807 : CollatzResearch.WordTrace tailWord_4806807 prefixEnd_4806807 822734134798826693068801 := by
  unfold tailWord_4806807
  simp only [CollatzResearch.WordTrace]
  refine ⟨175318654296766651122554675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116879102864511100748369783 175318654296766651122554675)
  ·
    refine ⟨262977981445149976683832013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175318654296766651122554675 262977981445149976683832013)
    ·
      refine ⟨98616743041931241256437005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 262977981445149976683832013 98616743041931241256437005)
      ·
        refine ⟨36981278640724215471163877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 98616743041931241256437005 36981278640724215471163877)
        ·
          refine ⟨6933989745135790400843227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 36981278640724215471163877 6933989745135790400843227)
          ·
            refine ⟨10400984617703685601264841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6933989745135790400843227 10400984617703685601264841)
            ·
              refine ⟨7800738463277764200948631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10400984617703685601264841 7800738463277764200948631)
              ·
                refine ⟨11701107694916646301422947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7800738463277764200948631 11701107694916646301422947)
                ·
                  refine ⟨17551661542374969452134421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11701107694916646301422947 17551661542374969452134421)
                  ·
                    refine ⟨822734134798826693068801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17551661542374969452134421 822734134798826693068801)
                    ·
                      rfl

theorem cell23_4806807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 2, 1, 1, 6].length) (baseStart_4806807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4806807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4806807 prefixEnd_4806807 := by exact prefixLift 4806807
  have htrace : WordTrace (prefixWord ++ tailWord_4806807) baseStart_4806807 baseEnd_4806807 := by
    simpa [prefixWord, tailWord_4806807, baseEnd_4806807] using wordTrace_append hprefix tailTrace_4806807
  have hstable : (prefixWord ++ tailWord_4806807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4806807).length < 2 ^ (prefixWord ++ tailWord_4806807).sum := by decide
  have hdescent : baseEnd_4806807 < baseStart_4806807 := by decide
  rcases family_descends (prefixWord ++ tailWord_4806807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4806817 : List Nat := [1, 2, 3, 3, 1, 2, 2, 1, 3, 2, 3]
def baseStart_4806817 : Nat := 118140960795 + 4806817 * 2 ^ 59
def prefixEnd_4806817 : Nat := 4983230072969 + 3 ^ 40 * 4806817 * 2
def baseEnd_4806817 : Nat := 2468207539203025040081357

theorem tailTrace_4806817 : CollatzResearch.WordTrace tailWord_4806817 prefixEnd_4806817 2468207539203025040081357 := by
  unfold tailWord_4806817
  simp only [CollatzResearch.WordTrace]
  refine ⟨175319019026730422830418705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116879346017820281886945803 175319019026730422830418705)
  ·
    refine ⟨131489264270047817122814029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 175319019026730422830418705 131489264270047817122814029)
    ·
      refine ⟨49308474101267931421055261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 131489264270047817122814029 49308474101267931421055261)
      ·
        refine ⟨18490677787975474282895723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49308474101267931421055261 18490677787975474282895723)
        ·
          refine ⟨27736016681963211424343585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18490677787975474282895723 27736016681963211424343585)
          ·
            refine ⟨20802012511472408568257689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27736016681963211424343585 20802012511472408568257689)
            ·
              refine ⟨15601509383604306426193267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20802012511472408568257689 15601509383604306426193267)
              ·
                refine ⟨23402264075406459639289901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15601509383604306426193267 23402264075406459639289901)
                ·
                  refine ⟨8775849028277422364733713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23402264075406459639289901 8775849028277422364733713)
                  ·
                    refine ⟨6581886771208066773550285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8775849028277422364733713 6581886771208066773550285)
                    ·
                      refine ⟨2468207539203025040081357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6581886771208066773550285 2468207539203025040081357)
                      ·
                        rfl

theorem cell23_4806817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 2, 1, 3, 2, 3].length) (baseStart_4806817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4806817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4806817 prefixEnd_4806817 := by exact prefixLift 4806817
  have htrace : WordTrace (prefixWord ++ tailWord_4806817) baseStart_4806817 baseEnd_4806817 := by
    simpa [prefixWord, tailWord_4806817, baseEnd_4806817] using wordTrace_append hprefix tailTrace_4806817
  have hstable : (prefixWord ++ tailWord_4806817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4806817).length < 2 ^ (prefixWord ++ tailWord_4806817).sum := by decide
  have hdescent : baseEnd_4806817 < baseStart_4806817 := by decide
  rcases family_descends (prefixWord ++ tailWord_4806817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4806837 : List Nat := [1, 3, 3, 4, 1, 1, 10]
def baseStart_4806837 : Nat := 118140960795 + 4806837 * 2 ^ 59
def prefixEnd_4806837 : Nat := 4983230072969 + 3 ^ 40 * 4806837 * 2
def baseEnd_4806837 : Nat := 30471824800198950146065

theorem tailTrace_4806837 : CollatzResearch.WordTrace tailWord_4806837 prefixEnd_4806837 30471824800198950146065 := by
  unfold tailWord_4806837
  simp only [CollatzResearch.WordTrace]
  refine ⟨175319748486657966246146765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116879832324438644164097843 175319748486657966246146765)
  ·
    refine ⟨65744905682496737342305037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 175319748486657966246146765 65744905682496737342305037)
    ·
      refine ⟨24654339630936276503364389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65744905682496737342305037 24654339630936276503364389)
      ·
        refine ⟨4622688680800551844380823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24654339630936276503364389 4622688680800551844380823)
        ·
          refine ⟨6934033021200827766571235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4622688680800551844380823 6934033021200827766571235)
          ·
            refine ⟨10401049531801241649856853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6934033021200827766571235 10401049531801241649856853)
            ·
              refine ⟨30471824800198950146065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 10401049531801241649856853 30471824800198950146065)
              ·
                rfl

theorem cell23_4806837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 10].length) (baseStart_4806837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4806837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4806837 prefixEnd_4806837 := by exact prefixLift 4806837
  have htrace : WordTrace (prefixWord ++ tailWord_4806837) baseStart_4806837 baseEnd_4806837 := by
    simpa [prefixWord, tailWord_4806837, baseEnd_4806837] using wordTrace_append hprefix tailTrace_4806837
  have hstable : (prefixWord ++ tailWord_4806837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4806837).length < 2 ^ (prefixWord ++ tailWord_4806837).sum := by decide
  have hdescent : baseEnd_4806837 < baseStart_4806837 := by decide
  rcases family_descends (prefixWord ++ tailWord_4806837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4806857 : List Nat := [1, 2, 1, 1, 2, 1, 1, 6, 3, 3, 2]
def baseStart_4806857 : Nat := 118140960795 + 4806857 * 2 ^ 59
def prefixEnd_4806857 : Nat := 4983230072969 + 3 ^ 40 * 4806857 * 2
def baseEnd_4806857 : Nat := 2468228078429204883581173

theorem tailTrace_4806857 : CollatzResearch.WordTrace tailWord_4806857 prefixEnd_4806857 2468228078429204883581173 := by
  unfold tailWord_4806857
  simp only [CollatzResearch.WordTrace]
  refine ⟨175320477946585509661874825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116880318631057006441249883 175320477946585509661874825)
  ·
    refine ⟨131490358459939132246406119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 175320477946585509661874825 131490358459939132246406119)
    ·
      refine ⟨197235537689908698369609179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131490358459939132246406119 197235537689908698369609179)
      ·
        refine ⟨295853306534863047554413769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 197235537689908698369609179 295853306534863047554413769)
        ·
          refine ⟨221889979901147285665810327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 295853306534863047554413769 221889979901147285665810327)
          ·
            refine ⟨332834969851720928498715491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 221889979901147285665810327 332834969851720928498715491)
            ·
              refine ⟨499252454777581392748073237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 332834969851720928498715491 499252454777581392748073237)
              ·
                refine ⟨23402458817699127785065933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 499252454777581392748073237 23402458817699127785065933)
                ·
                  refine ⟨8775922056637172919399725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23402458817699127785065933 8775922056637172919399725)
                  ·
                    refine ⟨3290970771238939844774897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8775922056637172919399725 3290970771238939844774897)
                    ·
                      refine ⟨2468228078429204883581173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3290970771238939844774897 2468228078429204883581173)
                      ·
                        rfl

theorem cell23_4806857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 6, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 6, 3, 3, 2].length) (baseStart_4806857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4806857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4806857 prefixEnd_4806857 := by exact prefixLift 4806857
  have htrace : WordTrace (prefixWord ++ tailWord_4806857) baseStart_4806857 baseEnd_4806857 := by
    simpa [prefixWord, tailWord_4806857, baseEnd_4806857] using wordTrace_append hprefix tailTrace_4806857
  have hstable : (prefixWord ++ tailWord_4806857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4806857).length < 2 ^ (prefixWord ++ tailWord_4806857).sum := by decide
  have hdescent : baseEnd_4806857 < baseStart_4806857 := by decide
  rcases family_descends (prefixWord ++ tailWord_4806857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4806874 : List Nat := [3, 1, 1, 2, 2, 1, 3, 4, 1, 3, 2]
def baseStart_4806874 : Nat := 118140960795 + 4806874 * 2 ^ 59
def prefixEnd_4806874 : Nat := 4983230072969 + 3 ^ 40 * 4806874 * 2
def baseEnd_4806874 : Nat := 2468236807600331317068595

theorem tailTrace_4806874 : CollatzResearch.WordTrace tailWord_4806874 prefixEnd_4806874 2468236807600331317068595 := by
  unfold tailWord_4806874
  simp only [CollatzResearch.WordTrace]
  refine ⟨43830274496880980391310919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 116880731991682614376829117 43830274496880980391310919)
  ·
    refine ⟨65745411745321470586966379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43830274496880980391310919 65745411745321470586966379)
    ·
      refine ⟨98618117617982205880449569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65745411745321470586966379 98618117617982205880449569)
      ·
        refine ⟨73963588213486654410337177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 98618117617982205880449569 73963588213486654410337177)
        ·
          refine ⟨55472691160114990807752883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73963588213486654410337177 55472691160114990807752883)
          ·
            refine ⟨83209036740172486211629325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55472691160114990807752883 83209036740172486211629325)
            ·
              refine ⟨31203388777564682329360997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 83209036740172486211629325 31203388777564682329360997)
              ·
                refine ⟨5850635395793377936755187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31203388777564682329360997 5850635395793377936755187)
                ·
                  refine ⟨8775953093690066905132781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5850635395793377936755187 8775953093690066905132781)
                  ·
                    refine ⟨3290982410133775089424793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8775953093690066905132781 3290982410133775089424793)
                    ·
                      refine ⟨2468236807600331317068595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3290982410133775089424793 2468236807600331317068595)
                      ·
                        rfl

theorem cell23_4806874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 3, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 3, 4, 1, 3, 2].length) (baseStart_4806874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4806874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4806874 prefixEnd_4806874 := by exact prefixLift 4806874
  have htrace : WordTrace (prefixWord ++ tailWord_4806874) baseStart_4806874 baseEnd_4806874 := by
    simpa [prefixWord, tailWord_4806874, baseEnd_4806874] using wordTrace_append hprefix tailTrace_4806874
  have hstable : (prefixWord ++ tailWord_4806874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4806874).length < 2 ^ (prefixWord ++ tailWord_4806874).sum := by decide
  have hdescent : baseEnd_4806874 < baseStart_4806874 := by decide
  rcases family_descends (prefixWord ++ tailWord_4806874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4806877 : List Nat := [1, 4, 3, 2, 1, 1, 1, 1, 2, 2, 5]
def baseStart_4806877 : Nat := 118140960795 + 4806877 * 2 ^ 59
def prefixEnd_4806877 : Nat := 4983230072969 + 3 ^ 40 * 4806877 * 2
def baseEnd_4806877 : Nat := 2468238348042294805331081

theorem tailTrace_4806877 : CollatzResearch.WordTrace tailWord_4806877 prefixEnd_4806877 2468238348042294805331081 := by
  unfold tailWord_4806877
  simp only [CollatzResearch.WordTrace]
  refine ⟨175321207406513053077602885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116880804937675368718401923 175321207406513053077602885)
  ·
    refine ⟨32872726388721197452050541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 175321207406513053077602885 32872726388721197452050541)
    ·
      refine ⟨12327272395770449044518953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32872726388721197452050541 12327272395770449044518953)
      ·
        refine ⟨9245454296827836783389215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12327272395770449044518953 9245454296827836783389215)
        ·
          refine ⟨13868181445241755175083823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9245454296827836783389215 13868181445241755175083823)
          ·
            refine ⟨20802272167862632762625735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13868181445241755175083823 20802272167862632762625735)
            ·
              refine ⟨31203408251793949143938603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20802272167862632762625735 31203408251793949143938603)
              ·
                refine ⟨46805112377690923715907905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31203408251793949143938603 46805112377690923715907905)
                ·
                  refine ⟨35103834283268192786930929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 46805112377690923715907905 35103834283268192786930929)
                  ·
                    refine ⟨26327875712451144590198197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 35103834283268192786930929 26327875712451144590198197)
                    ·
                      refine ⟨2468238348042294805331081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26327875712451144590198197 2468238348042294805331081)
                      ·
                        rfl

theorem cell23_4806877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 1, 1, 2, 2, 5].length) (baseStart_4806877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4806877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4806877 prefixEnd_4806877 := by exact prefixLift 4806877
  have htrace : WordTrace (prefixWord ++ tailWord_4806877) baseStart_4806877 baseEnd_4806877 := by
    simpa [prefixWord, tailWord_4806877, baseEnd_4806877] using wordTrace_append hprefix tailTrace_4806877
  have hstable : (prefixWord ++ tailWord_4806877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4806877).length < 2 ^ (prefixWord ++ tailWord_4806877).sum := by decide
  have hdescent : baseEnd_4806877 < baseStart_4806877 := by decide
  rcases family_descends (prefixWord ++ tailWord_4806877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4806921 : List Nat := [1, 2, 1, 1, 3, 5, 1, 3, 2, 2, 2]
def baseStart_4806921 : Nat := 118140960795 + 4806921 * 2 ^ 59
def prefixEnd_4806921 : Nat := 4983230072969 + 3 ^ 40 * 4806921 * 2
def baseEnd_4806921 : Nat := 2468260941191092633180879

theorem tailTrace_4806921 : CollatzResearch.WordTrace tailWord_4806921 prefixEnd_4806921 2468260941191092633180879 := by
  unfold tailWord_4806921
  simp only [CollatzResearch.WordTrace]
  refine ⟨175322812218353648592204617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116881874812235765728136411 175322812218353648592204617)
  ·
    refine ⟨131492109163765236444153463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 175322812218353648592204617 131492109163765236444153463)
    ·
      refine ⟨197238163745647854666230195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131492109163765236444153463 197238163745647854666230195)
      ·
        refine ⟨295857245618471781999345293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 197238163745647854666230195 295857245618471781999345293)
        ·
          refine ⟨110946467106926918249754485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 295857245618471781999345293 110946467106926918249754485)
          ·
            refine ⟨10401231291274398585914483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 110946467106926918249754485 10401231291274398585914483)
            ·
              refine ⟨15601846936911597878871725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10401231291274398585914483 15601846936911597878871725)
              ·
                refine ⟨5850692601341849204576897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15601846936911597878871725 5850692601341849204576897)
                ·
                  refine ⟨4388019451006386903432673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5850692601341849204576897 4388019451006386903432673)
                  ·
                    refine ⟨3291014588254790177574505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4388019451006386903432673 3291014588254790177574505)
                    ·
                      refine ⟨2468260941191092633180879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3291014588254790177574505 2468260941191092633180879)
                      ·
                        rfl

theorem cell23_4806921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 1, 3, 2, 2, 2].length) (baseStart_4806921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4806921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4806921 prefixEnd_4806921 := by exact prefixLift 4806921
  have htrace : WordTrace (prefixWord ++ tailWord_4806921) baseStart_4806921 baseEnd_4806921 := by
    simpa [prefixWord, tailWord_4806921, baseEnd_4806921] using wordTrace_append hprefix tailTrace_4806921
  have hstable : (prefixWord ++ tailWord_4806921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4806921).length < 2 ^ (prefixWord ++ tailWord_4806921).sum := by decide
  have hdescent : baseEnd_4806921 < baseStart_4806921 := by decide
  rcases family_descends (prefixWord ++ tailWord_4806921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4806994 : List Nat := [3, 2, 2, 1, 1, 1, 5, 1, 2, 1, 4]
def baseStart_4806994 : Nat := 118140960795 + 4806994 * 2 ^ 59
def prefixEnd_4806994 : Nat := 4983230072969 + 3 ^ 40 * 4806994 * 2
def baseEnd_4806994 : Nat := 2468298425278870847568043

theorem tailTrace_4806994 : CollatzResearch.WordTrace tailWord_4806994 prefixEnd_4806994 2468298425278870847568043 := by
  unfold tailWord_4806994
  simp only [CollatzResearch.WordTrace]
  refine ⟨43831368686772295514903009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 116883649831392788039741357 43831368686772295514903009)
  ·
    refine ⟨32873526515079221636177257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43831368686772295514903009 32873526515079221636177257)
    ·
      refine ⟨24655144886309416227132943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32873526515079221636177257 24655144886309416227132943)
      ·
        refine ⟨36982717329464124340699415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24655144886309416227132943 36982717329464124340699415)
        ·
          refine ⟨55474075994196186511049123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36982717329464124340699415 55474075994196186511049123)
          ·
            refine ⟨83211113991294279766573685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55474075994196186511049123 83211113991294279766573685)
            ·
              refine ⟨7801041936683838728116283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 83211113991294279766573685 7801041936683838728116283)
              ·
                refine ⟨11701562905025758092174425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7801041936683838728116283 11701562905025758092174425)
                ·
                  refine ⟨8776172178769318569130819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11701562905025758092174425 8776172178769318569130819)
                  ·
                    refine ⟨13164258268153977853696229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8776172178769318569130819 13164258268153977853696229)
                    ·
                      refine ⟨2468298425278870847568043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13164258268153977853696229 2468298425278870847568043)
                      ·
                        rfl

theorem cell23_4806994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 5, 1, 2, 1, 4].length) (baseStart_4806994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4806994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4806994 prefixEnd_4806994 := by exact prefixLift 4806994
  have htrace : WordTrace (prefixWord ++ tailWord_4806994) baseStart_4806994 baseEnd_4806994 := by
    simpa [prefixWord, tailWord_4806994, baseEnd_4806994] using wordTrace_append hprefix tailTrace_4806994
  have hstable : (prefixWord ++ tailWord_4806994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4806994).length < 2 ^ (prefixWord ++ tailWord_4806994).sum := by decide
  have hdescent : baseEnd_4806994 < baseStart_4806994 := by decide
  rcases family_descends (prefixWord ++ tailWord_4806994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4807006 : List Nat := [4, 4, 2, 1, 1, 2, 1, 2, 2, 2, 2]
def baseStart_4807006 : Nat := 118140960795 + 4807006 * 2 ^ 59
def prefixEnd_4807006 : Nat := 4983230072969 + 3 ^ 40 * 4807006 * 2
def baseEnd_4807006 : Nat := 2468304587046724800617989

theorem tailTrace_4807006 : CollatzResearch.WordTrace tailWord_4807006 prefixEnd_4807006 2468304587046724800617989 := by
  unfold tailWord_4807006
  simp only [CollatzResearch.WordTrace]
  refine ⟨21915739052880713513631109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 116883941615363805406032581 21915739052880713513631109)
  ·
    refine ⟨4109201072415133783805833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21915739052880713513631109 4109201072415133783805833)
    ·
      refine ⟨3081900804311350337854375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4109201072415133783805833 3081900804311350337854375)
      ·
        refine ⟨4622851206467025506781563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3081900804311350337854375 4622851206467025506781563)
        ·
          refine ⟨6934276809700538260172345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4622851206467025506781563 6934276809700538260172345)
          ·
            refine ⟨5200707607275403695129259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6934276809700538260172345 5200707607275403695129259)
            ·
              refine ⟨7801061410913105542693889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5200707607275403695129259 7801061410913105542693889)
              ·
                refine ⟨5850796058184829157020417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7801061410913105542693889 5850796058184829157020417)
                ·
                  refine ⟨4388097043638621867765313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5850796058184829157020417 4388097043638621867765313)
                  ·
                    refine ⟨3291072782728966400823985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4388097043638621867765313 3291072782728966400823985)
                    ·
                      refine ⟨2468304587046724800617989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3291072782728966400823985 2468304587046724800617989)
                      ·
                        rfl

theorem cell23_4807006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 2, 1, 2, 2, 2, 2].length) (baseStart_4807006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4807006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4807006 prefixEnd_4807006 := by exact prefixLift 4807006
  have htrace : WordTrace (prefixWord ++ tailWord_4807006) baseStart_4807006 baseEnd_4807006 := by
    simpa [prefixWord, tailWord_4807006, baseEnd_4807006] using wordTrace_append hprefix tailTrace_4807006
  have hstable : (prefixWord ++ tailWord_4807006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4807006).length < 2 ^ (prefixWord ++ tailWord_4807006).sum := by decide
  have hdescent : baseEnd_4807006 < baseStart_4807006 := by decide
  rcases family_descends (prefixWord ++ tailWord_4807006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4807021 : List Nat := [1, 5, 1, 1, 1, 2, 1, 6, 1, 4]
def baseStart_4807021 : Nat := 118140960795 + 4807021 * 2 ^ 59
def prefixEnd_4807021 : Nat := 4983230072969 + 3 ^ 40 * 4807021 * 2
def baseEnd_4807021 : Nat := 822770763085514080643473

theorem tailTrace_4807021 : CollatzResearch.WordTrace tailWord_4807021 prefixEnd_4807021 822770763085514080643473 := by
  unfold tailWord_4807021
  simp only [CollatzResearch.WordTrace]
  refine ⟨175326459517991365670844917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116884306345327577113896611 175326459517991365670844917)
  ·
    refine ⟨16436855579811690531641711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 175326459517991365670844917 16436855579811690531641711)
    ·
      refine ⟨24655283369717535797462567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16436855579811690531641711 24655283369717535797462567)
      ·
        refine ⟨36982925054576303696193851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24655283369717535797462567 36982925054576303696193851)
        ·
          refine ⟨55474387581864455544290777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36982925054576303696193851 55474387581864455544290777)
          ·
            refine ⟨41605790686398341658218083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55474387581864455544290777 41605790686398341658218083)
            ·
              refine ⟨62408686029597512487327125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41605790686398341658218083 62408686029597512487327125)
              ·
                refine ⟨2925407157637383397843459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 62408686029597512487327125 2925407157637383397843459)
                ·
                  refine ⟨4388110736456075096765189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2925407157637383397843459 4388110736456075096765189)
                  ·
                    refine ⟨822770763085514080643473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4388110736456075096765189 822770763085514080643473)
                    ·
                      rfl

theorem cell23_4807021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 6, 1, 4].length) (baseStart_4807021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4807021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4807021 prefixEnd_4807021 := by exact prefixLift 4807021
  have htrace : WordTrace (prefixWord ++ tailWord_4807021) baseStart_4807021 baseEnd_4807021 := by
    simpa [prefixWord, tailWord_4807021, baseEnd_4807021] using wordTrace_append hprefix tailTrace_4807021
  have hstable : (prefixWord ++ tailWord_4807021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4807021).length < 2 ^ (prefixWord ++ tailWord_4807021).sum := by decide
  have hdescent : baseEnd_4807021 < baseStart_4807021 := by decide
  rcases family_descends (prefixWord ++ tailWord_4807021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4807071 : List Nat := [1, 1, 2, 5, 1, 1, 3, 2, 2, 3, 2]
def baseStart_4807071 : Nat := 118140960795 + 4807071 * 2 ^ 59
def prefixEnd_4807071 : Nat := 4983230072969 + 3 ^ 40 * 4807071 * 2
def baseEnd_4807071 : Nat := 2468337963289267046305189

theorem tailTrace_4807071 : CollatzResearch.WordTrace tailWord_4807071 prefixEnd_4807071 2468337963289267046305189 := by
  unfold tailWord_4807071
  simp only [CollatzResearch.WordTrace]
  refine ⟨175328283167810224210165067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116885522111873482806776711 175328283167810224210165067)
  ·
    refine ⟨262992424751715336315247601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175328283167810224210165067 262992424751715336315247601)
    ·
      refine ⟨197244318563786502236435701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 262992424751715336315247601 197244318563786502236435701)
      ·
        refine ⟨18491654865354984584665847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 197244318563786502236435701 18491654865354984584665847)
        ·
          refine ⟨27737482298032476876998771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18491654865354984584665847 27737482298032476876998771)
          ·
            refine ⟨41606223447048715315498157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27737482298032476876998771 41606223447048715315498157)
            ·
              refine ⟨15602333792643268243311809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41606223447048715315498157 15602333792643268243311809)
              ·
                refine ⟨11701750344482451182483857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15602333792643268243311809 11701750344482451182483857)
                ·
                  refine ⟨8776312758361838386862893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11701750344482451182483857 8776312758361838386862893)
                  ·
                    refine ⟨3291117284385689395073585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8776312758361838386862893 3291117284385689395073585)
                    ·
                      refine ⟨2468337963289267046305189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3291117284385689395073585 2468337963289267046305189)
                      ·
                        rfl

theorem cell23_4807071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 3, 2, 2, 3, 2].length) (baseStart_4807071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4807071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4807071 prefixEnd_4807071 := by exact prefixLift 4807071
  have htrace : WordTrace (prefixWord ++ tailWord_4807071) baseStart_4807071 baseEnd_4807071 := by
    simpa [prefixWord, tailWord_4807071, baseEnd_4807071] using wordTrace_append hprefix tailTrace_4807071
  have hstable : (prefixWord ++ tailWord_4807071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4807071).length < 2 ^ (prefixWord ++ tailWord_4807071).sum := by decide
  have hdescent : baseEnd_4807071 < baseStart_4807071 := by decide
  rcases family_descends (prefixWord ++ tailWord_4807071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4807085 : List Nat := [1, 5, 2, 2, 3, 1, 2, 1, 6]
def baseStart_4807085 : Nat := 118140960795 + 4807085 * 2 ^ 59
def prefixEnd_4807085 : Nat := 4983230072969 + 3 ^ 40 * 4807085 * 2
def baseEnd_4807085 : Nat := 274260572446492221281125

theorem tailTrace_4807085 : CollatzResearch.WordTrace tailWord_4807085 prefixEnd_4807085 274260572446492221281125 := by
  unfold tailWord_4807085
  simp only [CollatzResearch.WordTrace]
  refine ⟨175328793789759504601174709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116885862526506336400783139 175328793789759504601174709)
  ·
    refine ⟨16437074417789953556360129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 175328793789759504601174709 16437074417789953556360129)
    ·
      refine ⟨12327805813342465167270097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16437074417789953556360129 12327805813342465167270097)
      ·
        refine ⟨9245854360006848875452573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12327805813342465167270097 9245854360006848875452573)
        ·
          refine ⟨3467195385002568328294715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9245854360006848875452573 3467195385002568328294715)
          ·
            refine ⟨5200793077503852492442073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3467195385002568328294715 5200793077503852492442073)
            ·
              refine ⟨3900594808127889369331555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5200793077503852492442073 3900594808127889369331555)
              ·
                refine ⟨5850892212191834053997333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3900594808127889369331555 5850892212191834053997333)
                ·
                  refine ⟨274260572446492221281125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5850892212191834053997333 274260572446492221281125)
                  ·
                    rfl

theorem cell23_4807085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 3, 1, 2, 1, 6].length) (baseStart_4807085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4807085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4807085 prefixEnd_4807085 := by exact prefixLift 4807085
  have htrace : WordTrace (prefixWord ++ tailWord_4807085) baseStart_4807085 baseEnd_4807085 := by
    simpa [prefixWord, tailWord_4807085, baseEnd_4807085] using wordTrace_append hprefix tailTrace_4807085
  have hstable : (prefixWord ++ tailWord_4807085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4807085).length < 2 ^ (prefixWord ++ tailWord_4807085).sum := by decide
  have hdescent : baseEnd_4807085 < baseStart_4807085 := by decide
  rcases family_descends (prefixWord ++ tailWord_4807085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4807087 : List Nat := [1, 1, 2, 1, 2, 2, 1, 1, 1, 8, 3]
def baseStart_4807087 : Nat := 118140960795 + 4807087 * 2 ^ 59
def prefixEnd_4807087 : Nat := 4983230072969 + 3 ^ 40 * 4807087 * 2
def baseEnd_4807087 : Nat := 2468346178979738983705115

theorem tailTrace_4807087 : CollatzResearch.WordTrace tailWord_4807087 prefixEnd_4807087 2468346178979738983705115 := by
  unfold tailWord_4807087
  simp only [CollatzResearch.WordTrace]
  refine ⟨175328866735752258942747515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116885911157168172628498343 175328866735752258942747515)
  ·
    refine ⟨262993300103628388414121273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175328866735752258942747515 262993300103628388414121273)
    ·
      refine ⟨197244975077721291310590955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 262993300103628388414121273 197244975077721291310590955)
      ·
        refine ⟨295867462616581936965886433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 197244975077721291310590955 295867462616581936965886433)
        ·
          refine ⟨221900596962436452724414825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 295867462616581936965886433 221900596962436452724414825)
          ·
            refine ⟨166425447721827339543311119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 221900596962436452724414825 166425447721827339543311119)
            ·
              refine ⟨249638171582741009314966679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 166425447721827339543311119 249638171582741009314966679)
              ·
                refine ⟨374457257374111513972450019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 249638171582741009314966679 374457257374111513972450019)
                ·
                  refine ⟨561685886061167270958675029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 374457257374111513972450019 561685886061167270958675029)
                  ·
                    refine ⟨6582256477279303956546973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 561685886061167270958675029 6582256477279303956546973)
                    ·
                      refine ⟨2468346178979738983705115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6582256477279303956546973 2468346178979738983705115)
                      ·
                        rfl

theorem cell23_4807087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 1, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 1, 1, 8, 3].length) (baseStart_4807087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4807087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4807087 prefixEnd_4807087 := by exact prefixLift 4807087
  have htrace : WordTrace (prefixWord ++ tailWord_4807087) baseStart_4807087 baseEnd_4807087 := by
    simpa [prefixWord, tailWord_4807087, baseEnd_4807087] using wordTrace_append hprefix tailTrace_4807087
  have hstable : (prefixWord ++ tailWord_4807087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4807087).length < 2 ^ (prefixWord ++ tailWord_4807087).sum := by decide
  have hdescent : baseEnd_4807087 < baseStart_4807087 := by decide
  rcases family_descends (prefixWord ++ tailWord_4807087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4807101 : List Nat := [1, 4, 1, 2, 2, 2, 3, 2, 1, 1, 4]
def baseStart_4807101 : Nat := 118140960795 + 4807101 * 2 ^ 59
def prefixEnd_4807101 : Nat := 4983230072969 + 3 ^ 40 * 4807101 * 2
def baseEnd_4807101 : Nat := 2468353367708901928930051

theorem tailTrace_4807101 : CollatzResearch.WordTrace tailWord_4807101 prefixEnd_4807101 2468353367708901928930051 := by
  unfold tailWord_4807101
  simp only [CollatzResearch.WordTrace]
  refine ⟨175329377357701539333757157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116886251571801026222504771 175329377357701539333757157)
  ·
    refine ⟨32874258254569038625079467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 175329377357701539333757157 32874258254569038625079467)
    ·
      refine ⟨49311387381853557937619201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32874258254569038625079467 49311387381853557937619201)
      ·
        refine ⟨36983540536390168453214401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49311387381853557937619201 36983540536390168453214401)
        ·
          refine ⟨27737655402292626339910801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36983540536390168453214401 27737655402292626339910801)
          ·
            refine ⟨20803241551719469754933101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27737655402292626339910801 20803241551719469754933101)
            ·
              refine ⟨7801215581894801158099913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20803241551719469754933101 7801215581894801158099913)
              ·
                refine ⟨5850911686421100868574935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7801215581894801158099913 5850911686421100868574935)
                ·
                  refine ⟨8776367529631651302862403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5850911686421100868574935 8776367529631651302862403)
                  ·
                    refine ⟨13164551294447476954293605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8776367529631651302862403 13164551294447476954293605)
                    ·
                      refine ⟨2468353367708901928930051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13164551294447476954293605 2468353367708901928930051)
                      ·
                        rfl

theorem cell23_4807101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 3, 2, 1, 1, 4].length) (baseStart_4807101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4807101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4807101 prefixEnd_4807101 := by exact prefixLift 4807101
  have htrace : WordTrace (prefixWord ++ tailWord_4807101) baseStart_4807101 baseEnd_4807101 := by
    simpa [prefixWord, tailWord_4807101, baseEnd_4807101] using wordTrace_append hprefix tailTrace_4807101
  have hstable : (prefixWord ++ tailWord_4807101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4807101).length < 2 ^ (prefixWord ++ tailWord_4807101).sum := by decide
  have hdescent : baseEnd_4807101 < baseStart_4807101 := by decide
  rcases family_descends (prefixWord ++ tailWord_4807101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4807114 : List Nat := [3, 1, 2, 1, 2, 2, 3, 2, 1, 2, 4]
def baseStart_4807114 : Nat := 118140960795 + 4807114 * 2 ^ 59
def prefixEnd_4807114 : Nat := 4983230072969 + 3 ^ 40 * 4807114 * 2
def baseEnd_4807114 : Nat := 2468360042957410378067491

theorem tailTrace_4807114 : CollatzResearch.WordTrace tailWord_4807114 prefixEnd_4807114 2468360042957410378067491 := by
  unfold tailWord_4807114
  simp only [CollatzResearch.WordTrace]
  refine ⟨43832462876663610638495099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 116886567671102961702653597 43832462876663610638495099)
  ·
    refine ⟨65748694314995415957742649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43832462876663610638495099 65748694314995415957742649)
    ·
      refine ⟨49311520736246561968306987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65748694314995415957742649 49311520736246561968306987)
      ·
        refine ⟨73967281104369842952460481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49311520736246561968306987 73967281104369842952460481)
        ·
          refine ⟨55475460828277382214345361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73967281104369842952460481 55475460828277382214345361)
          ·
            refine ⟨41606595621208036660759021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55475460828277382214345361 41606595621208036660759021)
            ·
              refine ⟨15602473357953013747784633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41606595621208036660759021 15602473357953013747784633)
              ·
                refine ⟨11701855018464760310838475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15602473357953013747784633 11701855018464760310838475)
                ·
                  refine ⟨17552782527697140466257713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11701855018464760310838475 17552782527697140466257713)
                  ·
                    refine ⟨13164586895772855349693285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17552782527697140466257713 13164586895772855349693285)
                    ·
                      refine ⟨2468360042957410378067491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13164586895772855349693285 2468360042957410378067491)
                      ·
                        rfl

theorem cell23_4807114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 3, 2, 1, 2, 4].length) (baseStart_4807114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4807114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4807114 prefixEnd_4807114 := by exact prefixLift 4807114
  have htrace : WordTrace (prefixWord ++ tailWord_4807114) baseStart_4807114 baseEnd_4807114 := by
    simpa [prefixWord, tailWord_4807114, baseEnd_4807114] using wordTrace_append hprefix tailTrace_4807114
  have hstable : (prefixWord ++ tailWord_4807114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4807114).length < 2 ^ (prefixWord ++ tailWord_4807114).sum := by decide
  have hdescent : baseEnd_4807114 < baseStart_4807114 := by decide
  rcases family_descends (prefixWord ++ tailWord_4807114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4807135 : List Nat := [1, 1, 2, 3, 3, 3, 1, 4, 1, 2, 2]
def baseStart_4807135 : Nat := 118140960795 + 4807135 * 2 ^ 59
def prefixEnd_4807135 : Nat := 4983230072969 + 3 ^ 40 * 4807135 * 2
def baseEnd_4807135 : Nat := 2468370826051154795904895

theorem tailTrace_4807135 : CollatzResearch.WordTrace tailWord_4807135 prefixEnd_4807135 2468370826051154795904895 := by
  unfold tailWord_4807135
  simp only [CollatzResearch.WordTrace]
  refine ⟨175330617439578363140494859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116887078293052242093663239 175330617439578363140494859)
  ·
    refine ⟨262995926159367544710742289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175330617439578363140494859 262995926159367544710742289)
    ·
      refine ⟨197246944619525658533056717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 262995926159367544710742289 197246944619525658533056717)
      ·
        refine ⟨73967604232322121949896269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 197246944619525658533056717 73967604232322121949896269)
        ·
          refine ⟨27737851587120795731211101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 73967604232322121949896269 27737851587120795731211101)
          ·
            refine ⟨10401694345170298399204163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27737851587120795731211101 10401694345170298399204163)
            ·
              refine ⟨15602541517755447598806245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10401694345170298399204163 15602541517755447598806245)
              ·
                refine ⟨2925476534579146424776171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15602541517755447598806245 2925476534579146424776171)
                ·
                  refine ⟨4388214801868719637164257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2925476534579146424776171 4388214801868719637164257)
                  ·
                    refine ⟨3291161101401539727873193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4388214801868719637164257 3291161101401539727873193)
                    ·
                      refine ⟨2468370826051154795904895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3291161101401539727873193 2468370826051154795904895)
                      ·
                        rfl

theorem cell23_4807135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 1, 4, 1, 2, 2].length) (baseStart_4807135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4807135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4807135 prefixEnd_4807135 := by exact prefixLift 4807135
  have htrace : WordTrace (prefixWord ++ tailWord_4807135) baseStart_4807135 baseEnd_4807135 := by
    simpa [prefixWord, tailWord_4807135, baseEnd_4807135] using wordTrace_append hprefix tailTrace_4807135
  have hstable : (prefixWord ++ tailWord_4807135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4807135).length < 2 ^ (prefixWord ++ tailWord_4807135).sum := by decide
  have hdescent : baseEnd_4807135 < baseStart_4807135 := by decide
  rcases family_descends (prefixWord ++ tailWord_4807135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4807137 : List Nat := [1, 2, 3, 1, 2, 2, 1, 1, 1, 9]
def baseStart_4807137 : Nat := 118140960795 + 4807137 * 2 ^ 59
def prefixEnd_4807137 : Nat := 4983230072969 + 3 ^ 40 * 4807137 * 2
def baseEnd_4807137 : Nat := 822790617670821262693295

theorem tailTrace_4807137 : CollatzResearch.WordTrace tailWord_4807137 prefixEnd_4807137 822790617670821262693295 := by
  unfold tailWord_4807137
  simp only [CollatzResearch.WordTrace]
  refine ⟨175330690385571117482067665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116887126923714078321378443 175330690385571117482067665)
  ·
    refine ⟨131498017789178338111550749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 175330690385571117482067665 131498017789178338111550749)
    ·
      refine ⟨49311756670941876791831531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 131498017789178338111550749 49311756670941876791831531)
      ·
        refine ⟨73967635006412815187747297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49311756670941876791831531 73967635006412815187747297)
        ·
          refine ⟨55475726254809611390810473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73967635006412815187747297 55475726254809611390810473)
          ·
            refine ⟨41606794691107208543107855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55475726254809611390810473 41606794691107208543107855)
            ·
              refine ⟨62410192036660812814661783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41606794691107208543107855 62410192036660812814661783)
              ·
                refine ⟨93615288054991219221992675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62410192036660812814661783 93615288054991219221992675)
                ·
                  refine ⟨140422932082486828832989013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 93615288054991219221992675 140422932082486828832989013)
                  ·
                    refine ⟨822790617670821262693295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 140422932082486828832989013 822790617670821262693295)
                    ·
                      rfl

theorem cell23_4807137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 1, 1, 9].length) (baseStart_4807137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4807137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4807137 prefixEnd_4807137 := by exact prefixLift 4807137
  have htrace : WordTrace (prefixWord ++ tailWord_4807137) baseStart_4807137 baseEnd_4807137 := by
    simpa [prefixWord, tailWord_4807137, baseEnd_4807137] using wordTrace_append hprefix tailTrace_4807137
  have hstable : (prefixWord ++ tailWord_4807137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4807137).length < 2 ^ (prefixWord ++ tailWord_4807137).sum := by decide
  have hdescent : baseEnd_4807137 < baseStart_4807137 := by decide
  rcases family_descends (prefixWord ++ tailWord_4807137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4807141 : List Nat := [1, 3, 1, 5, 2, 2, 1, 8]
def baseStart_4807141 : Nat := 118140960795 + 4807141 * 2 ^ 59
def prefixEnd_4807141 : Nat := 4983230072969 + 3 ^ 40 * 4807141 * 2
def baseEnd_4807141 : Nat := 91421255812410436015921

theorem tailTrace_4807141 : CollatzResearch.WordTrace tailWord_4807141 prefixEnd_4807141 91421255812410436015921 := by
  unfold tailWord_4807141
  simp only [CollatzResearch.WordTrace]
  refine ⟨175330836277556626165213277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116887224185037750776808851 175330836277556626165213277)
  ·
    refine ⟨65749063604083734811954979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 175330836277556626165213277 65749063604083734811954979)
    ·
      refine ⟨98623595406125602217932469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65749063604083734811954979 98623595406125602217932469)
      ·
        refine ⟨9245962069324275207931169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 98623595406125602217932469 9245962069324275207931169)
        ·
          refine ⟨6934471551993206405948377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9245962069324275207931169 6934471551993206405948377)
          ·
            refine ⟨5200853663994904804461283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6934471551993206405948377 5200853663994904804461283)
            ·
              refine ⟨7801280495992357206691925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5200853663994904804461283 7801280495992357206691925)
              ·
                refine ⟨91421255812410436015921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7801280495992357206691925 91421255812410436015921)
                ·
                  rfl

theorem cell23_4807141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 2, 1, 8].length) (baseStart_4807141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4807141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4807141 prefixEnd_4807141 := by exact prefixLift 4807141
  have htrace : WordTrace (prefixWord ++ tailWord_4807141) baseStart_4807141 baseEnd_4807141 := by
    simpa [prefixWord, tailWord_4807141, baseEnd_4807141] using wordTrace_append hprefix tailTrace_4807141
  have hstable : (prefixWord ++ tailWord_4807141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4807141).length < 2 ^ (prefixWord ++ tailWord_4807141).sum := by decide
  have hdescent : baseEnd_4807141 < baseStart_4807141 := by decide
  rcases family_descends (prefixWord ++ tailWord_4807141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4807161 : List Nat := [1, 2, 1, 3, 1, 2, 4, 1, 3, 3, 2]
def baseStart_4807161 : Nat := 118140960795 + 4807161 * 2 ^ 59
def prefixEnd_4807161 : Nat := 4983230072969 + 3 ^ 40 * 4807161 * 2
def baseEnd_4807161 : Nat := 2468384176548171694179775

theorem tailTrace_4807161 : CollatzResearch.WordTrace tailWord_4807161 prefixEnd_4807161 2468384176548171694179775 := by
  unfold tailWord_4807161
  simp only [CollatzResearch.WordTrace]
  refine ⟨175331565737484169580941337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116887710491656113053960891 175331565737484169580941337)
  ·
    refine ⟨131498674303113127185706003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 175331565737484169580941337 131498674303113127185706003)
    ·
      refine ⟨197248011454669690778559005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131498674303113127185706003 197248011454669690778559005)
      ·
        refine ⟨73968004295501134041959627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 197248011454669690778559005 73968004295501134041959627)
        ·
          refine ⟨110952006443251701062939441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73968004295501134041959627 110952006443251701062939441)
          ·
            refine ⟨83214004832438775797204581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 110952006443251701062939441 83214004832438775797204581)
            ·
              refine ⟨15602625906082270461975859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 83214004832438775797204581 15602625906082270461975859)
              ·
                refine ⟨23403938859123405692963789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15602625906082270461975859 23403938859123405692963789)
                ·
                  refine ⟨8776477072171277134861421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23403938859123405692963789 8776477072171277134861421)
                  ·
                    refine ⟨3291178902064228925573033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8776477072171277134861421 3291178902064228925573033)
                    ·
                      refine ⟨2468384176548171694179775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3291178902064228925573033 2468384176548171694179775)
                      ·
                        rfl

theorem cell23_4807161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 4, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 4, 1, 3, 3, 2].length) (baseStart_4807161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4807161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4807161 prefixEnd_4807161 := by exact prefixLift 4807161
  have htrace : WordTrace (prefixWord ++ tailWord_4807161) baseStart_4807161 baseEnd_4807161 := by
    simpa [prefixWord, tailWord_4807161, baseEnd_4807161] using wordTrace_append hprefix tailTrace_4807161
  have hstable : (prefixWord ++ tailWord_4807161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4807161).length < 2 ^ (prefixWord ++ tailWord_4807161).sum := by decide
  have hdescent : baseEnd_4807161 < baseStart_4807161 := by decide
  rcases family_descends (prefixWord ++ tailWord_4807161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4807167 : List Nat := [1, 1, 2, 2, 1, 2, 3, 2, 1, 8]
def baseStart_4807167 : Nat := 118140960795 + 4807167 * 2 ^ 59
def prefixEnd_4807167 : Nat := 4983230072969 + 3 ^ 40 * 4807167 * 2
def baseEnd_4807167 : Nat := 822795752477366223568249

theorem tailTrace_4807167 : CollatzResearch.WordTrace tailWord_4807167 prefixEnd_4807167 822795752477366223568249 := by
  unfold tailWord_4807167
  simp only [CollatzResearch.WordTrace]
  refine ⟨175331784575462432605659755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116887856383641621737106503 175331784575462432605659755)
  ·
    refine ⟨262997676863193648908489633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175331784575462432605659755 262997676863193648908489633)
    ·
      refine ⟨197248257647395236681367225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 262997676863193648908489633 197248257647395236681367225)
      ·
        refine ⟨147936193235546427511025419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 197248257647395236681367225 147936193235546427511025419)
        ·
          refine ⟨221904289853319641266538129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 147936193235546427511025419 221904289853319641266538129)
          ·
            refine ⟨166428217389989730949903597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 221904289853319641266538129 166428217389989730949903597)
            ·
              refine ⟨62410581521246149106213849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 166428217389989730949903597 62410581521246149106213849)
              ·
                refine ⟨46807936140934611829660387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 62410581521246149106213849 46807936140934611829660387)
                ·
                  refine ⟨70211904211401917744490581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 46807936140934611829660387 70211904211401917744490581)
                  ·
                    refine ⟨822795752477366223568249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 70211904211401917744490581 822795752477366223568249)
                    ·
                      rfl

theorem cell23_4807167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 2, 1, 8].length) (baseStart_4807167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4807167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4807167 prefixEnd_4807167 := by exact prefixLift 4807167
  have htrace : WordTrace (prefixWord ++ tailWord_4807167) baseStart_4807167 baseEnd_4807167 := by
    simpa [prefixWord, tailWord_4807167, baseEnd_4807167] using wordTrace_append hprefix tailTrace_4807167
  have hstable : (prefixWord ++ tailWord_4807167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4807167).length < 2 ^ (prefixWord ++ tailWord_4807167).sum := by decide
  have hdescent : baseEnd_4807167 < baseStart_4807167 := by decide
  rcases family_descends (prefixWord ++ tailWord_4807167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4807178 : List Nat := [3, 1, 2, 2, 2, 1, 3, 3, 1, 3, 2]
def baseStart_4807178 : Nat := 118140960795 + 4807178 * 2 ^ 59
def prefixEnd_4807178 : Nat := 4983230072969 + 3 ^ 40 * 4807178 * 2
def baseEnd_4807178 : Nat := 2468392905719298127667197

theorem tailTrace_4807178 : CollatzResearch.WordTrace tailWord_4807178 prefixEnd_4807178 2468392905719298127667197 := by
  unfold tailWord_4807178
  simp only [CollatzResearch.WordTrace]
  refine ⟨43833046444605645371077547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 116888123852281720989540125 43833046444605645371077547)
  ·
    refine ⟨65749569666908468056616321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43833046444605645371077547 65749569666908468056616321)
    ·
      refine ⟨49312177250181351042462241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65749569666908468056616321 49312177250181351042462241)
      ·
        refine ⟨36984132937636013281846681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49312177250181351042462241 36984132937636013281846681)
        ·
          refine ⟨27738099703227009961385011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36984132937636013281846681 27738099703227009961385011)
          ·
            refine ⟨41607149554840514942077517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27738099703227009961385011 41607149554840514942077517)
            ·
              refine ⟨15602681083065193103279069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41607149554840514942077517 15602681083065193103279069)
              ·
                refine ⟨5851005406149447413729651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15602681083065193103279069 5851005406149447413729651)
                ·
                  refine ⟨8776508109224171120594477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5851005406149447413729651 8776508109224171120594477)
                  ·
                    refine ⟨3291190540959064170222929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8776508109224171120594477 3291190540959064170222929)
                    ·
                      refine ⟨2468392905719298127667197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3291190540959064170222929 2468392905719298127667197)
                      ·
                        rfl

theorem cell23_4807178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 3, 3, 1, 3, 2].length) (baseStart_4807178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4807178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4807178 prefixEnd_4807178 := by exact prefixLift 4807178
  have htrace : WordTrace (prefixWord ++ tailWord_4807178) baseStart_4807178 baseEnd_4807178 := by
    simpa [prefixWord, tailWord_4807178, baseEnd_4807178] using wordTrace_append hprefix tailTrace_4807178
  have hstable : (prefixWord ++ tailWord_4807178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4807178).length < 2 ^ (prefixWord ++ tailWord_4807178).sum := by decide
  have hdescent : baseEnd_4807178 < baseStart_4807178 := by decide
  rcases family_descends (prefixWord ++ tailWord_4807178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4807194 : List Nat := [3, 1, 1, 3, 1, 1, 2, 1, 1, 6, 3]
def baseStart_4807194 : Nat := 118140960795 + 4807194 * 2 ^ 59
def prefixEnd_4807194 : Nat := 4983230072969 + 3 ^ 40 * 4807194 * 2
def baseEnd_4807194 : Nat := 2468401121409770065067123

theorem tailTrace_4807194 : CollatzResearch.WordTrace tailWord_4807194 prefixEnd_4807194 2468401121409770065067123 := by
  unfold tailWord_4807194
  simp only [CollatzResearch.WordTrace]
  refine ⟨43833192336591154054223159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 116888512897576410811261757 43833192336591154054223159)
  ·
    refine ⟨65749788504886731081334739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43833192336591154054223159 65749788504886731081334739)
    ·
      refine ⟨98624682757330096622002109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65749788504886731081334739 98624682757330096622002109)
      ·
        refine ⟨36984256033998786233250791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 98624682757330096622002109 36984256033998786233250791)
        ·
          refine ⟨55476384050998179349876187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36984256033998786233250791 55476384050998179349876187)
          ·
            refine ⟨83214576076497269024814281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55476384050998179349876187 83214576076497269024814281)
            ·
              refine ⟨62410932057372951768610711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 83214576076497269024814281 62410932057372951768610711)
              ·
                refine ⟨93616398086059427652916067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62410932057372951768610711 93616398086059427652916067)
                ·
                  refine ⟨140424597129089141479374101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 93616398086059427652916067 140424597129089141479374101)
                  ·
                    refine ⟨6582402990426053506845661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 140424597129089141479374101 6582402990426053506845661)
                    ·
                      refine ⟨2468401121409770065067123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6582402990426053506845661 2468401121409770065067123)
                      ·
                        rfl

theorem cell23_4807194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 1, 1, 6, 3].length) (baseStart_4807194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4807194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4807194 prefixEnd_4807194 := by exact prefixLift 4807194
  have htrace : WordTrace (prefixWord ++ tailWord_4807194) baseStart_4807194 baseEnd_4807194 := by
    simpa [prefixWord, tailWord_4807194, baseEnd_4807194] using wordTrace_append hprefix tailTrace_4807194
  have hstable : (prefixWord ++ tailWord_4807194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4807194).length < 2 ^ (prefixWord ++ tailWord_4807194).sum := by decide
  have hdescent : baseEnd_4807194 < baseStart_4807194 := by decide
  rcases family_descends (prefixWord ++ tailWord_4807194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4807264 : List Nat := [2, 1, 1, 3, 2, 1, 2, 1, 3, 3, 4]
def baseStart_4807264 : Nat := 118140960795 + 4807264 * 2 ^ 59
def prefixEnd_4807264 : Nat := 4983230072969 + 3 ^ 40 * 4807264 * 2
def baseEnd_4807264 : Nat := 2468437065055584791191801

theorem tailTrace_4807264 : CollatzResearch.WordTrace tailWord_4807264 prefixEnd_4807264 2468437065055584791191801 := by
  unfold tailWord_4807264
  simp only [CollatzResearch.WordTrace]
  refine ⟨87667661228055509085970423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116890214970740678781293897 87667661228055509085970423)
  ·
    refine ⟨131501491842083263628955635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87667661228055509085970423 131501491842083263628955635)
    ·
      refine ⟨197252237763124895443433453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131501491842083263628955635 197252237763124895443433453)
      ·
        refine ⟨73969589161171835791287545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 197252237763124895443433453 73969589161171835791287545)
        ·
          refine ⟨55477191870878876843465659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73969589161171835791287545 55477191870878876843465659)
          ·
            refine ⟨83215787806318315265198489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55477191870878876843465659 83215787806318315265198489)
            ·
              refine ⟨62411840854738736448898867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 83215787806318315265198489 62411840854738736448898867)
              ·
                refine ⟨93617761282108104673348301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62411840854738736448898867 93617761282108104673348301)
                ·
                  refine ⟨35106660480790539252505613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 93617761282108104673348301 35106660480790539252505613)
                  ·
                    refine ⟨13164997680296452219689605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 35106660480790539252505613 13164997680296452219689605)
                    ·
                      refine ⟨2468437065055584791191801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13164997680296452219689605 2468437065055584791191801)
                      ·
                        rfl

theorem cell23_4807264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 1, 3, 3, 4].length) (baseStart_4807264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4807264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4807264 prefixEnd_4807264 := by exact prefixLift 4807264
  have htrace : WordTrace (prefixWord ++ tailWord_4807264) baseStart_4807264 baseEnd_4807264 := by
    simpa [prefixWord, tailWord_4807264, baseEnd_4807264] using wordTrace_append hprefix tailTrace_4807264
  have hstable : (prefixWord ++ tailWord_4807264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4807264).length < 2 ^ (prefixWord ++ tailWord_4807264).sum := by decide
  have hdescent : baseEnd_4807264 < baseStart_4807264 := by decide
  rcases family_descends (prefixWord ++ tailWord_4807264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4807278 : List Nat := [4, 1, 2, 2, 2, 2, 2, 1, 2, 5]
def baseStart_4807278 : Nat := 118140960795 + 4807278 * 2 ^ 59
def prefixEnd_4807278 : Nat := 4983230072969 + 3 ^ 40 * 4807278 * 2
def baseEnd_4807278 : Nat := 822814751261582578805579

theorem tailTrace_4807278 : CollatzResearch.WordTrace tailWord_4807278 prefixEnd_4807278 822814751261582578805579 := by
  unfold tailWord_4807278
  simp only [CollatzResearch.WordTrace]
  refine ⟨21916979134757537320368811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 116890555385373532375300325 21916979134757537320368811)
  ·
    refine ⟨32875468702136305980553217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21916979134757537320368811 32875468702136305980553217)
    ·
      refine ⟨24656601526602229485414913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32875468702136305980553217 24656601526602229485414913)
      ·
        refine ⟨18492451144951672114061185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24656601526602229485414913 18492451144951672114061185)
        ·
          refine ⟨13869338358713754085545889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18492451144951672114061185 13869338358713754085545889)
          ·
            refine ⟨10402003769035315564159417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13869338358713754085545889 10402003769035315564159417)
            ·
              refine ⟨7801502826776486673119563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10402003769035315564159417 7801502826776486673119563)
              ·
                refine ⟨11702254240164730009679345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7801502826776486673119563 11702254240164730009679345)
                ·
                  refine ⟨8776690680123547507259509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11702254240164730009679345 8776690680123547507259509)
                  ·
                    refine ⟨822814751261582578805579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8776690680123547507259509 822814751261582578805579)
                    ·
                      rfl

theorem cell23_4807278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 2, 1, 2, 5].length) (baseStart_4807278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4807278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4807278 prefixEnd_4807278 := by exact prefixLift 4807278
  have htrace : WordTrace (prefixWord ++ tailWord_4807278) baseStart_4807278 baseEnd_4807278 := by
    simpa [prefixWord, tailWord_4807278, baseEnd_4807278] using wordTrace_append hprefix tailTrace_4807278
  have hstable : (prefixWord ++ tailWord_4807278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4807278).length < 2 ^ (prefixWord ++ tailWord_4807278).sum := by decide
  have hdescent : baseEnd_4807278 < baseStart_4807278 := by decide
  rcases family_descends (prefixWord ++ tailWord_4807278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4807281 : List Nat := [1, 2, 2, 2, 1, 1, 1, 1, 6, 4, 2]
def baseStart_4807281 : Nat := 118140960795 + 4807281 * 2 ^ 59
def prefixEnd_4807281 : Nat := 4983230072969 + 3 ^ 40 * 4807281 * 2
def baseEnd_4807281 : Nat := 2468445794226711224679223

theorem tailTrace_4807281 : CollatzResearch.WordTrace tailWord_4807281 prefixEnd_4807281 2468445794226711224679223 := by
  unfold tailWord_4807281
  simp only [CollatzResearch.WordTrace]
  refine ⟨175335942497049430075309697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116890628331366286716873131 175335942497049430075309697)
  ·
    refine ⟨131501956872787072556482273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 175335942497049430075309697 131501956872787072556482273)
    ·
      refine ⟨98626467654590304417361705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 131501956872787072556482273 98626467654590304417361705)
      ·
        refine ⟨73969850740942728313021279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 98626467654590304417361705 73969850740942728313021279)
        ·
          refine ⟨110954776111414092469531919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73969850740942728313021279 110954776111414092469531919)
          ·
            refine ⟨166432164167121138704297879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 110954776111414092469531919 166432164167121138704297879)
            ·
              refine ⟨249648246250681708056446819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 166432164167121138704297879 249648246250681708056446819)
              ·
                refine ⟨374472369376022562084670229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 249648246250681708056446819 374472369376022562084670229)
                ·
                  refine ⟨17553392314501057597718917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 374472369376022562084670229 17553392314501057597718917)
                  ·
                    refine ⟨3291261058968948299572297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17553392314501057597718917 3291261058968948299572297)
                    ·
                      refine ⟨2468445794226711224679223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3291261058968948299572297 2468445794226711224679223)
                      ·
                        rfl

theorem cell23_4807281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 1, 6, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 1, 6, 4, 2].length) (baseStart_4807281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4807281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4807281 prefixEnd_4807281 := by exact prefixLift 4807281
  have htrace : WordTrace (prefixWord ++ tailWord_4807281) baseStart_4807281 baseEnd_4807281 := by
    simpa [prefixWord, tailWord_4807281, baseEnd_4807281] using wordTrace_append hprefix tailTrace_4807281
  have hstable : (prefixWord ++ tailWord_4807281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4807281).length < 2 ^ (prefixWord ++ tailWord_4807281).sum := by decide
  have hdescent : baseEnd_4807281 < baseStart_4807281 := by decide
  rcases family_descends (prefixWord ++ tailWord_4807281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4807335 : List Nat := [1, 1, 6, 3, 1, 1, 1, 1, 1, 4, 3]
def baseStart_4807335 : Nat := 118140960795 + 4807335 * 2 ^ 59
def prefixEnd_4807335 : Nat := 4983230072969 + 3 ^ 40 * 4807335 * 2
def baseEnd_4807335 : Nat := 2468473522182054013403975

theorem tailTrace_4807335 : CollatzResearch.WordTrace tailWord_4807335 prefixEnd_4807335 2468473522182054013403975 := by
  unfold tailWord_4807335
  simp only [CollatzResearch.WordTrace]
  refine ⟨175337912038853797297775459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116891941359235864865183639 175337912038853797297775459)
  ·
    refine ⟨263006868058280695946663189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175337912038853797297775459 263006868058280695946663189)
    ·
      refine ⟨12328446940231907622499837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 263006868058280695946663189 12328446940231907622499837)
      ·
        refine ⟨4623167602586965358437439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12328446940231907622499837 4623167602586965358437439)
        ·
          refine ⟨6934751403880448037656159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4623167602586965358437439 6934751403880448037656159)
          ·
            refine ⟨10402127105820672056484239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6934751403880448037656159 10402127105820672056484239)
            ·
              refine ⟨15603190658731008084726359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10402127105820672056484239 15603190658731008084726359)
              ·
                refine ⟨23404785988096512127089539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15603190658731008084726359 23404785988096512127089539)
                ·
                  refine ⟨35107178982144768190634309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23404785988096512127089539 35107178982144768190634309)
                  ·
                    refine ⟨6582596059152144035743933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 35107178982144768190634309 6582596059152144035743933)
                    ·
                      refine ⟨2468473522182054013403975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6582596059152144035743933 2468473522182054013403975)
                      ·
                        rfl

theorem cell23_4807335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 1, 1, 1, 4, 3].length) (baseStart_4807335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4807335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4807335 prefixEnd_4807335 := by exact prefixLift 4807335
  have htrace : WordTrace (prefixWord ++ tailWord_4807335) baseStart_4807335 baseEnd_4807335 := by
    simpa [prefixWord, tailWord_4807335, baseEnd_4807335] using wordTrace_append hprefix tailTrace_4807335
  have hstable : (prefixWord ++ tailWord_4807335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4807335).length < 2 ^ (prefixWord ++ tailWord_4807335).sum := by decide
  have hdescent : baseEnd_4807335 < baseStart_4807335 := by decide
  rcases family_descends (prefixWord ++ tailWord_4807335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4807342 : List Nat := [4, 1, 4, 1, 1, 1, 1, 5, 1, 4]
def baseStart_4807342 : Nat := 118140960795 + 4807342 * 2 ^ 59
def prefixEnd_4807342 : Nat := 4983230072969 + 3 ^ 40 * 4807342 * 2
def baseEnd_4807342 : Nat := 822825705515545162005481

theorem tailTrace_4807342 : CollatzResearch.WordTrace tailWord_4807342 prefixEnd_4807342 822825705515545162005481 := by
  unfold tailWord_4807342
  simp only [CollatzResearch.WordTrace]
  refine ⟨21917270918728554686660035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 116892111566552291662186853 21917270918728554686660035)
  ·
    refine ⟨32875906378092832029990053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21917270918728554686660035 32875906378092832029990053)
    ·
      refine ⟨6164232445892406005623135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32875906378092832029990053 6164232445892406005623135)
      ·
        refine ⟨9246348668838609008434703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6164232445892406005623135 9246348668838609008434703)
        ·
          refine ⟨13869523003257913512652055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9246348668838609008434703 13869523003257913512652055)
          ·
            refine ⟨20804284504886870268978083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13869523003257913512652055 20804284504886870268978083)
            ·
              refine ⟨31206426757330305403467125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20804284504886870268978083 31206426757330305403467125)
              ·
                refine ⟨2925602508499716131575043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 31206426757330305403467125 2925602508499716131575043)
                ·
                  refine ⟨4388403762749574197362565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2925602508499716131575043 4388403762749574197362565)
                  ·
                    refine ⟨822825705515545162005481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4388403762749574197362565 822825705515545162005481)
                    ·
                      rfl

theorem cell23_4807342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 1, 5, 1, 4].length) (baseStart_4807342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4807342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4807342 prefixEnd_4807342 := by exact prefixLift 4807342
  have htrace : WordTrace (prefixWord ++ tailWord_4807342) baseStart_4807342 baseEnd_4807342 := by
    simpa [prefixWord, tailWord_4807342, baseEnd_4807342] using wordTrace_append hprefix tailTrace_4807342
  have hstable : (prefixWord ++ tailWord_4807342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4807342).length < 2 ^ (prefixWord ++ tailWord_4807342).sum := by decide
  have hdescent : baseEnd_4807342 < baseStart_4807342 := by decide
  rcases family_descends (prefixWord ++ tailWord_4807342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4807344 : List Nat := [2, 1, 1, 1, 2, 1, 3, 1, 2, 4, 5]
def baseStart_4807344 : Nat := 118140960795 + 4807344 * 2 ^ 59
def prefixEnd_4807344 : Nat := 4983230072969 + 3 ^ 40 * 4807344 * 2
def baseEnd_4807344 : Nat := 2468478143507944478191433

theorem tailTrace_4807344 : CollatzResearch.WordTrace tailWord_4807344 prefixEnd_4807344 2468478143507944478191433 := by
  unfold tailWord_4807344
  simp only [CollatzResearch.WordTrace]
  refine ⟨87669120147910595917426543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116892160197214127889902057 87669120147910595917426543)
  ·
    refine ⟨131503680221865893876139815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87669120147910595917426543 131503680221865893876139815)
    ·
      refine ⟨197255520332798840814209723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131503680221865893876139815 197255520332798840814209723)
      ·
        refine ⟨295883280499198261221314585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 197255520332798840814209723 295883280499198261221314585)
        ·
          refine ⟨221912460374398695915985939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 295883280499198261221314585 221912460374398695915985939)
          ·
            refine ⟨332868690561598043873978909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 221912460374398695915985939 332868690561598043873978909)
            ·
              refine ⟨124825758960599266452742091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 332868690561598043873978909 124825758960599266452742091)
              ·
                refine ⟨187238638440898899679113137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 124825758960599266452742091 187238638440898899679113137)
                ·
                  refine ⟨140428978830674174759334853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 187238638440898899679113137 140428978830674174759334853)
                  ·
                    refine ⟨26330433530751407767375285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 140428978830674174759334853 26330433530751407767375285)
                    ·
                      refine ⟨2468478143507944478191433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26330433530751407767375285 2468478143507944478191433)
                      ·
                        rfl

theorem cell23_4807344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 1, 2, 4, 5].length) (baseStart_4807344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4807344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4807344 prefixEnd_4807344 := by exact prefixLift 4807344
  have htrace : WordTrace (prefixWord ++ tailWord_4807344) baseStart_4807344 baseEnd_4807344 := by
    simpa [prefixWord, tailWord_4807344, baseEnd_4807344] using wordTrace_append hprefix tailTrace_4807344
  have hstable : (prefixWord ++ tailWord_4807344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4807344).length < 2 ^ (prefixWord ++ tailWord_4807344).sum := by decide
  have hdescent : baseEnd_4807344 < baseStart_4807344 := by decide
  rcases family_descends (prefixWord ++ tailWord_4807344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4807401 : List Nat := [1, 2, 1, 1, 1, 2, 4, 4, 1, 2, 4]
def baseStart_4807401 : Nat := 118140960795 + 4807401 * 2 ^ 59
def prefixEnd_4807401 : Nat := 4983230072969 + 3 ^ 40 * 4807401 * 2
def baseEnd_4807401 : Nat := 2468507411905250755178671

theorem tailTrace_4807401 : CollatzResearch.WordTrace tailWord_4807401 prefixEnd_4807401 2468507411905250755178671 := by
  unfold tailWord_4807401
  simp only [CollatzResearch.WordTrace]
  refine ⟨175340319256614690569678057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116893546171076460379785371 175340319256614690569678057)
  ·
    refine ⟨131505239442461017927258543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 175340319256614690569678057 131505239442461017927258543)
    ·
      refine ⟨197257859163691526890887815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131505239442461017927258543 197257859163691526890887815)
      ·
        refine ⟨295886788745537290336331723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 197257859163691526890887815 295886788745537290336331723)
        ·
          refine ⟨443830183118305935504497585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 295886788745537290336331723 443830183118305935504497585)
          ·
            refine ⟨332872637338729451628373189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 443830183118305935504497585 332872637338729451628373189)
            ·
              refine ⟨62413619501011772180319973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 332872637338729451628373189 62413619501011772180319973)
              ·
                refine ⟨11702553656439707283809995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 62413619501011772180319973 11702553656439707283809995)
                ·
                  refine ⟨17553830484659560925714993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11702553656439707283809995 17553830484659560925714993)
                  ·
                    refine ⟨13165372863494670694286245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17553830484659560925714993 13165372863494670694286245)
                    ·
                      refine ⟨2468507411905250755178671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13165372863494670694286245 2468507411905250755178671)
                      ·
                        rfl

theorem cell23_4807401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 4, 1, 2, 4].length) (baseStart_4807401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4807401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4807401 prefixEnd_4807401 := by exact prefixLift 4807401
  have htrace : WordTrace (prefixWord ++ tailWord_4807401) baseStart_4807401 baseEnd_4807401 := by
    simpa [prefixWord, tailWord_4807401, baseEnd_4807401] using wordTrace_append hprefix tailTrace_4807401
  have hstable : (prefixWord ++ tailWord_4807401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4807401).length < 2 ^ (prefixWord ++ tailWord_4807401).sum := by decide
  have hdescent : baseEnd_4807401 < baseStart_4807401 := by decide
  rcases family_descends (prefixWord ++ tailWord_4807401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4807408 : List Nat := [2, 1, 1, 1, 3, 1, 3, 5, 1, 2, 3]
def baseStart_4807408 : Nat := 118140960795 + 4807408 * 2 ^ 59
def prefixEnd_4807408 : Nat := 4983230072969 + 3 ^ 40 * 4807408 * 2
def baseEnd_4807408 : Nat := 2468511006269832227791139

theorem tailTrace_4807408 : CollatzResearch.WordTrace tailWord_4807408 prefixEnd_4807408 2468511006269832227791139 := by
  unfold tailWord_4807408
  simp only [CollatzResearch.WordTrace]
  refine ⟨87670287283794665382591439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116893716378392887176788585 87670287283794665382591439)
  ·
    refine ⟨131505430925691998073887159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87670287283794665382591439 131505430925691998073887159)
    ·
      refine ⟨197258146388537997110830739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131505430925691998073887159 197258146388537997110830739)
      ·
        refine ⟨295887219582806995666246109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 197258146388537997110830739 295887219582806995666246109)
        ·
          refine ⟨110957707343552623374842291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 295887219582806995666246109 110957707343552623374842291)
          ·
            refine ⟨166436561015328935062263437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 110957707343552623374842291 166436561015328935062263437)
            ·
              refine ⟨62413710380748350648348789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 166436561015328935062263437 62413710380748350648348789)
              ·
                refine ⟨5851285348195157873282699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 62413710380748350648348789 5851285348195157873282699)
                ·
                  refine ⟨8776928022292736809924049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5851285348195157873282699 8776928022292736809924049)
                  ·
                    refine ⟨6582696016719552607443037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8776928022292736809924049 6582696016719552607443037)
                    ·
                      refine ⟨2468511006269832227791139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6582696016719552607443037 2468511006269832227791139)
                      ·
                        rfl

theorem cell23_4807408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 5, 1, 2, 3].length) (baseStart_4807408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4807408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4807408 prefixEnd_4807408 := by exact prefixLift 4807408
  have htrace : WordTrace (prefixWord ++ tailWord_4807408) baseStart_4807408 baseEnd_4807408 := by
    simpa [prefixWord, tailWord_4807408, baseEnd_4807408] using wordTrace_append hprefix tailTrace_4807408
  have hstable : (prefixWord ++ tailWord_4807408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4807408).length < 2 ^ (prefixWord ++ tailWord_4807408).sum := by decide
  have hdescent : baseEnd_4807408 < baseStart_4807408 := by decide
  rcases family_descends (prefixWord ++ tailWord_4807408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4807432 : List Nat := [2, 1, 3, 2, 2, 4, 2, 1, 2, 4]
def baseStart_4807432 : Nat := 118140960795 + 4807432 * 2 ^ 59
def prefixEnd_4807432 : Nat := 4983230072969 + 3 ^ 40 * 4807432 * 2
def baseEnd_4807432 : Nat := 822841109935180044630343

theorem tailTrace_4807432 : CollatzResearch.WordTrace tailWord_4807432 prefixEnd_4807432 822841109935180044630343 := by
  unfold tailWord_4807432
  simp only [CollatzResearch.WordTrace]
  refine ⟨87670724959751191432028275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116894299946334921909371033 87670724959751191432028275)
  ·
    refine ⟨131506087439626787148042413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87670724959751191432028275 131506087439626787148042413)
    ·
      refine ⟨49314782789860045180515905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 131506087439626787148042413 49314782789860045180515905)
      ·
        refine ⟨36986087092395033885386929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49314782789860045180515905 36986087092395033885386929)
        ·
          refine ⟨27739565319296275414040197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36986087092395033885386929 27739565319296275414040197)
          ·
            refine ⟨5201168497368051640132537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27739565319296275414040197 5201168497368051640132537)
            ·
              refine ⟨3900876373026038730099403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5201168497368051640132537 3900876373026038730099403)
              ·
                refine ⟨5851314559539058095149105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3900876373026038730099403 5851314559539058095149105)
                ·
                  refine ⟨4388485919654293571361829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5851314559539058095149105 4388485919654293571361829)
                  ·
                    refine ⟨822841109935180044630343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4388485919654293571361829 822841109935180044630343)
                    ·
                      rfl

theorem cell23_4807432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 4, 2, 1, 2, 4].length) (baseStart_4807432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4807432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4807432 prefixEnd_4807432 := by exact prefixLift 4807432
  have htrace : WordTrace (prefixWord ++ tailWord_4807432) baseStart_4807432 baseEnd_4807432 := by
    simpa [prefixWord, tailWord_4807432, baseEnd_4807432] using wordTrace_append hprefix tailTrace_4807432
  have hstable : (prefixWord ++ tailWord_4807432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4807432).length < 2 ^ (prefixWord ++ tailWord_4807432).sum := by decide
  have hdescent : baseEnd_4807432 < baseStart_4807432 := by decide
  rcases family_descends (prefixWord ++ tailWord_4807432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4807438 : List Nat := [4, 1, 1, 2, 1, 1, 1, 5, 1, 3, 3]
def baseStart_4807438 : Nat := 118140960795 + 4807438 * 2 ^ 59
def prefixEnd_4807438 : Nat := 4983230072969 + 3 ^ 40 * 4807438 * 2
def baseEnd_4807438 : Nat := 2468526410689467110416001

theorem tailTrace_4807438 : CollatzResearch.WordTrace tailWord_4807438 prefixEnd_4807438 2468526410689467110416001 := by
  unfold tailWord_4807438
  simp only [CollatzResearch.WordTrace]
  refine ⟨21917708594685080736096871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 116894445838320430592516645 21917708594685080736096871)
  ·
    refine ⟨32876562892027621104145307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21917708594685080736096871 32876562892027621104145307)
    ·
      refine ⟨49314844338041431656217961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32876562892027621104145307 49314844338041431656217961)
      ·
        refine ⟨36986133253531073742163471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49314844338041431656217961 36986133253531073742163471)
        ·
          refine ⟨55479199880296610613245207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36986133253531073742163471 55479199880296610613245207)
          ·
            refine ⟨83218799820444915919867811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55479199880296610613245207 83218799820444915919867811)
            ·
              refine ⟨124828199730667373879801717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83218799820444915919867811 124828199730667373879801717)
              ·
                refine ⟨11702643724750066301231411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 124828199730667373879801717 11702643724750066301231411)
                ·
                  refine ⟨17553965587125099451847117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11702643724750066301231411 17553965587125099451847117)
                  ·
                    refine ⟨6582737095171912294442669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17553965587125099451847117 6582737095171912294442669)
                    ·
                      refine ⟨2468526410689467110416001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6582737095171912294442669 2468526410689467110416001)
                      ·
                        rfl

theorem cell23_4807438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 5, 1, 3, 3].length) (baseStart_4807438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4807438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4807438 prefixEnd_4807438 := by exact prefixLift 4807438
  have htrace : WordTrace (prefixWord ++ tailWord_4807438) baseStart_4807438 baseEnd_4807438 := by
    simpa [prefixWord, tailWord_4807438, baseEnd_4807438] using wordTrace_append hprefix tailTrace_4807438
  have hstable : (prefixWord ++ tailWord_4807438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4807438).length < 2 ^ (prefixWord ++ tailWord_4807438).sum := by decide
  have hdescent : baseEnd_4807438 < baseStart_4807438 := by decide
  rcases family_descends (prefixWord ++ tailWord_4807438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4807442 : List Nat := [3, 2, 4, 1, 2, 1, 1, 1, 3, 2, 3]
def baseStart_4807442 : Nat := 118140960795 + 4807442 * 2 ^ 59
def prefixEnd_4807442 : Nat := 4983230072969 + 3 ^ 40 * 4807442 * 2
def baseEnd_4807442 : Nat := 2468528464612085094765983

theorem tailTrace_4807442 : CollatzResearch.WordTrace tailWord_4807442 prefixEnd_4807442 2468528464612085094765983 := by
  unfold tailWord_4807442
  simp only [CollatzResearch.WordTrace]
  refine ⟨43835453662366538642980145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 116894543099644103047947053 43835453662366538642980145)
  ·
    refine ⟨32876590246774903982235109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43835453662366538642980145 32876590246774903982235109)
    ·
      refine ⟨6164360671270294496669083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32876590246774903982235109 6164360671270294496669083)
      ·
        refine ⟨9246541006905441745003625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6164360671270294496669083 9246541006905441745003625)
        ·
          refine ⟨6934905755179081308752719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9246541006905441745003625 6934905755179081308752719)
          ·
            refine ⟨10402358632768621963129079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6934905755179081308752719 10402358632768621963129079)
            ·
              refine ⟨15603537949152932944693619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10402358632768621963129079 15603537949152932944693619)
              ·
                refine ⟨23405306923729399417040429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15603537949152932944693619 23405306923729399417040429)
                ·
                  refine ⟨8776990096398524781390161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23405306923729399417040429 8776990096398524781390161)
                  ·
                    refine ⟨6582742572298893586042621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8776990096398524781390161 6582742572298893586042621)
                    ·
                      refine ⟨2468528464612085094765983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6582742572298893586042621 2468528464612085094765983)
                      ·
                        rfl

theorem cell23_4807442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 1, 1, 3, 2, 3].length) (baseStart_4807442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4807442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4807442 prefixEnd_4807442 := by exact prefixLift 4807442
  have htrace : WordTrace (prefixWord ++ tailWord_4807442) baseStart_4807442 baseEnd_4807442 := by
    simpa [prefixWord, tailWord_4807442, baseEnd_4807442] using wordTrace_append hprefix tailTrace_4807442
  have hstable : (prefixWord ++ tailWord_4807442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4807442).length < 2 ^ (prefixWord ++ tailWord_4807442).sum := by decide
  have hdescent : baseEnd_4807442 < baseStart_4807442 := by decide
  rcases family_descends (prefixWord ++ tailWord_4807442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4807495 : List Nat := [1, 1, 4, 1, 2, 1, 1, 2, 6, 2, 2]
def baseStart_4807495 : Nat := 118140960795 + 4807495 * 2 ^ 59
def prefixEnd_4807495 : Nat := 4983230072969 + 3 ^ 40 * 4807495 * 2
def baseEnd_4807495 : Nat := 2468555679086773387403239

theorem tailTrace_4807495 : CollatzResearch.WordTrace tailWord_4807495 prefixEnd_4807495 2468555679086773387403239 := by
  unfold tailWord_4807495
  simp only [CollatzResearch.WordTrace]
  refine ⟨175343747718274144623599939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116895831812182763082399959 175343747718274144623599939)
  ·
    refine ⟨263015621577411216935399909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175343747718274144623599939 263015621577411216935399909)
    ·
      refine ⟨49315429045764603175387483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 263015621577411216935399909 49315429045764603175387483)
      ·
        refine ⟨73973143568646904763081225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49315429045764603175387483 73973143568646904763081225)
        ·
          refine ⟨55479857676485178572310919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73973143568646904763081225 55479857676485178572310919)
          ·
            refine ⟨83219786514727767858466379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55479857676485178572310919 83219786514727767858466379)
            ·
              refine ⟨124829679772091651787699569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83219786514727767858466379 124829679772091651787699569)
              ·
                refine ⟨93622259829068738840774677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 124829679772091651787699569 93622259829068738840774677)
                ·
                  refine ⟨4388543429487597133161313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 93622259829068738840774677 4388543429487597133161313)
                  ·
                    refine ⟨3291407572115697849870985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4388543429487597133161313 3291407572115697849870985)
                    ·
                      refine ⟨2468555679086773387403239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3291407572115697849870985 2468555679086773387403239)
                      ·
                        rfl

theorem cell23_4807495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 2, 6, 2, 2].length) (baseStart_4807495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4807495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4807495 prefixEnd_4807495 := by exact prefixLift 4807495
  have htrace : WordTrace (prefixWord ++ tailWord_4807495) baseStart_4807495 baseEnd_4807495 := by
    simpa [prefixWord, tailWord_4807495, baseEnd_4807495] using wordTrace_append hprefix tailTrace_4807495
  have hstable : (prefixWord ++ tailWord_4807495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4807495).length < 2 ^ (prefixWord ++ tailWord_4807495).sum := by decide
  have hdescent : baseEnd_4807495 < baseStart_4807495 := by decide
  rcases family_descends (prefixWord ++ tailWord_4807495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4807516 : List Nat := [2, 2, 4, 2, 1, 3, 2, 1, 1, 3, 2]
def baseStart_4807516 : Nat := 118140960795 + 4807516 * 2 ^ 59
def prefixEnd_4807516 : Nat := 4983230072969 + 3 ^ 40 * 4807516 * 2
def baseEnd_4807516 : Nat := 2468566462180517805240643

theorem tailTrace_4807516 : CollatzResearch.WordTrace tailWord_4807516 prefixEnd_4807516 2468566462180517805240643 := by
  unfold tailWord_4807516
  simp only [CollatzResearch.WordTrace]
  refine ⟨87672256825599032605057201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116896342434132043473409601 87672256825599032605057201)
  ·
    refine ⟨65754192619199274453792901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87672256825599032605057201 65754192619199274453792901)
    ·
      refine ⟨12328911116099863960086169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 65754192619199274453792901 12328911116099863960086169)
      ·
        refine ⟨9246683337074897970064627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12328911116099863960086169 9246683337074897970064627)
        ·
          refine ⟨13870025005612346955096941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9246683337074897970064627 13870025005612346955096941)
          ·
            refine ⟨5201259377104630108161353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13870025005612346955096941 5201259377104630108161353)
            ·
              refine ⟨3900944532828472581121015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5201259377104630108161353 3900944532828472581121015)
              ·
                refine ⟨5851416799242708871681523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3900944532828472581121015 5851416799242708871681523)
                ·
                  refine ⟨8777125198864063307522285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5851416799242708871681523 8777125198864063307522285)
                  ·
                    refine ⟨3291421949574023740320857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8777125198864063307522285 3291421949574023740320857)
                    ·
                      refine ⟨2468566462180517805240643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3291421949574023740320857 2468566462180517805240643)
                      ·
                        rfl

theorem cell23_4807516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 3, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 3, 2, 1, 1, 3, 2].length) (baseStart_4807516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4807516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4807516 prefixEnd_4807516 := by exact prefixLift 4807516
  have htrace : WordTrace (prefixWord ++ tailWord_4807516) baseStart_4807516 baseEnd_4807516 := by
    simpa [prefixWord, tailWord_4807516, baseEnd_4807516] using wordTrace_append hprefix tailTrace_4807516
  have hstable : (prefixWord ++ tailWord_4807516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4807516).length < 2 ^ (prefixWord ++ tailWord_4807516).sum := by decide
  have hdescent : baseEnd_4807516 < baseStart_4807516 := by decide
  rcases family_descends (prefixWord ++ tailWord_4807516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4807585 : List Nat := [1, 2, 3, 4, 1, 1, 1, 1, 4, 1, 4]
def baseStart_4807585 : Nat := 118140960795 + 4807585 * 2 ^ 59
def prefixEnd_4807585 : Nat := 4983230072969 + 3 ^ 40 * 4807585 * 2
def baseEnd_4807585 : Nat := 2468601892345678035277825

theorem tailTrace_4807585 : CollatzResearch.WordTrace tailWord_4807585 prefixEnd_4807585 2468601892345678035277825 := by
  unfold tailWord_4807585
  simp only [CollatzResearch.WordTrace]
  refine ⟨175347030287948089994376209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116898020191965393329584139 175347030287948089994376209)
  ·
    refine ⟨131510272715961067495782157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 175347030287948089994376209 131510272715961067495782157)
    ·
      refine ⟨49316352268485400310918309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 131510272715961067495782157 49316352268485400310918309)
      ·
        refine ⟨9246816050341012558297183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 49316352268485400310918309 9246816050341012558297183)
        ·
          refine ⟨13870224075511518837445775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9246816050341012558297183 13870224075511518837445775)
          ·
            refine ⟨20805336113267278256168663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13870224075511518837445775 20805336113267278256168663)
            ·
              refine ⟨31208004169900917384252995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20805336113267278256168663 31208004169900917384252995)
              ·
                refine ⟨46812006254851376076379493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31208004169900917384252995 46812006254851376076379493)
                ·
                  refine ⟨8777251172784633014321155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 46812006254851376076379493 8777251172784633014321155)
                  ·
                    refine ⟨13165876759176949521481733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8777251172784633014321155 13165876759176949521481733)
                    ·
                      refine ⟨2468601892345678035277825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13165876759176949521481733 2468601892345678035277825)
                      ·
                        rfl

theorem cell23_4807585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 1, 1, 4, 1, 4].length) (baseStart_4807585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4807585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4807585 prefixEnd_4807585 := by exact prefixLift 4807585
  have htrace : WordTrace (prefixWord ++ tailWord_4807585) baseStart_4807585 baseEnd_4807585 := by
    simpa [prefixWord, tailWord_4807585, baseEnd_4807585] using wordTrace_append hprefix tailTrace_4807585
  have hstable : (prefixWord ++ tailWord_4807585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4807585).length < 2 ^ (prefixWord ++ tailWord_4807585).sum := by decide
  have hdescent : baseEnd_4807585 < baseStart_4807585 := by decide
  rcases family_descends (prefixWord ++ tailWord_4807585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4807605 : List Nat := [1, 3, 3, 2, 1, 1, 1, 2, 4, 2, 3]
def baseStart_4807605 : Nat := 118140960795 + 4807605 * 2 ^ 59
def prefixEnd_4807605 : Nat := 4983230072969 + 3 ^ 40 * 4807605 * 2
def baseEnd_4807605 : Nat := 2468612161958767957027733

theorem tailTrace_4807605 : CollatzResearch.WordTrace tailWord_4807605 prefixEnd_4807605 2468612161958767957027733 := by
  unfold tailWord_4807605
  simp only [CollatzResearch.WordTrace]
  refine ⟨175347759747875633410104269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116898506498583755606736179 175347759747875633410104269)
  ·
    refine ⟨65755409905453362528789101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 175347759747875633410104269 65755409905453362528789101)
    ·
      refine ⟨24658278714545010948295913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65755409905453362528789101 24658278714545010948295913)
      ·
        refine ⟨18493709035908758211221935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24658278714545010948295913 18493709035908758211221935)
        ·
          refine ⟨27740563553863137316832903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18493709035908758211221935 27740563553863137316832903)
          ·
            refine ⟨41610845330794705975249355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27740563553863137316832903 41610845330794705975249355)
            ·
              refine ⟨62416267996192058962874033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41610845330794705975249355 62416267996192058962874033)
              ·
                refine ⟨46812200997144044222155525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 62416267996192058962874033 46812200997144044222155525)
                ·
                  refine ⟨8777287686964508291654161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 46812200997144044222155525 8777287686964508291654161)
                  ·
                    refine ⟨6582965765223381218740621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8777287686964508291654161 6582965765223381218740621)
                    ·
                      refine ⟨2468612161958767957027733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6582965765223381218740621 2468612161958767957027733)
                      ·
                        rfl

theorem cell23_4807605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 2, 4, 2, 3].length) (baseStart_4807605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4807605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4807605 prefixEnd_4807605 := by exact prefixLift 4807605
  have htrace : WordTrace (prefixWord ++ tailWord_4807605) baseStart_4807605 baseEnd_4807605 := by
    simpa [prefixWord, tailWord_4807605, baseEnd_4807605] using wordTrace_append hprefix tailTrace_4807605
  have hstable : (prefixWord ++ tailWord_4807605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4807605).length < 2 ^ (prefixWord ++ tailWord_4807605).sum := by decide
  have hdescent : baseEnd_4807605 < baseStart_4807605 := by decide
  rcases family_descends (prefixWord ++ tailWord_4807605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4807655 : List Nat := [1, 1, 5, 2, 2, 1, 1, 2, 3, 5]
def baseStart_4807655 : Nat := 118140960795 + 4807655 * 2 ^ 59
def prefixEnd_4807655 : Nat := 4983230072969 + 3 ^ 40 * 4807655 * 2
def baseEnd_4807655 : Nat := 822879278663830920467501

theorem tailTrace_4807655 : CollatzResearch.WordTrace tailWord_4807655 prefixEnd_4807655 822879278663830920467501 := by
  unfold tailWord_4807655
  simp only [CollatzResearch.WordTrace]
  refine ⟨175349583397694491949424419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116899722265129661299616279 175349583397694491949424419)
  ·
    refine ⟨263024375096541737924136629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175349583397694491949424419 263024375096541737924136629)
    ·
      refine ⟨24658535165300787930387809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 263024375096541737924136629 24658535165300787930387809)
      ·
        refine ⟨18493901373975590947790857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24658535165300787930387809 18493901373975590947790857)
        ·
          refine ⟨13870426030481693210843143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18493901373975590947790857 13870426030481693210843143)
          ·
            refine ⟨20805639045722539816264715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13870426030481693210843143 20805639045722539816264715)
            ·
              refine ⟨31208458568583809724397073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20805639045722539816264715 31208458568583809724397073)
              ·
                refine ⟨23406343926437857293297805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31208458568583809724397073 23406343926437857293297805)
                ·
                  refine ⟨8777378972414196484986677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23406343926437857293297805 8777378972414196484986677)
                  ·
                    refine ⟨822879278663830920467501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8777378972414196484986677 822879278663830920467501)
                    ·
                      rfl

theorem cell23_4807655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 1, 2, 3, 5].length) (baseStart_4807655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4807655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4807655 prefixEnd_4807655 := by exact prefixLift 4807655
  have htrace : WordTrace (prefixWord ++ tailWord_4807655) baseStart_4807655 baseEnd_4807655 := by
    simpa [prefixWord, tailWord_4807655, baseEnd_4807655] using wordTrace_append hprefix tailTrace_4807655
  have hstable : (prefixWord ++ tailWord_4807655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4807655).length < 2 ^ (prefixWord ++ tailWord_4807655).sum := by decide
  have hdescent : baseEnd_4807655 < baseStart_4807655 := by decide
  rcases family_descends (prefixWord ++ tailWord_4807655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4807675 : List Nat := [1, 1, 1, 1, 1, 3, 3, 6, 1, 1, 4]
def baseStart_4807675 : Nat := 118140960795 + 4807675 * 2 ^ 59
def prefixEnd_4807675 : Nat := 4983230072969 + 3 ^ 40 * 4807675 * 2
def baseEnd_4807675 : Nat := 2468648105604582683152411

theorem tailTrace_4807675 : CollatzResearch.WordTrace tailWord_4807675 prefixEnd_4807675 2468648105604582683152411 := by
  unfold tailWord_4807675
  simp only [CollatzResearch.WordTrace]
  refine ⟨175350312857622035365152479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116900208571748023576768319 175350312857622035365152479)
  ·
    refine ⟨263025469286433053047728719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175350312857622035365152479 263025469286433053047728719)
    ·
      refine ⟨394538203929649579571593079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 263025469286433053047728719 394538203929649579571593079)
      ·
        refine ⟨591807305894474369357389619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 394538203929649579571593079 591807305894474369357389619)
        ·
          refine ⟨887710958841711554036084429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 591807305894474369357389619 887710958841711554036084429)
          ·
            refine ⟨332891609565641832763531661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 887710958841711554036084429 332891609565641832763531661)
            ·
              refine ⟨124834353587115687286324373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 332891609565641832763531661 124834353587115687286324373)
              ·
                refine ⟨5851610324396047841546455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 124834353587115687286324373 5851610324396047841546455)
                ·
                  refine ⟨8777415486594071762319683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5851610324396047841546455 8777415486594071762319683)
                  ·
                    refine ⟨13166123229891107643479525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8777415486594071762319683 13166123229891107643479525)
                    ·
                      refine ⟨2468648105604582683152411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13166123229891107643479525 2468648105604582683152411)
                      ·
                        rfl

theorem cell23_4807675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 6, 1, 1, 4].length) (baseStart_4807675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4807675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4807675 prefixEnd_4807675 := by exact prefixLift 4807675
  have htrace : WordTrace (prefixWord ++ tailWord_4807675) baseStart_4807675 baseEnd_4807675 := by
    simpa [prefixWord, tailWord_4807675, baseEnd_4807675] using wordTrace_append hprefix tailTrace_4807675
  have hstable : (prefixWord ++ tailWord_4807675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4807675).length < 2 ^ (prefixWord ++ tailWord_4807675).sum := by decide
  have hdescent : baseEnd_4807675 < baseStart_4807675 := by decide
  rcases family_descends (prefixWord ++ tailWord_4807675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4807685 : List Nat := [1, 3, 1, 1, 2, 3, 2, 2, 4, 4]
def baseStart_4807685 : Nat := 118140960795 + 4807685 * 2 ^ 59
def prefixEnd_4807685 : Nat := 4983230072969 + 3 ^ 40 * 4807685 * 2
def baseEnd_4807685 : Nat := 822884413470375881342455

theorem tailTrace_4807685 : CollatzResearch.WordTrace tailWord_4807685 prefixEnd_4807685 822884413470375881342455 := by
  unfold tailWord_4807685
  simp only [CollatzResearch.WordTrace]
  refine ⟨175350677587585807073016509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116900451725057204715344339 175350677587585807073016509)
  ·
    refine ⟨65756504095344677652381191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 175350677587585807073016509 65756504095344677652381191)
    ·
      refine ⟨98634756143017016478571787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65756504095344677652381191 98634756143017016478571787)
      ·
        refine ⟨147952134214525524717857681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98634756143017016478571787 147952134214525524717857681)
        ·
          refine ⟨110964100660894143538393261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 147952134214525524717857681 110964100660894143538393261)
          ·
            refine ⟨41611537747835303826897473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 110964100660894143538393261 41611537747835303826897473)
            ·
              refine ⟨31208653310876477870173105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41611537747835303826897473 31208653310876477870173105)
              ·
                refine ⟨23406489983157358402629829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31208653310876477870173105 23406489983157358402629829)
                ·
                  refine ⟨4388716871842004700493093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23406489983157358402629829 4388716871842004700493093)
                  ·
                    refine ⟨822884413470375881342455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4388716871842004700493093 822884413470375881342455)
                    ·
                      rfl

theorem cell23_4807685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 2, 2, 4, 4].length) (baseStart_4807685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4807685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4807685 prefixEnd_4807685 := by exact prefixLift 4807685
  have htrace : WordTrace (prefixWord ++ tailWord_4807685) baseStart_4807685 baseEnd_4807685 := by
    simpa [prefixWord, tailWord_4807685, baseEnd_4807685] using wordTrace_append hprefix tailTrace_4807685
  have hstable : (prefixWord ++ tailWord_4807685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4807685).length < 2 ^ (prefixWord ++ tailWord_4807685).sum := by decide
  have hdescent : baseEnd_4807685 < baseStart_4807685 := by decide
  rcases family_descends (prefixWord ++ tailWord_4807685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4807692 : List Nat := [2, 2, 1, 2, 3, 3, 1, 3, 1, 1, 4]
def baseStart_4807692 : Nat := 118140960795 + 4807692 * 2 ^ 59
def prefixEnd_4807692 : Nat := 4983230072969 + 3 ^ 40 * 4807692 * 2
def baseEnd_4807692 : Nat := 2468656834775709116639833

theorem tailTrace_4807692 : CollatzResearch.WordTrace tailWord_4807692 prefixEnd_4807692 2468656834775709116639833 := by
  unfold tailWord_4807692
  simp only [CollatzResearch.WordTrace]
  refine ⟨87675466449280223634260665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116900621932373631512347553 87675466449280223634260665)
  ·
    refine ⟨65756599836960167725695499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87675466449280223634260665 65756599836960167725695499)
    ·
      refine ⟨98634899755440251588543249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65756599836960167725695499 98634899755440251588543249)
      ·
        refine ⟨73976174816580188691407437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 98634899755440251588543249 73976174816580188691407437)
        ·
          refine ⟨27741065556217570759277789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 73976174816580188691407437 27741065556217570759277789)
          ·
            refine ⟨10402899583581589034729171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27741065556217570759277789 10402899583581589034729171)
            ·
              refine ⟨15604349375372383552093757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10402899583581589034729171 15604349375372383552093757)
              ·
                refine ⟨5851631015764643832035159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15604349375372383552093757 5851631015764643832035159)
                ·
                  refine ⟨8777446523646965748052739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5851631015764643832035159 8777446523646965748052739)
                  ·
                    refine ⟨13166169785470448622079109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8777446523646965748052739 13166169785470448622079109)
                    ·
                      refine ⟨2468656834775709116639833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13166169785470448622079109 2468656834775709116639833)
                      ·
                        rfl

theorem cell23_4807692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 1, 3, 1, 1, 4].length) (baseStart_4807692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4807692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4807692 prefixEnd_4807692 := by exact prefixLift 4807692
  have htrace : WordTrace (prefixWord ++ tailWord_4807692) baseStart_4807692 baseEnd_4807692 := by
    simpa [prefixWord, tailWord_4807692, baseEnd_4807692] using wordTrace_append hprefix tailTrace_4807692
  have hstable : (prefixWord ++ tailWord_4807692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4807692).length < 2 ^ (prefixWord ++ tailWord_4807692).sum := by decide
  have hdescent : baseEnd_4807692 < baseStart_4807692 := by decide
  rcases family_descends (prefixWord ++ tailWord_4807692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4807719 : List Nat := [1, 1, 7, 1, 1, 3, 1, 1, 1, 6]
def baseStart_4807719 : Nat := 118140960795 + 4807719 * 2 ^ 59
def prefixEnd_4807719 : Nat := 4983230072969 + 3 ^ 40 * 4807719 * 2
def baseEnd_4807719 : Nat := 822890232917793503667403

theorem tailTrace_4807719 : CollatzResearch.WordTrace tailWord_4807719 prefixEnd_4807719 822890232917793503667403 := by
  unfold tailWord_4807719
  simp only [CollatzResearch.WordTrace]
  refine ⟨175351917669462630879754211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116901278446308420586502807 175351917669462630879754211)
  ·
    refine ⟨263027876504193946319631317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175351917669462630879754211 263027876504193946319631317)
    ·
      refine ⟨6164715855567045616866359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 263027876504193946319631317 6164715855567045616866359)
      ·
        refine ⟨9247073783350568425299539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6164715855567045616866359 9247073783350568425299539)
        ·
          refine ⟨13870610675025852637949309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9247073783350568425299539 13870610675025852637949309)
          ·
            refine ⟨5201479003134694739230991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13870610675025852637949309 5201479003134694739230991)
            ·
              refine ⟨7802218504702042108846487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5201479003134694739230991 7802218504702042108846487)
              ·
                refine ⟨11703327757053063163269731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7802218504702042108846487 11703327757053063163269731)
                ·
                  refine ⟨17554991635579594744904597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11703327757053063163269731 17554991635579594744904597)
                  ·
                    refine ⟨822890232917793503667403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17554991635579594744904597 822890232917793503667403)
                    ·
                      rfl

theorem cell23_4807719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 3, 1, 1, 1, 6].length) (baseStart_4807719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4807719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4807719 prefixEnd_4807719 := by exact prefixLift 4807719
  have htrace : WordTrace (prefixWord ++ tailWord_4807719) baseStart_4807719 baseEnd_4807719 := by
    simpa [prefixWord, tailWord_4807719, baseEnd_4807719] using wordTrace_append hprefix tailTrace_4807719
  have hstable : (prefixWord ++ tailWord_4807719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4807719).length < 2 ^ (prefixWord ++ tailWord_4807719).sum := by decide
  have hdescent : baseEnd_4807719 < baseStart_4807719 := by decide
  rcases family_descends (prefixWord ++ tailWord_4807719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4807722 : List Nat := [3, 1, 4, 1, 3, 1, 1, 1, 1, 1, 6]
def baseStart_4807722 : Nat := 118140960795 + 4807722 * 2 ^ 59
def prefixEnd_4807722 : Nat := 4983230072969 + 3 ^ 40 * 4807722 * 2
def baseEnd_4807722 : Nat := 2468672239195343999264695

theorem tailTrace_4807722 : CollatzResearch.WordTrace tailWord_4807722 prefixEnd_4807722 2468672239195343999264695 := by
  unfold tailWord_4807722
  simp only [CollatzResearch.WordTrace]
  refine ⟨43838006772112940598028355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 116901351392301174928075613 43838006772112940598028355)
  ·
    refine ⟨65757010158169410897042533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43838006772112940598028355 65757010158169410897042533)
    ·
      refine ⟨12329439404656764543195475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 65757010158169410897042533 12329439404656764543195475)
      ·
        refine ⟨18494159106985146814793213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12329439404656764543195475 18494159106985146814793213)
        ·
          refine ⟨6935309665119430055547455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18494159106985146814793213 6935309665119430055547455)
          ·
            refine ⟨10402964497679145083321183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6935309665119430055547455 10402964497679145083321183)
            ·
              refine ⟨15604446746518717624981775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10402964497679145083321183 15604446746518717624981775)
              ·
                refine ⟨23406670119778076437472663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15604446746518717624981775 23406670119778076437472663)
                ·
                  refine ⟨35110005179667114656208995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23406670119778076437472663 35110005179667114656208995)
                  ·
                    refine ⟨52665007769500671984313493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 35110005179667114656208995 52665007769500671984313493)
                    ·
                      refine ⟨2468672239195343999264695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 52665007769500671984313493 2468672239195343999264695)
                      ·
                        rfl

theorem cell23_4807722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 1, 1, 1, 1, 6].length) (baseStart_4807722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4807722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4807722 prefixEnd_4807722 := by exact prefixLift 4807722
  have htrace : WordTrace (prefixWord ++ tailWord_4807722) baseStart_4807722 baseEnd_4807722 := by
    simpa [prefixWord, tailWord_4807722, baseEnd_4807722] using wordTrace_append hprefix tailTrace_4807722
  have hstable : (prefixWord ++ tailWord_4807722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4807722).length < 2 ^ (prefixWord ++ tailWord_4807722).sum := by decide
  have hdescent : baseEnd_4807722 < baseStart_4807722 := by decide
  rcases family_descends (prefixWord ++ tailWord_4807722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4807732 : List Nat := [2, 5, 1, 2, 1, 2, 1, 9]
def baseStart_4807732 : Nat := 118140960795 + 4807732 * 2 ^ 59
def prefixEnd_4807732 : Nat := 4983230072969 + 3 ^ 40 * 4807732 * 2
def baseEnd_4807732 : Nat := 91432495333403294819987

theorem tailTrace_4807732 : CollatzResearch.WordTrace tailWord_4807732 prefixEnd_4807732 91432495333403294819987 := by
  unfold tailWord_4807732
  simp only [CollatzResearch.WordTrace]
  refine ⟨87676195909207767049988725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116901594545610356066651633 87676195909207767049988725)
  ·
    refine ⟨8219643366488228160936443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 87676195909207767049988725 8219643366488228160936443)
    ·
      refine ⟨12329465049732342241404665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8219643366488228160936443 12329465049732342241404665)
      ·
        refine ⟨9247098787299256681053499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12329465049732342241404665 9247098787299256681053499)
        ·
          refine ⟨13870648180948885021580249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9247098787299256681053499 13870648180948885021580249)
          ·
            refine ⟨10402986135711663766185187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13870648180948885021580249 10402986135711663766185187)
            ·
              refine ⟨15604479203567495649277781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10402986135711663766185187 15604479203567495649277781)
              ·
                refine ⟨91432495333403294819987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 15604479203567495649277781 91432495333403294819987)
                ·
                  rfl

theorem cell23_4807732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 1, 9].length) (baseStart_4807732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4807732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4807732 prefixEnd_4807732 := by exact prefixLift 4807732
  have htrace : WordTrace (prefixWord ++ tailWord_4807732) baseStart_4807732 baseEnd_4807732 := by
    simpa [prefixWord, tailWord_4807732, baseEnd_4807732] using wordTrace_append hprefix tailTrace_4807732
  have hstable : (prefixWord ++ tailWord_4807732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4807732).length < 2 ^ (prefixWord ++ tailWord_4807732).sum := by decide
  have hdescent : baseEnd_4807732 < baseStart_4807732 := by decide
  rcases family_descends (prefixWord ++ tailWord_4807732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4807765 : List Nat := [1, 3, 2, 2, 1, 2, 2, 1, 2, 3, 4]
def baseStart_4807765 : Nat := 118140960795 + 4807765 * 2 ^ 59
def prefixEnd_4807765 : Nat := 4983230072969 + 3 ^ 40 * 4807765 * 2
def baseEnd_4807765 : Nat := 2468694318863487331026997

theorem tailTrace_4807765 : CollatzResearch.WordTrace tailWord_4807765 prefixEnd_4807765 2468694318863487331026997 := by
  unfold tailWord_4807765
  simp only [CollatzResearch.WordTrace]
  refine ⟨175353595427295980735928749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116902396951530653823952499 175353595427295980735928749)
  ·
    refine ⟨65757598285235992775973281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 175353595427295980735928749 65757598285235992775973281)
    ·
      refine ⟨49318198713926994581979961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65757598285235992775973281 49318198713926994581979961)
      ·
        refine ⟨36988649035445245936484971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49318198713926994581979961 36988649035445245936484971)
        ·
          refine ⟨55482973553167868904727457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36988649035445245936484971 55482973553167868904727457)
          ·
            refine ⟨41612230164875901678545593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55482973553167868904727457 41612230164875901678545593)
            ·
              refine ⟨31209172623656926258909195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41612230164875901678545593 31209172623656926258909195)
              ·
                refine ⟨46813758935485389388363793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31209172623656926258909195 46813758935485389388363793)
                ·
                  refine ⟨35110319201614042041272845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 46813758935485389388363793 35110319201614042041272845)
                  ·
                    refine ⟨13166369700605265765477317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 35110319201614042041272845 13166369700605265765477317)
                    ·
                      refine ⟨2468694318863487331026997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13166369700605265765477317 2468694318863487331026997)
                      ·
                        rfl

theorem cell23_4807765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 2, 1, 2, 3, 4].length) (baseStart_4807765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4807765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4807765 prefixEnd_4807765 := by exact prefixLift 4807765
  have htrace : WordTrace (prefixWord ++ tailWord_4807765) baseStart_4807765 baseEnd_4807765 := by
    simpa [prefixWord, tailWord_4807765, baseEnd_4807765] using wordTrace_append hprefix tailTrace_4807765
  have hstable : (prefixWord ++ tailWord_4807765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4807765).length < 2 ^ (prefixWord ++ tailWord_4807765).sum := by decide
  have hdescent : baseEnd_4807765 < baseStart_4807765 := by decide
  rcases family_descends (prefixWord ++ tailWord_4807765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4807785 : List Nat := [1, 2, 1, 1, 1, 6, 1, 2, 2, 1, 5]
def baseStart_4807785 : Nat := 118140960795 + 4807785 * 2 ^ 59
def prefixEnd_4807785 : Nat := 4983230072969 + 3 ^ 40 * 4807785 * 2
def baseEnd_4807785 : Nat := 2468704588476577252776905

theorem tailTrace_4807785 : CollatzResearch.WordTrace tailWord_4807785 prefixEnd_4807785 2468704588476577252776905 := by
  unfold tailWord_4807785
  simp only [CollatzResearch.WordTrace]
  refine ⟨175354324887223524151656809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116902883258149016101104539 175354324887223524151656809)
  ·
    refine ⟨131515743665417643113742607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 175354324887223524151656809 131515743665417643113742607)
    ·
      refine ⟨197273615498126464670613911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131515743665417643113742607 197273615498126464670613911)
      ·
        refine ⟨295910423247189697005920867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 197273615498126464670613911 295910423247189697005920867)
        ·
          refine ⟨443865634870784545508881301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 295910423247189697005920867 443865634870784545508881301)
          ·
            refine ⟨20806201634568025570728811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 443865634870784545508881301 20806201634568025570728811)
            ·
              refine ⟨31209302451852038356093217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20806201634568025570728811 31209302451852038356093217)
              ·
                refine ⟨23406976838889028767069913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31209302451852038356093217 23406976838889028767069913)
                ·
                  refine ⟨17555232629166771575302435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23406976838889028767069913 17555232629166771575302435)
                  ·
                    refine ⟨26332848943750157362953653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17555232629166771575302435 26332848943750157362953653)
                    ·
                      refine ⟨2468704588476577252776905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26332848943750157362953653 2468704588476577252776905)
                      ·
                        rfl

theorem cell23_4807785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 1, 2, 2, 1, 5].length) (baseStart_4807785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4807785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4807785 prefixEnd_4807785 := by exact prefixLift 4807785
  have htrace : WordTrace (prefixWord ++ tailWord_4807785) baseStart_4807785 baseEnd_4807785 := by
    simpa [prefixWord, tailWord_4807785, baseEnd_4807785] using wordTrace_append hprefix tailTrace_4807785
  have hstable : (prefixWord ++ tailWord_4807785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4807785).length < 2 ^ (prefixWord ++ tailWord_4807785).sum := by decide
  have hdescent : baseEnd_4807785 < baseStart_4807785 := by decide
  rcases family_descends (prefixWord ++ tailWord_4807785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4807786 : List Nat := [3, 1, 3, 2, 2, 1, 3, 2, 1, 3, 2]
def baseStart_4807786 : Nat := 118140960795 + 4807786 * 2 ^ 59
def prefixEnd_4807786 : Nat := 4983230072969 + 3 ^ 40 * 4807786 * 2
def baseEnd_4807786 : Nat := 2468705101957231748864401

theorem tailTrace_4807786 : CollatzResearch.WordTrace tailWord_4807786 prefixEnd_4807786 2468705101957231748864401 := by
  unfold tailWord_4807786
  simp only [CollatzResearch.WordTrace]
  refine ⟨43838590340054975330610803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 116902907573479934214962141 43838590340054975330610803)
  ·
    refine ⟨65757885510082462995916205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43838590340054975330610803 65757885510082462995916205)
    ·
      refine ⟨24659207066280923623468577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65757885510082462995916205 24659207066280923623468577)
      ·
        refine ⟨18494405299710692717601433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24659207066280923623468577 18494405299710692717601433)
        ·
          refine ⟨13870803974783019538201075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18494405299710692717601433 13870803974783019538201075)
          ·
            refine ⟨20806205962174529307301613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13870803974783019538201075 20806205962174529307301613)
            ·
              refine ⟨7802327235815448490238105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20806205962174529307301613 7802327235815448490238105)
              ·
                refine ⟨5851745426861586367678579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7802327235815448490238105 5851745426861586367678579)
                ·
                  refine ⟨8777618140292379551517869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5851745426861586367678579 8777618140292379551517869)
                  ·
                    refine ⟨3291606802609642331819201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8777618140292379551517869 3291606802609642331819201)
                    ·
                      refine ⟨2468705101957231748864401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3291606802609642331819201 2468705101957231748864401)
                      ·
                        rfl

theorem cell23_4807786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 3, 2, 1, 3, 2].length) (baseStart_4807786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4807786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4807786 prefixEnd_4807786 := by exact prefixLift 4807786
  have htrace : WordTrace (prefixWord ++ tailWord_4807786) baseStart_4807786 baseEnd_4807786 := by
    simpa [prefixWord, tailWord_4807786, baseEnd_4807786] using wordTrace_append hprefix tailTrace_4807786
  have hstable : (prefixWord ++ tailWord_4807786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4807786).length < 2 ^ (prefixWord ++ tailWord_4807786).sum := by decide
  have hdescent : baseEnd_4807786 < baseStart_4807786 := by decide
  rcases family_descends (prefixWord ++ tailWord_4807786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4807832 : List Nat := [2, 1, 2, 4, 2, 1, 1, 1, 1, 5, 3]
def baseStart_4807832 : Nat := 118140960795 + 4807832 * 2 ^ 59
def prefixEnd_4807832 : Nat := 4983230072969 + 3 ^ 40 * 4807832 * 2
def baseEnd_4807832 : Nat := 2468728722067338568889189

theorem tailTrace_4807832 : CollatzResearch.WordTrace tailWord_4807832 prefixEnd_4807832 2468728722067338568889189 := by
  unfold tailWord_4807832
  simp only [CollatzResearch.WordTrace]
  refine ⟨87678019559026625589308875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116904026078702167452411833 87678019559026625589308875)
  ·
    refine ⟨131517029338539938383963313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87678019559026625589308875 131517029338539938383963313)
    ·
      refine ⟨98637772003904953787972485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 131517029338539938383963313 98637772003904953787972485)
      ·
        refine ⟨18494582250732178835244841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 98637772003904953787972485 18494582250732178835244841)
        ·
          refine ⟨13870936688049134126433631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18494582250732178835244841 13870936688049134126433631)
          ·
            refine ⟨20806405032073701189650447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13870936688049134126433631 20806405032073701189650447)
            ·
              refine ⟨31209607548110551784475671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20806405032073701189650447 31209607548110551784475671)
              ·
                refine ⟨46814411322165827676713507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31209607548110551784475671 46814411322165827676713507)
                ·
                  refine ⟨70221616983248741515070261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 46814411322165827676713507 70221616983248741515070261)
                  ·
                    refine ⟨6583276592179569517037837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 70221616983248741515070261 6583276592179569517037837)
                    ·
                      refine ⟨2468728722067338568889189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6583276592179569517037837 2468728722067338568889189)
                      ·
                        rfl

theorem cell23_4807832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 1, 1, 1, 5, 3].length) (baseStart_4807832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4807832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4807832 prefixEnd_4807832 := by exact prefixLift 4807832
  have htrace : WordTrace (prefixWord ++ tailWord_4807832) baseStart_4807832 baseEnd_4807832 := by
    simpa [prefixWord, tailWord_4807832, baseEnd_4807832] using wordTrace_append hprefix tailTrace_4807832
  have hstable : (prefixWord ++ tailWord_4807832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4807832).length < 2 ^ (prefixWord ++ tailWord_4807832).sum := by decide
  have hdescent : baseEnd_4807832 < baseStart_4807832 := by decide
  rcases family_descends (prefixWord ++ tailWord_4807832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4807916 : List Nat := [2, 2, 1, 1, 2, 4, 3, 3, 1, 4]
def baseStart_4807916 : Nat := 118140960795 + 4807916 * 2 ^ 59
def prefixEnd_4807916 : Nat := 4983230072969 + 3 ^ 40 * 4807916 * 2
def baseEnd_4807916 : Nat := 822923951480772080079601

theorem tailTrace_4807916 : CollatzResearch.WordTrace tailWord_4807916 prefixEnd_4807916 822923951480772080079601 := by
  unfold tailWord_4807916
  simp only [CollatzResearch.WordTrace]
  refine ⟨87679551424874466762337801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116906068566499289016450401 87679551424874466762337801)
  ·
    refine ⟨65759663568655850071753351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87679551424874466762337801 65759663568655850071753351)
    ·
      refine ⟨98639495352983775107630027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65759663568655850071753351 98639495352983775107630027)
      ·
        refine ⟨147959243029475662661445041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98639495352983775107630027 147959243029475662661445041)
        ·
          refine ⟨110969432272106746996083781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 147959243029475662661445041 110969432272106746996083781)
          ·
            refine ⟨20806768551020015061765709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 110969432272106746996083781 20806768551020015061765709)
            ·
              refine ⟨7802538206632505648162141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20806768551020015061765709 7802538206632505648162141)
              ·
                refine ⟨2925951827487189618060803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7802538206632505648162141 2925951827487189618060803)
                ·
                  refine ⟨4388927741230784427091205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2925951827487189618060803 4388927741230784427091205)
                  ·
                    refine ⟨822923951480772080079601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4388927741230784427091205 822923951480772080079601)
                    ·
                      rfl

theorem cell23_4807916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 3, 3, 1, 4].length) (baseStart_4807916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4807916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4807916 prefixEnd_4807916 := by exact prefixLift 4807916
  have htrace : WordTrace (prefixWord ++ tailWord_4807916) baseStart_4807916 baseEnd_4807916 := by
    simpa [prefixWord, tailWord_4807916, baseEnd_4807916] using wordTrace_append hprefix tailTrace_4807916
  have hstable : (prefixWord ++ tailWord_4807916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4807916).length < 2 ^ (prefixWord ++ tailWord_4807916).sum := by decide
  have hdescent : baseEnd_4807916 < baseStart_4807916 := by decide
  rcases family_descends (prefixWord ++ tailWord_4807916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4807992 : List Nat := [2, 1, 2, 1, 3, 1, 1, 1, 5, 2, 4]
def baseStart_4807992 : Nat := 118140960795 + 4807992 * 2 ^ 59
def prefixEnd_4807992 : Nat := 4983230072969 + 3 ^ 40 * 4807992 * 2
def baseEnd_4807992 : Nat := 2468810878972057942888453

theorem tailTrace_4807992 : CollatzResearch.WordTrace tailWord_4807992 prefixEnd_4807992 2468810878972057942888453 := by
  unfold tailWord_4807992
  simp only [CollatzResearch.WordTrace]
  refine ⟨87680937398736799252221115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116907916531649065669628153 87680937398736799252221115)
  ·
    refine ⟨131521406098105198878331673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87680937398736799252221115 131521406098105198878331673)
    ·
      refine ⟨98641054573578899158748755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 131521406098105198878331673 98641054573578899158748755)
      ·
        refine ⟨147961581860368348738123133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98641054573578899158748755 147961581860368348738123133)
        ·
          refine ⟨55485593197638130776796175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 147961581860368348738123133 55485593197638130776796175)
          ·
            refine ⟨83228389796457196165194263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55485593197638130776796175 83228389796457196165194263)
            ·
              refine ⟨124842584694685794247791395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83228389796457196165194263 124842584694685794247791395)
              ·
                refine ⟨187263877042028691371687093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 124842584694685794247791395 187263877042028691371687093)
                ·
                  refine ⟨17555988472690189816095665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 187263877042028691371687093 17555988472690189816095665)
                  ·
                    refine ⟨13166991354517642362071749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17555988472690189816095665 13166991354517642362071749)
                    ·
                      refine ⟨2468810878972057942888453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13166991354517642362071749 2468810878972057942888453)
                      ·
                        rfl

theorem cell23_4807992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 1, 5, 2, 4].length) (baseStart_4807992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4807992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4807992 prefixEnd_4807992 := by exact prefixLift 4807992
  have htrace : WordTrace (prefixWord ++ tailWord_4807992) baseStart_4807992 baseEnd_4807992 := by
    simpa [prefixWord, tailWord_4807992, baseEnd_4807992] using wordTrace_append hprefix tailTrace_4807992
  have hstable : (prefixWord ++ tailWord_4807992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4807992).length < 2 ^ (prefixWord ++ tailWord_4807992).sum := by decide
  have hdescent : baseEnd_4807992 < baseStart_4807992 := by decide
  rcases family_descends (prefixWord ++ tailWord_4807992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4807999 : List Nat := [1, 1, 2, 2, 4, 2, 1, 2, 3, 2, 3]
def baseStart_4807999 : Nat := 118140960795 + 4807999 * 2 ^ 59
def prefixEnd_4807999 : Nat := 4983230072969 + 3 ^ 40 * 4807999 * 2
def baseEnd_4807999 : Nat := 2468814473336639415500921

theorem tailTrace_4807999 : CollatzResearch.WordTrace tailWord_4807999 prefixEnd_4807999 2468814473336639415500921 := by
  unfold tailWord_4807999
  simp only [CollatzResearch.WordTrace]
  refine ⟨175362130108448238699947051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116908086738965492466631367 175362130108448238699947051)
  ·
    refine ⟨263043195162672358049920577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175362130108448238699947051 263043195162672358049920577)
    ·
      refine ⟨197282396372004268537440433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 263043195162672358049920577 197282396372004268537440433)
      ·
        refine ⟨147961797279003201403080325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 197282396372004268537440433 147961797279003201403080325)
        ·
          refine ⟨27742836989813100263077561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 147961797279003201403080325 27742836989813100263077561)
          ·
            refine ⟨20807127742359825197308171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27742836989813100263077561 20807127742359825197308171)
            ·
              refine ⟨31210691613539737795962257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20807127742359825197308171 31210691613539737795962257)
              ·
                refine ⟨23408018710154803346971693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31210691613539737795962257 23408018710154803346971693)
                ·
                  refine ⟨8778007016308051255114385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23408018710154803346971693 8778007016308051255114385)
                  ·
                    refine ⟨6583505262231038441335789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8778007016308051255114385 6583505262231038441335789)
                    ·
                      refine ⟨2468814473336639415500921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6583505262231038441335789 2468814473336639415500921)
                      ·
                        rfl

theorem cell23_4807999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 1, 2, 3, 2, 3].length) (baseStart_4807999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4807999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4807999 prefixEnd_4807999 := by exact prefixLift 4807999
  have htrace : WordTrace (prefixWord ++ tailWord_4807999) baseStart_4807999 baseEnd_4807999 := by
    simpa [prefixWord, tailWord_4807999, baseEnd_4807999] using wordTrace_append hprefix tailTrace_4807999
  have hstable : (prefixWord ++ tailWord_4807999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4807999).length < 2 ^ (prefixWord ++ tailWord_4807999).sum := by decide
  have hdescent : baseEnd_4807999 < baseStart_4807999 := by decide
  rcases family_descends (prefixWord ++ tailWord_4807999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4808040 : List Nat := [2, 1, 4, 2, 4, 1, 1, 2, 2, 4]
def baseStart_4808040 : Nat := 118140960795 + 4808040 * 2 ^ 59
def prefixEnd_4808040 : Nat := 4983230072969 + 3 ^ 40 * 4808040 * 2
def baseEnd_4808040 : Nat := 822945175347824585029411

theorem tailTrace_4808040 : CollatzResearch.WordTrace tailWord_4808040 prefixEnd_4808040 822945175347824585029411 := by
  unfold tailWord_4808040
  simp only [CollatzResearch.WordTrace]
  refine ⟨87681812750649851351094787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116909083667533135134793049 87681812750649851351094787)
  ·
    refine ⟨131522719125974777026642181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87681812750649851351094787 131522719125974777026642181)
    ·
      refine ⟨24660509836120270692495409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 131522719125974777026642181 24660509836120270692495409)
      ·
        refine ⟨18495382377090203019371557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24660509836120270692495409 18495382377090203019371557)
        ·
          refine ⟨3467884195704413066132167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18495382377090203019371557 3467884195704413066132167)
          ·
            refine ⟨5201826293556619599198251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3467884195704413066132167 5201826293556619599198251)
            ·
              refine ⟨7802739440334929398797377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5201826293556619599198251 7802739440334929398797377)
              ·
                refine ⟨5852054580251197049098033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7802739440334929398797377 5852054580251197049098033)
                ·
                  refine ⟨4389040935188397786823525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5852054580251197049098033 4389040935188397786823525)
                  ·
                    refine ⟨822945175347824585029411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4389040935188397786823525 822945175347824585029411)
                    ·
                      rfl

theorem cell23_4808040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 4, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 4, 1, 1, 2, 2, 4].length) (baseStart_4808040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4808040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4808040 prefixEnd_4808040 := by exact prefixLift 4808040
  have htrace : WordTrace (prefixWord ++ tailWord_4808040) baseStart_4808040 baseEnd_4808040 := by
    simpa [prefixWord, tailWord_4808040, baseEnd_4808040] using wordTrace_append hprefix tailTrace_4808040
  have hstable : (prefixWord ++ tailWord_4808040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4808040).length < 2 ^ (prefixWord ++ tailWord_4808040).sum := by decide
  have hdescent : baseEnd_4808040 < baseStart_4808040 := by decide
  rcases family_descends (prefixWord ++ tailWord_4808040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4808089 : List Nat := [1, 2, 1, 2, 1, 6, 1, 1, 2, 1, 5]
def baseStart_4808089 : Nat := 118140960795 + 4808089 * 2 ^ 59
def prefixEnd_4808089 : Nat := 4983230072969 + 3 ^ 40 * 4808089 * 2
def baseEnd_4808089 : Nat := 2468860686595544063375507

theorem tailTrace_4808089 : CollatzResearch.WordTrace tailWord_4808089 prefixEnd_4808089 2468860686595544063375507 := by
  unfold tailWord_4808089
  simp only [CollatzResearch.WordTrace]
  refine ⟨175365412678122184070723321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116910275118748122713815547 175365412678122184070723321)
  ·
    refine ⟨131524059508591638053042491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 175365412678122184070723321 131524059508591638053042491)
    ·
      refine ⟨197286089262887457079563737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131524059508591638053042491 197286089262887457079563737)
      ·
        refine ⟨147964566947165592809672803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 197286089262887457079563737 147964566947165592809672803)
        ·
          refine ⟨221946850420748389214509205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 147964566947165592809672803 221946850420748389214509205)
          ·
            refine ⟨10403758613472580744430119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 221946850420748389214509205 10403758613472580744430119)
            ·
              refine ⟨15605637920208871116645179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10403758613472580744430119 15605637920208871116645179)
              ·
                refine ⟨23408456880313306674967769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15605637920208871116645179 23408456880313306674967769)
                ·
                  refine ⟨17556342660234980006225827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23408456880313306674967769 17556342660234980006225827)
                  ·
                    refine ⟨26334513990352470009338741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17556342660234980006225827 26334513990352470009338741)
                    ·
                      refine ⟨2468860686595544063375507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26334513990352470009338741 2468860686595544063375507)
                      ·
                        rfl

theorem cell23_4808089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 1, 1, 2, 1, 5].length) (baseStart_4808089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4808089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4808089 prefixEnd_4808089 := by exact prefixLift 4808089
  have htrace : WordTrace (prefixWord ++ tailWord_4808089) baseStart_4808089 baseEnd_4808089 := by
    simpa [prefixWord, tailWord_4808089, baseEnd_4808089] using wordTrace_append hprefix tailTrace_4808089
  have hstable : (prefixWord ++ tailWord_4808089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4808089).length < 2 ^ (prefixWord ++ tailWord_4808089).sum := by decide
  have hdescent : baseEnd_4808089 < baseStart_4808089 := by decide
  rcases family_descends (prefixWord ++ tailWord_4808089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4808103 : List Nat := [1, 1, 6, 1, 1, 1, 1, 3, 4, 2, 2]
def baseStart_4808103 : Nat := 118140960795 + 4808103 * 2 ^ 59
def prefixEnd_4808103 : Nat := 4983230072969 + 3 ^ 40 * 4808103 * 2
def baseEnd_4808103 : Nat := 2468867875324707008600443

theorem tailTrace_4808103 : CollatzResearch.WordTrace tailWord_4808103 prefixEnd_4808103 2468867875324707008600443 := by
  unfold tailWord_4808103
  simp only [CollatzResearch.WordTrace]
  refine ⟨175365923300071464461732963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116910615533380976307821975 175365923300071464461732963)
  ·
    refine ⟨263048884950107196692599445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175365923300071464461732963 263048884950107196692599445)
    ·
      refine ⟨12330416482036274844965599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 263048884950107196692599445 12330416482036274844965599)
      ·
        refine ⟨18495624723054412267448399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12330416482036274844965599 18495624723054412267448399)
        ·
          refine ⟨27743437084581618401172599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18495624723054412267448399 27743437084581618401172599)
          ·
            refine ⟨41615155626872427601758899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27743437084581618401172599 41615155626872427601758899)
            ·
              refine ⟨62422733440308641402638349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41615155626872427601758899 62422733440308641402638349)
              ·
                refine ⟨23408525040115740525989381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 62422733440308641402638349 23408525040115740525989381)
                ·
                  refine ⟨4389098445021701348623009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23408525040115740525989381 4389098445021701348623009)
                  ·
                    refine ⟨3291823833766276011467257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4389098445021701348623009 3291823833766276011467257)
                    ·
                      refine ⟨2468867875324707008600443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3291823833766276011467257 2468867875324707008600443)
                      ·
                        rfl

theorem cell23_4808103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 3, 4, 2, 2].length) (baseStart_4808103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4808103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4808103 prefixEnd_4808103 := by exact prefixLift 4808103
  have htrace : WordTrace (prefixWord ++ tailWord_4808103) baseStart_4808103 baseEnd_4808103 := by
    simpa [prefixWord, tailWord_4808103, baseEnd_4808103] using wordTrace_append hprefix tailTrace_4808103
  have hstable : (prefixWord ++ tailWord_4808103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4808103).length < 2 ^ (prefixWord ++ tailWord_4808103).sum := by decide
  have hdescent : baseEnd_4808103 < baseStart_4808103 := by decide
  rcases family_descends (prefixWord ++ tailWord_4808103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4808112 : List Nat := [2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 8]
def baseStart_4808112 : Nat := 118140960795 + 4808112 * 2 ^ 59
def prefixEnd_4808112 : Nat := 4983230072969 + 3 ^ 40 * 4808112 * 2
def baseEnd_4808112 : Nat := 2468872496650597473387901

theorem tailTrace_4808112 : CollatzResearch.WordTrace tailWord_4808112 prefixEnd_4808112 2468872496650597473387901 := by
  unfold tailWord_4808112
  simp only [CollatzResearch.WordTrace]
  refine ⟨87683125778519429499405295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116910834371359239332540393 87683125778519429499405295)
  ·
    refine ⟨131524688667779144249107943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87683125778519429499405295 131524688667779144249107943)
    ·
      refine ⟨197287033001668716373661915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131524688667779144249107943 197287033001668716373661915)
      ·
        refine ⟨295930549502503074560492873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 197287033001668716373661915 295930549502503074560492873)
        ·
          refine ⟨221947912126877305920369655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 295930549502503074560492873 221947912126877305920369655)
          ·
            refine ⟨332921868190315958880554483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 221947912126877305920369655 332921868190315958880554483)
            ·
              refine ⟨499382802285473938320831725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 332921868190315958880554483 499382802285473938320831725)
              ·
                refine ⟨187268550857052726870311897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 499382802285473938320831725 187268550857052726870311897)
                ·
                  refine ⟨140451413142789545152733923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 187268550857052726870311897 140451413142789545152733923)
                  ·
                    refine ⟨210677119714184317729100885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 140451413142789545152733923 210677119714184317729100885)
                    ·
                      refine ⟨2468872496650597473387901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 210677119714184317729100885 2468872496650597473387901)
                      ·
                        rfl

theorem cell23_4808112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 8].length) (baseStart_4808112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4808112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4808112 prefixEnd_4808112 := by exact prefixLift 4808112
  have htrace : WordTrace (prefixWord ++ tailWord_4808112) baseStart_4808112 baseEnd_4808112 := by
    simpa [prefixWord, tailWord_4808112, baseEnd_4808112] using wordTrace_append hprefix tailTrace_4808112
  have hstable : (prefixWord ++ tailWord_4808112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4808112).length < 2 ^ (prefixWord ++ tailWord_4808112).sum := by decide
  have hdescent : baseEnd_4808112 < baseStart_4808112 := by decide
  rcases family_descends (prefixWord ++ tailWord_4808112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4808119 : List Nat := [1, 1, 3, 1, 3, 2, 2, 1, 1, 5, 3]
def baseStart_4808119 : Nat := 118140960795 + 4808119 * 2 ^ 59
def prefixEnd_4808119 : Nat := 4983230072969 + 3 ^ 40 * 4808119 * 2
def baseEnd_4808119 : Nat := 2468876091015178946000369

theorem tailTrace_4808119 : CollatzResearch.WordTrace tailWord_4808119 prefixEnd_4808119 2468876091015178946000369 := by
  unfold tailWord_4808119
  simp only [CollatzResearch.WordTrace]
  refine ⟨175366506868013499194315411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116911004578675666129543607 175366506868013499194315411)
  ·
    refine ⟨263049760302020248791473117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175366506868013499194315411 263049760302020248791473117)
    ·
      refine ⟨98643660113257593296802419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 263049760302020248791473117 98643660113257593296802419)
      ·
        refine ⟨147965490169886389945203629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98643660113257593296802419 147965490169886389945203629)
        ·
          refine ⟨55487058813707396229451361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 147965490169886389945203629 55487058813707396229451361)
          ·
            refine ⟨41615294110280547172088521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55487058813707396229451361 41615294110280547172088521)
            ·
              refine ⟨31211470582710410379066391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41615294110280547172088521 31211470582710410379066391)
              ·
                refine ⟨46817205874065615568599587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31211470582710410379066391 46817205874065615568599587)
                ·
                  refine ⟨70225808811098423352899381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 46817205874065615568599587 70225808811098423352899381)
                  ·
                    refine ⟨6583669576040477189334317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 70225808811098423352899381 6583669576040477189334317)
                    ·
                      refine ⟨2468876091015178946000369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6583669576040477189334317 2468876091015178946000369)
                      ·
                        rfl

theorem cell23_4808119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 2, 1, 1, 5, 3].length) (baseStart_4808119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4808119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4808119 prefixEnd_4808119 := by exact prefixLift 4808119
  have htrace : WordTrace (prefixWord ++ tailWord_4808119) baseStart_4808119 baseEnd_4808119 := by
    simpa [prefixWord, tailWord_4808119, baseEnd_4808119] using wordTrace_append hprefix tailTrace_4808119
  have hstable : (prefixWord ++ tailWord_4808119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4808119).length < 2 ^ (prefixWord ++ tailWord_4808119).sum := by decide
  have hdescent : baseEnd_4808119 < baseStart_4808119 := by decide
  rcases family_descends (prefixWord ++ tailWord_4808119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4808120 : List Nat := [2, 1, 2, 1, 2, 2, 6, 1, 2, 2, 2]
def baseStart_4808120 : Nat := 118140960795 + 4808120 * 2 ^ 59
def prefixEnd_4808120 : Nat := 4983230072969 + 3 ^ 40 * 4808120 * 2
def baseEnd_4808120 : Nat := 2468876604495833442087865

theorem tailTrace_4808120 : CollatzResearch.WordTrace tailWord_4808120 prefixEnd_4808120 2468876604495833442087865 := by
  unfold tailWord_4808120
  simp only [CollatzResearch.WordTrace]
  refine ⟨87683271670504938182550907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116911028894006584243401209 87683271670504938182550907)
  ·
    refine ⟨131524907505757407273826361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87683271670504938182550907 131524907505757407273826361)
    ·
      refine ⟨98643680629318055455369771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 131524907505757407273826361 98643680629318055455369771)
      ·
        refine ⟨147965520943977083183054657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98643680629318055455369771 147965520943977083183054657)
        ·
          refine ⟨110974140707982812387290993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 147965520943977083183054657 110974140707982812387290993)
          ·
            refine ⟨83230605530987109290468245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 110974140707982812387290993 83230605530987109290468245)
            ·
              refine ⟨3901434634265020747990699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 83230605530987109290468245 3901434634265020747990699)
              ·
                refine ⟨5852151951397531121986049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3901434634265020747990699 5852151951397531121986049)
                ·
                  refine ⟨4389113963548148341489537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5852151951397531121986049 4389113963548148341489537)
                  ·
                    refine ⟨3291835472661111256117153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4389113963548148341489537 3291835472661111256117153)
                    ·
                      refine ⟨2468876604495833442087865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3291835472661111256117153 2468876604495833442087865)
                      ·
                        rfl

theorem cell23_4808120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 6, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 6, 1, 2, 2, 2].length) (baseStart_4808120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4808120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4808120 prefixEnd_4808120 := by exact prefixLift 4808120
  have htrace : WordTrace (prefixWord ++ tailWord_4808120) baseStart_4808120 baseEnd_4808120 := by
    simpa [prefixWord, tailWord_4808120, baseEnd_4808120] using wordTrace_append hprefix tailTrace_4808120
  have hstable : (prefixWord ++ tailWord_4808120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4808120).length < 2 ^ (prefixWord ++ tailWord_4808120).sum := by decide
  have hdescent : baseEnd_4808120 < baseStart_4808120 := by decide
  rcases family_descends (prefixWord ++ tailWord_4808120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4808139 : List Nat := [1, 1, 1, 1, 3, 3, 3, 3, 2, 5]
def baseStart_4808139 : Nat := 118140960795 + 4808139 * 2 ^ 59
def prefixEnd_4808139 : Nat := 4983230072969 + 3 ^ 40 * 4808139 * 2
def baseEnd_4808139 : Nat := 822962120209422955916759

theorem tailTrace_4808139 : CollatzResearch.WordTrace tailWord_4808139 prefixEnd_4808139 822962120209422955916759 := by
  unfold tailWord_4808139
  simp only [CollatzResearch.WordTrace]
  refine ⟨175367236327941042610043471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116911490885294028406695647 175367236327941042610043471)
  ·
    refine ⟨263050854491911563915065207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175367236327941042610043471 263050854491911563915065207)
    ·
      refine ⟨394576281737867345872597811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 263050854491911563915065207 394576281737867345872597811)
      ·
        refine ⟨591864422606801018808896717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 394576281737867345872597811 591864422606801018808896717)
        ·
          refine ⟨221949158477550382053336269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 591864422606801018808896717 221949158477550382053336269)
          ·
            refine ⟨83230934429081393270001101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 221949158477550382053336269 83230934429081393270001101)
            ·
              refine ⟨31211600410905522476250413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 83230934429081393270001101 31211600410905522476250413)
              ·
                refine ⟨11704350154089570928593905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31211600410905522476250413 11704350154089570928593905)
                ·
                  refine ⟨8778262615567178196445429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11704350154089570928593905 8778262615567178196445429)
                  ·
                    refine ⟨822962120209422955916759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8778262615567178196445429 822962120209422955916759)
                    ·
                      rfl

theorem cell23_4808139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 3, 3, 2, 5].length) (baseStart_4808139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4808139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4808139 prefixEnd_4808139 := by exact prefixLift 4808139
  have htrace : WordTrace (prefixWord ++ tailWord_4808139) baseStart_4808139 baseEnd_4808139 := by
    simpa [prefixWord, tailWord_4808139, baseEnd_4808139] using wordTrace_append hprefix tailTrace_4808139
  have hstable : (prefixWord ++ tailWord_4808139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4808139).length < 2 ^ (prefixWord ++ tailWord_4808139).sum := by decide
  have hdescent : baseEnd_4808139 < baseStart_4808139 := by decide
  rcases family_descends (prefixWord ++ tailWord_4808139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4808149 : List Nat := [1, 3, 2, 3, 1, 1, 1, 1, 3, 2, 5]
def baseStart_4808149 : Nat := 118140960795 + 4808149 * 2 ^ 59
def prefixEnd_4808149 : Nat := 4983230072969 + 3 ^ 40 * 4808149 * 2
def baseEnd_4808149 : Nat := 2468891495434813828625231

theorem tailTrace_4808149 : CollatzResearch.WordTrace tailWord_4808149 prefixEnd_4808149 2468891495434813828625231 := by
  unfold tailWord_4808149
  simp only [CollatzResearch.WordTrace]
  refine ⟨175367601057904814317907501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116911734038603209545271667 175367601057904814317907501)
  ·
    refine ⟨65762850396714305369215313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 175367601057904814317907501 65762850396714305369215313)
    ·
      refine ⟨49322137797535729026911485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65762850396714305369215313 49322137797535729026911485)
      ·
        refine ⟨18495801674075898385091807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49322137797535729026911485 18495801674075898385091807)
        ·
          refine ⟨27743702511113847577637711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18495801674075898385091807 27743702511113847577637711)
          ·
            refine ⟨41615553766670771366456567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27743702511113847577637711 41615553766670771366456567)
            ·
              refine ⟨62423330650006157049684851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41615553766670771366456567 62423330650006157049684851)
              ·
                refine ⟨93634995975009235574527277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62423330650006157049684851 93634995975009235574527277)
                ·
                  refine ⟨35113123490628463340447729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 93634995975009235574527277 35113123490628463340447729)
                  ·
                    refine ⟨26334842617971347505335797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 35113123490628463340447729 26334842617971347505335797)
                    ·
                      refine ⟨2468891495434813828625231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26334842617971347505335797 2468891495434813828625231)
                      ·
                        rfl

theorem cell23_4808149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 1, 3, 2, 5].length) (baseStart_4808149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4808149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4808149 prefixEnd_4808149 := by exact prefixLift 4808149
  have htrace : WordTrace (prefixWord ++ tailWord_4808149) baseStart_4808149 baseEnd_4808149 := by
    simpa [prefixWord, tailWord_4808149, baseEnd_4808149] using wordTrace_append hprefix tailTrace_4808149
  have hstable : (prefixWord ++ tailWord_4808149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4808149).length < 2 ^ (prefixWord ++ tailWord_4808149).sum := by decide
  have hdescent : baseEnd_4808149 < baseStart_4808149 := by decide
  rcases family_descends (prefixWord ++ tailWord_4808149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4808176 : List Nat := [2, 1, 1, 1, 3, 4, 1, 1, 1, 6, 2]
def baseStart_4808176 : Nat := 118140960795 + 4808176 * 2 ^ 59
def prefixEnd_4808176 : Nat := 4983230072969 + 3 ^ 40 * 4808176 * 2
def baseEnd_4808176 : Nat := 2468905359412485222987607

theorem tailTrace_4808176 : CollatzResearch.WordTrace tailWord_4808176 prefixEnd_4808176 2468905359412485222987607 := by
  unfold tailWord_4808176
  simp only [CollatzResearch.WordTrace]
  refine ⟨87684292914403498964570191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116912390552537998619426921 87684292914403498964570191)
  ·
    refine ⟨131526439371605248446855287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87684292914403498964570191 131526439371605248446855287)
    ·
      refine ⟨197289659057407872670282931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131526439371605248446855287 197289659057407872670282931)
      ·
        refine ⟨295934488586111809005424397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 197289659057407872670282931 295934488586111809005424397)
        ·
          refine ⟨110975433219791928377034149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 295934488586111809005424397 110975433219791928377034149)
          ·
            refine ⟨20807893728710986570693903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 110975433219791928377034149 20807893728710986570693903)
            ·
              refine ⟨31211840593066479856040855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20807893728710986570693903 31211840593066479856040855)
              ·
                refine ⟨46817760889599719784061283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31211840593066479856040855 46817760889599719784061283)
                ·
                  refine ⟨70226641334399579676091925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 46817760889599719784061283 70226641334399579676091925)
                  ·
                    refine ⟨3291873812549980297316809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 70226641334399579676091925 3291873812549980297316809)
                    ·
                      refine ⟨2468905359412485222987607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3291873812549980297316809 2468905359412485222987607)
                      ·
                        rfl

theorem cell23_4808176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 1, 1, 1, 6, 2].length) (baseStart_4808176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4808176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4808176 prefixEnd_4808176 := by exact prefixLift 4808176
  have htrace : WordTrace (prefixWord ++ tailWord_4808176) baseStart_4808176 baseEnd_4808176 := by
    simpa [prefixWord, tailWord_4808176, baseEnd_4808176] using wordTrace_append hprefix tailTrace_4808176
  have hstable : (prefixWord ++ tailWord_4808176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4808176).length < 2 ^ (prefixWord ++ tailWord_4808176).sum := by decide
  have hdescent : baseEnd_4808176 < baseStart_4808176 := by decide
  rcases family_descends (prefixWord ++ tailWord_4808176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4808186 : List Nat := [3, 1, 1, 1, 1, 2, 5, 2, 3, 4]
def baseStart_4808186 : Nat := 118140960795 + 4808186 * 2 ^ 59
def prefixEnd_4808186 : Nat := 4983230072969 + 3 ^ 40 * 4808186 * 2
def baseEnd_4808186 : Nat := 822970164739676727954187

theorem tailTrace_4808186 : CollatzResearch.WordTrace tailWord_4808186 prefixEnd_4808186 822970164739676727954187 := by
  unfold tailWord_4808186
  simp only [CollatzResearch.WordTrace]
  refine ⟨43842237639692692409251103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 116912633705847179758002941 43842237639692692409251103)
  ·
    refine ⟨65763356459539038613876655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43842237639692692409251103 65763356459539038613876655)
    ·
      refine ⟨98645034689308557920814983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65763356459539038613876655 98645034689308557920814983)
      ·
        refine ⟨147967552033962836881222475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98645034689308557920814983 147967552033962836881222475)
        ·
          refine ⟨221951328050944255321833713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 147967552033962836881222475 221951328050944255321833713)
          ·
            refine ⟨166463496038208191491375285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 221951328050944255321833713 166463496038208191491375285)
            ·
              refine ⟨15605952753582017952316433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 166463496038208191491375285 15605952753582017952316433)
              ·
                refine ⟨11704464565186513464237325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15605952753582017952316433 11704464565186513464237325)
                ·
                  refine ⟨4389174211944942549088997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11704464565186513464237325 4389174211944942549088997)
                  ·
                    refine ⟨822970164739676727954187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4389174211944942549088997 822970164739676727954187)
                    ·
                      rfl

theorem cell23_4808186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 5, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 5, 2, 3, 4].length) (baseStart_4808186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4808186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4808186 prefixEnd_4808186 := by exact prefixLift 4808186
  have htrace : WordTrace (prefixWord ++ tailWord_4808186) baseStart_4808186 baseEnd_4808186 := by
    simpa [prefixWord, tailWord_4808186, baseEnd_4808186] using wordTrace_append hprefix tailTrace_4808186
  have hstable : (prefixWord ++ tailWord_4808186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4808186).length < 2 ^ (prefixWord ++ tailWord_4808186).sum := by decide
  have hdescent : baseEnd_4808186 < baseStart_4808186 := by decide
  rcases family_descends (prefixWord ++ tailWord_4808186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4808216 : List Nat := [2, 1, 2, 3, 4, 1, 1, 1, 8]
def baseStart_4808216 : Nat := 118140960795 + 4808216 * 2 ^ 59
def prefixEnd_4808216 : Nat := 4983230072969 + 3 ^ 40 * 4808216 * 2
def baseEnd_4808216 : Nat := 274325099848740562943047

theorem tailTrace_4808216 : CollatzResearch.WordTrace tailWord_4808216 prefixEnd_4808216 274325099848740562943047 := by
  unfold tailWord_4808216
  simp only [CollatzResearch.WordTrace]
  refine ⟨87685022374331042380298251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116913363165774723173731001 87685022374331042380298251)
  ·
    refine ⟨131527533561496563570447377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87685022374331042380298251 131527533561496563570447377)
    ·
      refine ⟨98645650171122422677835533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 131527533561496563570447377 98645650171122422677835533)
      ·
        refine ⟨36992118814170908504188325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 98645650171122422677835533 36992118814170908504188325)
        ·
          refine ⟨6936022277657045344535311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 36992118814170908504188325 6936022277657045344535311)
          ·
            refine ⟨10404033416485568016802967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6936022277657045344535311 10404033416485568016802967)
            ·
              refine ⟨15606050124728352025204451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10404033416485568016802967 15606050124728352025204451)
              ·
                refine ⟨23409075187092528037806677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15606050124728352025204451 23409075187092528037806677)
                ·
                  refine ⟨274325099848740562943047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 23409075187092528037806677 274325099848740562943047)
                  ·
                    rfl

theorem cell23_4808216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 1, 1, 8].length) (baseStart_4808216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4808216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4808216 prefixEnd_4808216 := by exact prefixLift 4808216
  have htrace : WordTrace (prefixWord ++ tailWord_4808216) baseStart_4808216 baseEnd_4808216 := by
    simpa [prefixWord, tailWord_4808216, baseEnd_4808216] using wordTrace_append hprefix tailTrace_4808216
  have hstable : (prefixWord ++ tailWord_4808216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4808216).length < 2 ^ (prefixWord ++ tailWord_4808216).sum := by decide
  have hdescent : baseEnd_4808216 < baseStart_4808216 := by decide
  rcases family_descends (prefixWord ++ tailWord_4808216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4808243 : List Nat := [1, 1, 1, 2, 4, 3, 2, 2, 3, 1, 3]
def baseStart_4808243 : Nat := 118140960795 + 4808243 * 2 ^ 59
def prefixEnd_4808243 : Nat := 4983230072969 + 3 ^ 40 * 4808243 * 2
def baseEnd_4808243 : Nat := 2468939762616336460849799

theorem tailTrace_4808243 : CollatzResearch.WordTrace tailWord_4808243 prefixEnd_4808243 2468939762616336460849799 := by
  unfold tailWord_4808243
  simp only [CollatzResearch.WordTrace]
  refine ⟨175371029519564268371829383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116914019679709512247886255 175371029519564268371829383)
  ·
    refine ⟨263056544279346402557744075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175371029519564268371829383 263056544279346402557744075)
    ·
      refine ⟨394584816419019603836616113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 263056544279346402557744075 394584816419019603836616113)
      ·
        refine ⟨295938612314264702877462085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 394584816419019603836616113 295938612314264702877462085)
        ·
          refine ⟨55488489808924631789524141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 295938612314264702877462085 55488489808924631789524141)
          ·
            refine ⟨20808183678346736921071553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55488489808924631789524141 20808183678346736921071553)
            ·
              refine ⟨15606137758760052690803665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20808183678346736921071553 15606137758760052690803665)
              ·
                refine ⟨11704603319070039518102749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15606137758760052690803665 11704603319070039518102749)
                ·
                  refine ⟨4389226244651264819288531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11704603319070039518102749 4389226244651264819288531)
                  ·
                    refine ⟨6583839366976897228932797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4389226244651264819288531 6583839366976897228932797)
                    ·
                      refine ⟨2468939762616336460849799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6583839366976897228932797 2468939762616336460849799)
                      ·
                        rfl

theorem cell23_4808243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 2, 2, 3, 1, 3].length) (baseStart_4808243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4808243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4808243 prefixEnd_4808243 := by exact prefixLift 4808243
  have htrace : WordTrace (prefixWord ++ tailWord_4808243) baseStart_4808243 baseEnd_4808243 := by
    simpa [prefixWord, tailWord_4808243, baseEnd_4808243] using wordTrace_append hprefix tailTrace_4808243
  have hstable : (prefixWord ++ tailWord_4808243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4808243).length < 2 ^ (prefixWord ++ tailWord_4808243).sum := by decide
  have hdescent : baseEnd_4808243 < baseStart_4808243 := by decide
  rcases family_descends (prefixWord ++ tailWord_4808243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4808306 : List Nat := [3, 2, 1, 2, 3, 1, 2, 9]
def baseStart_4808306 : Nat := 118140960795 + 4808306 * 2 ^ 59
def prefixEnd_4808306 : Nat := 4983230072969 + 3 ^ 40 * 4808306 * 2
def baseEnd_4808306 : Nat := 91443411551761841272667

theorem tailTrace_4808306 : CollatzResearch.WordTrace tailWord_4808306 prefixEnd_4808306 91443411551761841272667 := by
  unfold tailWord_4808306
  simp only [CollatzResearch.WordTrace]
  refine ⟨43843331829584007532843193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 116915551545557353420915181 43843331829584007532843193)
  ·
    refine ⟨32882498872188005649632395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43843331829584007532843193 32882498872188005649632395)
    ·
      refine ⟨49323748308282008474448593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32882498872188005649632395 49323748308282008474448593)
      ·
        refine ⟨36992811231211506355836445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49323748308282008474448593 36992811231211506355836445)
        ·
          refine ⟨13872304211704314883438667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36992811231211506355836445 13872304211704314883438667)
          ·
            refine ⟨20808456317556472325158001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13872304211704314883438667 20808456317556472325158001)
            ·
              refine ⟨15606342238167354243868501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20808456317556472325158001 15606342238167354243868501)
              ·
                refine ⟨91443411551761841272667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 15606342238167354243868501 91443411551761841272667)
                ·
                  rfl

theorem cell23_4808306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 2, 9].length) (baseStart_4808306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4808306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4808306 prefixEnd_4808306 := by exact prefixLift 4808306
  have htrace : WordTrace (prefixWord ++ tailWord_4808306) baseStart_4808306 baseEnd_4808306 := by
    simpa [prefixWord, tailWord_4808306, baseEnd_4808306] using wordTrace_append hprefix tailTrace_4808306
  have hstable : (prefixWord ++ tailWord_4808306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4808306).length < 2 ^ (prefixWord ++ tailWord_4808306).sum := by decide
  have hdescent : baseEnd_4808306 < baseStart_4808306 := by decide
  rcases family_descends (prefixWord ++ tailWord_4808306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4808320 : List Nat := [2, 1, 1, 2, 1, 4, 5, 1, 1, 2, 3]
def baseStart_4808320 : Nat := 118140960795 + 4808320 * 2 ^ 59
def prefixEnd_4808320 : Nat := 4983230072969 + 3 ^ 40 * 4808320 * 2
def baseEnd_4808320 : Nat := 2468979300626732659586945

theorem tailTrace_4808320 : CollatzResearch.WordTrace tailWord_4808320 prefixEnd_4808320 2468979300626732659586945 := by
  unfold tailWord_4808320
  simp only [CollatzResearch.WordTrace]
  refine ⟨87686918970142655261191207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116915891960190207014921609 87686918970142655261191207)
  ·
    refine ⟨131530378455213982891786811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87686918970142655261191207 131530378455213982891786811)
    ·
      refine ⟨197295567682820974337680217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131530378455213982891786811 197295567682820974337680217)
      ·
        refine ⟨147971675762115730753260163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 197295567682820974337680217 147971675762115730753260163)
        ·
          refine ⟨221957513643173596129890245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 147971675762115730753260163 221957513643173596129890245)
          ·
            refine ⟨41617033808095049274354421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 221957513643173596129890245 41617033808095049274354421)
            ·
              refine ⟨3901596919508910869470727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 41617033808095049274354421 3901596919508910869470727)
              ·
                refine ⟨5852395379263366304206091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3901596919508910869470727 5852395379263366304206091)
                ·
                  refine ⟨8778593068895049456309137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5852395379263366304206091 8778593068895049456309137)
                  ·
                    refine ⟨6583944801671287092231853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8778593068895049456309137 6583944801671287092231853)
                    ·
                      refine ⟨2468979300626732659586945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6583944801671287092231853 2468979300626732659586945)
                      ·
                        rfl

theorem cell23_4808320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 5, 1, 1, 2, 3].length) (baseStart_4808320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4808320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4808320 prefixEnd_4808320 := by exact prefixLift 4808320
  have htrace : WordTrace (prefixWord ++ tailWord_4808320) baseStart_4808320 baseEnd_4808320 := by
    simpa [prefixWord, tailWord_4808320, baseEnd_4808320] using wordTrace_append hprefix tailTrace_4808320
  have hstable : (prefixWord ++ tailWord_4808320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4808320).length < 2 ^ (prefixWord ++ tailWord_4808320).sum := by decide
  have hdescent : baseEnd_4808320 < baseStart_4808320 := by decide
  rcases family_descends (prefixWord ++ tailWord_4808320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4808328 : List Nat := [2, 1, 3, 5, 2, 1, 2, 2, 1, 1, 3]
def baseStart_4808328 : Nat := 118140960795 + 4808328 * 2 ^ 59
def prefixEnd_4808328 : Nat := 4983230072969 + 3 ^ 40 * 4808328 * 2
def baseEnd_4808328 : Nat := 2468983408471968628286909

theorem tailTrace_4808328 : CollatzResearch.WordTrace tailWord_4808328 prefixEnd_4808328 2468983408471968628286909 := by
  unfold tailWord_4808328
  simp only [CollatzResearch.WordTrace]
  refine ⟨87687064862128163944336819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116916086482837551925782425 87687064862128163944336819)
  ·
    refine ⟨131530597293192245916505229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87687064862128163944336819 131530597293192245916505229)
    ·
      refine ⟨49323973984947092218689461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 131530597293192245916505229 49323973984947092218689461)
      ·
        refine ⟨4624122561088789895502137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 49323973984947092218689461 4624122561088789895502137)
        ·
          refine ⟨3468091920816592421626603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4624122561088789895502137 3468091920816592421626603)
          ·
            refine ⟨5202137881224888632439905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3468091920816592421626603 5202137881224888632439905)
            ·
              refine ⟨3901603410918666474329929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5202137881224888632439905 3901603410918666474329929)
              ·
                refine ⟨2926202558188999855747447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3901603410918666474329929 2926202558188999855747447)
                ·
                  refine ⟨4389303837283499783621171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2926202558188999855747447 4389303837283499783621171)
                  ·
                    refine ⟨6583955755925249675431757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4389303837283499783621171 6583955755925249675431757)
                    ·
                      refine ⟨2468983408471968628286909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6583955755925249675431757 2468983408471968628286909)
                      ·
                        rfl

theorem cell23_4808328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 2, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 2, 1, 2, 2, 1, 1, 3].length) (baseStart_4808328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4808328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4808328 prefixEnd_4808328 := by exact prefixLift 4808328
  have htrace : WordTrace (prefixWord ++ tailWord_4808328) baseStart_4808328 baseEnd_4808328 := by
    simpa [prefixWord, tailWord_4808328, baseEnd_4808328] using wordTrace_append hprefix tailTrace_4808328
  have hstable : (prefixWord ++ tailWord_4808328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4808328).length < 2 ^ (prefixWord ++ tailWord_4808328).sum := by decide
  have hdescent : baseEnd_4808328 < baseStart_4808328 := by decide
  rcases family_descends (prefixWord ++ tailWord_4808328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4808334 : List Nat := [4, 1, 1, 3, 1, 3, 1, 4, 1, 2, 2]
def baseStart_4808334 : Nat := 118140960795 + 4808334 * 2 ^ 59
def prefixEnd_4808334 : Nat := 4983230072969 + 3 ^ 40 * 4808334 * 2
def baseEnd_4808334 : Nat := 2468986489355895604811881

theorem tailTrace_4808334 : CollatzResearch.WordTrace tailWord_4808334 prefixEnd_4808334 2468986489355895604811881 := by
  unfold tailWord_4808334
  simp only [CollatzResearch.WordTrace]
  refine ⟨21921793570279323864174007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 116916232374823060608928037 21921793570279323864174007)
  ·
    refine ⟨32882690355418985796261011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21921793570279323864174007 32882690355418985796261011)
    ·
      refine ⟨49324035533128478694391517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32882690355418985796261011 49324035533128478694391517)
      ·
        refine ⟨18496513324923179510396819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49324035533128478694391517 18496513324923179510396819)
        ·
          refine ⟨27744769987384769265595229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18496513324923179510396819 27744769987384769265595229)
          ·
            refine ⟨10404288745269288474598211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27744769987384769265595229 10404288745269288474598211)
            ·
              refine ⟨15606433117903932711897317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10404288745269288474598211 15606433117903932711897317)
              ·
                refine ⟨2926206209606987383480747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15606433117903932711897317 2926206209606987383480747)
                ·
                  refine ⟨4389309314410481075221121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2926206209606987383480747 4389309314410481075221121)
                  ·
                    refine ⟨3291981985807860806415841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4389309314410481075221121 3291981985807860806415841)
                    ·
                      refine ⟨2468986489355895604811881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3291981985807860806415841 2468986489355895604811881)
                      ·
                        rfl

theorem cell23_4808334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 1, 4, 1, 2, 2].length) (baseStart_4808334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4808334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4808334 prefixEnd_4808334 := by exact prefixLift 4808334
  have htrace : WordTrace (prefixWord ++ tailWord_4808334) baseStart_4808334 baseEnd_4808334 := by
    simpa [prefixWord, tailWord_4808334, baseEnd_4808334] using wordTrace_append hprefix tailTrace_4808334
  have hstable : (prefixWord ++ tailWord_4808334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4808334).length < 2 ^ (prefixWord ++ tailWord_4808334).sum := by decide
  have hdescent : baseEnd_4808334 < baseStart_4808334 := by decide
  rcases family_descends (prefixWord ++ tailWord_4808334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4808340 : List Nat := [2, 4, 2, 2, 2, 2, 1, 8]
def baseStart_4808340 : Nat := 118140960795 + 4808340 * 2 ^ 59
def prefixEnd_4808340 : Nat := 4983230072969 + 3 ^ 40 * 4808340 * 2
def baseEnd_4808340 : Nat := 91444058157030465975439

theorem tailTrace_4808340 : CollatzResearch.WordTrace tailWord_4808340 prefixEnd_4808340 91444058157030465975439 := by
  unfold tailWord_4808340
  simp only [CollatzResearch.WordTrace]
  refine ⟨87687283700106426969055237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116916378266808569292073649 87687283700106426969055237)
  ·
    refine ⟨16441365693769955056697857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 87687283700106426969055237 16441365693769955056697857)
    ·
      refine ⟨12331024270327466292523393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16441365693769955056697857 12331024270327466292523393)
      ·
        refine ⟨9248268202745599719392545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12331024270327466292523393 9248268202745599719392545)
        ·
          refine ⟨6936201152059199789544409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9248268202745599719392545 6936201152059199789544409)
          ·
            refine ⟨5202150864044399842158307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6936201152059199789544409 5202150864044399842158307)
            ·
              refine ⟨7803226296066599763237461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5202150864044399842158307 7803226296066599763237461)
              ·
                refine ⟨91444058157030465975439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7803226296066599763237461 91444058157030465975439)
                ·
                  rfl

theorem cell23_4808340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 2, 1, 8].length) (baseStart_4808340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4808340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4808340 prefixEnd_4808340 := by exact prefixLift 4808340
  have htrace : WordTrace (prefixWord ++ tailWord_4808340) baseStart_4808340 baseEnd_4808340 := by
    simpa [prefixWord, tailWord_4808340, baseEnd_4808340] using wordTrace_append hprefix tailTrace_4808340
  have hstable : (prefixWord ++ tailWord_4808340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4808340).length < 2 ^ (prefixWord ++ tailWord_4808340).sum := by decide
  have hdescent : baseEnd_4808340 < baseStart_4808340 := by decide
  rcases family_descends (prefixWord ++ tailWord_4808340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4808350 : List Nat := [4, 3, 1, 1, 1, 2, 1, 3, 1, 3, 3]
def baseStart_4808350 : Nat := 118140960795 + 4808350 * 2 ^ 59
def prefixEnd_4808350 : Nat := 4983230072969 + 3 ^ 40 * 4808350 * 2
def baseEnd_4808350 : Nat := 2468994705046367542211807

theorem tailTrace_4808350 : CollatzResearch.WordTrace tailWord_4808350 prefixEnd_4808350 2468994705046367542211807 := by
  unfold tailWord_4808350
  simp only [CollatzResearch.WordTrace]
  refine ⟨21921866516272078205746813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 116916621420117750430649669 21921866516272078205746813)
  ·
    refine ⟨8220699943602029327155055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21921866516272078205746813 8220699943602029327155055)
    ·
      refine ⟨12331049915403043990732583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8220699943602029327155055 12331049915403043990732583)
      ·
        refine ⟨18496574873104565986098875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12331049915403043990732583 18496574873104565986098875)
        ·
          refine ⟨27744862309656848979148313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18496574873104565986098875 27744862309656848979148313)
          ·
            refine ⟨20808646732242636734361235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27744862309656848979148313 20808646732242636734361235)
            ·
              refine ⟨31212970098363955101541853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20808646732242636734361235 31212970098363955101541853)
              ·
                refine ⟨11704863786886483163078195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31212970098363955101541853 11704863786886483163078195)
                ·
                  refine ⟨17557295680329724744617293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11704863786886483163078195 17557295680329724744617293)
                  ·
                    refine ⟨6583985880123646779231485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17557295680329724744617293 6583985880123646779231485)
                    ·
                      refine ⟨2468994705046367542211807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6583985880123646779231485 2468994705046367542211807)
                      ·
                        rfl

theorem cell23_4808350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 1, 3, 1, 3, 3].length) (baseStart_4808350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4808350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4808350 prefixEnd_4808350 := by exact prefixLift 4808350
  have htrace : WordTrace (prefixWord ++ tailWord_4808350) baseStart_4808350 baseEnd_4808350 := by
    simpa [prefixWord, tailWord_4808350, baseEnd_4808350] using wordTrace_append hprefix tailTrace_4808350
  have hstable : (prefixWord ++ tailWord_4808350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4808350).length < 2 ^ (prefixWord ++ tailWord_4808350).sum := by decide
  have hdescent : baseEnd_4808350 < baseStart_4808350 := by decide
  rcases family_descends (prefixWord ++ tailWord_4808350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4808376 : List Nat := [2, 1, 2, 1, 2, 1, 1, 5, 2, 1, 5]
def baseStart_4808376 : Nat := 118140960795 + 4808376 * 2 ^ 59
def prefixEnd_4808376 : Nat := 4983230072969 + 3 ^ 40 * 4808376 * 2
def baseEnd_4808376 : Nat := 2469008055543384440486687

theorem tailTrace_4808376 : CollatzResearch.WordTrace tailWord_4808376 prefixEnd_4808376 2469008055543384440486687 := by
  unfold tailWord_4808376
  simp only [CollatzResearch.WordTrace]
  refine ⟨87687940214041216043210491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116917253618721621390947321 87687940214041216043210491)
  ·
    refine ⟨131531910321061824064815737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87687940214041216043210491 131531910321061824064815737)
    ·
      refine ⟨98648932740796368048611803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 131531910321061824064815737 98648932740796368048611803)
      ·
        refine ⟨147973399111194552072917705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98648932740796368048611803 147973399111194552072917705)
        ·
          refine ⟨110980049333395914054688279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 147973399111194552072917705 110980049333395914054688279)
          ·
            refine ⟨166470074000093871082032419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 110980049333395914054688279 166470074000093871082032419)
            ·
              refine ⟨249705111000140806623048629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 166470074000093871082032419 249705111000140806623048629)
              ·
                refine ⟨23409854156263200620910809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 249705111000140806623048629 23409854156263200620910809)
                ·
                  refine ⟨17557390617197400465683107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23409854156263200620910809 17557390617197400465683107)
                  ·
                    refine ⟨26336085925796100698524661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17557390617197400465683107 26336085925796100698524661)
                    ·
                      refine ⟨2469008055543384440486687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26336085925796100698524661 2469008055543384440486687)
                      ·
                        rfl

theorem cell23_4808376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 5, 2, 1, 5].length) (baseStart_4808376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4808376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4808376 prefixEnd_4808376 := by exact prefixLift 4808376
  have htrace : WordTrace (prefixWord ++ tailWord_4808376) baseStart_4808376 baseEnd_4808376 := by
    simpa [prefixWord, tailWord_4808376, baseEnd_4808376] using wordTrace_append hprefix tailTrace_4808376
  have hstable : (prefixWord ++ tailWord_4808376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4808376).length < 2 ^ (prefixWord ++ tailWord_4808376).sum := by decide
  have hdescent : baseEnd_4808376 < baseStart_4808376 := by decide
  rcases family_descends (prefixWord ++ tailWord_4808376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4808377 : List Nat := [1, 2, 1, 4, 1, 1, 6, 1, 1, 3, 2]
def baseStart_4808377 : Nat := 118140960795 + 4808377 * 2 ^ 59
def prefixEnd_4808377 : Nat := 4983230072969 + 3 ^ 40 * 4808377 * 2
def baseEnd_4808377 : Nat := 2469008569024038936574183

theorem tailTrace_4808377 : CollatzResearch.WordTrace tailWord_4808377 prefixEnd_4808377 2469008569024038936574183 := by
  unfold tailWord_4808377
  simp only [CollatzResearch.WordTrace]
  refine ⟨175375916901078809257207385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116917277934052539504804923 175375916901078809257207385)
  ·
    refine ⟨131531937675809106942905539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 175375916901078809257207385 131531937675809106942905539)
    ·
      refine ⟨197297906513713660414358309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131531937675809106942905539 197297906513713660414358309)
      ·
        refine ⟨36993357471321311327692183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 197297906513713660414358309 36993357471321311327692183)
        ·
          refine ⟨55490036206981966991538275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36993357471321311327692183 55490036206981966991538275)
          ·
            refine ⟨83235054310472950487307413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55490036206981966991538275 83235054310472950487307413)
            ·
              refine ⟨3901643170803419554092535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 83235054310472950487307413 3901643170803419554092535)
              ·
                refine ⟨5852464756205129331138803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3901643170803419554092535 5852464756205129331138803)
                ·
                  refine ⟨8778697134307693996708205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5852464756205129331138803 8778697134307693996708205)
                  ·
                    refine ⟨3292011425365385248765577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8778697134307693996708205 3292011425365385248765577)
                    ·
                      refine ⟨2469008569024038936574183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3292011425365385248765577 2469008569024038936574183)
                      ·
                        rfl

theorem cell23_4808377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 6, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 6, 1, 1, 3, 2].length) (baseStart_4808377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4808377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4808377 prefixEnd_4808377 := by exact prefixLift 4808377
  have htrace : WordTrace (prefixWord ++ tailWord_4808377) baseStart_4808377 baseEnd_4808377 := by
    simpa [prefixWord, tailWord_4808377, baseEnd_4808377] using wordTrace_append hprefix tailTrace_4808377
  have hstable : (prefixWord ++ tailWord_4808377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4808377).length < 2 ^ (prefixWord ++ tailWord_4808377).sum := by decide
  have hdescent : baseEnd_4808377 < baseStart_4808377 := by decide
  rcases family_descends (prefixWord ++ tailWord_4808377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4808480 : List Nat := [2, 1, 1, 5, 1, 1, 4, 1, 2, 1, 4]
def baseStart_4808480 : Nat := 118140960795 + 4808480 * 2 ^ 59
def prefixEnd_4808480 : Nat := 4983230072969 + 3 ^ 40 * 4808480 * 2
def baseEnd_4808480 : Nat := 2469061457531452033586209

theorem tailTrace_4808480 : CollatzResearch.WordTrace tailWord_4808480 prefixEnd_4808480 2469061457531452033586209 := by
  unfold tailWord_4808480
  simp only [CollatzResearch.WordTrace]
  refine ⟨87689836809852828924103447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116919782413137105232137929 87689836809852828924103447)
  ·
    refine ⟨131534755214779243386155171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87689836809852828924103447 131534755214779243386155171)
    ·
      refine ⟨197302132822168865079232757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131534755214779243386155171 197302132822168865079232757)
      ·
        refine ⟨18497074952078331101178071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 197302132822168865079232757 18497074952078331101178071)
        ·
          refine ⟨27745612428117496651767107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18497074952078331101178071 27745612428117496651767107)
          ·
            refine ⟨41618418642176244977650661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27745612428117496651767107 41618418642176244977650661)
            ·
              refine ⟨7803453495408045933309499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 41618418642176244977650661 7803453495408045933309499)
              ·
                refine ⟨11705180243112068899964249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7803453495408045933309499 11705180243112068899964249)
                ·
                  refine ⟨8778885182334051674973187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11705180243112068899964249 8778885182334051674973187)
                  ·
                    refine ⟨13168327773501077512459781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8778885182334051674973187 13168327773501077512459781)
                    ·
                      refine ⟨2469061457531452033586209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13168327773501077512459781 2469061457531452033586209)
                      ·
                        rfl

theorem cell23_4808480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 4, 1, 2, 1, 4].length) (baseStart_4808480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4808480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4808480 prefixEnd_4808480 := by exact prefixLift 4808480
  have htrace : WordTrace (prefixWord ++ tailWord_4808480) baseStart_4808480 baseEnd_4808480 := by
    simpa [prefixWord, tailWord_4808480, baseEnd_4808480] using wordTrace_append hprefix tailTrace_4808480
  have hstable : (prefixWord ++ tailWord_4808480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4808480).length < 2 ^ (prefixWord ++ tailWord_4808480).sum := by decide
  have hdescent : baseEnd_4808480 < baseStart_4808480 := by decide
  rcases family_descends (prefixWord ++ tailWord_4808480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4808483 : List Nat := [1, 1, 1, 4, 2, 1, 2, 3, 1, 4, 3]
def baseStart_4808483 : Nat := 118140960795 + 4808483 * 2 ^ 59
def prefixEnd_4808483 : Nat := 4983230072969 + 3 ^ 40 * 4808483 * 2
def baseEnd_4808483 : Nat := 2469062997973415521848695

theorem tailTrace_4808483 : CollatzResearch.WordTrace tailWord_4808483 prefixEnd_4808483 2469062997973415521848695 := by
  unfold tailWord_4808483
  simp only [CollatzResearch.WordTrace]
  refine ⟨175379783038694789360566103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116919855359129859573710735 175379783038694789360566103)
  ·
    refine ⟨263069674558042184040849155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175379783038694789360566103 263069674558042184040849155)
    ·
      refine ⟨394604511837063276061273733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 263069674558042184040849155 394604511837063276061273733)
      ·
        refine ⟨73988345969449364261488825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 394604511837063276061273733 73988345969449364261488825)
        ·
          refine ⟨55491259477087023196116619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73988345969449364261488825 55491259477087023196116619)
          ·
            refine ⟨83236889215630534794174929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55491259477087023196116619 83236889215630534794174929)
            ·
              refine ⟨62427666911722901095631197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 83236889215630534794174929 62427666911722901095631197)
              ·
                refine ⟨23410375091896087910861699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 62427666911722901095631197 23410375091896087910861699)
                ·
                  refine ⟨35115562637844131866292549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23410375091896087910861699 35115562637844131866292549)
                  ·
                    refine ⟨6584167994595774724929853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 35115562637844131866292549 6584167994595774724929853)
                    ·
                      refine ⟨2469062997973415521848695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6584167994595774724929853 2469062997973415521848695)
                      ·
                        rfl

theorem cell23_4808483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 3, 1, 4, 3].length) (baseStart_4808483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4808483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4808483 prefixEnd_4808483 := by exact prefixLift 4808483
  have htrace : WordTrace (prefixWord ++ tailWord_4808483) baseStart_4808483 baseEnd_4808483 := by
    simpa [prefixWord, tailWord_4808483, baseEnd_4808483] using wordTrace_append hprefix tailTrace_4808483
  have hstable : (prefixWord ++ tailWord_4808483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4808483).length < 2 ^ (prefixWord ++ tailWord_4808483).sum := by decide
  have hdescent : baseEnd_4808483 < baseStart_4808483 := by decide
  rcases family_descends (prefixWord ++ tailWord_4808483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4808554 : List Nat := [3, 1, 3, 4, 1, 2, 1, 2, 6]
def baseStart_4808554 : Nat := 118140960795 + 4808554 * 2 ^ 59
def prefixEnd_4808554 : Nat := 4983230072969 + 3 ^ 40 * 4808554 * 2
def baseEnd_4808554 : Nat := 274344383899987193784541

theorem tailTrace_4808554 : CollatzResearch.WordTrace tailWord_4808554 prefixEnd_4808554 274344383899987193784541 := by
  unfold tailWord_4808554
  simp only [CollatzResearch.WordTrace]
  refine ⟨43845593155359392121600179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 116921581747625045657600477 43845593155359392121600179)
  ·
    refine ⟨65768389733039088182400269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43845593155359392121600179 65768389733039088182400269)
    ·
      refine ⟨24663146149889658068400101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65768389733039088182400269 24663146149889658068400101)
      ·
        refine ⟨4624339903104310887825019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24663146149889658068400101 4624339903104310887825019)
        ·
          refine ⟨6936509854656466331737529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4624339903104310887825019 6936509854656466331737529)
          ·
            refine ⟨5202382390992349748803147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6936509854656466331737529 5202382390992349748803147)
            ·
              refine ⟨7803573586488524623204721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5202382390992349748803147 7803573586488524623204721)
              ·
                refine ⟨5852680189866393467403541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7803573586488524623204721 5852680189866393467403541)
                ·
                  refine ⟨274344383899987193784541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5852680189866393467403541 274344383899987193784541)
                  ·
                    rfl

theorem cell23_4808554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 2, 1, 2, 6].length) (baseStart_4808554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4808554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4808554 prefixEnd_4808554 := by exact prefixLift 4808554
  have htrace : WordTrace (prefixWord ++ tailWord_4808554) baseStart_4808554 baseEnd_4808554 := by
    simpa [prefixWord, tailWord_4808554, baseEnd_4808554] using wordTrace_append hprefix tailTrace_4808554
  have hstable : (prefixWord ++ tailWord_4808554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4808554).length < 2 ^ (prefixWord ++ tailWord_4808554).sum := by decide
  have hdescent : baseEnd_4808554 < baseStart_4808554 := by decide
  rcases family_descends (prefixWord ++ tailWord_4808554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4808557 : List Nat := [1, 5, 1, 1, 1, 1, 2, 4, 2, 3, 2]
def baseStart_4808557 : Nat := 118140960795 + 4808557 * 2 ^ 59
def prefixEnd_4808557 : Nat := 4983230072969 + 3 ^ 40 * 4808557 * 2
def baseEnd_4808557 : Nat := 2469100995541848232323355

theorem tailTrace_4808557 : CollatzResearch.WordTrace tailWord_4808557 prefixEnd_4808557 2469100995541848232323355 := by
  unfold tailWord_4808557
  simp only [CollatzResearch.WordTrace]
  refine ⟨175382482040426699998759925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116921654693617799999173283 175382482040426699998759925)
  ·
    refine ⟨16442107691290003124883743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 175382482040426699998759925 16442107691290003124883743)
    ·
      refine ⟨24663161536935004687325615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16442107691290003124883743 24663161536935004687325615)
      ·
        refine ⟨36994742305402507030988423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24663161536935004687325615 36994742305402507030988423)
        ·
          refine ⟨55492113458103760546482635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36994742305402507030988423 55492113458103760546482635)
          ·
            refine ⟨83238170187155640819723953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55492113458103760546482635 83238170187155640819723953)
            ·
              refine ⟨62428627640366730614792965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 83238170187155640819723953 62428627640366730614792965)
              ·
                refine ⟨11705367682568761990273681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 62428627640366730614792965 11705367682568761990273681)
                ·
                  refine ⟨8779025761926571492705261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11705367682568761990273681 8779025761926571492705261)
                  ·
                    refine ⟨3292134660722464309764473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8779025761926571492705261 3292134660722464309764473)
                    ·
                      refine ⟨2469100995541848232323355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3292134660722464309764473 2469100995541848232323355)
                      ·
                        rfl

theorem cell23_4808557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 4, 2, 3, 2].length) (baseStart_4808557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4808557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4808557 prefixEnd_4808557 := by exact prefixLift 4808557
  have htrace : WordTrace (prefixWord ++ tailWord_4808557) baseStart_4808557 baseEnd_4808557 := by
    simpa [prefixWord, tailWord_4808557, baseEnd_4808557] using wordTrace_append hprefix tailTrace_4808557
  have hstable : (prefixWord ++ tailWord_4808557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4808557).length < 2 ^ (prefixWord ++ tailWord_4808557).sum := by decide
  have hdescent : baseEnd_4808557 < baseStart_4808557 := by decide
  rcases family_descends (prefixWord ++ tailWord_4808557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4808574 : List Nat := [4, 2, 3, 1, 1, 1, 1, 2, 1, 5, 2]
def baseStart_4808574 : Nat := 118140960795 + 4808574 * 2 ^ 59
def prefixEnd_4808574 : Nat := 4983230072969 + 3 ^ 40 * 4808574 * 2
def baseEnd_4808574 : Nat := 2469109724712974665810777

theorem tailTrace_4808574 : CollatzResearch.WordTrace tailWord_4808574 prefixEnd_4808574 2469109724712974665810777 := by
  unfold tailWord_4808574
  simp only [CollatzResearch.WordTrace]
  refine ⟨21922887760170638987766097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 116922068054243407934752517 21922887760170638987766097)
  ·
    refine ⟨16442165820127979240824573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21922887760170638987766097 16442165820127979240824573)
    ·
      refine ⟨6165812182547992215309215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16442165820127979240824573 6165812182547992215309215)
      ·
        refine ⟨9248718273821988322963823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6165812182547992215309215 9248718273821988322963823)
        ·
          refine ⟨13873077410732982484445735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9248718273821988322963823 13873077410732982484445735)
          ·
            refine ⟨20809616116099473726668603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13873077410732982484445735 20809616116099473726668603)
            ·
              refine ⟨31214424174149210590002905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20809616116099473726668603 31214424174149210590002905)
              ·
                refine ⟨23410818130611907942502179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31214424174149210590002905 23410818130611907942502179)
                ·
                  refine ⟨35116227195917861913753269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23410818130611907942502179 35116227195917861913753269)
                  ·
                    refine ⟨3292146299617299554414369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 35116227195917861913753269 3292146299617299554414369)
                    ·
                      refine ⟨2469109724712974665810777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3292146299617299554414369 2469109724712974665810777)
                      ·
                        rfl

theorem cell23_4808574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 1, 2, 1, 5, 2].length) (baseStart_4808574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4808574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4808574 prefixEnd_4808574 := by exact prefixLift 4808574
  have htrace : WordTrace (prefixWord ++ tailWord_4808574) baseStart_4808574 baseEnd_4808574 := by
    simpa [prefixWord, tailWord_4808574, baseEnd_4808574] using wordTrace_append hprefix tailTrace_4808574
  have hstable : (prefixWord ++ tailWord_4808574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4808574).length < 2 ^ (prefixWord ++ tailWord_4808574).sum := by decide
  have hdescent : baseEnd_4808574 < baseStart_4808574 := by decide
  rcases family_descends (prefixWord ++ tailWord_4808574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4808580 : List Nat := [2, 3, 2, 1, 1, 1, 5, 1, 1, 6]
def baseStart_4808580 : Nat := 118140960795 + 4808580 * 2 ^ 59
def prefixEnd_4808580 : Nat := 4983230072969 + 3 ^ 40 * 4808580 * 2
def baseEnd_4808580 : Nat := 823037601865633880778583

theorem tailTrace_4808580 : CollatzResearch.WordTrace tailWord_4808580 prefixEnd_4808580 823037601865633880778583 := by
  unfold tailWord_4808580
  simp only [CollatzResearch.WordTrace]
  refine ⟨87691660459671687463423597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116922213946228916617898129 87691660459671687463423597)
  ·
    refine ⟨32884372672376882798783849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 87691660459671687463423597 32884372672376882798783849)
    ·
      refine ⟨24663279504282662099087887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32884372672376882798783849 24663279504282662099087887)
      ·
        refine ⟨36994919256423993148631831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24663279504282662099087887 36994919256423993148631831)
        ·
          refine ⟨55492378884635989722947747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36994919256423993148631831 55492378884635989722947747)
          ·
            refine ⟨83238568326953984584421621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55492378884635989722947747 83238568326953984584421621)
            ·
              refine ⟨7803615780651936054789527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 83238568326953984584421621 7803615780651936054789527)
              ·
                refine ⟨11705423670977904082184291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7803615780651936054789527 11705423670977904082184291)
                ·
                  refine ⟨17558135506466856123276437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11705423670977904082184291 17558135506466856123276437)
                  ·
                    refine ⟨823037601865633880778583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17558135506466856123276437 823037601865633880778583)
                    ·
                      rfl

theorem cell23_4808580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 5, 1, 1, 6].length) (baseStart_4808580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4808580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4808580 prefixEnd_4808580 := by exact prefixLift 4808580
  have htrace : WordTrace (prefixWord ++ tailWord_4808580) baseStart_4808580 baseEnd_4808580 := by
    simpa [prefixWord, tailWord_4808580, baseEnd_4808580] using wordTrace_append hprefix tailTrace_4808580
  have hstable : (prefixWord ++ tailWord_4808580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4808580).length < 2 ^ (prefixWord ++ tailWord_4808580).sum := by decide
  have hdescent : baseEnd_4808580 < baseStart_4808580 := by decide
  rcases family_descends (prefixWord ++ tailWord_4808580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4808607 : List Nat := [1, 1, 2, 5, 3, 1, 2, 1, 1, 1, 5]
def baseStart_4808607 : Nat := 118140960795 + 4808607 * 2 ^ 59
def prefixEnd_4808607 : Nat := 4983230072969 + 3 ^ 40 * 4808607 * 2
def baseEnd_4808607 : Nat := 2469126669574573036698125

theorem tailTrace_4808607 : CollatzResearch.WordTrace tailWord_4808607 prefixEnd_4808607 2469126669574573036698125 := by
  unfold tailWord_4808607
  simp only [CollatzResearch.WordTrace]
  refine ⟨175384305690245558538080075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116922870460163705692053383 175384305690245558538080075)
  ·
    refine ⟨263076458535368337807120113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175384305690245558538080075 263076458535368337807120113)
    ·
      refine ⟨197307343901526253355340085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 263076458535368337807120113 197307343901526253355340085)
      ·
        refine ⟨18497563490768086252063133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 197307343901526253355340085 18497563490768086252063133)
        ·
          refine ⟨6936586309038032344523675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18497563490768086252063133 6936586309038032344523675)
          ·
            refine ⟨10404879463557048516785513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6936586309038032344523675 10404879463557048516785513)
            ·
              refine ⟨7803659597667786387589135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10404879463557048516785513 7803659597667786387589135)
              ·
                refine ⟨11705489396501679581383703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7803659597667786387589135 11705489396501679581383703)
                ·
                  refine ⟨17558234094752519372075555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11705489396501679581383703 17558234094752519372075555)
                  ·
                    refine ⟨26337351142128779058113333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17558234094752519372075555 26337351142128779058113333)
                    ·
                      refine ⟨2469126669574573036698125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26337351142128779058113333 2469126669574573036698125)
                      ·
                        rfl

theorem cell23_4808607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 2, 1, 1, 1, 5].length) (baseStart_4808607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4808607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4808607 prefixEnd_4808607 := by exact prefixLift 4808607
  have htrace : WordTrace (prefixWord ++ tailWord_4808607) baseStart_4808607 baseEnd_4808607 := by
    simpa [prefixWord, tailWord_4808607, baseEnd_4808607] using wordTrace_append hprefix tailTrace_4808607
  have hstable : (prefixWord ++ tailWord_4808607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4808607).length < 2 ^ (prefixWord ++ tailWord_4808607).sum := by decide
  have hdescent : baseEnd_4808607 < baseStart_4808607 := by decide
  rcases family_descends (prefixWord ++ tailWord_4808607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4808623 : List Nat := [1, 1, 2, 1, 2, 2, 4, 1, 2, 7]
def baseStart_4808623 : Nat := 118140960795 + 4808623 * 2 ^ 59
def prefixEnd_4808623 : Nat := 4983230072969 + 3 ^ 40 * 4808623 * 2
def baseEnd_4808623 : Nat := 823044961755014991366017

theorem tailTrace_4808623 : CollatzResearch.WordTrace tailWord_4808623 prefixEnd_4808623 823044961755014991366017 := by
  unfold tailWord_4808623
  simp only [CollatzResearch.WordTrace]
  refine ⟨175384889258187593270662523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116923259505458395513775015 175384889258187593270662523)
  ·
    refine ⟨263077333887281389905993785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175384889258187593270662523 263077333887281389905993785)
    ·
      refine ⟨197308000415461042429495339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 263077333887281389905993785 197308000415461042429495339)
      ·
        refine ⟨295962000623191563644243009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 197308000415461042429495339 295962000623191563644243009)
        ·
          refine ⟨221971500467393672733182257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 295962000623191563644243009 221971500467393672733182257)
          ·
            refine ⟨166478625350545254549886693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 221971500467393672733182257 166478625350545254549886693)
            ·
              refine ⟨31214742253227235228103755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 166478625350545254549886693 31214742253227235228103755)
              ·
                refine ⟨46822113379840852842155633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31214742253227235228103755 46822113379840852842155633)
                ·
                  refine ⟨35116585034880639631616725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 46822113379840852842155633 35116585034880639631616725)
                  ·
                    refine ⟨823044961755014991366017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 35116585034880639631616725 823044961755014991366017)
                    ·
                      rfl

theorem cell23_4808623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 4, 1, 2, 7].length) (baseStart_4808623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4808623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4808623 prefixEnd_4808623 := by exact prefixLift 4808623
  have htrace : WordTrace (prefixWord ++ tailWord_4808623) baseStart_4808623 baseEnd_4808623 := by
    simpa [prefixWord, tailWord_4808623, baseEnd_4808623] using wordTrace_append hprefix tailTrace_4808623
  have hstable : (prefixWord ++ tailWord_4808623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4808623).length < 2 ^ (prefixWord ++ tailWord_4808623).sum := by decide
  have hdescent : baseEnd_4808623 < baseStart_4808623 := by decide
  rcases family_descends (prefixWord ++ tailWord_4808623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4808683 : List Nat := [1, 1, 1, 1, 2, 3, 1, 2, 11]
def baseStart_4808683 : Nat := 118140960795 + 4808683 * 2 ^ 59
def prefixEnd_4808683 : Nat := 4983230072969 + 3 ^ 40 * 4808683 * 2
def baseEnd_4808683 : Nat := 274351743789368304371975

theorem tailTrace_4808683 : CollatzResearch.WordTrace tailWord_4808683 prefixEnd_4808683 274351743789368304371975 := by
  unfold tailWord_4808683
  simp only [CollatzResearch.WordTrace]
  refine ⟨175387077637970223517846703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116924718425313482345231135 175387077637970223517846703)
  ·
    refine ⟨263080616456955335276770055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175387077637970223517846703 263080616456955335276770055)
    ·
      refine ⟨394620924685433002915155083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 263080616456955335276770055 394620924685433002915155083)
      ·
        refine ⟨591931387028149504372732625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 394620924685433002915155083 591931387028149504372732625)
        ·
          refine ⟨443948540271112128279549469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 591931387028149504372732625 443948540271112128279549469)
          ·
            refine ⟨166480702601667048104831051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 443948540271112128279549469 166480702601667048104831051)
            ·
              refine ⟨249721053902500572157246577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 166480702601667048104831051 249721053902500572157246577)
              ·
                refine ⟨187290790426875429117934933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 249721053902500572157246577 187290790426875429117934933)
                ·
                  refine ⟨274351743789368304371975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 187290790426875429117934933 274351743789368304371975)
                  ·
                    rfl

theorem cell23_4808683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 2, 11].length) (baseStart_4808683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4808683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4808683 prefixEnd_4808683 := by exact prefixLift 4808683
  have htrace : WordTrace (prefixWord ++ tailWord_4808683) baseStart_4808683 baseEnd_4808683 := by
    simpa [prefixWord, tailWord_4808683, baseEnd_4808683] using wordTrace_append hprefix tailTrace_4808683
  have hstable : (prefixWord ++ tailWord_4808683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4808683).length < 2 ^ (prefixWord ++ tailWord_4808683).sum := by decide
  have hdescent : baseEnd_4808683 < baseStart_4808683 := by decide
  rcases family_descends (prefixWord ++ tailWord_4808683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4808700 : List Nat := [2, 2, 2, 1, 2, 2, 3, 2, 7]
def baseStart_4808700 : Nat := 118140960795 + 4808700 * 2 ^ 59
def prefixEnd_4808700 : Nat := 4983230072969 + 3 ^ 40 * 4808700 * 2
def baseEnd_4808700 : Nat := 274352713697271241426133

theorem tailTrace_4808700 : CollatzResearch.WordTrace tailWord_4808700 prefixEnd_4808700 274352713697271241426133 := by
  unfold tailWord_4808700
  simp only [CollatzResearch.WordTrace]
  refine ⟨87693848839454317710607777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116925131785939090280810369 87693848839454317710607777)
  ·
    refine ⟨65770386629590738282955833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87693848839454317710607777 65770386629590738282955833)
    ·
      refine ⟨49327789972193053712216875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65770386629590738282955833 49327789972193053712216875)
      ·
        refine ⟨73991684958289580568325313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49327789972193053712216875 73991684958289580568325313)
        ·
          refine ⟨55493763718717185426243985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73991684958289580568325313 55493763718717185426243985)
          ·
            refine ⟨41620322789037889069682989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55493763718717185426243985 41620322789037889069682989)
            ·
              refine ⟨15607621045889208401131121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41620322789037889069682989 15607621045889208401131121)
              ·
                refine ⟨11705715784416906300848341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15607621045889208401131121 11705715784416906300848341)
                ·
                  refine ⟨274352713697271241426133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11705715784416906300848341 274352713697271241426133)
                  ·
                    rfl

theorem cell23_4808700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 3, 2, 7].length) (baseStart_4808700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4808700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4808700 prefixEnd_4808700 := by exact prefixLift 4808700
  have htrace : WordTrace (prefixWord ++ tailWord_4808700) baseStart_4808700 baseEnd_4808700 := by
    simpa [prefixWord, tailWord_4808700, baseEnd_4808700] using wordTrace_append hprefix tailTrace_4808700
  have hstable : (prefixWord ++ tailWord_4808700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4808700).length < 2 ^ (prefixWord ++ tailWord_4808700).sum := by decide
  have hdescent : baseEnd_4808700 < baseStart_4808700 := by decide
  rcases family_descends (prefixWord ++ tailWord_4808700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4808767 : List Nat := [1, 1, 2, 2, 3, 1, 2, 2, 1, 6, 2]
def baseStart_4808767 : Nat := 118140960795 + 4808767 * 2 ^ 59
def prefixEnd_4808767 : Nat := 4983230072969 + 3 ^ 40 * 4808767 * 2
def baseEnd_4808767 : Nat := 2469208826479292410697389

theorem tailTrace_4808767 : CollatzResearch.WordTrace tailWord_4808767 prefixEnd_4808767 2469208826479292410697389 := by
  unfold tailWord_4808767
  simp only [CollatzResearch.WordTrace]
  refine ⟨175390141369665905863904555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116926760913110603909269703 175390141369665905863904555)
  ·
    refine ⟨263085212054498858795856833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175390141369665905863904555 263085212054498858795856833)
    ·
      refine ⟨197313909040874144096892625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 263085212054498858795856833 197313909040874144096892625)
      ·
        refine ⟨147985431780655608072669469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 197313909040874144096892625 147985431780655608072669469)
        ·
          refine ⟨55494536917745853027251051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 147985431780655608072669469 55494536917745853027251051)
          ·
            refine ⟨83241805376618779540876577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55494536917745853027251051 83241805376618779540876577)
            ·
              refine ⟨62431354032464084655657433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 83241805376618779540876577 62431354032464084655657433)
              ·
                refine ⟨46823515524348063491743075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 62431354032464084655657433 46823515524348063491743075)
                ·
                  refine ⟨70235273286522095237614613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 46823515524348063491743075 70235273286522095237614613)
                  ·
                    refine ⟨3292278435305723214263185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 70235273286522095237614613 3292278435305723214263185)
                    ·
                      refine ⟨2469208826479292410697389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3292278435305723214263185 2469208826479292410697389)
                      ·
                        rfl

theorem cell23_4808767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 2, 1, 6, 2].length) (baseStart_4808767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4808767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4808767 prefixEnd_4808767 := by exact prefixLift 4808767
  have htrace : WordTrace (prefixWord ++ tailWord_4808767) baseStart_4808767 baseEnd_4808767 := by
    simpa [prefixWord, tailWord_4808767, baseEnd_4808767] using wordTrace_append hprefix tailTrace_4808767
  have hstable : (prefixWord ++ tailWord_4808767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4808767).length < 2 ^ (prefixWord ++ tailWord_4808767).sum := by decide
  have hdescent : baseEnd_4808767 < baseStart_4808767 := by decide
  rcases family_descends (prefixWord ++ tailWord_4808767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4808774 : List Nat := [6, 1, 1, 1, 1, 1, 2, 2, 1, 2, 5]
def baseStart_4808774 : Nat := 118140960795 + 4808774 * 2 ^ 59
def prefixEnd_4808774 : Nat := 4983230072969 + 3 ^ 40 * 4808774 * 2
def baseEnd_4808774 : Nat := 2469212420843873883309857

theorem tailTrace_4808774 : CollatzResearch.WordTrace tailWord_4808774 prefixEnd_4808774 2469212420843873883309857 := by
  unfold tailWord_4808774
  simp only [CollatzResearch.WordTrace]
  refine ⟨5480949896270017064356543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 116926931120427030706272917 5480949896270017064356543)
  ·
    refine ⟨8221424844405025596534815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5480949896270017064356543 8221424844405025596534815)
    ·
      refine ⟨12332137266607538394802223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8221424844405025596534815 12332137266607538394802223)
      ·
        refine ⟨18498205899911307592203335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12332137266607538394802223 18498205899911307592203335)
        ·
          refine ⟨27747308849866961388305003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18498205899911307592203335 27747308849866961388305003)
          ·
            refine ⟨41620963274800442082457505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27747308849866961388305003 41620963274800442082457505)
            ·
              refine ⟨31215722456100331561843129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41620963274800442082457505 31215722456100331561843129)
              ·
                refine ⟨23411791842075248671382347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31215722456100331561843129 23411791842075248671382347)
                ·
                  refine ⟨35117687763112873007073521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23411791842075248671382347 35117687763112873007073521)
                  ·
                    refine ⟨26338265822334654755305141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 35117687763112873007073521 26338265822334654755305141)
                    ·
                      refine ⟨2469212420843873883309857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26338265822334654755305141 2469212420843873883309857)
                      ·
                        rfl

theorem cell23_4808774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 2, 2, 1, 2, 5].length) (baseStart_4808774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4808774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4808774 prefixEnd_4808774 := by exact prefixLift 4808774
  have htrace : WordTrace (prefixWord ++ tailWord_4808774) baseStart_4808774 baseEnd_4808774 := by
    simpa [prefixWord, tailWord_4808774, baseEnd_4808774] using wordTrace_append hprefix tailTrace_4808774
  have hstable : (prefixWord ++ tailWord_4808774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4808774).length < 2 ^ (prefixWord ++ tailWord_4808774).sum := by decide
  have hdescent : baseEnd_4808774 < baseStart_4808774 := by decide
  rcases family_descends (prefixWord ++ tailWord_4808774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4808780 : List Nat := [2, 2, 1, 3, 1, 1, 2, 1, 1, 3, 6]
def baseStart_4808780 : Nat := 118140960795 + 4808780 * 2 ^ 59
def prefixEnd_4808780 : Nat := 4983230072969 + 3 ^ 40 * 4808780 * 2
def baseEnd_4808780 : Nat := 2469215501727800859834829

theorem tailTrace_4808780 : CollatzResearch.WordTrace tailWord_4808780 prefixEnd_4808780 2469215501727800859834829 := by
  unfold tailWord_4808780
  simp only [CollatzResearch.WordTrace]
  refine ⟨87695307759309404542063897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116927077012412539389418529 87695307759309404542063897)
  ·
    refine ⟨65771480819482053406547923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87695307759309404542063897 65771480819482053406547923)
    ·
      refine ⟨98657221229223080109821885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65771480819482053406547923 98657221229223080109821885)
      ·
        refine ⟨36996457960958655041183207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 98657221229223080109821885 36996457960958655041183207)
        ·
          refine ⟨55494686941437982561774811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36996457960958655041183207 55494686941437982561774811)
          ·
            refine ⟨83242030412156973842662217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55494686941437982561774811 83242030412156973842662217)
            ·
              refine ⟨62431522809117730381996663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 83242030412156973842662217 62431522809117730381996663)
              ·
                refine ⟨93647284213676595572994995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62431522809117730381996663 93647284213676595572994995)
                ·
                  refine ⟨140470926320514893359492493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 93647284213676595572994995 140470926320514893359492493)
                  ·
                    refine ⟨52676597370193085009809685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 140470926320514893359492493 52676597370193085009809685)
                    ·
                      refine ⟨2469215501727800859834829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 52676597370193085009809685 2469215501727800859834829)
                      ·
                        rfl

theorem cell23_4808780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 1, 1, 3, 6].length) (baseStart_4808780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4808780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4808780 prefixEnd_4808780 := by exact prefixLift 4808780
  have htrace : WordTrace (prefixWord ++ tailWord_4808780) baseStart_4808780 baseEnd_4808780 := by
    simpa [prefixWord, tailWord_4808780, baseEnd_4808780] using wordTrace_append hprefix tailTrace_4808780
  have hstable : (prefixWord ++ tailWord_4808780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4808780).length < 2 ^ (prefixWord ++ tailWord_4808780).sum := by decide
  have hdescent : baseEnd_4808780 < baseStart_4808780 := by decide
  rcases family_descends (prefixWord ++ tailWord_4808780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4808807 : List Nat := [1, 1, 5, 1, 1, 2, 3, 3, 6]
def baseStart_4808807 : Nat := 118140960795 + 4808807 * 2 ^ 59
def prefixEnd_4808807 : Nat := 4983230072969 + 3 ^ 40 * 4808807 * 2
def baseEnd_4808807 : Nat := 274358818411719139355245

theorem tailTrace_4808807 : CollatzResearch.WordTrace tailWord_4808807 prefixEnd_4808807 274358818411719139355245 := by
  unfold tailWord_4808807
  simp only [CollatzResearch.WordTrace]
  refine ⟨175391600289520992695360675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116927733526347328463573783 175391600289520992695360675)
  ·
    refine ⟨263087400434281489043041013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175391600289520992695360675 263087400434281489043041013)
    ·
      refine ⟨24664443790713889597785095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 263087400434281489043041013 24664443790713889597785095)
      ·
        refine ⟨36996665686070834396677643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24664443790713889597785095 36996665686070834396677643)
        ·
          refine ⟨55494998529106251595016465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36996665686070834396677643 55494998529106251595016465)
          ·
            refine ⟨41621248896829688696262349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55494998529106251595016465 41621248896829688696262349)
            ·
              refine ⟨15607968336311133261098381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41621248896829688696262349 15607968336311133261098381)
              ·
                refine ⟨5852988126116674972911893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15607968336311133261098381 5852988126116674972911893)
                ·
                  refine ⟨274358818411719139355245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5852988126116674972911893 274358818411719139355245)
                  ·
                    rfl

theorem cell23_4808807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 3, 3, 6].length) (baseStart_4808807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4808807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4808807 prefixEnd_4808807 := by exact prefixLift 4808807
  have htrace : WordTrace (prefixWord ++ tailWord_4808807) baseStart_4808807 baseEnd_4808807 := by
    simpa [prefixWord, tailWord_4808807, baseEnd_4808807] using wordTrace_append hprefix tailTrace_4808807
  have hstable : (prefixWord ++ tailWord_4808807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4808807).length < 2 ^ (prefixWord ++ tailWord_4808807).sum := by decide
  have hdescent : baseEnd_4808807 < baseStart_4808807 := by decide
  rcases family_descends (prefixWord ++ tailWord_4808807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4808867 : List Nat := [1, 1, 1, 4, 1, 1, 1, 1, 8, 4]
def baseStart_4808867 : Nat := 118140960795 + 4808867 * 2 ^ 59
def prefixEnd_4808867 : Nat := 4983230072969 + 3 ^ 40 * 4808867 * 2
def baseEnd_4808867 : Nat := 823086724848247339815643

theorem tailTrace_4808867 : CollatzResearch.WordTrace tailWord_4808867 prefixEnd_4808867 823086724848247339815643 := by
  unfold tailWord_4808867
  simp only [CollatzResearch.WordTrace]
  refine ⟨175393788669303622942544855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116929192446202415295029903 175393788669303622942544855)
  ·
    refine ⟨263090683003955434413817283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175393788669303622942544855 263090683003955434413817283)
    ·
      refine ⟨394636024505933151620725925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 263090683003955434413817283 394636024505933151620725925)
      ·
        refine ⟨73994254594862465928886111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 394636024505933151620725925 73994254594862465928886111)
        ·
          refine ⟨110991381892293698893329167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73994254594862465928886111 110991381892293698893329167)
          ·
            refine ⟨166487072838440548339993751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 110991381892293698893329167 166487072838440548339993751)
            ·
              refine ⟨249730609257660822509990627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 166487072838440548339993751 249730609257660822509990627)
              ·
                refine ⟨374595913886491233764985941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 249730609257660822509990627 374595913886491233764985941)
                ·
                  refine ⟨4389795865857319145683429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 374595913886491233764985941 4389795865857319145683429)
                  ·
                    refine ⟨823086724848247339815643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4389795865857319145683429 823086724848247339815643)
                    ·
                      rfl

theorem cell23_4808867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 1, 8, 4].length) (baseStart_4808867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4808867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4808867 prefixEnd_4808867 := by exact prefixLift 4808867
  have htrace : WordTrace (prefixWord ++ tailWord_4808867) baseStart_4808867 baseEnd_4808867 := by
    simpa [prefixWord, tailWord_4808867, baseEnd_4808867] using wordTrace_append hprefix tailTrace_4808867
  have hstable : (prefixWord ++ tailWord_4808867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4808867).length < 2 ^ (prefixWord ++ tailWord_4808867).sum := by decide
  have hdescent : baseEnd_4808867 < baseStart_4808867 := by decide
  rcases family_descends (prefixWord ++ tailWord_4808867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4808918 : List Nat := [5, 2, 1, 2, 1, 3, 1, 1, 1, 6]
def baseStart_4808918 : Nat := 118140960795 + 4808918 * 2 ^ 59
def prefixEnd_4808918 : Nat := 4983230072969 + 3 ^ 40 * 4808918 * 2
def baseEnd_4808918 : Nat := 823095454019373773303065

theorem tailTrace_4808918 : CollatzResearch.WordTrace tailWord_4808918 prefixEnd_4808918 823095454019373773303065 := by
  unfold tailWord_4808918
  simp only [CollatzResearch.WordTrace]
  refine ⟨10962228049507428665790713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 116930432528079239101767605 10962228049507428665790713)
  ·
    refine ⟨8221671037130571499343035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10962228049507428665790713 8221671037130571499343035)
    ·
      refine ⟨12332506555695857249014553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8221671037130571499343035 12332506555695857249014553)
      ·
        refine ⟨9249379916771892936760915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12332506555695857249014553 9249379916771892936760915)
        ·
          refine ⟨13874069875157839405141373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9249379916771892936760915 13874069875157839405141373)
          ·
            refine ⟨5202776203184189776928015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13874069875157839405141373 5202776203184189776928015)
            ·
              refine ⟨7804164304776284665392023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5202776203184189776928015 7804164304776284665392023)
              ·
                refine ⟨11706246457164426998088035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7804164304776284665392023 11706246457164426998088035)
                ·
                  refine ⟨17559369685746640497132053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11706246457164426998088035 17559369685746640497132053)
                  ·
                    refine ⟨823095454019373773303065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17559369685746640497132053 823095454019373773303065)
                    ·
                      rfl

theorem cell23_4808918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 3, 1, 1, 1, 6].length) (baseStart_4808918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4808918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4808918 prefixEnd_4808918 := by exact prefixLift 4808918
  have htrace : WordTrace (prefixWord ++ tailWord_4808918) baseStart_4808918 baseEnd_4808918 := by
    simpa [prefixWord, tailWord_4808918, baseEnd_4808918] using wordTrace_append hprefix tailTrace_4808918
  have hstable : (prefixWord ++ tailWord_4808918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4808918).length < 2 ^ (prefixWord ++ tailWord_4808918).sum := by decide
  have hdescent : baseEnd_4808918 < baseStart_4808918 := by decide
  rcases family_descends (prefixWord ++ tailWord_4808918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4808957 : List Nat := [1, 4, 1, 1, 1, 1, 1, 3, 4, 6]
def baseStart_4808957 : Nat := 118140960795 + 4808957 * 2 ^ 59
def prefixEnd_4808957 : Nat := 4983230072969 + 3 ^ 40 * 4808957 * 2
def baseEnd_4808957 : Nat := 823102129267882222440505

theorem tailTrace_4808957 : CollatzResearch.WordTrace tailWord_4808957 prefixEnd_4808957 823102129267882222440505 := by
  unfold tailWord_4808957
  simp only [CollatzResearch.WordTrace]
  refine ⟨175397071238977568313321125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116931380825985045542214083 175397071238977568313321125)
  ·
    refine ⟨32886950857308294058747711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 175397071238977568313321125 32886950857308294058747711)
    ·
      refine ⟨49330426285962441088121567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32886950857308294058747711 49330426285962441088121567)
      ·
        refine ⟨73995639428943661632182351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49330426285962441088121567 73995639428943661632182351)
        ·
          refine ⟨110993459143415492448273527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73995639428943661632182351 110993459143415492448273527)
          ·
            refine ⟨166490188715123238672410291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 110993459143415492448273527 166490188715123238672410291)
            ·
              refine ⟨249735283072684858008615437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 166490188715123238672410291 249735283072684858008615437)
              ·
                refine ⟨93650731152256821753230789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 249735283072684858008615437 93650731152256821753230789)
                ·
                  refine ⟨17559512091048154078730773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 93650731152256821753230789 17559512091048154078730773)
                  ·
                    refine ⟨823102129267882222440505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17559512091048154078730773 823102129267882222440505)
                    ·
                      rfl

theorem cell23_4808957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 3, 4, 6].length) (baseStart_4808957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4808957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4808957 prefixEnd_4808957 := by exact prefixLift 4808957
  have htrace : WordTrace (prefixWord ++ tailWord_4808957) baseStart_4808957 baseEnd_4808957 := by
    simpa [prefixWord, tailWord_4808957, baseEnd_4808957] using wordTrace_append hprefix tailTrace_4808957
  have hstable : (prefixWord ++ tailWord_4808957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4808957).length < 2 ^ (prefixWord ++ tailWord_4808957).sum := by decide
  have hdescent : baseEnd_4808957 < baseStart_4808957 := by decide
  rcases family_descends (prefixWord ++ tailWord_4808957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4808958 : List Nat := [4, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3]
def baseStart_4808958 : Nat := 118140960795 + 4808958 * 2 ^ 59
def prefixEnd_4808958 : Nat := 4983230072969 + 3 ^ 40 * 4808958 * 2
def baseEnd_4808958 : Nat := 2469306901284301163409011

theorem tailTrace_4808958 : CollatzResearch.WordTrace tailWord_4808958 prefixEnd_4808958 2469306901284301163409011 := by
  unfold tailWord_4808958
  simp only [CollatzResearch.WordTrace]
  refine ⟨21924638463996743185513441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 116931405141315963656071685 21924638463996743185513441)
  ·
    refine ⟨16443478847997557389135081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21924638463996743185513441 16443478847997557389135081)
    ·
      refine ⟨12332609135998168041851311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16443478847997557389135081 12332609135998168041851311)
      ·
        refine ⟨18498913703997252062776967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12332609135998168041851311 18498913703997252062776967)
        ·
          refine ⟨27748370555995878094165451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18498913703997252062776967 27748370555995878094165451)
          ·
            refine ⟨41622555833993817141248177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27748370555995878094165451 41622555833993817141248177)
            ·
              refine ⟨31216916875495362855936133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41622555833993817141248177 31216916875495362855936133)
              ·
                refine ⟨5853171914155380535488025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31216916875495362855936133 5853171914155380535488025)
                ·
                  refine ⟨4389878935616535401616019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5853171914155380535488025 4389878935616535401616019)
                  ·
                    refine ⟨6584818403424803102424029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4389878935616535401616019 6584818403424803102424029)
                    ·
                      refine ⟨2469306901284301163409011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6584818403424803102424029 2469306901284301163409011)
                      ·
                        rfl

theorem cell23_4808958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3].length) (baseStart_4808958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4808958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4808958 prefixEnd_4808958 := by exact prefixLift 4808958
  have htrace : WordTrace (prefixWord ++ tailWord_4808958) baseStart_4808958 baseEnd_4808958 := by
    simpa [prefixWord, tailWord_4808958, baseEnd_4808958] using wordTrace_append hprefix tailTrace_4808958
  have hstable : (prefixWord ++ tailWord_4808958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4808958).length < 2 ^ (prefixWord ++ tailWord_4808958).sum := by decide
  have hdescent : baseEnd_4808958 < baseStart_4808958 := by decide
  rcases family_descends (prefixWord ++ tailWord_4808958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4808987 : List Nat := [1, 1, 1, 1, 1, 1, 6, 4, 7]
def baseStart_4808987 : Nat := 118140960795 + 4808987 * 2 ^ 59
def prefixEnd_4808987 : Nat := 4983230072969 + 3 ^ 40 * 4808987 * 2
def baseEnd_4808987 : Nat := 274369088024809061105153

theorem tailTrace_4808987 : CollatzResearch.WordTrace tailWord_4808987 prefixEnd_4808987 274369088024809061105153 := by
  unfold tailWord_4808987
  simp only [CollatzResearch.WordTrace]
  refine ⟨175398165428868883436913215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116932110285912588957942143 175398165428868883436913215)
  ·
    refine ⟨263097248143303325155369823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175398165428868883436913215 263097248143303325155369823)
    ·
      refine ⟨394645872214954987733054735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 263097248143303325155369823 394645872214954987733054735)
      ·
        refine ⟨591968808322432481599582103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 394645872214954987733054735 591968808322432481599582103)
        ·
          refine ⟨887953212483648722399373155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 591968808322432481599582103 887953212483648722399373155)
          ·
            refine ⟨1331929818725473083599059733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 887953212483648722399373155 1331929818725473083599059733)
            ·
              refine ⟨62434210252756550793705925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1331929818725473083599059733 62434210252756550793705925)
              ·
                refine ⟨11706414422391853273819861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 62434210252756550793705925 11706414422391853273819861)
                ·
                  refine ⟨274369088024809061105153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11706414422391853273819861 274369088024809061105153)
                  ·
                    rfl

theorem cell23_4808987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 4, 7].length) (baseStart_4808987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4808987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4808987 prefixEnd_4808987 := by exact prefixLift 4808987
  have htrace : WordTrace (prefixWord ++ tailWord_4808987) baseStart_4808987 baseEnd_4808987 := by
    simpa [prefixWord, tailWord_4808987, baseEnd_4808987] using wordTrace_append hprefix tailTrace_4808987
  have hstable : (prefixWord ++ tailWord_4808987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4808987).length < 2 ^ (prefixWord ++ tailWord_4808987).sum := by decide
  have hdescent : baseEnd_4808987 < baseStart_4808987 := by decide
  rcases family_descends (prefixWord ++ tailWord_4808987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4809002 : List Nat := [3, 1, 4, 2, 2, 1, 3, 1, 1, 3, 2]
def baseStart_4809002 : Nat := 118140960795 + 4809002 * 2 ^ 59
def prefixEnd_4809002 : Nat := 4983230072969 + 3 ^ 40 * 4809002 * 2
def baseEnd_4809002 : Nat := 2469329494433098991258809

theorem tailTrace_4809002 : CollatzResearch.WordTrace tailWord_4809002 prefixEnd_4809002 2469329494433098991258809 := by
  unfold tailWord_4809002
  simp only [CollatzResearch.WordTrace]
  refine ⟨43849678130953635249677315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 116932475015876360665806173 43849678130953635249677315)
  ·
    refine ⟨65774517196430452874515973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43849678130953635249677315 65774517196430452874515973)
    ·
      refine ⟨12332721974330709913971745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 65774517196430452874515973 12332721974330709913971745)
      ·
        refine ⟨9249541480748032435478809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12332721974330709913971745 9249541480748032435478809)
        ·
          refine ⟨6937156110561024326609107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9249541480748032435478809 6937156110561024326609107)
          ·
            refine ⟨10405734165841536489913661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6937156110561024326609107 10405734165841536489913661)
            ·
              refine ⟨3902150312190576183717623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10405734165841536489913661 3902150312190576183717623)
              ·
                refine ⟨5853225468285864275576435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3902150312190576183717623 5853225468285864275576435)
                ·
                  refine ⟨8779838202428796413364653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5853225468285864275576435 8779838202428796413364653)
                  ·
                    refine ⟨3292439325910798655011745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8779838202428796413364653 3292439325910798655011745)
                    ·
                      refine ⟨2469329494433098991258809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3292439325910798655011745 2469329494433098991258809)
                      ·
                        rfl

theorem cell23_4809002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 3, 1, 1, 3, 2].length) (baseStart_4809002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4809002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4809002 prefixEnd_4809002 := by exact prefixLift 4809002
  have htrace : WordTrace (prefixWord ++ tailWord_4809002) baseStart_4809002 baseEnd_4809002 := by
    simpa [prefixWord, tailWord_4809002, baseEnd_4809002] using wordTrace_append hprefix tailTrace_4809002
  have hstable : (prefixWord ++ tailWord_4809002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4809002).length < 2 ^ (prefixWord ++ tailWord_4809002).sum := by decide
  have hdescent : baseEnd_4809002 < baseStart_4809002 := by decide
  rcases family_descends (prefixWord ++ tailWord_4809002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4809028 : List Nat := [2, 3, 4, 1, 2, 1, 1, 1, 2, 2, 4]
def baseStart_4809028 : Nat := 118140960795 + 4809028 * 2 ^ 59
def prefixEnd_4809028 : Nat := 4983230072969 + 3 ^ 40 * 4809028 * 2
def baseEnd_4809028 : Nat := 2469342844930115889533689

theorem tailTrace_4809028 : CollatzResearch.WordTrace tailWord_4809028 prefixEnd_4809028 2469342844930115889533689 := by
  unfold tailWord_4809028
  simp only [CollatzResearch.WordTrace]
  refine ⟨87699830410860173719577869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116933107214480231626103825 87699830410860173719577869)
  ·
    refine ⟨32887436404072565144841701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 87699830410860173719577869 32887436404072565144841701)
    ·
      refine ⟨6166394325763605964657819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32887436404072565144841701 6166394325763605964657819)
      ·
        refine ⟨9249591488645408946986729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6166394325763605964657819 9249591488645408946986729)
        ·
          refine ⟨6937193616484056710240047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9249591488645408946986729 6937193616484056710240047)
          ·
            refine ⟨10405790424726085065360071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6937193616484056710240047 10405790424726085065360071)
            ·
              refine ⟨15608685637089127598040107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10405790424726085065360071 15608685637089127598040107)
              ·
                refine ⟨23413028455633691397060161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15608685637089127598040107 23413028455633691397060161)
                ·
                  refine ⟨17559771341725268547795121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23413028455633691397060161 17559771341725268547795121)
                  ·
                    refine ⟨13169828506293951410846341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17559771341725268547795121 13169828506293951410846341)
                    ·
                      refine ⟨2469342844930115889533689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13169828506293951410846341 2469342844930115889533689)
                      ·
                        rfl

theorem cell23_4809028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 1, 1, 2, 2, 4].length) (baseStart_4809028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4809028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4809028 prefixEnd_4809028 := by exact prefixLift 4809028
  have htrace : WordTrace (prefixWord ++ tailWord_4809028) baseStart_4809028 baseEnd_4809028 := by
    simpa [prefixWord, tailWord_4809028, baseEnd_4809028] using wordTrace_append hprefix tailTrace_4809028
  have hstable : (prefixWord ++ tailWord_4809028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4809028).length < 2 ^ (prefixWord ++ tailWord_4809028).sum := by decide
  have hdescent : baseEnd_4809028 < baseStart_4809028 := by decide
  rcases family_descends (prefixWord ++ tailWord_4809028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4809144 : List Nat := [2, 1, 2, 1, 2, 2, 1, 1, 2, 5, 4]
def baseStart_4809144 : Nat := 118140960795 + 4809144 * 2 ^ 59
def prefixEnd_4809144 : Nat := 4983230072969 + 3 ^ 40 * 4809144 * 2
def baseEnd_4809144 : Nat := 2469402408686037435683155

theorem tailTrace_4809144 : CollatzResearch.WordTrace tailWord_4809144 prefixEnd_4809144 2469402408686037435683155 := by
  unfold tailWord_4809144
  simp only [CollatzResearch.WordTrace]
  refine ⟨87701945844650049625189243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116935927792866732833585657 87701945844650049625189243)
  ·
    refine ⟨131552918766975074437783865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87701945844650049625189243 131552918766975074437783865)
    ·
      refine ⟨98664689075231305828337899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 131552918766975074437783865 98664689075231305828337899)
      ·
        refine ⟨147997033612846958742506849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98664689075231305828337899 147997033612846958742506849)
        ·
          refine ⟨110997775209635219056880137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 147997033612846958742506849 110997775209635219056880137)
          ·
            refine ⟨83248331407226414292660103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 110997775209635219056880137 83248331407226414292660103)
            ·
              refine ⟨124872497110839621438990155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83248331407226414292660103 124872497110839621438990155)
              ·
                refine ⟨187308745666259432158485233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 124872497110839621438990155 187308745666259432158485233)
                ·
                  refine ⟨140481559249694574118863925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 187308745666259432158485233 140481559249694574118863925)
                  ·
                    refine ⟨13170146179658866323643493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 140481559249694574118863925 13170146179658866323643493)
                    ·
                      refine ⟨2469402408686037435683155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13170146179658866323643493 2469402408686037435683155)
                      ·
                        rfl

theorem cell23_4809144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 1, 2, 5, 4].length) (baseStart_4809144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4809144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4809144 prefixEnd_4809144 := by exact prefixLift 4809144
  have htrace : WordTrace (prefixWord ++ tailWord_4809144) baseStart_4809144 baseEnd_4809144 := by
    simpa [prefixWord, tailWord_4809144, baseEnd_4809144] using wordTrace_append hprefix tailTrace_4809144
  have hstable : (prefixWord ++ tailWord_4809144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4809144).length < 2 ^ (prefixWord ++ tailWord_4809144).sum := by decide
  have hdescent : baseEnd_4809144 < baseStart_4809144 := by decide
  rcases family_descends (prefixWord ++ tailWord_4809144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4809161 : List Nat := [1, 2, 1, 1, 2, 1, 4, 1, 2, 6, 2]
def baseStart_4809161 : Nat := 118140960795 + 4809161 * 2 ^ 59
def prefixEnd_4809161 : Nat := 4983230072969 + 3 ^ 40 * 4809161 * 2
def baseEnd_4809161 : Nat := 2469411137857163869170577

theorem tailTrace_4809161 : CollatzResearch.WordTrace tailWord_4809161 prefixEnd_4809161 2469411137857163869170577 := by
  unfold tailWord_4809161
  simp only [CollatzResearch.WordTrace]
  refine ⟨175404511730238511153747337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116936341153492340769164891 175404511730238511153747337)
  ·
    refine ⟨131553383797678883365310503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 175404511730238511153747337 131553383797678883365310503)
    ·
      refine ⟨197330075696518325047965755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131553383797678883365310503 197330075696518325047965755)
      ·
        refine ⟨295995113544777487571948633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 197330075696518325047965755 295995113544777487571948633)
        ·
          refine ⟨221996335158583115678961475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 295995113544777487571948633 221996335158583115678961475)
          ·
            refine ⟨332994502737874673518442213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 221996335158583115678961475 332994502737874673518442213)
            ·
              refine ⟨62436469263351501284707915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 332994502737874673518442213 62436469263351501284707915)
              ·
                refine ⟨93654703895027251927061873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62436469263351501284707915 93654703895027251927061873)
                ·
                  refine ⟨70241027921270438945296405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 93654703895027251927061873 70241027921270438945296405)
                  ·
                    refine ⟨3292548183809551825560769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 70241027921270438945296405 3292548183809551825560769)
                    ·
                      refine ⟨2469411137857163869170577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3292548183809551825560769 2469411137857163869170577)
                      ·
                        rfl

theorem cell23_4809161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 1, 2, 6, 2].length) (baseStart_4809161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4809161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4809161 prefixEnd_4809161 := by exact prefixLift 4809161
  have htrace : WordTrace (prefixWord ++ tailWord_4809161) baseStart_4809161 baseEnd_4809161 := by
    simpa [prefixWord, tailWord_4809161, baseEnd_4809161] using wordTrace_append hprefix tailTrace_4809161
  have hstable : (prefixWord ++ tailWord_4809161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4809161).length < 2 ^ (prefixWord ++ tailWord_4809161).sum := by decide
  have hdescent : baseEnd_4809161 < baseStart_4809161 := by decide
  rcases family_descends (prefixWord ++ tailWord_4809161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4809191 : List Nat := [1, 1, 5, 2, 1, 1, 1, 2, 3, 2, 4]
def baseStart_4809191 : Nat := 118140960795 + 4809191 * 2 ^ 59
def prefixEnd_4809191 : Nat := 4983230072969 + 3 ^ 40 * 4809191 * 2
def baseEnd_4809191 : Nat := 2469426542276798751795439

theorem tailTrace_4809191 : CollatzResearch.WordTrace tailWord_4809191 prefixEnd_4809191 2469426542276798751795439 := by
  unfold tailWord_4809191
  simp only [CollatzResearch.WordTrace]
  refine ⟨175405605920129826277339427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116937070613419884184892951 175405605920129826277339427)
  ·
    refine ⟨263108408880194739416009141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175405605920129826277339427 263108408880194739416009141)
    ·
      refine ⟨24666413332518256820250857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 263108408880194739416009141 24666413332518256820250857)
      ·
        refine ⟨18499809999388692615188143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24666413332518256820250857 18499809999388692615188143)
        ·
          refine ⟨27749714999083038922782215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18499809999388692615188143 27749714999083038922782215)
          ·
            refine ⟨41624572498624558384173323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27749714999083038922782215 41624572498624558384173323)
            ·
              refine ⟨62436858747936837576259985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41624572498624558384173323 62436858747936837576259985)
              ·
                refine ⟨46827644060952628182194989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 62436858747936837576259985 46827644060952628182194989)
                ·
                  refine ⟨17560366522857235568323121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 46827644060952628182194989 17560366522857235568323121)
                  ·
                    refine ⟨13170274892142926676242341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17560366522857235568323121 13170274892142926676242341)
                    ·
                      refine ⟨2469426542276798751795439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13170274892142926676242341 2469426542276798751795439)
                      ·
                        rfl

theorem cell23_4809191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 2, 3, 2, 4].length) (baseStart_4809191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4809191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4809191 prefixEnd_4809191 := by exact prefixLift 4809191
  have htrace : WordTrace (prefixWord ++ tailWord_4809191) baseStart_4809191 baseEnd_4809191 := by
    simpa [prefixWord, tailWord_4809191, baseEnd_4809191] using wordTrace_append hprefix tailTrace_4809191
  have hstable : (prefixWord ++ tailWord_4809191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4809191).length < 2 ^ (prefixWord ++ tailWord_4809191).sum := by decide
  have hdescent : baseEnd_4809191 < baseStart_4809191 := by decide
  rcases family_descends (prefixWord ++ tailWord_4809191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4809198 : List Nat := [4, 1, 2, 1, 2, 2, 1, 2, 3, 2, 3]
def baseStart_4809198 : Nat := 118140960795 + 4809198 * 2 ^ 59
def prefixEnd_4809198 : Nat := 4983230072969 + 3 ^ 40 * 4809198 * 2
def baseEnd_4809198 : Nat := 2469430136641380224407907

theorem tailTrace_4809198 : CollatzResearch.WordTrace tailWord_4809198 prefixEnd_4809198 2469430136641380224407907 := by
  unfold tailWord_4809198
  simp only [CollatzResearch.WordTrace]
  refine ⟨21925732653888058309105531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 116937240820736310981896165 21925732653888058309105531)
  ·
    refine ⟨32888598980832087463658297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21925732653888058309105531 32888598980832087463658297)
    ·
      refine ⟨24666449235624065597743723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32888598980832087463658297 24666449235624065597743723)
      ·
        refine ⟨36999673853436098396615585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24666449235624065597743723 36999673853436098396615585)
        ·
          refine ⟨27749755390077073797461689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36999673853436098396615585 27749755390077073797461689)
          ·
            refine ⟨20812316542557805348096267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27749755390077073797461689 20812316542557805348096267)
            ·
              refine ⟨31218474813836708022144401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20812316542557805348096267 31218474813836708022144401)
              ·
                refine ⟨23413856110377531016608301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31218474813836708022144401 23413856110377531016608301)
                ·
                  refine ⟨8780196041391574131228113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23413856110377531016608301 8780196041391574131228113)
                  ·
                    refine ⟨6585147031043680598421085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8780196041391574131228113 6585147031043680598421085)
                    ·
                      refine ⟨2469430136641380224407907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6585147031043680598421085 2469430136641380224407907)
                      ·
                        rfl

theorem cell23_4809198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 1, 2, 3, 2, 3].length) (baseStart_4809198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4809198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4809198 prefixEnd_4809198 := by exact prefixLift 4809198
  have htrace : WordTrace (prefixWord ++ tailWord_4809198) baseStart_4809198 baseEnd_4809198 := by
    simpa [prefixWord, tailWord_4809198, baseEnd_4809198] using wordTrace_append hprefix tailTrace_4809198
  have hstable : (prefixWord ++ tailWord_4809198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4809198).length < 2 ^ (prefixWord ++ tailWord_4809198).sum := by decide
  have hdescent : baseEnd_4809198 < baseStart_4809198 := by decide
  rcases family_descends (prefixWord ++ tailWord_4809198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4809205 : List Nat := [1, 3, 5, 1, 2, 1, 2, 1, 1, 6]
def baseStart_4809205 : Nat := 118140960795 + 4809205 * 2 ^ 59
def prefixEnd_4809205 : Nat := 4983230072969 + 3 ^ 40 * 4809205 * 2
def baseEnd_4809205 : Nat := 823144577001987232340125

theorem tailTrace_4809205 : CollatzResearch.WordTrace tailWord_4809205 prefixEnd_4809205 823144577001987232340125 := by
  unfold tailWord_4809205
  simp only [CollatzResearch.WordTrace]
  refine ⟨175406116542079106668349069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116937411028052737778899379 175406116542079106668349069)
  ·
    refine ⟨65777293703279665000630901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 175406116542079106668349069 65777293703279665000630901)
    ·
      refine ⟨6166621284682468593809147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 65777293703279665000630901 6166621284682468593809147)
      ·
        refine ⟨9249931927023702890713721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6166621284682468593809147 9249931927023702890713721)
        ·
          refine ⟨6937448945267777168035291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9249931927023702890713721 6937448945267777168035291)
          ·
            refine ⟨10406173417901665752052937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6937448945267777168035291 10406173417901665752052937)
            ·
              refine ⟨7804630063426249314039703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10406173417901665752052937 7804630063426249314039703)
              ·
                refine ⟨11706945095139373971059555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7804630063426249314039703 11706945095139373971059555)
                ·
                  refine ⟨17560417642709060956589333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11706945095139373971059555 17560417642709060956589333)
                  ·
                    refine ⟨823144577001987232340125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17560417642709060956589333 823144577001987232340125)
                    ·
                      rfl

theorem cell23_4809205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 2, 1, 1, 6].length) (baseStart_4809205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4809205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4809205 prefixEnd_4809205 := by exact prefixLift 4809205
  have htrace : WordTrace (prefixWord ++ tailWord_4809205) baseStart_4809205 baseEnd_4809205 := by
    simpa [prefixWord, tailWord_4809205, baseEnd_4809205] using wordTrace_append hprefix tailTrace_4809205
  have hstable : (prefixWord ++ tailWord_4809205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4809205).length < 2 ^ (prefixWord ++ tailWord_4809205).sum := by decide
  have hdescent : baseEnd_4809205 < baseStart_4809205 := by decide
  rcases family_descends (prefixWord ++ tailWord_4809205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4809222 : List Nat := [6, 2, 1, 1, 1, 1, 2, 2, 1, 6]
def baseStart_4809222 : Nat := 118140960795 + 4809222 * 2 ^ 59
def prefixEnd_4809222 : Nat := 4983230072969 + 3 ^ 40 * 4809222 * 2
def baseEnd_4809222 : Nat := 823147486725696043502599

theorem tailTrace_4809222 : CollatzResearch.WordTrace tailWord_4809222 prefixEnd_4809222 823147486725696043502599 := by
  unfold tailWord_4809222
  simp only [CollatzResearch.WordTrace]
  refine ⟨5481460518219297455366185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 116937824388678345714478613 5481460518219297455366185)
  ·
    refine ⟨4111095388664473091524639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5481460518219297455366185 4111095388664473091524639)
    ·
      refine ⟨6166643082996709637286959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4111095388664473091524639 6166643082996709637286959)
      ·
        refine ⟨9249964624495064455930439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6166643082996709637286959 9249964624495064455930439)
        ·
          refine ⟨13874946936742596683895659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9249964624495064455930439 13874946936742596683895659)
          ·
            refine ⟨20812420405113895025843489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13874946936742596683895659 20812420405113895025843489)
            ·
              refine ⟨15609315303835421269382617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20812420405113895025843489 15609315303835421269382617)
              ·
                refine ⟨11706986477876565952036963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15609315303835421269382617 11706986477876565952036963)
                ·
                  refine ⟨17560479716814848928055445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11706986477876565952036963 17560479716814848928055445)
                  ·
                    refine ⟨823147486725696043502599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17560479716814848928055445 823147486725696043502599)
                    ·
                      rfl

theorem cell23_4809222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 2, 2, 1, 6].length) (baseStart_4809222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4809222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4809222 prefixEnd_4809222 := by exact prefixLift 4809222
  have htrace : WordTrace (prefixWord ++ tailWord_4809222) baseStart_4809222 baseEnd_4809222 := by
    simpa [prefixWord, tailWord_4809222, baseEnd_4809222] using wordTrace_append hprefix tailTrace_4809222
  have hstable : (prefixWord ++ tailWord_4809222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4809222).length < 2 ^ (prefixWord ++ tailWord_4809222).sum := by decide
  have hdescent : baseEnd_4809222 < baseStart_4809222 := by decide
  rcases family_descends (prefixWord ++ tailWord_4809222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4809228 : List Nat := [2, 2, 1, 2, 4, 1, 2, 2, 1, 3, 3]
def baseStart_4809228 : Nat := 118140960795 + 4809228 * 2 ^ 59
def prefixEnd_4809228 : Nat := 4983230072969 + 3 ^ 40 * 4809228 * 2
def baseEnd_4809228 : Nat := 2469445541061015107032769

theorem tailTrace_4809228 : CollatzResearch.WordTrace tailWord_4809228 prefixEnd_4809228 2469445541061015107032769 := by
  unfold tailWord_4809228
  simp only [CollatzResearch.WordTrace]
  refine ⟨87703477710497890798218169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116937970280663854397624225 87703477710497890798218169)
  ·
    refine ⟨65777608282873418098663627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87703477710497890798218169 65777608282873418098663627)
    ·
      refine ⟨98666412424310127147995441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65777608282873418098663627 98666412424310127147995441)
      ·
        refine ⟨73999809318232595360996581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 98666412424310127147995441 73999809318232595360996581)
        ·
          refine ⟨13874964247168611630186859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 73999809318232595360996581 13874964247168611630186859)
          ·
            refine ⟨20812446370752917445280289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13874964247168611630186859 20812446370752917445280289)
            ·
              refine ⟨15609334778064688083960217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20812446370752917445280289 15609334778064688083960217)
              ·
                refine ⟨11707001083548516062970163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15609334778064688083960217 11707001083548516062970163)
                ·
                  refine ⟨17560501625322774094455245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11707001083548516062970163 17560501625322774094455245)
                  ·
                    refine ⟨6585188109496040285420717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17560501625322774094455245 6585188109496040285420717)
                    ·
                      refine ⟨2469445541061015107032769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6585188109496040285420717 2469445541061015107032769)
                      ·
                        rfl

theorem cell23_4809228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 2, 2, 1, 3, 3].length) (baseStart_4809228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4809228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4809228 prefixEnd_4809228 := by exact prefixLift 4809228
  have htrace : WordTrace (prefixWord ++ tailWord_4809228) baseStart_4809228 baseEnd_4809228 := by
    simpa [prefixWord, tailWord_4809228, baseEnd_4809228] using wordTrace_append hprefix tailTrace_4809228
  have hstable : (prefixWord ++ tailWord_4809228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4809228).length < 2 ^ (prefixWord ++ tailWord_4809228).sum := by decide
  have hdescent : baseEnd_4809228 < baseStart_4809228 := by decide
  rcases family_descends (prefixWord ++ tailWord_4809228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4809229 : List Nat := [1, 7, 1, 1, 1, 1, 4, 1, 1, 1, 4]
def baseStart_4809229 : Nat := 118140960795 + 4809229 * 2 ^ 59
def prefixEnd_4809229 : Nat := 4983230072969 + 3 ^ 40 * 4809229 * 2
def baseEnd_4809229 : Nat := 2469446054541669603120265

theorem tailTrace_4809229 : CollatzResearch.WordTrace tailWord_4809229 prefixEnd_4809229 2469446054541669603120265 := by
  unfold tailWord_4809229
  simp only [CollatzResearch.WordTrace]
  refine ⟨175406991893992158767222741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116937994595994772511481827 175406991893992158767222741)
  ·
    refine ⟨4111101372515441221106783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 175406991893992158767222741 4111101372515441221106783)
    ·
      refine ⟨6166652058773161831660175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4111101372515441221106783 6166652058773161831660175)
      ·
        refine ⟨9249978088159742747490263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6166652058773161831660175 9249978088159742747490263)
        ·
          refine ⟨13874967132239614121235395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9249978088159742747490263 13874967132239614121235395)
          ·
            refine ⟨20812450698359421181853093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13874967132239614121235395 20812450698359421181853093)
            ·
              refine ⟨3902334505942391471597455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20812450698359421181853093 3902334505942391471597455)
              ·
                refine ⟨5853501758913587207396183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3902334505942391471597455 5853501758913587207396183)
                ·
                  refine ⟨8780252638370380811094275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5853501758913587207396183 8780252638370380811094275)
                  ·
                    refine ⟨13170378957555571216641413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8780252638370380811094275 13170378957555571216641413)
                    ·
                      refine ⟨2469446054541669603120265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13170378957555571216641413 2469446054541669603120265)
                      ·
                        rfl

theorem cell23_4809229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 4, 1, 1, 1, 4].length) (baseStart_4809229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4809229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4809229 prefixEnd_4809229 := by exact prefixLift 4809229
  have htrace : WordTrace (prefixWord ++ tailWord_4809229) baseStart_4809229 baseEnd_4809229 := by
    simpa [prefixWord, tailWord_4809229, baseEnd_4809229] using wordTrace_append hprefix tailTrace_4809229
  have hstable : (prefixWord ++ tailWord_4809229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4809229).length < 2 ^ (prefixWord ++ tailWord_4809229).sum := by decide
  have hdescent : baseEnd_4809229 < baseStart_4809229 := by decide
  rcases family_descends (prefixWord ++ tailWord_4809229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4809239 : List Nat := [1, 1, 3, 6, 2, 1, 1, 2, 2, 4]
def baseStart_4809239 : Nat := 118140960795 + 4809239 * 2 ^ 59
def prefixEnd_4809239 : Nat := 4983230072969 + 3 ^ 40 * 4809239 * 2
def baseEnd_4809239 : Nat := 823150396449404854665073

theorem tailTrace_4809239 : CollatzResearch.WordTrace tailWord_4809239 prefixEnd_4809239 823150396449404854665073 := by
  unfold tailWord_4809239
  simp only [CollatzResearch.WordTrace]
  refine ⟨175407356623955930475086771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116938237749303953650057847 175407356623955930475086771)
  ·
    refine ⟨263111034935933895712630157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175407356623955930475086771 263111034935933895712630157)
    ·
      refine ⟨98666638100975210892236309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 263111034935933895712630157 98666638100975210892236309)
      ·
        refine ⟨4624998660983213010573577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 98666638100975210892236309 4624998660983213010573577)
        ·
          refine ⟨3468748995737409757930183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4624998660983213010573577 3468748995737409757930183)
          ·
            refine ⟨5203123493606114636895275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3468748995737409757930183 5203123493606114636895275)
            ·
              refine ⟨7804685240409171955342913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5203123493606114636895275 7804685240409171955342913)
              ·
                refine ⟨5853513930306878966507185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7804685240409171955342913 5853513930306878966507185)
                ·
                  refine ⟨4390135447730159224880389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5853513930306878966507185 4390135447730159224880389)
                  ·
                    refine ⟨823150396449404854665073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4390135447730159224880389 823150396449404854665073)
                    ·
                      rfl

theorem cell23_4809239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 2, 1, 1, 2, 2, 4].length) (baseStart_4809239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4809239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4809239 prefixEnd_4809239 := by exact prefixLift 4809239
  have htrace : WordTrace (prefixWord ++ tailWord_4809239) baseStart_4809239 baseEnd_4809239 := by
    simpa [prefixWord, tailWord_4809239, baseEnd_4809239] using wordTrace_append hprefix tailTrace_4809239
  have hstable : (prefixWord ++ tailWord_4809239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4809239).length < 2 ^ (prefixWord ++ tailWord_4809239).sum := by decide
  have hdescent : baseEnd_4809239 < baseStart_4809239 := by decide
  rcases family_descends (prefixWord ++ tailWord_4809239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4809245 : List Nat := [1, 4, 2, 2, 1, 3, 1, 1, 4, 1, 3]
def baseStart_4809245 : Nat := 118140960795 + 4809245 * 2 ^ 59
def prefixEnd_4809245 : Nat := 4983230072969 + 3 ^ 40 * 4809245 * 2
def baseEnd_4809245 : Nat := 2469454270232141540520191

theorem tailTrace_4809245 : CollatzResearch.WordTrace tailWord_4809245 prefixEnd_4809245 2469454270232141540520191 := by
  unfold tailWord_4809245
  simp only [CollatzResearch.WordTrace]
  refine ⟨175407575461934193499805189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116938383641289462333203459 175407575461934193499805189)
  ·
    refine ⟨32888920399112661281213473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 175407575461934193499805189 32888920399112661281213473)
    ·
      refine ⟨24666690299334495960910105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32888920399112661281213473 24666690299334495960910105)
      ·
        refine ⟨18500017724500871970682579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24666690299334495960910105 18500017724500871970682579)
        ·
          refine ⟨27750026586751307956023869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18500017724500871970682579 27750026586751307956023869)
          ·
            refine ⟨10406259970031740483508951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27750026586751307956023869 10406259970031740483508951)
            ·
              refine ⟨15609389955047610725263427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10406259970031740483508951 15609389955047610725263427)
              ·
                refine ⟨23414084932571416087895141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15609389955047610725263427 23414084932571416087895141)
                ·
                  refine ⟨4390140924857140516480339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23414084932571416087895141 4390140924857140516480339)
                  ·
                    refine ⟨6585211387285710774720509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4390140924857140516480339 6585211387285710774720509)
                    ·
                      refine ⟨2469454270232141540520191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6585211387285710774720509 2469454270232141540520191)
                      ·
                        rfl

theorem cell23_4809245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 1, 1, 4, 1, 3].length) (baseStart_4809245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4809245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4809245 prefixEnd_4809245 := by exact prefixLift 4809245
  have htrace : WordTrace (prefixWord ++ tailWord_4809245) baseStart_4809245 baseEnd_4809245 := by
    simpa [prefixWord, tailWord_4809245, baseEnd_4809245] using wordTrace_append hprefix tailTrace_4809245
  have hstable : (prefixWord ++ tailWord_4809245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4809245).length < 2 ^ (prefixWord ++ tailWord_4809245).sum := by decide
  have hdescent : baseEnd_4809245 < baseStart_4809245 := by decide
  rcases family_descends (prefixWord ++ tailWord_4809245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4809262 : List Nat := [4, 1, 3, 1, 3, 2, 1, 1, 1, 3, 3]
def baseStart_4809262 : Nat := 118140960795 + 4809262 * 2 ^ 59
def prefixEnd_4809262 : Nat := 4983230072969 + 3 ^ 40 * 4809262 * 2
def baseEnd_4809262 : Nat := 2469462999403267974007613

theorem tailTrace_4809262 : CollatzResearch.WordTrace tailWord_4809262 prefixEnd_4809262 2469462999403267974007613 := by
  unfold tailWord_4809262
  simp only [CollatzResearch.WordTrace]
  refine ⟨21926024437859075675396755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 116938797001915070268782693 21926024437859075675396755)
  ·
    refine ⟨32889036656788613513095133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21926024437859075675396755 32889036656788613513095133)
    ·
      refine ⟨12333388746295730067410675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32889036656788613513095133 12333388746295730067410675)
      ·
        refine ⟨18500083119443595101116013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12333388746295730067410675 18500083119443595101116013)
        ·
          refine ⟨6937531169791348162918505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18500083119443595101116013 6937531169791348162918505)
          ·
            refine ⟨5203148377343511122188879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6937531169791348162918505 5203148377343511122188879)
            ·
              refine ⟨7804722566015266683283319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5203148377343511122188879 7804722566015266683283319)
              ·
                refine ⟨11707083849022900024924979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7804722566015266683283319 11707083849022900024924979)
                ·
                  refine ⟨17560625773534350037387469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11707083849022900024924979 17560625773534350037387469)
                  ·
                    refine ⟨6585234665075381264020301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17560625773534350037387469 6585234665075381264020301)
                    ·
                      refine ⟨2469462999403267974007613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6585234665075381264020301 2469462999403267974007613)
                      ·
                        rfl

theorem cell23_4809262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 2, 1, 1, 1, 3, 3].length) (baseStart_4809262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4809262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4809262 prefixEnd_4809262 := by exact prefixLift 4809262
  have htrace : WordTrace (prefixWord ++ tailWord_4809262) baseStart_4809262 baseEnd_4809262 := by
    simpa [prefixWord, tailWord_4809262, baseEnd_4809262] using wordTrace_append hprefix tailTrace_4809262
  have hstable : (prefixWord ++ tailWord_4809262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4809262).length < 2 ^ (prefixWord ++ tailWord_4809262).sum := by decide
  have hdescent : baseEnd_4809262 < baseStart_4809262 := by decide
  rcases family_descends (prefixWord ++ tailWord_4809262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4809271 : List Nat := [1, 1, 3, 1, 2, 3, 2, 2, 2, 1, 5]
def baseStart_4809271 : Nat := 118140960795 + 4809271 * 2 ^ 59
def prefixEnd_4809271 : Nat := 4983230072969 + 3 ^ 40 * 4809271 * 2
def baseEnd_4809271 : Nat := 2469467620729158438795071

theorem tailTrace_4809271 : CollatzResearch.WordTrace tailWord_4809271 prefixEnd_4809271 2469467620729158438795071 := by
  unfold tailWord_4809271
  simp only [CollatzResearch.WordTrace]
  refine ⟨175408523759839999940251667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116939015839893333293501111 175408523759839999940251667)
  ·
    refine ⟨263112785639759999910377501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175408523759839999940251667 263112785639759999910377501)
    ·
      refine ⟨98667294614909999966391563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 263112785639759999910377501 98667294614909999966391563)
      ·
        refine ⟨148000941922364999949587345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98667294614909999966391563 148000941922364999949587345)
        ·
          refine ⟨111000706441773749962190509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 148000941922364999949587345 111000706441773749962190509)
          ·
            refine ⟨41625264915665156235821441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 111000706441773749962190509 41625264915665156235821441)
            ·
              refine ⟨31218948686748867176866081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41625264915665156235821441 31218948686748867176866081)
              ·
                refine ⟨23414211515061650382649561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31218948686748867176866081 23414211515061650382649561)
                ·
                  refine ⟨17560658636296237786987171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23414211515061650382649561 17560658636296237786987171)
                  ·
                    refine ⟨26340987954444356680480757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17560658636296237786987171 26340987954444356680480757)
                    ·
                      refine ⟨2469467620729158438795071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26340987954444356680480757 2469467620729158438795071)
                      ·
                        rfl

theorem cell23_4809271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 2, 2, 2, 1, 5].length) (baseStart_4809271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4809271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4809271 prefixEnd_4809271 := by exact prefixLift 4809271
  have htrace : WordTrace (prefixWord ++ tailWord_4809271) baseStart_4809271 baseEnd_4809271 := by
    simpa [prefixWord, tailWord_4809271, baseEnd_4809271] using wordTrace_append hprefix tailTrace_4809271
  have hstable : (prefixWord ++ tailWord_4809271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4809271).length < 2 ^ (prefixWord ++ tailWord_4809271).sum := by decide
  have hdescent : baseEnd_4809271 < baseStart_4809271 := by decide
  rcases family_descends (prefixWord ++ tailWord_4809271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4809285 : List Nat := [1, 3, 1, 1, 1, 5, 1, 2, 4, 2, 2]
def baseStart_4809285 : Nat := 118140960795 + 4809285 * 2 ^ 59
def prefixEnd_4809285 : Nat := 4983230072969 + 3 ^ 40 * 4809285 * 2
def baseEnd_4809285 : Nat := 2469474809458321384020007

theorem tailTrace_4809285 : CollatzResearch.WordTrace tailWord_4809285 prefixEnd_4809285 2469474809458321384020007 := by
  unfold tailWord_4809285
  simp only [CollatzResearch.WordTrace]
  refine ⟨175409034381789280331261309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116939356254526186887507539 175409034381789280331261309)
  ·
    refine ⟨65778387893170980124222991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 175409034381789280331261309 65778387893170980124222991)
    ·
      refine ⟨98667581839756470186334487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65778387893170980124222991 98667581839756470186334487)
      ·
        refine ⟨148001372759634705279501731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98667581839756470186334487 148001372759634705279501731)
        ·
          refine ⟨222002059139452057919252597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 148001372759634705279501731 222002059139452057919252597)
          ·
            refine ⟨20812693044323630429929931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 222002059139452057919252597 20812693044323630429929931)
            ·
              refine ⟨31219039566485445644894897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20812693044323630429929931 31219039566485445644894897)
              ·
                refine ⟨23414279674864084233671173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31219039566485445644894897 23414279674864084233671173)
                ·
                  refine ⟨4390177439037015793813345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23414279674864084233671173 4390177439037015793813345)
                  ·
                    refine ⟨3292633079277761845360009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4390177439037015793813345 3292633079277761845360009)
                    ·
                      refine ⟨2469474809458321384020007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3292633079277761845360009 2469474809458321384020007)
                      ·
                        rfl

theorem cell23_4809285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 1, 2, 4, 2, 2].length) (baseStart_4809285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4809285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4809285 prefixEnd_4809285 := by exact prefixLift 4809285
  have htrace : WordTrace (prefixWord ++ tailWord_4809285) baseStart_4809285 baseEnd_4809285 := by
    simpa [prefixWord, tailWord_4809285, baseEnd_4809285] using wordTrace_append hprefix tailTrace_4809285
  have hstable : (prefixWord ++ tailWord_4809285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4809285).length < 2 ^ (prefixWord ++ tailWord_4809285).sum := by decide
  have hdescent : baseEnd_4809285 < baseStart_4809285 := by decide
  rcases family_descends (prefixWord ++ tailWord_4809285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4809321 : List Nat := [1, 2, 1, 1, 1, 4, 1, 1, 6, 5]
def baseStart_4809321 : Nat := 118140960795 + 4809321 * 2 ^ 59
def prefixEnd_4809321 : Nat := 4983230072969 + 3 ^ 40 * 4809321 * 2
def baseEnd_4809321 : Nat := 823164431587294414389947

theorem tailTrace_4809321 : CollatzResearch.WordTrace tailWord_4809321 prefixEnd_4809321 823164431587294414389947 := by
  unfold tailWord_4809321
  simp only [CollatzResearch.WordTrace]
  refine ⟨175410347409658858479571817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116940231606439238986381211 175410347409658858479571817)
  ·
    refine ⟨131557760557244143859678863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 175410347409658858479571817 131557760557244143859678863)
    ·
      refine ⟨197336640835866215789518295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131557760557244143859678863 197336640835866215789518295)
      ·
        refine ⟨296004961253799323684277443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 197336640835866215789518295 296004961253799323684277443)
        ·
          refine ⟨444007441880698985526416165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 296004961253799323684277443 444007441880698985526416165)
          ·
            refine ⟨83251395352631059786203031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 444007441880698985526416165 83251395352631059786203031)
            ·
              refine ⟨124877093028946589679304547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83251395352631059786203031 124877093028946589679304547)
              ·
                refine ⟨187315639543419884518956821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 124877093028946589679304547 187315639543419884518956821)
                ·
                  refine ⟨8780420603597807086826101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 187315639543419884518956821 8780420603597807086826101)
                  ·
                    refine ⟨823164431587294414389947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8780420603597807086826101 823164431587294414389947)
                    ·
                      rfl

theorem cell23_4809321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 1, 6, 5].length) (baseStart_4809321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4809321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4809321 prefixEnd_4809321 := by exact prefixLift 4809321
  have htrace : WordTrace (prefixWord ++ tailWord_4809321) baseStart_4809321 baseEnd_4809321 := by
    simpa [prefixWord, tailWord_4809321, baseEnd_4809321] using wordTrace_append hprefix tailTrace_4809321
  have hstable : (prefixWord ++ tailWord_4809321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4809321).length < 2 ^ (prefixWord ++ tailWord_4809321).sum := by decide
  have hdescent : baseEnd_4809321 < baseStart_4809321 := by decide
  rcases family_descends (prefixWord ++ tailWord_4809321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4809348 : List Nat := [2, 3, 2, 1, 3, 1, 1, 2, 1, 2, 5]
def baseStart_4809348 : Nat := 118140960795 + 4809348 * 2 ^ 59
def prefixEnd_4809348 : Nat := 4983230072969 + 3 ^ 40 * 4809348 * 2
def baseEnd_4809348 : Nat := 2469507158739554637532217

theorem tailTrace_4809348 : CollatzResearch.WordTrace tailWord_4809348 prefixEnd_4809348 2469507158739554637532217 := by
  unfold tailWord_4809348
  simp only [CollatzResearch.WordTrace]
  refine ⟨87705666090280521045402349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116940888120374028060536465 87705666090280521045402349)
  ·
    refine ⟨32889624783855195392025881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 87705666090280521045402349 32889624783855195392025881)
    ·
      refine ⟨24667218587891396544019411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32889624783855195392025881 24667218587891396544019411)
      ·
        refine ⟨37000827881837094816029117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24667218587891396544019411 37000827881837094816029117)
        ·
          refine ⟨13875310455688910556010919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37000827881837094816029117 13875310455688910556010919)
          ·
            refine ⟨20812965683533365834016379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13875310455688910556010919 20812965683533365834016379)
            ·
              refine ⟨31219448525300048751024569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20812965683533365834016379 31219448525300048751024569)
              ·
                refine ⟨23414586393975036563268427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31219448525300048751024569 23414586393975036563268427)
                ·
                  refine ⟨35121879590962554844902641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23414586393975036563268427 35121879590962554844902641)
                  ·
                    refine ⟨26341409693221916133676981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 35121879590962554844902641 26341409693221916133676981)
                    ·
                      refine ⟨2469507158739554637532217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26341409693221916133676981 2469507158739554637532217)
                      ·
                        rfl

theorem cell23_4809348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 1, 2, 1, 2, 5].length) (baseStart_4809348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4809348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4809348 prefixEnd_4809348 := by exact prefixLift 4809348
  have htrace : WordTrace (prefixWord ++ tailWord_4809348) baseStart_4809348 baseEnd_4809348 := by
    simpa [prefixWord, tailWord_4809348, baseEnd_4809348] using wordTrace_append hprefix tailTrace_4809348
  have hstable : (prefixWord ++ tailWord_4809348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4809348).length < 2 ^ (prefixWord ++ tailWord_4809348).sum := by decide
  have hdescent : baseEnd_4809348 < baseStart_4809348 := by decide
  rcases family_descends (prefixWord ++ tailWord_4809348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4809371 : List Nat := [1, 1, 1, 1, 1, 1, 2, 2, 3, 6, 4]
def baseStart_4809371 : Nat := 118140960795 + 4809371 * 2 ^ 59
def prefixEnd_4809371 : Nat := 4983230072969 + 3 ^ 40 * 4809371 * 2
def baseEnd_4809371 : Nat := 2469518968794608047544611

theorem tailTrace_4809371 : CollatzResearch.WordTrace tailWord_4809371 prefixEnd_4809371 2469518968794608047544611 := by
  unfold tailWord_4809371
  simp only [CollatzResearch.WordTrace]
  refine ⟨175412171059477717018891967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116941447372985144679261311 175412171059477717018891967)
  ·
    refine ⟨263118256589216575528337951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175412171059477717018891967 263118256589216575528337951)
    ·
      refine ⟨394677384883824863292506927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 263118256589216575528337951 394677384883824863292506927)
      ·
        refine ⟨592016077325737294938760391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 394677384883824863292506927 592016077325737294938760391)
        ·
          refine ⟨888024115988605942408140587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 592016077325737294938760391 888024115988605942408140587)
          ·
            refine ⟨1332036173982908913612210881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 888024115988605942408140587 1332036173982908913612210881)
            ·
              refine ⟨999027130487181685209158161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1332036173982908913612210881 999027130487181685209158161)
              ·
                refine ⟨749270347865386263906868621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 999027130487181685209158161 749270347865386263906868621)
                ·
                  refine ⟨280976380449519848965075733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 749270347865386263906868621 280976380449519848965075733)
                  ·
                    refine ⟨13170767833571242920237925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 280976380449519848965075733 13170767833571242920237925)
                    ·
                      refine ⟨2469518968794608047544611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13170767833571242920237925 2469518968794608047544611)
                      ·
                        rfl

theorem cell23_4809371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 6, 4].length) (baseStart_4809371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4809371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4809371 prefixEnd_4809371 := by exact prefixLift 4809371
  have htrace : WordTrace (prefixWord ++ tailWord_4809371) baseStart_4809371 baseEnd_4809371 := by
    simpa [prefixWord, tailWord_4809371, baseEnd_4809371] using wordTrace_append hprefix tailTrace_4809371
  have hstable : (prefixWord ++ tailWord_4809371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4809371).length < 2 ^ (prefixWord ++ tailWord_4809371).sum := by decide
  have hdescent : baseEnd_4809371 < baseStart_4809371 := by decide
  rcases family_descends (prefixWord ++ tailWord_4809371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4809381 : List Nat := [1, 3, 1, 2, 1, 2, 1, 2, 10]
def baseStart_4809381 : Nat := 118140960795 + 4809381 * 2 ^ 59
def prefixEnd_4809381 : Nat := 4983230072969 + 3 ^ 40 * 4809381 * 2
def baseEnd_4809381 : Nat := 274391567066794778713285

theorem tailTrace_4809381 : CollatzResearch.WordTrace tailWord_4809381 prefixEnd_4809381 274391567066794778713285 := by
  unfold tailWord_4809381
  simp only [CollatzResearch.WordTrace]
  refine ⟨175412535789441488726755997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116941690526294325817837331 175412535789441488726755997)
  ·
    refine ⟨65779700921040558272533499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 175412535789441488726755997 65779700921040558272533499)
    ·
      refine ⟨98669551381560837408800249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65779700921040558272533499 98669551381560837408800249)
      ·
        refine ⟨74002163536170628056600187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 98669551381560837408800249 74002163536170628056600187)
        ·
          refine ⟨111003245304255942084900281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74002163536170628056600187 111003245304255942084900281)
          ·
            refine ⟨83252433978191956563675211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 111003245304255942084900281 83252433978191956563675211)
            ·
              refine ⟨124878650967287934845512817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83252433978191956563675211 124878650967287934845512817)
              ·
                refine ⟨93658988225465951134134613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 124878650967287934845512817 93658988225465951134134613)
                ·
                  refine ⟨274391567066794778713285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 93658988225465951134134613 274391567066794778713285)
                  ·
                    rfl

theorem cell23_4809381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 2, 10].length) (baseStart_4809381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4809381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4809381 prefixEnd_4809381 := by exact prefixLift 4809381
  have htrace : WordTrace (prefixWord ++ tailWord_4809381) baseStart_4809381 baseEnd_4809381 := by
    simpa [prefixWord, tailWord_4809381, baseEnd_4809381] using wordTrace_append hprefix tailTrace_4809381
  have hstable : (prefixWord ++ tailWord_4809381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4809381).length < 2 ^ (prefixWord ++ tailWord_4809381).sum := by decide
  have hdescent : baseEnd_4809381 < baseStart_4809381 := by decide
  rcases family_descends (prefixWord ++ tailWord_4809381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4809395 : List Nat := [1, 1, 1, 2, 3, 4, 3, 1, 2, 2, 3]
def baseStart_4809395 : Nat := 118140960795 + 4809395 * 2 ^ 59
def prefixEnd_4809395 : Nat := 4983230072969 + 3 ^ 40 * 4809395 * 2
def baseEnd_4809395 : Nat := 2469531292330315953644501

theorem tailTrace_4809395 : CollatzResearch.WordTrace tailWord_4809395 prefixEnd_4809395 2469531292330315953644501 := by
  unfold tailWord_4809395
  simp only [CollatzResearch.WordTrace]
  refine ⟨175413046411390769117765639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116942030940927179411843759 175413046411390769117765639)
  ·
    refine ⟨263119569617086153676648459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175413046411390769117765639 263119569617086153676648459)
    ·
      refine ⟨394679354425629230514972689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 263119569617086153676648459 394679354425629230514972689)
      ·
        refine ⟨296009515819221922886229517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 394679354425629230514972689 296009515819221922886229517)
        ·
          refine ⟨111003568432208221082336069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 296009515819221922886229517 111003568432208221082336069)
          ·
            refine ⟨20813169081039041452938013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 111003568432208221082336069 20813169081039041452938013)
            ·
              refine ⟨7804938405389640544851755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20813169081039041452938013 7804938405389640544851755)
              ·
                refine ⟨11707407608084460817277633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7804938405389640544851755 11707407608084460817277633)
                ·
                  refine ⟨8780555706063345612958225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11707407608084460817277633 8780555706063345612958225)
                  ·
                    refine ⟨6585416779547509209718669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8780555706063345612958225 6585416779547509209718669)
                    ·
                      refine ⟨2469531292330315953644501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6585416779547509209718669 2469531292330315953644501)
                      ·
                        rfl

theorem cell23_4809395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 3, 1, 2, 2, 3].length) (baseStart_4809395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4809395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4809395 prefixEnd_4809395 := by exact prefixLift 4809395
  have htrace : WordTrace (prefixWord ++ tailWord_4809395) baseStart_4809395 baseEnd_4809395 := by
    simpa [prefixWord, tailWord_4809395, baseEnd_4809395] using wordTrace_append hprefix tailTrace_4809395
  have hstable : (prefixWord ++ tailWord_4809395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4809395).length < 2 ^ (prefixWord ++ tailWord_4809395).sum := by decide
  have hdescent : baseEnd_4809395 < baseStart_4809395 := by decide
  rcases family_descends (prefixWord ++ tailWord_4809395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4809402 : List Nat := [3, 1, 1, 1, 2, 3, 4, 3, 1, 4]
def baseStart_4809402 : Nat := 118140960795 + 4809402 * 2 ^ 59
def prefixEnd_4809402 : Nat := 4983230072969 + 3 ^ 40 * 4809402 * 2
def baseEnd_4809402 : Nat := 823178295564965808752323

theorem tailTrace_4809402 : CollatzResearch.WordTrace tailWord_4809402 prefixEnd_4809402 823178295564965808752323 := by
  unfold tailWord_4809402
  simp only [CollatzResearch.WordTrace]
  refine ⟨43853325430591352328317615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 116942201148243606208846973 43853325430591352328317615)
  ·
    refine ⟨65779988145887028492476423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43853325430591352328317615 65779988145887028492476423)
    ·
      refine ⟨98669982218830542738714635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65779988145887028492476423 98669982218830542738714635)
      ·
        refine ⟨148004973328245814108071953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98669982218830542738714635 148004973328245814108071953)
        ·
          refine ⟨111003729996184360581053965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 148004973328245814108071953 111003729996184360581053965)
          ·
            refine ⟨41626398748569135217895237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 111003729996184360581053965 41626398748569135217895237)
            ·
              refine ⟨7804949765356712853355357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 41626398748569135217895237 7804949765356712853355357)
              ·
                refine ⟨2926856162008767320008259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7804949765356712853355357 2926856162008767320008259)
                ·
                  refine ⟨4390284243013150980012389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2926856162008767320008259 4390284243013150980012389)
                  ·
                    refine ⟨823178295564965808752323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4390284243013150980012389 823178295564965808752323)
                    ·
                      rfl

theorem cell23_4809402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 4, 3, 1, 4].length) (baseStart_4809402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4809402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4809402 prefixEnd_4809402 := by exact prefixLift 4809402
  have htrace : WordTrace (prefixWord ++ tailWord_4809402) baseStart_4809402 baseEnd_4809402 := by
    simpa [prefixWord, tailWord_4809402, baseEnd_4809402] using wordTrace_append hprefix tailTrace_4809402
  have hstable : (prefixWord ++ tailWord_4809402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4809402).length < 2 ^ (prefixWord ++ tailWord_4809402).sum := by decide
  have hdescent : baseEnd_4809402 < baseStart_4809402 := by decide
  rcases family_descends (prefixWord ++ tailWord_4809402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4809418 : List Nat := [3, 1, 2, 1, 4, 1, 1, 1, 1, 2, 6]
def baseStart_4809418 : Nat := 118140960795 + 4809418 * 2 ^ 59
def prefixEnd_4809418 : Nat := 4983230072969 + 3 ^ 40 * 4809418 * 2
def baseEnd_4809418 : Nat := 2469543102385369363656895

theorem tailTrace_4809418 : CollatzResearch.WordTrace tailWord_4809418 prefixEnd_4809418 2469543102385369363656895 := by
  unfold tailWord_4809418
  simp only [CollatzResearch.WordTrace]
  refine ⟨43853471322576861011463227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 116942590193538296030568605 43853471322576861011463227)
  ·
    refine ⟨65780206983865291517194841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43853471322576861011463227 65780206983865291517194841)
    ·
      refine ⟨49335155237898968637896131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65780206983865291517194841 49335155237898968637896131)
      ·
        refine ⟨74002732856848452956844197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49335155237898968637896131 74002732856848452956844197)
        ·
          refine ⟨13875512410659084929408287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 74002732856848452956844197 13875512410659084929408287)
          ·
            refine ⟨20813268615988627394112431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13875512410659084929408287 20813268615988627394112431)
            ·
              refine ⟨31219902923982941091168647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20813268615988627394112431 31219902923982941091168647)
              ·
                refine ⟨46829854385974411636752971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31219902923982941091168647 46829854385974411636752971)
                ·
                  refine ⟨70244781578961617455129457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 46829854385974411636752971 70244781578961617455129457)
                  ·
                    refine ⟨52683586184221213091347093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 70244781578961617455129457 52683586184221213091347093)
                    ·
                      refine ⟨2469543102385369363656895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 52683586184221213091347093 2469543102385369363656895)
                      ·
                        rfl

theorem cell23_4809418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 1, 1, 1, 2, 6].length) (baseStart_4809418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4809418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4809418 prefixEnd_4809418 := by exact prefixLift 4809418
  have htrace : WordTrace (prefixWord ++ tailWord_4809418) baseStart_4809418 baseEnd_4809418 := by
    simpa [prefixWord, tailWord_4809418, baseEnd_4809418] using wordTrace_append hprefix tailTrace_4809418
  have hstable : (prefixWord ++ tailWord_4809418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4809418).length < 2 ^ (prefixWord ++ tailWord_4809418).sum := by decide
  have hdescent : baseEnd_4809418 < baseStart_4809418 := by decide
  rcases family_descends (prefixWord ++ tailWord_4809418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
