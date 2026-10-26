import V185TrunkScan22Chunk422

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_3769853 : List Nat := [1, 4, 1, 1, 1, 5, 1, 2, 1, 5]
def baseStart_3769853 : Nat := 118140960795 + 3769853 * 2 ^ 59
def prefixEnd_3769853 : Nat := 4983230072969 + 3 ^ 40 * 3769853 * 2
def baseEnd_3769853 : Nat := 1290497723862762777666845

theorem tailTrace_3769853 : CollatzResearch.WordTrace tailWord_3769853 prefixEnd_3769853 1290497723862762777666845 := by
  unfold tailWord_3769853
  simp only [CollatzResearch.WordTrace]
  refine ⟨137497834811473895478818213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91665223207649263652545475 137497834811473895478818213)
  ·
    refine ⟨25780844027151355402278415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 137497834811473895478818213 25780844027151355402278415)
    ·
      refine ⟨38671266040727033103417623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25780844027151355402278415 38671266040727033103417623)
      ·
        refine ⟨58006899061090549655126435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38671266040727033103417623 58006899061090549655126435)
        ·
          refine ⟨87010348591635824482689653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58006899061090549655126435 87010348591635824482689653)
          ·
            refine ⟨8157220180465858545252155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 87010348591635824482689653 8157220180465858545252155)
            ·
              refine ⟨12235830270698787817878233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8157220180465858545252155 12235830270698787817878233)
              ·
                refine ⟨9176872703024090863408675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12235830270698787817878233 9176872703024090863408675)
                ·
                  refine ⟨13765309054536136295113013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9176872703024090863408675 13765309054536136295113013)
                  ·
                    refine ⟨1290497723862762777666845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13765309054536136295113013 1290497723862762777666845)
                    ·
                      rfl

theorem cell22_3769853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 1, 2, 1, 5].length) (baseStart_3769853 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3769853 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3769853 prefixEnd_3769853 := by exact prefixLift 3769853
  have htrace : WordTrace (prefixWord ++ tailWord_3769853) baseStart_3769853 baseEnd_3769853 := by
    simpa [prefixWord, tailWord_3769853, baseEnd_3769853] using wordTrace_append hprefix tailTrace_3769853
  have hstable : (prefixWord ++ tailWord_3769853).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3769853).length < 2 ^ (prefixWord ++ tailWord_3769853).sum := by decide
  have hdescent : baseEnd_3769853 < baseStart_3769853 := by decide
  rcases family_descends (prefixWord ++ tailWord_3769853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3769857 : List Nat := [1, 2, 4, 1, 4, 1, 3, 1, 1, 4]
def baseStart_3769857 : Nat := 118140960795 + 3769857 * 2 ^ 59
def prefixEnd_3769857 : Nat := 4983230072969 + 3 ^ 40 * 3769857 * 2
def baseEnd_3769857 : Nat := 1290499093144508100566833

theorem tailTrace_3769857 : CollatzResearch.WordTrace tailWord_3769857 prefixEnd_3769857 1290499093144508100566833 := by
  unfold tailWord_3769857
  simp only [CollatzResearch.WordTrace]
  refine ⟨137497980703459404161963825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91665320468972936107975883 137497980703459404161963825)
  ·
    refine ⟨103123485527594553121472869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137497980703459404161963825 103123485527594553121472869)
    ·
      refine ⟨19335653536423978710276163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 103123485527594553121472869 19335653536423978710276163)
      ·
        refine ⟨29003480304635968065414245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19335653536423978710276163 29003480304635968065414245)
        ·
          refine ⟨5438152557119244012265171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29003480304635968065414245 5438152557119244012265171)
          ·
            refine ⟨8157228835678866018397757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5438152557119244012265171 8157228835678866018397757)
            ·
              refine ⟨3058960813379574756899159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8157228835678866018397757 3058960813379574756899159)
              ·
                refine ⟨4588441220069362135348739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3058960813379574756899159 4588441220069362135348739)
                ·
                  refine ⟨6882661830104043203023109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4588441220069362135348739 6882661830104043203023109)
                  ·
                    refine ⟨1290499093144508100566833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6882661830104043203023109 1290499093144508100566833)
                    ·
                      rfl

theorem cell22_3769857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 3, 1, 1, 4].length) (baseStart_3769857 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3769857 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3769857 prefixEnd_3769857 := by exact prefixLift 3769857
  have htrace : WordTrace (prefixWord ++ tailWord_3769857) baseStart_3769857 baseEnd_3769857 := by
    simpa [prefixWord, tailWord_3769857, baseEnd_3769857] using wordTrace_append hprefix tailTrace_3769857
  have hstable : (prefixWord ++ tailWord_3769857).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3769857).length < 2 ^ (prefixWord ++ tailWord_3769857).sum := by decide
  have hdescent : baseEnd_3769857 < baseStart_3769857 := by decide
  rcases family_descends (prefixWord ++ tailWord_3769857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3769866 : List Nat := [3, 1, 2, 2, 2, 12]
def baseStart_3769866 : Nat := 118140960795 + 3769866 * 2 ^ 59
def prefixEnd_3769866 : Nat := 4983230072969 + 3 ^ 40 * 3769866 * 2
def baseEnd_3769866 : Nat := 15932125605289321939405

theorem tailTrace_3769866 : CollatzResearch.WordTrace tailWord_3769866 prefixEnd_3769866 15932125605289321939405 := by
  unfold tailWord_3769866
  simp only [CollatzResearch.WordTrace]
  refine ⟨34374577240106699674760363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91665539306951199132694301 34374577240106699674760363)
  ·
    refine ⟨51561865860160049512140545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34374577240106699674760363 51561865860160049512140545)
    ·
      refine ⟨38671399395120037134105409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51561865860160049512140545 38671399395120037134105409)
      ·
        refine ⟨29003549546340027850579057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38671399395120037134105409 29003549546340027850579057)
        ·
          refine ⟨21752662159755020887934293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29003549546340027850579057 21752662159755020887934293)
          ·
            refine ⟨15932125605289321939405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 21752662159755020887934293 15932125605289321939405)
            ·
              rfl

theorem cell22_3769866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 12].length) (baseStart_3769866 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3769866 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3769866 prefixEnd_3769866 := by exact prefixLift 3769866
  have htrace : WordTrace (prefixWord ++ tailWord_3769866) baseStart_3769866 baseEnd_3769866 := by
    simpa [prefixWord, tailWord_3769866, baseEnd_3769866] using wordTrace_append hprefix tailTrace_3769866
  have hstable : (prefixWord ++ tailWord_3769866).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3769866).length < 2 ^ (prefixWord ++ tailWord_3769866).sum := by decide
  have hdescent : baseEnd_3769866 < baseStart_3769866 := by decide
  rcases family_descends (prefixWord ++ tailWord_3769866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3769902 : List Nat := [4, 1, 3, 1, 2, 3, 1, 1, 2, 4]
def baseStart_3769902 : Nat := 118140960795 + 3769902 * 2 ^ 59
def prefixEnd_3769902 : Nat := 4983230072969 + 3 ^ 40 * 3769902 * 2
def baseEnd_3769902 : Nat := 1290514497564142983191695

theorem tailTrace_3769902 : CollatzResearch.WordTrace tailWord_3769902 prefixEnd_3769902 1290514497564142983191695 := by
  unfold tailWord_3769902
  simp only [CollatzResearch.WordTrace]
  refine ⟨17187452748537047105918995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 91666414658864251231567973 17187452748537047105918995)
  ·
    refine ⟨25781179122805570658878493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17187452748537047105918995 25781179122805570658878493)
    ·
      refine ⟨9667942171052088997079435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25781179122805570658878493 9667942171052088997079435)
      ·
        refine ⟨14501913256578133495619153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9667942171052088997079435 14501913256578133495619153)
        ·
          refine ⟨10876434942433600121714365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14501913256578133495619153 10876434942433600121714365)
          ·
            refine ⟨4078663103412600045642887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10876434942433600121714365 4078663103412600045642887)
            ·
              refine ⟨6117994655118900068464331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4078663103412600045642887 6117994655118900068464331)
              ·
                refine ⟨9176991982678350102696497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6117994655118900068464331 9176991982678350102696497)
                ·
                  refine ⟨6882743987008762577022373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9176991982678350102696497 6882743987008762577022373)
                  ·
                    refine ⟨1290514497564142983191695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6882743987008762577022373 1290514497564142983191695)
                    ·
                      rfl

theorem cell22_3769902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 3, 1, 1, 2, 4].length) (baseStart_3769902 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3769902 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3769902 prefixEnd_3769902 := by exact prefixLift 3769902
  have htrace : WordTrace (prefixWord ++ tailWord_3769902) baseStart_3769902 baseEnd_3769902 := by
    simpa [prefixWord, tailWord_3769902, baseEnd_3769902] using wordTrace_append hprefix tailTrace_3769902
  have hstable : (prefixWord ++ tailWord_3769902).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3769902).length < 2 ^ (prefixWord ++ tailWord_3769902).sum := by decide
  have hdescent : baseEnd_3769902 < baseStart_3769902 := by decide
  rcases family_descends (prefixWord ++ tailWord_3769902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3769932 : List Nat := [2, 2, 1, 3, 1, 3, 2, 4, 1, 3]
def baseStart_3769932 : Nat := 118140960795 + 3769932 * 2 ^ 59
def prefixEnd_3769932 : Nat := 4983230072969 + 3 ^ 40 * 3769932 * 2
def baseEnd_3769932 : Nat := 1290524767177232904941603

theorem tailTrace_3769932 : CollatzResearch.WordTrace tailWord_3769932 prefixEnd_3769932 1290524767177232904941603 := by
  unfold tailWord_3769932
  simp only [CollatzResearch.WordTrace]
  refine ⟨68750358089093845985472025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91667144118791794647296033 68750358089093845985472025)
  ·
    refine ⟨51562768566820384489104019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68750358089093845985472025 51562768566820384489104019)
    ·
      refine ⟨77344152850230576733656029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51562768566820384489104019 77344152850230576733656029)
      ·
        refine ⟨29004057318836466275121011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77344152850230576733656029 29004057318836466275121011)
        ·
          refine ⟨43506085978254699412681517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29004057318836466275121011 43506085978254699412681517)
          ·
            refine ⟨16314782241845512279755569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43506085978254699412681517 16314782241845512279755569)
            ·
              refine ⟨12236086681384134209816677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16314782241845512279755569 12236086681384134209816677)
              ·
                refine ⟨2294266252759525164340627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12236086681384134209816677 2294266252759525164340627)
                ·
                  refine ⟨3441399379139287746510941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2294266252759525164340627 3441399379139287746510941)
                  ·
                    refine ⟨1290524767177232904941603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3441399379139287746510941 1290524767177232904941603)
                    ·
                      rfl

theorem cell22_3769932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 2, 4, 1, 3].length) (baseStart_3769932 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3769932 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3769932 prefixEnd_3769932 := by exact prefixLift 3769932
  have htrace : WordTrace (prefixWord ++ tailWord_3769932) baseStart_3769932 baseEnd_3769932 := by
    simpa [prefixWord, tailWord_3769932, baseEnd_3769932] using wordTrace_append hprefix tailTrace_3769932
  have hstable : (prefixWord ++ tailWord_3769932).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3769932).length < 2 ^ (prefixWord ++ tailWord_3769932).sum := by decide
  have hdescent : baseEnd_3769932 < baseStart_3769932 := by decide
  rcases family_descends (prefixWord ++ tailWord_3769932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3769943 : List Nat := [1, 1, 3, 2, 2, 3, 2, 1, 2, 5]
def baseStart_3769943 : Nat := 118140960795 + 3769943 * 2 ^ 59
def prefixEnd_3769943 : Nat := 4983230072969 + 3 ^ 40 * 3769943 * 2
def baseEnd_3769943 : Nat := 1290528532702032542916569

theorem tailTrace_3769943 : CollatzResearch.WordTrace tailWord_3769943 prefixEnd_3769943 1290528532702032542916569 := by
  unfold tailWord_3769943
  simp only [CollatzResearch.WordTrace]
  refine ⟨137501117381147840849594483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91667411587431893899729655 137501117381147840849594483)
  ·
    refine ⟨206251676071721761274391725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137501117381147840849594483 206251676071721761274391725)
    ·
      refine ⟨77344378526895660477896897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 206251676071721761274391725 77344378526895660477896897)
      ·
        refine ⟨58008283895171745358422673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77344378526895660477896897 58008283895171745358422673)
        ·
          refine ⟨43506212921378809018817005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58008283895171745358422673 43506212921378809018817005)
          ·
            refine ⟨16314829845517053382056377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43506212921378809018817005 16314829845517053382056377)
            ·
              refine ⟨12236122384137790036542283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16314829845517053382056377 12236122384137790036542283)
              ·
                refine ⟨18354183576206685054813425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12236122384137790036542283 18354183576206685054813425)
                ·
                  refine ⟨13765637682155013791110069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18354183576206685054813425 13765637682155013791110069)
                  ·
                    refine ⟨1290528532702032542916569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13765637682155013791110069 1290528532702032542916569)
                    ·
                      rfl

theorem cell22_3769943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 2, 1, 2, 5].length) (baseStart_3769943 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3769943 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3769943 prefixEnd_3769943 := by exact prefixLift 3769943
  have htrace : WordTrace (prefixWord ++ tailWord_3769943) baseStart_3769943 baseEnd_3769943 := by
    simpa [prefixWord, tailWord_3769943, baseEnd_3769943] using wordTrace_append hprefix tailTrace_3769943
  have hstable : (prefixWord ++ tailWord_3769943).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3769943).length < 2 ^ (prefixWord ++ tailWord_3769943).sum := by decide
  have hdescent : baseEnd_3769943 < baseStart_3769943 := by decide
  rcases family_descends (prefixWord ++ tailWord_3769943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3769966 : List Nat := [4, 1, 2, 2, 3, 2, 1, 3, 1, 3]
def baseStart_3769966 : Nat := 118140960795 + 3769966 * 2 ^ 59
def prefixEnd_3769966 : Nat := 4983230072969 + 3 ^ 40 * 3769966 * 2
def baseEnd_3769966 : Nat := 1290536406072068149591499

theorem tailTrace_3769966 : CollatzResearch.WordTrace tailWord_3769966 prefixEnd_3769966 1290536406072068149591499 := by
  unfold tailWord_3769966
  simp only [CollatzResearch.WordTrace]
  refine ⟨17187744532508064472210219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 91667970840043010518454501 17187744532508064472210219)
  ·
    refine ⟨25781616798762096708315329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17187744532508064472210219 25781616798762096708315329)
    ·
      refine ⟨19336212599071572531236497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25781616798762096708315329 19336212599071572531236497)
      ·
        refine ⟨14502159449303679398427373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19336212599071572531236497 14502159449303679398427373)
        ·
          refine ⟨5438309793488879774410265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14502159449303679398427373 5438309793488879774410265)
          ·
            refine ⟨4078732345116659830807699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5438309793488879774410265 4078732345116659830807699)
            ·
              refine ⟨6118098517674989746211549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4078732345116659830807699 6118098517674989746211549)
              ·
                refine ⟨2294286944128121154829331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6118098517674989746211549 2294286944128121154829331)
                ·
                  refine ⟨3441430416192181732243997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2294286944128121154829331 3441430416192181732243997)
                  ·
                    refine ⟨1290536406072068149591499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3441430416192181732243997 1290536406072068149591499)
                    ·
                      rfl

theorem cell22_3769966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 2, 1, 3, 1, 3].length) (baseStart_3769966 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3769966 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3769966 prefixEnd_3769966 := by exact prefixLift 3769966
  have htrace : WordTrace (prefixWord ++ tailWord_3769966) baseStart_3769966 baseEnd_3769966 := by
    simpa [prefixWord, tailWord_3769966, baseEnd_3769966] using wordTrace_append hprefix tailTrace_3769966
  have hstable : (prefixWord ++ tailWord_3769966).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3769966).length < 2 ^ (prefixWord ++ tailWord_3769966).sum := by decide
  have hdescent : baseEnd_3769966 < baseStart_3769966 := by decide
  rcases family_descends (prefixWord ++ tailWord_3769966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3770020 : List Nat := [2, 3, 1, 2, 2, 2, 1, 3, 2, 4]
def baseStart_3770020 : Nat := 118140960795 + 3770020 * 2 ^ 59
def prefixEnd_3770020 : Nat := 4983230072969 + 3 ^ 40 * 3770020 * 2
def baseEnd_3770020 : Nat := 1290554891375630008741333

theorem tailTrace_3770020 : CollatzResearch.WordTrace tailWord_3770020 prefixEnd_3770020 1290554891375630008741333 := by
  unfold tailWord_3770020
  simp only [CollatzResearch.WordTrace]
  refine ⟨68751962900934441500073757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91669283867912588666765009 68751962900934441500073757)
  ·
    refine ⟨25781986087850415562527659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68751962900934441500073757 25781986087850415562527659)
    ·
      refine ⟨38672979131775623343791489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25781986087850415562527659 38672979131775623343791489)
      ·
        refine ⟨29004734348831717507843617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38672979131775623343791489 29004734348831717507843617)
        ·
          refine ⟨21753550761623788130882713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29004734348831717507843617 21753550761623788130882713)
          ·
            refine ⟨16315163071217841098162035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21753550761623788130882713 16315163071217841098162035)
            ·
              refine ⟨24472744606826761647243053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16315163071217841098162035 24472744606826761647243053)
              ·
                refine ⟨9177279227560035617716145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24472744606826761647243053 9177279227560035617716145)
                ·
                  refine ⟨6882959420670026713287109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9177279227560035617716145 6882959420670026713287109)
                  ·
                    refine ⟨1290554891375630008741333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6882959420670026713287109 1290554891375630008741333)
                    ·
                      rfl

theorem cell22_3770020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 1, 3, 2, 4].length) (baseStart_3770020 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3770020 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3770020 prefixEnd_3770020 := by exact prefixLift 3770020
  have htrace : WordTrace (prefixWord ++ tailWord_3770020) baseStart_3770020 baseEnd_3770020 := by
    simpa [prefixWord, tailWord_3770020, baseEnd_3770020] using wordTrace_append hprefix tailTrace_3770020
  have hstable : (prefixWord ++ tailWord_3770020).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3770020).length < 2 ^ (prefixWord ++ tailWord_3770020).sum := by decide
  have hdescent : baseEnd_3770020 < baseStart_3770020 := by decide
  rcases family_descends (prefixWord ++ tailWord_3770020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3770048 : List Nat := [2, 1, 1, 2, 4, 1, 1, 1, 1, 8]
def baseStart_3770048 : Nat := 118140960795 + 3770048 * 2 ^ 59
def prefixEnd_3770048 : Nat := 4983230072969 + 3 ^ 40 * 3770048 * 2
def baseEnd_3770048 : Nat := 1290564476347847269041247

theorem tailTrace_3770048 : CollatzResearch.WordTrace tailWord_3770048 prefixEnd_3770048 1290564476347847269041247 := by
  unfold tailWord_3770048
  simp only [CollatzResearch.WordTrace]
  refine ⟨68752473522883721891083399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91669964697178295854777865 68752473522883721891083399)
  ·
    refine ⟨103128710284325582836625099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68752473522883721891083399 103128710284325582836625099)
    ·
      refine ⟨154693065426488374254937649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103128710284325582836625099 154693065426488374254937649)
      ·
        refine ⟨116019799069866280691203237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154693065426488374254937649 116019799069866280691203237)
        ·
          refine ⟨21753712325599927629600607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 116019799069866280691203237 21753712325599927629600607)
          ·
            refine ⟨32630568488399891444400911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21753712325599927629600607 32630568488399891444400911)
            ·
              refine ⟨48945852732599837166601367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32630568488399891444400911 48945852732599837166601367)
              ·
                refine ⟨73418779098899755749902051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48945852732599837166601367 73418779098899755749902051)
                ·
                  refine ⟨110128168648349633624853077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73418779098899755749902051 110128168648349633624853077)
                  ·
                    refine ⟨1290564476347847269041247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 110128168648349633624853077 1290564476347847269041247)
                    ·
                      rfl

theorem cell22_3770048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 1, 1, 8].length) (baseStart_3770048 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3770048 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3770048 prefixEnd_3770048 := by exact prefixLift 3770048
  have htrace : WordTrace (prefixWord ++ tailWord_3770048) baseStart_3770048 baseEnd_3770048 := by
    simpa [prefixWord, tailWord_3770048, baseEnd_3770048] using wordTrace_append hprefix tailTrace_3770048
  have hstable : (prefixWord ++ tailWord_3770048).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3770048).length < 2 ^ (prefixWord ++ tailWord_3770048).sum := by decide
  have hdescent : baseEnd_3770048 < baseStart_3770048 := by decide
  rcases family_descends (prefixWord ++ tailWord_3770048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3770084 : List Nat := [2, 3, 1, 1, 1, 3, 4, 3, 1, 3]
def baseStart_3770084 : Nat := 118140960795 + 3770084 * 2 ^ 59
def prefixEnd_3770084 : Nat := 4983230072969 + 3 ^ 40 * 3770084 * 2
def baseEnd_3770084 : Nat := 1290576799883555175141137

theorem tailTrace_3770084 : CollatzResearch.WordTrace tailWord_3770084 prefixEnd_3770084 1290576799883555175141137 := by
  unfold tailWord_3770084
  simp only [CollatzResearch.WordTrace]
  refine ⟨68753130036818510965238653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91670840049091347953651537 68753130036818510965238653)
  ·
    refine ⟨25782423763806941611964495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68753130036818510965238653 25782423763806941611964495)
    ·
      refine ⟨38673635645710412417946743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25782423763806941611964495 38673635645710412417946743)
      ·
        refine ⟨58010453468565618626920115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38673635645710412417946743 58010453468565618626920115)
        ·
          refine ⟨87015680202848427940380173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58010453468565618626920115 87015680202848427940380173)
          ·
            refine ⟨32630880076068160477642565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87015680202848427940380173 32630880076068160477642565)
            ·
              refine ⟨6118290014262780089557981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32630880076068160477642565 6118290014262780089557981)
              ·
                refine ⟨2294358755348542533584243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6118290014262780089557981 2294358755348542533584243)
                ·
                  refine ⟨3441538133022813800376365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2294358755348542533584243 3441538133022813800376365)
                  ·
                    refine ⟨1290576799883555175141137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3441538133022813800376365 1290576799883555175141137)
                    ·
                      rfl

theorem cell22_3770084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 4, 3, 1, 3].length) (baseStart_3770084 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3770084 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3770084 prefixEnd_3770084 := by exact prefixLift 3770084
  have htrace : WordTrace (prefixWord ++ tailWord_3770084) baseStart_3770084 baseEnd_3770084 := by
    simpa [prefixWord, tailWord_3770084, baseEnd_3770084] using wordTrace_append hprefix tailTrace_3770084
  have hstable : (prefixWord ++ tailWord_3770084).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3770084).length < 2 ^ (prefixWord ++ tailWord_3770084).sum := by decide
  have hdescent : baseEnd_3770084 < baseStart_3770084 := by decide
  rcases family_descends (prefixWord ++ tailWord_3770084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3770097 : List Nat := [1, 2, 2, 2, 2, 5, 1, 2, 5]
def baseStart_3770097 : Nat := 118140960795 + 3770097 * 2 ^ 59
def prefixEnd_3770097 : Nat := 4983230072969 + 3 ^ 40 * 3770097 * 2
def baseEnd_3770097 : Nat := 430193750016409158188699

theorem tailTrace_3770097 : CollatzResearch.WordTrace tailWord_3770097 prefixEnd_3770097 430193750016409158188699 := by
  unfold tailWord_3770097
  simp only [CollatzResearch.WordTrace]
  refine ⟨137506734222589925150700545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91671156148393283433800363 137506734222589925150700545)
  ·
    refine ⟨103130050666942443863025409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137506734222589925150700545 103130050666942443863025409)
    ·
      refine ⟨77347538000206832897269057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103130050666942443863025409 77347538000206832897269057)
      ·
        refine ⟨58010653500155124672951793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77347538000206832897269057 58010653500155124672951793)
        ·
          refine ⟨43507990125116343504713845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58010653500155124672951793 43507990125116343504713845)
          ·
            refine ⟨4078874074229657203566923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 43507990125116343504713845 4078874074229657203566923)
            ·
              refine ⟨6118311111344485805350385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4078874074229657203566923 6118311111344485805350385)
              ·
                refine ⟨4588733333508364354012789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6118311111344485805350385 4588733333508364354012789)
                ·
                  refine ⟨430193750016409158188699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4588733333508364354012789 430193750016409158188699)
                  ·
                    rfl

theorem cell22_3770097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 5, 1, 2, 5].length) (baseStart_3770097 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3770097 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3770097 prefixEnd_3770097 := by exact prefixLift 3770097
  have htrace : WordTrace (prefixWord ++ tailWord_3770097) baseStart_3770097 baseEnd_3770097 := by
    simpa [prefixWord, tailWord_3770097, baseEnd_3770097] using wordTrace_append hprefix tailTrace_3770097
  have hstable : (prefixWord ++ tailWord_3770097).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3770097).length < 2 ^ (prefixWord ++ tailWord_3770097).sum := by decide
  have hdescent : baseEnd_3770097 < baseStart_3770097 := by decide
  rcases family_descends (prefixWord ++ tailWord_3770097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3770114 : List Nat := [3, 4, 1, 1, 1, 1, 5, 1, 5]
def baseStart_3770114 : Nat := 118140960795 + 3770114 * 2 ^ 59
def prefixEnd_3770114 : Nat := 4983230072969 + 3 ^ 40 * 3770114 * 2
def baseEnd_3770114 : Nat := 430195689832215032297015

theorem tailTrace_3770114 : CollatzResearch.WordTrace tailWord_3770114 prefixEnd_3770114 430195689832215032297015 := by
  unfold tailWord_3770114
  simp only [CollatzResearch.WordTrace]
  refine ⟨34376838565882084263517349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91671569509018891369379597 34376838565882084263517349)
  ·
    refine ⟨6445657231102890799409503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34376838565882084263517349 6445657231102890799409503)
    ·
      refine ⟨9668485846654336199114255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6445657231102890799409503 9668485846654336199114255)
      ·
        refine ⟨14502728769981504298671383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9668485846654336199114255 14502728769981504298671383)
        ·
          refine ⟨21754093154972256448007075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14502728769981504298671383 21754093154972256448007075)
          ·
            refine ⟨32631139732458384672010613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21754093154972256448007075 32631139732458384672010613)
            ·
              refine ⟨3059169349917973563000995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 32631139732458384672010613 3059169349917973563000995)
              ·
                refine ⟨4588754024876960344501493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3059169349917973563000995 4588754024876960344501493)
                ·
                  refine ⟨430195689832215032297015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4588754024876960344501493 430195689832215032297015)
                  ·
                    rfl

theorem cell22_3770114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 5, 1, 5].length) (baseStart_3770114 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3770114 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3770114 prefixEnd_3770114 := by exact prefixLift 3770114
  have htrace : WordTrace (prefixWord ++ tailWord_3770114) baseStart_3770114 baseEnd_3770114 := by
    simpa [prefixWord, tailWord_3770114, baseEnd_3770114] using wordTrace_append hprefix tailTrace_3770114
  have hstable : (prefixWord ++ tailWord_3770114).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3770114).length < 2 ^ (prefixWord ++ tailWord_3770114).sum := by decide
  have hdescent : baseEnd_3770114 < baseStart_3770114 := by decide
  rcases family_descends (prefixWord ++ tailWord_3770114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3770140 : List Nat := [2, 2, 3, 1, 1, 2, 2, 1, 3, 5]
def baseStart_3770140 : Nat := 118140960795 + 3770140 * 2 ^ 59
def prefixEnd_3770140 : Nat := 4983230072969 + 3 ^ 40 * 3770140 * 2
def baseEnd_3770140 : Nat := 1290595969827989695740965

theorem tailTrace_3770140 : CollatzResearch.WordTrace tailWord_3770140 prefixEnd_3770140 1290595969827989695740965 := by
  unfold tailWord_3770140
  simp only [CollatzResearch.WordTrace]
  refine ⟨68754151280717071747257937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91672201707622762329677249 68754151280717071747257937)
  ·
    refine ⟨51565613460537803810443453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68754151280717071747257937 51565613460537803810443453)
    ·
      refine ⟨19337105047701676428916295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51565613460537803810443453 19337105047701676428916295)
      ·
        refine ⟨29005657571552514643374443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19337105047701676428916295 29005657571552514643374443)
        ·
          refine ⟨43508486357328771965061665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29005657571552514643374443 43508486357328771965061665)
          ·
            refine ⟨32631364767996578973796249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43508486357328771965061665 32631364767996578973796249)
            ·
              refine ⟨24473523575997434230347187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32631364767996578973796249 24473523575997434230347187)
              ·
                refine ⟨36710285363996151345520781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24473523575997434230347187 36710285363996151345520781)
                ·
                  refine ⟨13766357011498556754570293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36710285363996151345520781 13766357011498556754570293)
                  ·
                    refine ⟨1290595969827989695740965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13766357011498556754570293 1290595969827989695740965)
                    ·
                      rfl

theorem cell22_3770140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 2, 1, 3, 5].length) (baseStart_3770140 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3770140 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3770140 prefixEnd_3770140 := by exact prefixLift 3770140
  have htrace : WordTrace (prefixWord ++ tailWord_3770140) baseStart_3770140 baseEnd_3770140 := by
    simpa [prefixWord, tailWord_3770140, baseEnd_3770140] using wordTrace_append hprefix tailTrace_3770140
  have hstable : (prefixWord ++ tailWord_3770140).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3770140).length < 2 ^ (prefixWord ++ tailWord_3770140).sum := by decide
  have hdescent : baseEnd_3770140 < baseStart_3770140 := by decide
  rcases family_descends (prefixWord ++ tailWord_3770140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3770170 : List Nat := [3, 1, 1, 1, 5, 1, 1, 9]
def baseStart_3770170 : Nat := 118140960795 + 3770170 * 2 ^ 59
def prefixEnd_3770170 : Nat := 4983230072969 + 3 ^ 40 * 3770170 * 2
def baseEnd_3770170 : Nat := 143400693271231068610097

theorem tailTrace_3770170 : CollatzResearch.WordTrace tailWord_3770170 prefixEnd_3770170 143400693271231068610097 := by
  unfold tailWord_3770170
  simp only [CollatzResearch.WordTrace]
  refine ⟨34377349187831364654526991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91672931167550305745405309 34377349187831364654526991)
  ·
    refine ⟨51566023781747046981790487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34377349187831364654526991 51566023781747046981790487)
    ·
      refine ⟨77349035672620570472685731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51566023781747046981790487 77349035672620570472685731)
      ·
        refine ⟨116023553508930855709028597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77349035672620570472685731 116023553508930855709028597)
        ·
          refine ⟨10877208141462267722721431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 116023553508930855709028597 10877208141462267722721431)
          ·
            refine ⟨16315812212193401584082147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10877208141462267722721431 16315812212193401584082147)
            ·
              refine ⟨24473718318290102376123221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16315812212193401584082147 24473718318290102376123221)
              ·
                refine ⟨143400693271231068610097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 24473718318290102376123221 143400693271231068610097)
                ·
                  rfl

theorem cell22_3770170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 1, 9].length) (baseStart_3770170 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3770170 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3770170 prefixEnd_3770170 := by exact prefixLift 3770170
  have htrace : WordTrace (prefixWord ++ tailWord_3770170) baseStart_3770170 baseEnd_3770170 := by
    simpa [prefixWord, tailWord_3770170, baseEnd_3770170] using wordTrace_append hprefix tailTrace_3770170
  have hstable : (prefixWord ++ tailWord_3770170).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3770170).length < 2 ^ (prefixWord ++ tailWord_3770170).sum := by decide
  have hdescent : baseEnd_3770170 < baseStart_3770170 := by decide
  rcases family_descends (prefixWord ++ tailWord_3770170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3770189 : List Nat := [1, 6, 1, 2, 1, 1, 1, 3, 2, 4]
def baseStart_3770189 : Nat := 118140960795 + 3770189 * 2 ^ 59
def prefixEnd_3770189 : Nat := 4983230072969 + 3 ^ 40 * 3770189 * 2
def baseEnd_3770189 : Nat := 1290612743529369901265815

theorem tailTrace_3770189 : CollatzResearch.WordTrace tailWord_3770189 prefixEnd_3770189 1290612743529369901265815 := by
  unfold tailWord_3770189
  simp only [CollatzResearch.WordTrace]
  refine ⟨137510089738256624863049621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91673393158837749908699747 137510089738256624863049621)
  ·
    refine ⟨6445785456480779290455451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 137510089738256624863049621 6445785456480779290455451)
    ·
      refine ⟨9668678184721168935683177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6445785456480779290455451 9668678184721168935683177)
      ·
        refine ⟨7251508638540876701762383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9668678184721168935683177 7251508638540876701762383)
        ·
          refine ⟨10877262957811315052643575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7251508638540876701762383 10877262957811315052643575)
          ·
            refine ⟨16315894436716972578965363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10877262957811315052643575 16315894436716972578965363)
            ·
              refine ⟨24473841655075458868448045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16315894436716972578965363 24473841655075458868448045)
              ·
                refine ⟨9177690620653297075668017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24473841655075458868448045 9177690620653297075668017)
                ·
                  refine ⟨6883267965489972806751013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9177690620653297075668017 6883267965489972806751013)
                  ·
                    refine ⟨1290612743529369901265815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6883267965489972806751013 1290612743529369901265815)
                    ·
                      rfl

theorem cell22_3770189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 1, 3, 2, 4].length) (baseStart_3770189 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3770189 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3770189 prefixEnd_3770189 := by exact prefixLift 3770189
  have htrace : WordTrace (prefixWord ++ tailWord_3770189) baseStart_3770189 baseEnd_3770189 := by
    simpa [prefixWord, tailWord_3770189, baseEnd_3770189] using wordTrace_append hprefix tailTrace_3770189
  have hstable : (prefixWord ++ tailWord_3770189).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3770189).length < 2 ^ (prefixWord ++ tailWord_3770189).sum := by decide
  have hdescent : baseEnd_3770189 < baseStart_3770189 := by decide
  rcases family_descends (prefixWord ++ tailWord_3770189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3770324 : List Nat := [2, 4, 1, 2, 1, 1, 3, 2, 2, 4]
def baseStart_3770324 : Nat := 118140960795 + 3770324 * 2 ^ 59
def prefixEnd_3770324 : Nat := 4983230072969 + 3 ^ 40 * 3770324 * 2
def baseEnd_3770324 : Nat := 1290658956788274549140401

theorem tailTrace_3770324 : CollatzResearch.WordTrace tailWord_3770324 prefixEnd_3770324 1290658956788274549140401 := by
  unfold tailWord_3770324
  simp only [CollatzResearch.WordTrace]
  refine ⟨68757506796383771459607013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91676675728511695279476017 68757506796383771459607013)
  ·
    refine ⟨12892032524321957148676315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 68757506796383771459607013 12892032524321957148676315)
    ·
      refine ⟨19338048786482935723014473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12892032524321957148676315 19338048786482935723014473)
      ·
        refine ⟨14503536589862201792260855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19338048786482935723014473 14503536589862201792260855)
        ·
          refine ⟨21755304884793302688391283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14503536589862201792260855 21755304884793302688391283)
          ·
            refine ⟨32632957327189954032586925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21755304884793302688391283 32632957327189954032586925)
            ·
              refine ⟨12237358997696232762220097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32632957327189954032586925 12237358997696232762220097)
              ·
                refine ⟨9178019248272174571665073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12237358997696232762220097 9178019248272174571665073)
                ·
                  refine ⟨6883514436204130928748805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9178019248272174571665073 6883514436204130928748805)
                  ·
                    refine ⟨1290658956788274549140401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6883514436204130928748805 1290658956788274549140401)
                    ·
                      rfl

theorem cell22_3770324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 3, 2, 2, 4].length) (baseStart_3770324 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3770324 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3770324 prefixEnd_3770324 := by exact prefixLift 3770324
  have htrace : WordTrace (prefixWord ++ tailWord_3770324) baseStart_3770324 baseEnd_3770324 := by
    simpa [prefixWord, tailWord_3770324, baseEnd_3770324] using wordTrace_append hprefix tailTrace_3770324
  have hstable : (prefixWord ++ tailWord_3770324).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3770324).length < 2 ^ (prefixWord ++ tailWord_3770324).sum := by decide
  have hdescent : baseEnd_3770324 < baseStart_3770324 := by decide
  rcases family_descends (prefixWord ++ tailWord_3770324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3770431 : List Nat := [1, 1, 2, 2, 3, 1, 6, 1, 1, 4]
def baseStart_3770431 : Nat := 118140960795 + 3770431 * 2 ^ 59
def prefixEnd_3770431 : Nat := 4983230072969 + 3 ^ 40 * 3770431 * 2
def baseEnd_3770431 : Nat := 1290695585074961936715073

theorem tailTrace_3770431 : CollatzResearch.WordTrace tailWord_3770431 prefixEnd_3770431 1290695585074961936715073 := by
  unfold tailWord_3770431
  simp only [CollatzResearch.WordTrace]
  refine ⟨137518916203379900193359147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91679277468919933462239431 137518916203379900193359147)
  ·
    refine ⟨206278374305069850290038721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137518916203379900193359147 206278374305069850290038721)
    ·
      refine ⟨154708780728802387717529041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 206278374305069850290038721 154708780728802387717529041)
      ·
        refine ⟨116031585546601790788146781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154708780728802387717529041 116031585546601790788146781)
        ·
          refine ⟨43511844579975671545555043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 116031585546601790788146781 43511844579975671545555043)
          ·
            refine ⟨65267766869963507318332565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43511844579975671545555043 65267766869963507318332565)
            ·
              refine ⟨3059426572029539405546839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 65267766869963507318332565 3059426572029539405546839)
              ·
                refine ⟨4589139858044309108320259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3059426572029539405546839 4589139858044309108320259)
                ·
                  refine ⟨6883709787066463662480389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4589139858044309108320259 6883709787066463662480389)
                  ·
                    refine ⟨1290695585074961936715073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6883709787066463662480389 1290695585074961936715073)
                    ·
                      rfl

theorem cell22_3770431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 6, 1, 1, 4].length) (baseStart_3770431 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3770431 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3770431 prefixEnd_3770431 := by exact prefixLift 3770431
  have htrace : WordTrace (prefixWord ++ tailWord_3770431) baseStart_3770431 baseEnd_3770431 := by
    simpa [prefixWord, tailWord_3770431, baseEnd_3770431] using wordTrace_append hprefix tailTrace_3770431
  have hstable : (prefixWord ++ tailWord_3770431).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3770431).length < 2 ^ (prefixWord ++ tailWord_3770431).sum := by decide
  have hdescent : baseEnd_3770431 < baseStart_3770431 := by decide
  rcases family_descends (prefixWord ++ tailWord_3770431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3770446 : List Nat := [4, 1, 1, 1, 1, 4, 2, 4, 4]
def baseStart_3770446 : Nat := 118140960795 + 3770446 * 2 ^ 59
def prefixEnd_3770446 : Nat := 4983230072969 + 3 ^ 40 * 3770446 * 2
def baseEnd_3770446 : Nat := 430233573293835632530009

theorem tailTrace_3770446 : CollatzResearch.WordTrace tailWord_3770446 prefixEnd_3770446 430233573293835632530009 := by
  unfold tailWord_3770446
  simp only [CollatzResearch.WordTrace]
  refine ⟨17189932912290694719394399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 91679642198883705170103461 17189932912290694719394399)
  ·
    refine ⟨25784899368436042079091599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17189932912290694719394399 25784899368436042079091599)
    ·
      refine ⟨38677349052654063118637399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25784899368436042079091599 38677349052654063118637399)
      ·
        refine ⟨58016023578981094677956099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38677349052654063118637399 58016023578981094677956099)
        ·
          refine ⟨87024035368471642016934149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58016023578981094677956099 87024035368471642016934149)
          ·
            refine ⟨16317006631588432878175153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 87024035368471642016934149 16317006631588432878175153)
            ·
              refine ⟨12237754973691324658631365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16317006631588432878175153 12237754973691324658631365)
              ·
                refine ⟨2294579057567123373493381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12237754973691324658631365 2294579057567123373493381)
                ·
                  refine ⟨430233573293835632530009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2294579057567123373493381 430233573293835632530009)
                  ·
                    rfl

theorem cell22_3770446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 2, 4, 4].length) (baseStart_3770446 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3770446 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3770446 prefixEnd_3770446 := by exact prefixLift 3770446
  have htrace : WordTrace (prefixWord ++ tailWord_3770446) baseStart_3770446 baseEnd_3770446 := by
    simpa [prefixWord, tailWord_3770446, baseEnd_3770446] using wordTrace_append hprefix tailTrace_3770446
  have hstable : (prefixWord ++ tailWord_3770446).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3770446).length < 2 ^ (prefixWord ++ tailWord_3770446).sum := by decide
  have hdescent : baseEnd_3770446 < baseStart_3770446 := by decide
  rcases family_descends (prefixWord ++ tailWord_3770446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3770457 : List Nat := [1, 2, 1, 2, 2, 1, 4, 9]
def baseStart_3770457 : Nat := 118140960795 + 3770457 * 2 ^ 59
def prefixEnd_3770457 : Nat := 4983230072969 + 3 ^ 40 * 3770457 * 2
def baseEnd_3770457 : Nat := 143411609489589615062777

theorem tailTrace_3770457 : CollatzResearch.WordTrace tailWord_3770457 prefixEnd_3770457 143411609489589615062777 := by
  unfold tailWord_3770457
  simp only [CollatzResearch.WordTrace]
  refine ⟨137519864501285706633805625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91679909667523804422537083 137519864501285706633805625)
  ·
    refine ⟨103139898375964279975354219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137519864501285706633805625 103139898375964279975354219)
    ·
      refine ⟨154709847563946419963031329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103139898375964279975354219 154709847563946419963031329)
      ·
        refine ⟨116032385672959814972273497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154709847563946419963031329 116032385672959814972273497)
        ·
          refine ⟨87024289254719861229205123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116032385672959814972273497 87024289254719861229205123)
          ·
            refine ⟨130536433882079791843807685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87024289254719861229205123 130536433882079791843807685)
            ·
              refine ⟨24475581352889960970713941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 130536433882079791843807685 24475581352889960970713941)
              ·
                refine ⟨143411609489589615062777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 24475581352889960970713941 143411609489589615062777)
                ·
                  rfl

theorem cell22_3770457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 4, 9].length) (baseStart_3770457 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3770457 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3770457 prefixEnd_3770457 := by exact prefixLift 3770457
  have htrace : WordTrace (prefixWord ++ tailWord_3770457) baseStart_3770457 baseEnd_3770457 := by
    simpa [prefixWord, tailWord_3770457, baseEnd_3770457] using wordTrace_append hprefix tailTrace_3770457
  have hstable : (prefixWord ++ tailWord_3770457).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3770457).length < 2 ^ (prefixWord ++ tailWord_3770457).sum := by decide
  have hdescent : baseEnd_3770457 < baseStart_3770457 := by decide
  rcases family_descends (prefixWord ++ tailWord_3770457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3770596 : List Nat := [2, 3, 1, 1, 1, 2, 1, 4, 4, 3]
def baseStart_3770596 : Nat := 118140960795 + 3770596 * 2 ^ 59
def prefixEnd_3770596 : Nat := 4983230072969 + 3 ^ 40 * 3770596 * 2
def baseEnd_3770596 : Nat := 1290752067946956506339567

theorem tailTrace_3770596 : CollatzResearch.WordTrace tailWord_3770596 prefixEnd_3770596 1290752067946956506339567 := by
  unfold tailWord_3770596
  simp only [CollatzResearch.WordTrace]
  refine ⟨68762467123891066686557821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91683289498521422248743761 68762467123891066686557821)
  ·
    refine ⟨25785925171459150007459183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68762467123891066686557821 25785925171459150007459183)
    ·
      refine ⟨38678887757188725011188775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25785925171459150007459183 38678887757188725011188775)
      ·
        refine ⟨58018331635783087516783163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38678887757188725011188775 58018331635783087516783163)
        ·
          refine ⟨87027497453674631275174745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58018331635783087516783163 87027497453674631275174745)
          ·
            refine ⟨65270623090255973456381059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87027497453674631275174745 65270623090255973456381059)
            ·
              refine ⟨97905934635383960184571589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65270623090255973456381059 97905934635383960184571589)
              ·
                refine ⟨18357362744134492534607173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 97905934635383960184571589 18357362744134492534607173)
                ·
                  refine ⟨3442005514525217350238845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18357362744134492534607173 3442005514525217350238845)
                  ·
                    refine ⟨1290752067946956506339567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3442005514525217350238845 1290752067946956506339567)
                    ·
                      rfl

theorem cell22_3770596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 4, 4, 3].length) (baseStart_3770596 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3770596 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3770596 prefixEnd_3770596 := by exact prefixLift 3770596
  have htrace : WordTrace (prefixWord ++ tailWord_3770596) baseStart_3770596 baseEnd_3770596 := by
    simpa [prefixWord, tailWord_3770596, baseEnd_3770596] using wordTrace_append hprefix tailTrace_3770596
  have hstable : (prefixWord ++ tailWord_3770596).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3770596).length < 2 ^ (prefixWord ++ tailWord_3770596).sum := by decide
  have hdescent : baseEnd_3770596 < baseStart_3770596 := by decide
  rcases family_descends (prefixWord ++ tailWord_3770596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3770600 : List Nat := [2, 1, 4, 1, 2, 4, 2, 1, 1, 4]
def baseStart_3770600 : Nat := 118140960795 + 3770600 * 2 ^ 59
def prefixEnd_3770600 : Nat := 4983230072969 + 3 ^ 40 * 3770600 * 2
def baseEnd_3770600 : Nat := 1290753437228701829239555

theorem tailTrace_3770600 : CollatzResearch.WordTrace tailWord_3770600 prefixEnd_3770600 1290753437228701829239555 := by
  unfold tailWord_3770600
  simp only [CollatzResearch.WordTrace]
  refine ⟨68762540069883821028130627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91683386759845094704174169 68762540069883821028130627)
  ·
    refine ⟨103143810104825731542195941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68762540069883821028130627 103143810104825731542195941)
    ·
      refine ⟨19339464394654824664161739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 103143810104825731542195941 19339464394654824664161739)
      ·
        refine ⟨29009196591982236996242609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19339464394654824664161739 29009196591982236996242609)
        ·
          refine ⟨21756897443986677747181957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29009196591982236996242609 21756897443986677747181957)
          ·
            refine ⟨4079418270747502077596617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21756897443986677747181957 4079418270747502077596617)
            ·
              refine ⟨3059563703060626558197463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4079418270747502077596617 3059563703060626558197463)
              ·
                refine ⟨4589345554590939837296195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3059563703060626558197463 4589345554590939837296195)
                ·
                  refine ⟨6884018331886409755944293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4589345554590939837296195 6884018331886409755944293)
                  ·
                    refine ⟨1290753437228701829239555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6884018331886409755944293 1290753437228701829239555)
                    ·
                      rfl

theorem cell22_3770600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 4, 2, 1, 1, 4].length) (baseStart_3770600 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3770600 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3770600 prefixEnd_3770600 := by exact prefixLift 3770600
  have htrace : WordTrace (prefixWord ++ tailWord_3770600) baseStart_3770600 baseEnd_3770600 := by
    simpa [prefixWord, tailWord_3770600, baseEnd_3770600] using wordTrace_append hprefix tailTrace_3770600
  have hstable : (prefixWord ++ tailWord_3770600).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3770600).length < 2 ^ (prefixWord ++ tailWord_3770600).sum := by decide
  have hdescent : baseEnd_3770600 < baseStart_3770600 := by decide
  rcases family_descends (prefixWord ++ tailWord_3770600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3770639 : List Nat := [1, 1, 2, 1, 1, 1, 3, 4, 2, 6]
def baseStart_3770639 : Nat := 118140960795 + 3770639 * 2 ^ 59
def prefixEnd_3770639 : Nat := 4983230072969 + 3 ^ 40 * 3770639 * 2
def baseEnd_3770639 : Nat := 1290766787725718727514435

theorem tailTrace_3770639 : CollatzResearch.WordTrace tailWord_3770639 prefixEnd_3770639 1290766787725718727514435 := by
  unfold tailWord_3770639
  simp only [CollatzResearch.WordTrace]
  refine ⟨137526502586626351716930971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91684335057750901144620647 137526502586626351716930971)
  ·
    refine ⟨206289753879939527575396457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137526502586626351716930971 206289753879939527575396457)
    ·
      refine ⟨154717315409954645681547343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 206289753879939527575396457 154717315409954645681547343)
      ·
        refine ⟨232075973114931968522321015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154717315409954645681547343 232075973114931968522321015)
        ·
          refine ⟨348113959672397952783481523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 232075973114931968522321015 348113959672397952783481523)
          ·
            refine ⟨522170939508596929175222285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 348113959672397952783481523 522170939508596929175222285)
            ·
              refine ⟨195814102315723848440708357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 522170939508596929175222285 195814102315723848440708357)
              ·
                refine ⟨36715144184198221582632817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 195814102315723848440708357 36715144184198221582632817)
                ·
                  refine ⟨27536358138148666186974613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36715144184198221582632817 27536358138148666186974613)
                  ·
                    refine ⟨1290766787725718727514435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27536358138148666186974613 1290766787725718727514435)
                    ·
                      rfl

theorem cell22_3770639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 4, 2, 6].length) (baseStart_3770639 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3770639 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3770639 prefixEnd_3770639 := by exact prefixLift 3770639
  have htrace : WordTrace (prefixWord ++ tailWord_3770639) baseStart_3770639 baseEnd_3770639 := by
    simpa [prefixWord, tailWord_3770639, baseEnd_3770639] using wordTrace_append hprefix tailTrace_3770639
  have hstable : (prefixWord ++ tailWord_3770639).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3770639).length < 2 ^ (prefixWord ++ tailWord_3770639).sum := by decide
  have hdescent : baseEnd_3770639 < baseStart_3770639 := by decide
  rcases family_descends (prefixWord ++ tailWord_3770639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3770763 : List Nat := [1, 1, 1, 1, 4, 4, 3, 1, 2, 4]
def baseStart_3770763 : Nat := 118140960795 + 3770763 * 2 ^ 59
def prefixEnd_3770763 : Nat := 4983230072969 + 3 ^ 40 * 3770763 * 2
def baseEnd_3770763 : Nat := 1290809235459823737414055

theorem tailTrace_3770763 : CollatzResearch.WordTrace tailWord_3770763 prefixEnd_3770763 1290809235459823737414055 := by
  unfold tailWord_3770763
  simp only [CollatzResearch.WordTrace]
  refine ⟨137531025238177120894444943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91687350158784747262963295 137531025238177120894444943)
  ·
    refine ⟨206296537857265681341667415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137531025238177120894444943 206296537857265681341667415)
    ·
      refine ⟨309444806785898522012501123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206296537857265681341667415 309444806785898522012501123)
      ·
        refine ⟨464167210178847783018751685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 309444806785898522012501123 464167210178847783018751685)
        ·
          refine ⟨87031351908533959316015941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 464167210178847783018751685 87031351908533959316015941)
          ·
            refine ⟨16318378482850117371752989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 87031351908533959316015941 16318378482850117371752989)
            ·
              refine ⟨6119391931068794014407371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16318378482850117371752989 6119391931068794014407371)
              ·
                refine ⟨9179087896603191021611057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6119391931068794014407371 9179087896603191021611057)
                ·
                  refine ⟨6884315922452393266208293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9179087896603191021611057 6884315922452393266208293)
                  ·
                    refine ⟨1290809235459823737414055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6884315922452393266208293 1290809235459823737414055)
                    ·
                      rfl

theorem cell22_3770763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 3, 1, 2, 4].length) (baseStart_3770763 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3770763 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3770763 prefixEnd_3770763 := by exact prefixLift 3770763
  have htrace : WordTrace (prefixWord ++ tailWord_3770763) baseStart_3770763 baseEnd_3770763 := by
    simpa [prefixWord, tailWord_3770763, baseEnd_3770763] using wordTrace_append hprefix tailTrace_3770763
  have hstable : (prefixWord ++ tailWord_3770763).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3770763).length < 2 ^ (prefixWord ++ tailWord_3770763).sum := by decide
  have hdescent : baseEnd_3770763 < baseStart_3770763 := by decide
  rcases family_descends (prefixWord ++ tailWord_3770763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3770782 : List Nat := [4, 3, 1, 2, 1, 2, 1, 1, 4, 3]
def baseStart_3770782 : Nat := 118140960795 + 3770782 * 2 ^ 59
def prefixEnd_3770782 : Nat := 4983230072969 + 3 ^ 40 * 3770782 * 2
def baseEnd_3770782 : Nat := 1290815739548114021188997

theorem tailTrace_3770782 : CollatzResearch.WordTrace tailWord_3770782 prefixEnd_3770782 1290815739548114021188997 := by
  unfold tailWord_3770782
  simp only [CollatzResearch.WordTrace]
  refine ⟨17191464778138535892423325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 91687812150072191426257733 17191464778138535892423325)
  ·
    refine ⟨6446799291801950959658747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17191464778138535892423325 6446799291801950959658747)
    ·
      refine ⟨9670198937702926439488121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6446799291801950959658747 9670198937702926439488121)
      ·
        refine ⟨7252649203277194829616091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9670198937702926439488121 7252649203277194829616091)
        ·
          refine ⟨10878973804915792244424137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7252649203277194829616091 10878973804915792244424137)
          ·
            refine ⟨8159230353686844183318103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10878973804915792244424137 8159230353686844183318103)
            ·
              refine ⟨12238845530530266274977155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8159230353686844183318103 12238845530530266274977155)
              ·
                refine ⟨18358268295795399412465733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12238845530530266274977155 18358268295795399412465733)
                ·
                  refine ⟨3442175305461637389837325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18358268295795399412465733 3442175305461637389837325)
                  ·
                    refine ⟨1290815739548114021188997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3442175305461637389837325 1290815739548114021188997)
                    ·
                      rfl

theorem cell22_3770782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 1, 1, 4, 3].length) (baseStart_3770782 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3770782 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3770782 prefixEnd_3770782 := by exact prefixLift 3770782
  have htrace : WordTrace (prefixWord ++ tailWord_3770782) baseStart_3770782 baseEnd_3770782 := by
    simpa [prefixWord, tailWord_3770782, baseEnd_3770782] using wordTrace_append hprefix tailTrace_3770782
  have hstable : (prefixWord ++ tailWord_3770782).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3770782).length < 2 ^ (prefixWord ++ tailWord_3770782).sum := by decide
  have hdescent : baseEnd_3770782 < baseStart_3770782 := by decide
  rcases family_descends (prefixWord ++ tailWord_3770782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3770870 : List Nat := [5, 1, 1, 1, 2, 1, 3, 1, 3, 4]
def baseStart_3770870 : Nat := 118140960795 + 3770870 * 2 ^ 59
def prefixEnd_3770870 : Nat := 4983230072969 + 3 ^ 40 * 3770870 * 2
def baseEnd_3770870 : Nat := 1290845863746511124988727

theorem tailTrace_3770870 : CollatzResearch.WordTrace tailWord_3770870 prefixEnd_3770870 1290845863746511124988727 := by
  unfold tailWord_3770870
  simp only [CollatzResearch.WordTrace]
  refine ⟨8595932990549342385536879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 91689951899192985445726709 8595932990549342385536879)
  ·
    refine ⟨12893899485824013578305319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8595932990549342385536879 12893899485824013578305319)
    ·
      refine ⟨19340849228736020367457979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12893899485824013578305319 19340849228736020367457979)
      ·
        refine ⟨29011273843104030551186969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19340849228736020367457979 29011273843104030551186969)
        ·
          refine ⟨21758455382328022913390227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29011273843104030551186969 21758455382328022913390227)
          ·
            refine ⟨32637683073492034370085341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21758455382328022913390227 32637683073492034370085341)
            ·
              refine ⟨12239131152559512888782003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32637683073492034370085341 12239131152559512888782003)
              ·
                refine ⟨18358696728839269333173005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12239131152559512888782003 18358696728839269333173005)
                ·
                  refine ⟨6884511273314725999939877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18358696728839269333173005 6884511273314725999939877)
                  ·
                    refine ⟨1290845863746511124988727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6884511273314725999939877 1290845863746511124988727)
                    ·
                      rfl

theorem cell22_3770870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 3, 1, 3, 4].length) (baseStart_3770870 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3770870 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3770870 prefixEnd_3770870 := by exact prefixLift 3770870
  have htrace : WordTrace (prefixWord ++ tailWord_3770870) baseStart_3770870 baseEnd_3770870 := by
    simpa [prefixWord, tailWord_3770870, baseEnd_3770870] using wordTrace_append hprefix tailTrace_3770870
  have hstable : (prefixWord ++ tailWord_3770870).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3770870).length < 2 ^ (prefixWord ++ tailWord_3770870).sum := by decide
  have hdescent : baseEnd_3770870 < baseStart_3770870 := by decide
  rcases family_descends (prefixWord ++ tailWord_3770870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3770883 : List Nat := [1, 1, 1, 3, 2, 1, 5, 2, 1, 5]
def baseStart_3770883 : Nat := 118140960795 + 3770883 * 2 ^ 59
def prefixEnd_3770883 : Nat := 4983230072969 + 3 ^ 40 * 3770883 * 2
def baseEnd_3770883 : Nat := 1290850313912183424413687

theorem tailTrace_3770883 : CollatzResearch.WordTrace tailWord_3770883 prefixEnd_3770883 1290850313912183424413687 := by
  unfold tailWord_3770883
  simp only [CollatzResearch.WordTrace]
  refine ⟨137535401997742381388813303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91690267998494920925875535 137535401997742381388813303)
  ·
    refine ⟨206303102996613572083219955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137535401997742381388813303 206303102996613572083219955)
    ·
      refine ⟨309454654494920358124829933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206303102996613572083219955 309454654494920358124829933)
      ·
        refine ⟨116045495435595134296811225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 309454654494920358124829933 116045495435595134296811225)
        ·
          refine ⟨87034121576696350722608419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116045495435595134296811225 87034121576696350722608419)
          ·
            refine ⟨130551182365044526083912629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87034121576696350722608419 130551182365044526083912629)
            ·
              refine ⟨12239173346722924320366809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 130551182365044526083912629 12239173346722924320366809)
              ·
                refine ⟨9179380010042193240275107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12239173346722924320366809 9179380010042193240275107)
                ·
                  refine ⟨13769070015063289860412661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9179380010042193240275107 13769070015063289860412661)
                  ·
                    refine ⟨1290850313912183424413687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13769070015063289860412661 1290850313912183424413687)
                    ·
                      rfl

theorem cell22_3770883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 5, 2, 1, 5].length) (baseStart_3770883 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3770883 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3770883 prefixEnd_3770883 := by exact prefixLift 3770883
  have htrace : WordTrace (prefixWord ++ tailWord_3770883) baseStart_3770883 baseEnd_3770883 := by
    simpa [prefixWord, tailWord_3770883, baseEnd_3770883] using wordTrace_append hprefix tailTrace_3770883
  have hstable : (prefixWord ++ tailWord_3770883).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3770883).length < 2 ^ (prefixWord ++ tailWord_3770883).sum := by decide
  have hdescent : baseEnd_3770883 < baseStart_3770883 := by decide
  rcases family_descends (prefixWord ++ tailWord_3770883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3770962 : List Nat := [3, 2, 2, 1, 2, 1, 4, 1, 3, 3]
def baseStart_3770962 : Nat := 118140960795 + 3770962 * 2 ^ 59
def prefixEnd_3770962 : Nat := 4983230072969 + 3 ^ 40 * 3770962 * 2
def baseEnd_3770962 : Nat := 1290877357226653551688445

theorem tailTrace_3770962 : CollatzResearch.WordTrace tailWord_3770962 prefixEnd_3770962 1290877357226653551688445 := by
  unfold tailWord_3770962
  simp only [CollatzResearch.WordTrace]
  refine ⟨34384570841114044470234785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91692188909637451920626093 34384570841114044470234785)
  ·
    refine ⟨25788428130835533352676089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34384570841114044470234785 25788428130835533352676089)
    ·
      refine ⟨19341321098126650014507067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25788428130835533352676089 19341321098126650014507067)
      ·
        refine ⟨29011981647189975021760601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19341321098126650014507067 29011981647189975021760601)
        ·
          refine ⟨21758986235392481266320451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29011981647189975021760601 21758986235392481266320451)
          ·
            refine ⟨32638479353088721899480677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21758986235392481266320451 32638479353088721899480677)
            ·
              refine ⟨6119714878704135356152627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32638479353088721899480677 6119714878704135356152627)
              ·
                refine ⟨9179572318056203034228941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6119714878704135356152627 9179572318056203034228941)
                ·
                  refine ⟨3442339619271076137835853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9179572318056203034228941 3442339619271076137835853)
                  ·
                    refine ⟨1290877357226653551688445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3442339619271076137835853 1290877357226653551688445)
                    ·
                      rfl

theorem cell22_3770962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 4, 1, 3, 3].length) (baseStart_3770962 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3770962 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3770962 prefixEnd_3770962 := by exact prefixLift 3770962
  have htrace : WordTrace (prefixWord ++ tailWord_3770962) baseStart_3770962 baseEnd_3770962 := by
    simpa [prefixWord, tailWord_3770962, baseEnd_3770962] using wordTrace_append hprefix tailTrace_3770962
  have hstable : (prefixWord ++ tailWord_3770962).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3770962).length < 2 ^ (prefixWord ++ tailWord_3770962).sum := by decide
  have hdescent : baseEnd_3770962 < baseStart_3770962 := by decide
  rcases family_descends (prefixWord ++ tailWord_3770962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3771069 : List Nat := [1, 4, 1, 2, 1, 4, 2, 2, 2, 3]
def baseStart_3771069 : Nat := 118140960795 + 3771069 * 2 ^ 59
def prefixEnd_3771069 : Nat := 4983230072969 + 3 ^ 40 * 3771069 * 2
def baseEnd_3771069 : Nat := 1290913985513340939263117

theorem tailTrace_3771069 : CollatzResearch.WordTrace tailWord_3771069 prefixEnd_3771069 1290913985513340939263117 := by
  unfold tailWord_3771069
  simp only [CollatzResearch.WordTrace]
  refine ⟨137542185975068535155084261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91694790650045690103389507 137542185975068535155084261)
  ·
    refine ⟨25789159870325350341578299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 137542185975068535155084261 25789159870325350341578299)
    ·
      refine ⟨38683739805488025512367449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25789159870325350341578299 38683739805488025512367449)
      ·
        refine ⟨29012804854116019134275587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38683739805488025512367449 29012804854116019134275587)
        ·
          refine ⟨43519207281174028701413381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29012804854116019134275587 43519207281174028701413381)
          ·
            refine ⟨8159851365220130381515009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43519207281174028701413381 8159851365220130381515009)
            ·
              refine ⟨6119888523915097786136257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8159851365220130381515009 6119888523915097786136257)
              ·
                refine ⟨4589916392936323339602193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6119888523915097786136257 4589916392936323339602193)
                ·
                  refine ⟨3442437294702242504701645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4589916392936323339602193 3442437294702242504701645)
                  ·
                    refine ⟨1290913985513340939263117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3442437294702242504701645 1290913985513340939263117)
                    ·
                      rfl

theorem cell22_3771069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 2, 2, 2, 3].length) (baseStart_3771069 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3771069 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3771069 prefixEnd_3771069 := by exact prefixLift 3771069
  have htrace : WordTrace (prefixWord ++ tailWord_3771069) baseStart_3771069 baseEnd_3771069 := by
    simpa [prefixWord, tailWord_3771069, baseEnd_3771069] using wordTrace_append hprefix tailTrace_3771069
  have hstable : (prefixWord ++ tailWord_3771069).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3771069).length < 2 ^ (prefixWord ++ tailWord_3771069).sum := by decide
  have hdescent : baseEnd_3771069 < baseStart_3771069 := by decide
  rcases family_descends (prefixWord ++ tailWord_3771069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3771082 : List Nat := [3, 1, 2, 1, 4, 3, 1, 7]
def baseStart_3771082 : Nat := 118140960795 + 3771082 * 2 ^ 59
def prefixEnd_3771082 : Nat := 4983230072969 + 3 ^ 40 * 3771082 * 2
def baseEnd_3771082 : Nat := 143435381742112582076453

theorem tailTrace_3771082 : CollatzResearch.WordTrace tailWord_3771082 prefixEnd_3771082 143435381742112582076453 := by
  unfold tailWord_3771082
  simp only [CollatzResearch.WordTrace]
  refine ⟨34385665031005359593826875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91695106749347625583538333 34385665031005359593826875)
  ·
    refine ⟨51578497546508039390740313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34385665031005359593826875 51578497546508039390740313)
    ·
      refine ⟨38683873159881029543055235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51578497546508039390740313 38683873159881029543055235)
      ·
        refine ⟨58025809739821544314582853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38683873159881029543055235 58025809739821544314582853)
        ·
          refine ⟨10879839326216539558984285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 58025809739821544314582853 10879839326216539558984285)
          ·
            refine ⟨4079939747331202334619107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10879839326216539558984285 4079939747331202334619107)
            ·
              refine ⟨6119909620996803501928661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4079939747331202334619107 6119909620996803501928661)
              ·
                refine ⟨143435381742112582076453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6119909620996803501928661 143435381742112582076453)
                ·
                  rfl

theorem cell22_3771082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 3, 1, 7].length) (baseStart_3771082 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3771082 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3771082 prefixEnd_3771082 := by exact prefixLift 3771082
  have htrace : WordTrace (prefixWord ++ tailWord_3771082) baseStart_3771082 baseEnd_3771082 := by
    simpa [prefixWord, tailWord_3771082, baseEnd_3771082] using wordTrace_append hprefix tailTrace_3771082
  have hstable : (prefixWord ++ tailWord_3771082).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3771082).length < 2 ^ (prefixWord ++ tailWord_3771082).sum := by decide
  have hdescent : baseEnd_3771082 < baseStart_3771082 := by decide
  rcases family_descends (prefixWord ++ tailWord_3771082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3771097 : List Nat := [1, 2, 1, 2, 3, 2, 3, 2, 3, 3]
def baseStart_3771097 : Nat := 118140960795 + 3771097 * 2 ^ 59
def prefixEnd_3771097 : Nat := 4983230072969 + 3 ^ 40 * 3771097 * 2
def baseEnd_3771097 : Nat := 1290923570485558199563031

theorem tailTrace_3771097 : CollatzResearch.WordTrace tailWord_3771097 prefixEnd_3771097 1290923570485558199563031 := by
  unfold tailWord_3771097
  simp only [CollatzResearch.WordTrace]
  refine ⟨137543207218967095937103545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91695471479311397291402363 137543207218967095937103545)
  ·
    refine ⟨103157405414225321952827659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137543207218967095937103545 103157405414225321952827659)
    ·
      refine ⟨154736108121337982929241489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103157405414225321952827659 154736108121337982929241489)
      ·
        refine ⟨116052081091003487196931117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154736108121337982929241489 116052081091003487196931117)
        ·
          refine ⟨43519530409126307698849169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 116052081091003487196931117 43519530409126307698849169)
          ·
            refine ⟨32639647806844730774136877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43519530409126307698849169 32639647806844730774136877)
            ·
              refine ⟨12239867927566774040301329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32639647806844730774136877 12239867927566774040301329)
              ·
                refine ⟨9179900945675080530225997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12239867927566774040301329 9179900945675080530225997)
                ·
                  refine ⟨3442462854628155198834749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9179900945675080530225997 3442462854628155198834749)
                  ·
                    refine ⟨1290923570485558199563031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3442462854628155198834749 1290923570485558199563031)
                    ·
                      rfl

theorem cell22_3771097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 3, 2, 3, 3].length) (baseStart_3771097 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3771097 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3771097 prefixEnd_3771097 := by exact prefixLift 3771097
  have htrace : WordTrace (prefixWord ++ tailWord_3771097) baseStart_3771097 baseEnd_3771097 := by
    simpa [prefixWord, tailWord_3771097, baseEnd_3771097] using wordTrace_append hprefix tailTrace_3771097
  have hstable : (prefixWord ++ tailWord_3771097).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3771097).length < 2 ^ (prefixWord ++ tailWord_3771097).sum := by decide
  have hdescent : baseEnd_3771097 < baseStart_3771097 := by decide
  rcases family_descends (prefixWord ++ tailWord_3771097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3771144 : List Nat := [2, 1, 3, 2, 2, 3, 3, 1, 5]
def baseStart_3771144 : Nat := 118140960795 + 3771144 * 2 ^ 59
def prefixEnd_3771144 : Nat := 4983230072969 + 3 ^ 40 * 3771144 * 2
def baseEnd_3771144 : Nat := 430313219848688581212629

theorem tailTrace_3771144 : CollatzResearch.WordTrace tailWord_3771144 prefixEnd_3771144 430313219848688581212629 := by
  unfold tailWord_3771144
  simp only [CollatzResearch.WordTrace]
  refine ⟨68772460724898411482032243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91696614299864548642709657 68772460724898411482032243)
  ·
    refine ⟨103158691087347617223048365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68772460724898411482032243 103158691087347617223048365)
    ·
      refine ⟨38684509157755356458643137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103158691087347617223048365 38684509157755356458643137)
      ·
        refine ⟨29013381868316517343982353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38684509157755356458643137 29013381868316517343982353)
        ·
          refine ⟨21760036401237388007986765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29013381868316517343982353 21760036401237388007986765)
          ·
            refine ⟨8160013650464020502995037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21760036401237388007986765 8160013650464020502995037)
            ·
              refine ⟨3060005118924007688623139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8160013650464020502995037 3060005118924007688623139)
              ·
                refine ⟨4590007678386011532934709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3060005118924007688623139 4590007678386011532934709)
                ·
                  refine ⟨430313219848688581212629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4590007678386011532934709 430313219848688581212629)
                  ·
                    rfl

theorem cell22_3771144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 3, 1, 5].length) (baseStart_3771144 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3771144 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3771144 prefixEnd_3771144 := by exact prefixLift 3771144
  have htrace : WordTrace (prefixWord ++ tailWord_3771144) baseStart_3771144 baseEnd_3771144 := by
    simpa [prefixWord, tailWord_3771144, baseEnd_3771144] using wordTrace_append hprefix tailTrace_3771144
  have hstable : (prefixWord ++ tailWord_3771144).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3771144).length < 2 ^ (prefixWord ++ tailWord_3771144).sum := by decide
  have hdescent : baseEnd_3771144 < baseStart_3771144 := by decide
  rcases family_descends (prefixWord ++ tailWord_3771144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3771155 : List Nat := [1, 1, 1, 2, 1, 3, 3, 4, 6]
def baseStart_3771155 : Nat := 118140960795 + 3771155 * 2 ^ 59
def prefixEnd_3771155 : Nat := 4983230072969 + 3 ^ 40 * 3771155 * 2
def baseEnd_3771155 : Nat := 430314475023621793870951

theorem tailTrace_3771155 : CollatzResearch.WordTrace tailWord_3771155 prefixEnd_3771155 430314475023621793870951 := by
  unfold tailWord_3771155
  simp only [CollatzResearch.WordTrace]
  refine ⟨137545322652756971842714919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91696881768504647895143279 137545322652756971842714919)
  ·
    refine ⟨206317983979135457764072379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137545322652756971842714919 206317983979135457764072379)
    ·
      refine ⟨309476975968703186646108569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206317983979135457764072379 309476975968703186646108569)
      ·
        refine ⟨232107731976527389984581427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 309476975968703186646108569 232107731976527389984581427)
        ·
          refine ⟨348161597964791084976872141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 232107731976527389984581427 348161597964791084976872141)
          ·
            refine ⟨130560599236796656866327053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 348161597964791084976872141 130560599236796656866327053)
            ·
              refine ⟨48960224713798746324872645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 130560599236796656866327053 48960224713798746324872645)
              ·
                refine ⟨9180042133837264935913621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48960224713798746324872645 9180042133837264935913621)
                ·
                  refine ⟨430314475023621793870951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9180042133837264935913621 430314475023621793870951)
                  ·
                    rfl

theorem cell22_3771155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 4, 6].length) (baseStart_3771155 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3771155 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3771155 prefixEnd_3771155 := by exact prefixLift 3771155
  have htrace : WordTrace (prefixWord ++ tailWord_3771155) baseStart_3771155 baseEnd_3771155 := by
    simpa [prefixWord, tailWord_3771155, baseEnd_3771155] using wordTrace_append hprefix tailTrace_3771155
  have hstable : (prefixWord ++ tailWord_3771155).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3771155).length < 2 ^ (prefixWord ++ tailWord_3771155).sum := by decide
  have hdescent : baseEnd_3771155 < baseStart_3771155 := by decide
  rcases family_descends (prefixWord ++ tailWord_3771155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3771165 : List Nat := [1, 4, 2, 4, 1, 2, 1, 3, 1, 3]
def baseStart_3771165 : Nat := 118140960795 + 3771165 * 2 ^ 59
def prefixEnd_3771165 : Nat := 4983230072969 + 3 ^ 40 * 3771165 * 2
def baseEnd_3771165 : Nat := 1290946848275228688862823

theorem tailTrace_3771165 : CollatzResearch.WordTrace tailWord_3771165 prefixEnd_3771165 1290946848275228688862823 := by
  unfold tailWord_3771165
  simp only [CollatzResearch.WordTrace]
  refine ⟨137545687382720743550578949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91697124921813829033719299 137545687382720743550578949)
  ·
    refine ⟨25789816384260139415733553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 137545687382720743550578949 25789816384260139415733553)
    ·
      refine ⟨19342362288195104561800165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25789816384260139415733553 19342362288195104561800165)
      ·
        refine ⟨3626692929036582105337531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19342362288195104561800165 3626692929036582105337531)
        ·
          refine ⟨5440039393554873158006297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3626692929036582105337531 5440039393554873158006297)
          ·
            refine ⟨4080029545166154868504723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5440039393554873158006297 4080029545166154868504723)
            ·
              refine ⟨6120044317749232302757085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4080029545166154868504723 6120044317749232302757085)
              ·
                refine ⟨2295016619155962113533907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6120044317749232302757085 2295016619155962113533907)
                ·
                  refine ⟨3442524928733943170300861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2295016619155962113533907 3442524928733943170300861)
                  ·
                    refine ⟨1290946848275228688862823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3442524928733943170300861 1290946848275228688862823)
                    ·
                      rfl

theorem cell22_3771165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 2, 1, 3, 1, 3].length) (baseStart_3771165 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3771165 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3771165 prefixEnd_3771165 := by exact prefixLift 3771165
  have htrace : WordTrace (prefixWord ++ tailWord_3771165) baseStart_3771165 baseEnd_3771165 := by
    simpa [prefixWord, tailWord_3771165, baseEnd_3771165] using wordTrace_append hprefix tailTrace_3771165
  have hstable : (prefixWord ++ tailWord_3771165).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3771165).length < 2 ^ (prefixWord ++ tailWord_3771165).sum := by decide
  have hdescent : baseEnd_3771165 < baseStart_3771165 := by decide
  rcases family_descends (prefixWord ++ tailWord_3771165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3771189 : List Nat := [1, 3, 3, 1, 3, 3, 1, 1, 6]
def baseStart_3771189 : Nat := 118140960795 + 3771189 * 2 ^ 59
def prefixEnd_3771189 : Nat := 4983230072969 + 3 ^ 40 * 3771189 * 2
def baseEnd_3771189 : Nat := 430318354655233542087583

theorem tailTrace_3771189 : CollatzResearch.WordTrace tailWord_3771189 prefixEnd_3771189 430318354655233542087583 := by
  unfold tailWord_3771189
  simp only [CollatzResearch.WordTrace]
  refine ⟨137546562734633795649452621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91697708489755863766301747 137546562734633795649452621)
  ·
    refine ⟨51579961025487673368544733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137546562734633795649452621 51579961025487673368544733)
    ·
      refine ⟨19342485384557877513204275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51579961025487673368544733 19342485384557877513204275)
      ·
        refine ⟨29013728076836816269806413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19342485384557877513204275 29013728076836816269806413)
        ·
          refine ⟨10880148028813806101177405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29013728076836816269806413 10880148028813806101177405)
          ·
            refine ⟨4080055510805177287941527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10880148028813806101177405 4080055510805177287941527)
            ·
              refine ⟨6120083266207765931912291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4080055510805177287941527 6120083266207765931912291)
              ·
                refine ⟨9180124899311648897868437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6120083266207765931912291 9180124899311648897868437)
                ·
                  refine ⟨430318354655233542087583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9180124899311648897868437 430318354655233542087583)
                  ·
                    rfl

theorem cell22_3771189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 3, 1, 1, 6].length) (baseStart_3771189 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3771189 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3771189 prefixEnd_3771189 := by exact prefixLift 3771189
  have htrace : WordTrace (prefixWord ++ tailWord_3771189) baseStart_3771189 baseEnd_3771189 := by
    simpa [prefixWord, tailWord_3771189, baseEnd_3771189] using wordTrace_append hprefix tailTrace_3771189
  have hstable : (prefixWord ++ tailWord_3771189).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3771189).length < 2 ^ (prefixWord ++ tailWord_3771189).sum := by decide
  have hdescent : baseEnd_3771189 < baseStart_3771189 := by decide
  rcases family_descends (prefixWord ++ tailWord_3771189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3771234 : List Nat := [3, 3, 2, 1, 4, 9]
def baseStart_3771234 : Nat := 118140960795 + 3771234 * 2 ^ 59
def prefixEnd_3771234 : Nat := 4983230072969 + 3 ^ 40 * 3771234 * 2
def baseEnd_3771234 : Nat := 15937907017102907517131

theorem tailTrace_3771234 : CollatzResearch.WordTrace tailWord_3771234 prefixEnd_3771234 15937907017102907517131 := by
  unfold tailWord_3771234
  simp only [CollatzResearch.WordTrace]
  refine ⟨34387051004867692083710189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91698802679647178889893837 34387051004867692083710189)
  ·
    refine ⟨12895144126825384531391321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34387051004867692083710189 12895144126825384531391321)
    ·
      refine ⟨9671358095119038398543491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12895144126825384531391321 9671358095119038398543491)
      ·
        refine ⟨14507037142678557597815237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9671358095119038398543491 14507037142678557597815237)
        ·
          refine ⟨2720069464252229549590357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14507037142678557597815237 2720069464252229549590357)
          ·
            refine ⟨15937907017102907517131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2720069464252229549590357 15937907017102907517131)
            ·
              rfl

theorem cell22_3771234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 4, 9].length) (baseStart_3771234 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3771234 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3771234 prefixEnd_3771234 := by exact prefixLift 3771234
  have htrace : WordTrace (prefixWord ++ tailWord_3771234) baseStart_3771234 baseEnd_3771234 := by
    simpa [prefixWord, tailWord_3771234, baseEnd_3771234] using wordTrace_append hprefix tailTrace_3771234
  have hstable : (prefixWord ++ tailWord_3771234).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3771234).length < 2 ^ (prefixWord ++ tailWord_3771234).sum := by decide
  have hdescent : baseEnd_3771234 < baseStart_3771234 := by decide
  rcases family_descends (prefixWord ++ tailWord_3771234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3771326 : List Nat := [4, 2, 1, 1, 1, 2, 4, 2, 1, 4]
def baseStart_3771326 : Nat := 118140960795 + 3771326 * 2 ^ 59
def prefixEnd_3771326 : Nat := 4983230072969 + 3 ^ 40 * 3771326 * 2
def baseEnd_3771326 : Nat := 1291001961865477935587329

theorem tailTrace_3771326 : CollatzResearch.WordTrace tailWord_3771326 prefixEnd_3771326 1291001961865477935587329 := by
  unfold tailWord_3771326
  simp only [CollatzResearch.WordTrace]
  refine ⟨17193944941892183505898729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 91701039690091645364793221 17193944941892183505898729)
  ·
    refine ⟨12895458706419137629424047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17193944941892183505898729 12895458706419137629424047)
    ·
      refine ⟨19343188059628706444136071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12895458706419137629424047 19343188059628706444136071)
      ·
        refine ⟨29014782089443059666204107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19343188059628706444136071 29014782089443059666204107)
        ·
          refine ⟨43522173134164589499306161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29014782089443059666204107 43522173134164589499306161)
          ·
            refine ⟨32641629850623442124479621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43522173134164589499306161 32641629850623442124479621)
            ·
              refine ⟨6120305596991895398339929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32641629850623442124479621 6120305596991895398339929)
              ·
                refine ⟨4590229197743921548754947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6120305596991895398339929 4590229197743921548754947)
                ·
                  refine ⟨6885343796615882323132421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4590229197743921548754947 6885343796615882323132421)
                  ·
                    refine ⟨1291001961865477935587329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6885343796615882323132421 1291001961865477935587329)
                    ·
                      rfl

theorem cell22_3771326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 4, 2, 1, 4].length) (baseStart_3771326 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3771326 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3771326 prefixEnd_3771326 := by exact prefixLift 3771326
  have htrace : WordTrace (prefixWord ++ tailWord_3771326) baseStart_3771326 baseEnd_3771326 := by
    simpa [prefixWord, tailWord_3771326, baseEnd_3771326] using wordTrace_append hprefix tailTrace_3771326
  have hstable : (prefixWord ++ tailWord_3771326).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3771326).length < 2 ^ (prefixWord ++ tailWord_3771326).sum := by decide
  have hdescent : baseEnd_3771326 < baseStart_3771326 := by decide
  rcases family_descends (prefixWord ++ tailWord_3771326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3771339 : List Nat := [1, 1, 1, 1, 3, 5, 1, 2, 4, 3]
def baseStart_3771339 : Nat := 118140960795 + 3771339 * 2 ^ 59
def prefixEnd_3771339 : Nat := 4983230072969 + 3 ^ 40 * 3771339 * 2
def baseEnd_3771339 : Nat := 1291006412031150235012289

theorem tailTrace_3771339 : CollatzResearch.WordTrace tailWord_3771339 prefixEnd_3771339 1291006412031150235012289 := by
  unfold tailWord_3771339
  simp only [CollatzResearch.WordTrace]
  refine ⟨137552033684090371267413071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91701355789393580844942047 137552033684090371267413071)
  ·
    refine ⟨206328050526135556901119607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137552033684090371267413071 206328050526135556901119607)
    ·
      refine ⟨309492075789203335351679411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206328050526135556901119607 309492075789203335351679411)
      ·
        refine ⟨464238113683805003027519117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 309492075789203335351679411 464238113683805003027519117)
        ·
          refine ⟨174089292631426876135319669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 464238113683805003027519117 174089292631426876135319669)
          ·
            refine ⟨16320871184196269637686219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 174089292631426876135319669 16320871184196269637686219)
            ·
              refine ⟨24481306776294404456529329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16320871184196269637686219 24481306776294404456529329)
              ·
                refine ⟨18360980082220803342396997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24481306776294404456529329 18360980082220803342396997)
                ·
                  refine ⟨3442683765416400626699437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18360980082220803342396997 3442683765416400626699437)
                  ·
                    refine ⟨1291006412031150235012289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3442683765416400626699437 1291006412031150235012289)
                    ·
                      rfl

theorem cell22_3771339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 1, 2, 4, 3].length) (baseStart_3771339 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3771339 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3771339 prefixEnd_3771339 := by exact prefixLift 3771339
  have htrace : WordTrace (prefixWord ++ tailWord_3771339) baseStart_3771339 baseEnd_3771339 := by
    simpa [prefixWord, tailWord_3771339, baseEnd_3771339] using wordTrace_append hprefix tailTrace_3771339
  have hstable : (prefixWord ++ tailWord_3771339).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3771339).length < 2 ^ (prefixWord ++ tailWord_3771339).sum := by decide
  have hdescent : baseEnd_3771339 < baseStart_3771339 := by decide
  rcases family_descends (prefixWord ++ tailWord_3771339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3771352 : List Nat := [2, 1, 2, 2, 2, 3, 10]
def baseStart_3771352 : Nat := 118140960795 + 3771352 * 2 ^ 59
def prefixEnd_3771352 : Nat := 4983230072969 + 3 ^ 40 * 3771352 * 2
def baseEnd_3771352 : Nat := 47815217118400834608787

theorem tailTrace_3771352 : CollatzResearch.WordTrace tailWord_3771352 prefixEnd_3771352 47815217118400834608787 := by
  unfold tailWord_3771352
  simp only [CollatzResearch.WordTrace]
  refine ⟨68776253916521637243818155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91701671888695516325090873 68776253916521637243818155)
  ·
    refine ⟨103164380874782455865727233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68776253916521637243818155 103164380874782455865727233)
    ·
      refine ⟨77373285656086841899295425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103164380874782455865727233 77373285656086841899295425)
      ·
        refine ⟨58029964242065131424471569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77373285656086841899295425 58029964242065131424471569)
        ·
          refine ⟨43522473181548848568353677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58029964242065131424471569 43522473181548848568353677)
          ·
            refine ⟨16320927443080818213132629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43522473181548848568353677 16320927443080818213132629)
            ·
              refine ⟨47815217118400834608787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 16320927443080818213132629 47815217118400834608787)
              ·
                rfl

theorem cell22_3771352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 10].length) (baseStart_3771352 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3771352 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3771352 prefixEnd_3771352 := by exact prefixLift 3771352
  have htrace : WordTrace (prefixWord ++ tailWord_3771352) baseStart_3771352 baseEnd_3771352 := by
    simpa [prefixWord, tailWord_3771352, baseEnd_3771352] using wordTrace_append hprefix tailTrace_3771352
  have hstable : (prefixWord ++ tailWord_3771352).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3771352).length < 2 ^ (prefixWord ++ tailWord_3771352).sum := by decide
  have hdescent : baseEnd_3771352 < baseStart_3771352 := by decide
  rcases family_descends (prefixWord ++ tailWord_3771352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3771354 : List Nat := [3, 1, 1, 2, 4, 1, 1, 1, 4, 4]
def baseStart_3771354 : Nat := 118140960795 + 3771354 * 2 ^ 59
def prefixEnd_3771354 : Nat := 4983230072969 + 3 ^ 40 * 3771354 * 2
def baseEnd_3771354 : Nat := 1291011546837695195887243

theorem tailTrace_3771354 : CollatzResearch.WordTrace tailWord_3771354 prefixEnd_3771354 1291011546837695195887243 := by
  unfold tailWord_3771354
  simp only [CollatzResearch.WordTrace]
  refine ⟨34388145194759007207302279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91701720519357352552806077 34388145194759007207302279)
  ·
    refine ⟨51582217792138510810953419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34388145194759007207302279 51582217792138510810953419)
    ·
      refine ⟨77373326688207766216430129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51582217792138510810953419 77373326688207766216430129)
      ·
        refine ⟨58029995016155824662322597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77373326688207766216430129 58029995016155824662322597)
        ·
          refine ⟨10880624065529217124185487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 58029995016155824662322597 10880624065529217124185487)
          ·
            refine ⟨16320936098293825686278231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10880624065529217124185487 16320936098293825686278231)
            ·
              refine ⟨24481404147440738529417347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16320936098293825686278231 24481404147440738529417347)
              ·
                refine ⟨36722106221161107794126021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24481404147440738529417347 36722106221161107794126021)
                ·
                  refine ⟨6885394916467707711398629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36722106221161107794126021 6885394916467707711398629)
                  ·
                    refine ⟨1291011546837695195887243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6885394916467707711398629 1291011546837695195887243)
                    ·
                      rfl

theorem cell22_3771354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 1, 1, 4, 4].length) (baseStart_3771354 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3771354 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3771354 prefixEnd_3771354 := by exact prefixLift 3771354
  have htrace : WordTrace (prefixWord ++ tailWord_3771354) baseStart_3771354 baseEnd_3771354 := by
    simpa [prefixWord, tailWord_3771354, baseEnd_3771354] using wordTrace_append hprefix tailTrace_3771354
  have hstable : (prefixWord ++ tailWord_3771354).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3771354).length < 2 ^ (prefixWord ++ tailWord_3771354).sum := by decide
  have hdescent : baseEnd_3771354 < baseStart_3771354 := by decide
  rcases family_descends (prefixWord ++ tailWord_3771354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3771384 : List Nat := [2, 1, 2, 1, 1, 3, 1, 3, 5, 3]
def baseStart_3771384 : Nat := 118140960795 + 3771384 * 2 ^ 59
def prefixEnd_3771384 : Nat := 4983230072969 + 3 ^ 40 * 3771384 * 2
def baseEnd_3771384 : Nat := 1291021816450785117637151

theorem tailTrace_3771384 : CollatzResearch.WordTrace tailWord_3771384 prefixEnd_3771384 1291021816450785117637151 := by
  unfold tailWord_3771384
  simp only [CollatzResearch.WordTrace]
  refine ⟨68776837484463671976400603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91702449979284895968534137 68776837484463671976400603)
  ·
    refine ⟨103165256226695507964600905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68776837484463671976400603 103165256226695507964600905)
    ·
      refine ⟨77373942170021630973450679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103165256226695507964600905 77373942170021630973450679)
      ·
        refine ⟨116060913255032446460176019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77373942170021630973450679 116060913255032446460176019)
        ·
          refine ⟨174091369882548669690264029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116060913255032446460176019 174091369882548669690264029)
          ·
            refine ⟨65284263705955751133849011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 174091369882548669690264029 65284263705955751133849011)
            ·
              refine ⟨97926395558933626700773517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65284263705955751133849011 97926395558933626700773517)
              ·
                refine ⟨36722398334600110012790069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 97926395558933626700773517 36722398334600110012790069)
                ·
                  refine ⟨3442724843868760313699069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 36722398334600110012790069 3442724843868760313699069)
                  ·
                    refine ⟨1291021816450785117637151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3442724843868760313699069 1291021816450785117637151)
                    ·
                      rfl

theorem cell22_3771384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 3, 5, 3].length) (baseStart_3771384 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3771384 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3771384 prefixEnd_3771384 := by exact prefixLift 3771384
  have htrace : WordTrace (prefixWord ++ tailWord_3771384) baseStart_3771384 baseEnd_3771384 := by
    simpa [prefixWord, tailWord_3771384, baseEnd_3771384] using wordTrace_append hprefix tailTrace_3771384
  have hstable : (prefixWord ++ tailWord_3771384).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3771384).length < 2 ^ (prefixWord ++ tailWord_3771384).sum := by decide
  have hdescent : baseEnd_3771384 < baseStart_3771384 := by decide
  rcases family_descends (prefixWord ++ tailWord_3771384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3771418 : List Nat := [3, 1, 1, 3, 1, 2, 3, 4, 1, 3]
def baseStart_3771418 : Nat := 118140960795 + 3771418 * 2 ^ 59
def prefixEnd_3771418 : Nat := 4983230072969 + 3 ^ 40 * 3771418 * 2
def baseEnd_3771418 : Nat := 1291033455345620362287047

theorem tailTrace_3771418 : CollatzResearch.WordTrace tailWord_3771418 prefixEnd_3771418 1291033455345620362287047 := by
  unfold tailWord_3771418
  simp only [CollatzResearch.WordTrace]
  refine ⟨34388728762701041939884727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91703276700536111839692605 34388728762701041939884727)
  ·
    refine ⟨51583093144051562909827091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34388728762701041939884727 51583093144051562909827091)
    ·
      refine ⟨77374639716077344364740637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51583093144051562909827091 77374639716077344364740637)
      ·
        refine ⟨29015489893529004136777739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77374639716077344364740637 29015489893529004136777739)
        ·
          refine ⟨43523234840293506205166609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29015489893529004136777739 43523234840293506205166609)
          ·
            refine ⟨32642426130220129653874957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43523234840293506205166609 32642426130220129653874957)
            ·
              refine ⟨12240909798832548620203109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32642426130220129653874957 12240909798832548620203109)
              ·
                refine ⟨2295170587281102866288083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12240909798832548620203109 2295170587281102866288083)
                ·
                  refine ⟨3442755880921654299432125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2295170587281102866288083 3442755880921654299432125)
                  ·
                    refine ⟨1291033455345620362287047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3442755880921654299432125 1291033455345620362287047)
                    ·
                      rfl

theorem cell22_3771418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 3, 4, 1, 3].length) (baseStart_3771418 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3771418 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3771418 prefixEnd_3771418 := by exact prefixLift 3771418
  have htrace : WordTrace (prefixWord ++ tailWord_3771418) baseStart_3771418 baseEnd_3771418 := by
    simpa [prefixWord, tailWord_3771418, baseEnd_3771418] using wordTrace_append hprefix tailTrace_3771418
  have hstable : (prefixWord ++ tailWord_3771418).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3771418).length < 2 ^ (prefixWord ++ tailWord_3771418).sum := by decide
  have hdescent : baseEnd_3771418 < baseStart_3771418 := by decide
  rcases family_descends (prefixWord ++ tailWord_3771418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3771429 : List Nat := [1, 3, 1, 2, 2, 2, 3, 1, 2, 5]
def baseStart_3771429 : Nat := 118140960795 + 3771429 * 2 ^ 59
def prefixEnd_3771429 : Nat := 4983230072969 + 3 ^ 40 * 3771429 * 2
def baseEnd_3771429 : Nat := 1291037220870420000262013

theorem tailTrace_3771429 : CollatzResearch.WordTrace tailWord_3771429 prefixEnd_3771429 1291037220870420000262013 := by
  unfold tailWord_3771429
  simp only [CollatzResearch.WordTrace]
  refine ⟨137555316253764316638189341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91703544169176211092126227 137555316253764316638189341)
  ·
    refine ⟨51583243595161618739321003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137555316253764316638189341 51583243595161618739321003)
    ·
      refine ⟨77374865392742428108981505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51583243595161618739321003 77374865392742428108981505)
      ·
        refine ⟨58031149044556821081736129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77374865392742428108981505 58031149044556821081736129)
        ·
          refine ⟨43523361783417615811302097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58031149044556821081736129 43523361783417615811302097)
          ·
            refine ⟨32642521337563211858476573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43523361783417615811302097 32642521337563211858476573)
            ·
              refine ⟨12240945501586204446928715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32642521337563211858476573 12240945501586204446928715)
              ·
                refine ⟨18361418252379306670393073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12240945501586204446928715 18361418252379306670393073)
                ·
                  refine ⟨13771063689284480002794805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18361418252379306670393073 13771063689284480002794805)
                  ·
                    refine ⟨1291037220870420000262013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13771063689284480002794805 1291037220870420000262013)
                    ·
                      rfl

theorem cell22_3771429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 3, 1, 2, 5].length) (baseStart_3771429 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3771429 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3771429 prefixEnd_3771429 := by exact prefixLift 3771429
  have htrace : WordTrace (prefixWord ++ tailWord_3771429) baseStart_3771429 baseEnd_3771429 := by
    simpa [prefixWord, tailWord_3771429, baseEnd_3771429] using wordTrace_append hprefix tailTrace_3771429
  have hstable : (prefixWord ++ tailWord_3771429).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3771429).length < 2 ^ (prefixWord ++ tailWord_3771429).sum := by decide
  have hdescent : baseEnd_3771429 < baseStart_3771429 := by decide
  rcases family_descends (prefixWord ++ tailWord_3771429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3771489 : List Nat := [1, 2, 3, 1, 1, 2, 3, 2, 1, 6]
def baseStart_3771489 : Nat := 118140960795 + 3771489 * 2 ^ 59
def prefixEnd_3771489 : Nat := 4983230072969 + 3 ^ 40 * 3771489 * 2
def baseEnd_3771489 : Nat := 1291057760096599843761829

theorem tailTrace_3771489 : CollatzResearch.WordTrace tailWord_3771489 prefixEnd_3771489 1291057760096599843761829 := by
  unfold tailWord_3771489
  simp only [CollatzResearch.WordTrace]
  refine ⟨137557504633546946885373521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91705003089031297923582347 137557504633546946885373521)
  ·
    refine ⟨103168128475160210164030141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137557504633546946885373521 103168128475160210164030141)
    ·
      refine ⟨38688048178185078811511303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103168128475160210164030141 38688048178185078811511303)
      ·
        refine ⟨58032072267277618217266955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38688048178185078811511303 58032072267277618217266955)
        ·
          refine ⟨87048108400916427325900433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58032072267277618217266955 87048108400916427325900433)
          ·
            refine ⟨65286081300687320494425325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87048108400916427325900433 65286081300687320494425325)
            ·
              refine ⟨24482280487757745185409497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65286081300687320494425325 24482280487757745185409497)
              ·
                refine ⟨18361710365818308889057123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24482280487757745185409497 18361710365818308889057123)
                ·
                  refine ⟨27542565548727463333585685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18361710365818308889057123 27542565548727463333585685)
                  ·
                    refine ⟨1291057760096599843761829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27542565548727463333585685 1291057760096599843761829)
                    ·
                      rfl

theorem cell22_3771489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 3, 2, 1, 6].length) (baseStart_3771489 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3771489 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3771489 prefixEnd_3771489 := by exact prefixLift 3771489
  have htrace : WordTrace (prefixWord ++ tailWord_3771489) baseStart_3771489 baseEnd_3771489 := by
    simpa [prefixWord, tailWord_3771489, baseEnd_3771489] using wordTrace_append hprefix tailTrace_3771489
  have hstable : (prefixWord ++ tailWord_3771489).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3771489).length < 2 ^ (prefixWord ++ tailWord_3771489).sum := by decide
  have hdescent : baseEnd_3771489 < baseStart_3771489 := by decide
  rcases family_descends (prefixWord ++ tailWord_3771489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3771504 : List Nat := [2, 1, 1, 1, 5, 1, 3, 8]
def baseStart_3771504 : Nat := 118140960795 + 3771504 * 2 ^ 59
def prefixEnd_3771504 : Nat := 4983230072969 + 3 ^ 40 * 3771504 * 2
def baseEnd_3771504 : Nat := 143451432767016089404087

theorem tailTrace_3771504 : CollatzResearch.WordTrace tailWord_3771504 prefixEnd_3771504 143451432767016089404087 := by
  unfold tailWord_3771504
  simp only [CollatzResearch.WordTrace]
  refine ⟨68779025864246302223584783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91705367818995069631446377 68779025864246302223584783)
  ·
    refine ⟨103168538796369453335377175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68779025864246302223584783 103168538796369453335377175)
    ·
      refine ⟨154752808194554180003065763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103168538796369453335377175 154752808194554180003065763)
      ·
        refine ⟨232129212291831270004598645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154752808194554180003065763 232129212291831270004598645)
        ·
          refine ⟨21762113652359181562931123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 232129212291831270004598645 21762113652359181562931123)
          ·
            refine ⟨32643170478538772344396685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21762113652359181562931123 32643170478538772344396685)
            ·
              refine ⟨12241188929452039629148757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32643170478538772344396685 12241188929452039629148757)
              ·
                refine ⟨143451432767016089404087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12241188929452039629148757 143451432767016089404087)
                ·
                  rfl

theorem cell22_3771504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 3, 8].length) (baseStart_3771504 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3771504 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3771504 prefixEnd_3771504 := by exact prefixLift 3771504
  have htrace : WordTrace (prefixWord ++ tailWord_3771504) baseStart_3771504 baseEnd_3771504 := by
    simpa [prefixWord, tailWord_3771504, baseEnd_3771504] using wordTrace_append hprefix tailTrace_3771504
  have hstable : (prefixWord ++ tailWord_3771504).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3771504).length < 2 ^ (prefixWord ++ tailWord_3771504).sum := by decide
  have hdescent : baseEnd_3771504 < baseStart_3771504 := by decide
  rcases family_descends (prefixWord ++ tailWord_3771504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3771506 : List Nat := [3, 2, 1, 2, 2, 1, 2, 3, 2, 4]
def baseStart_3771506 : Nat := 118140960795 + 3771506 * 2 ^ 59
def prefixEnd_3771506 : Nat := 4983230072969 + 3 ^ 40 * 3771506 * 2
def baseEnd_3771506 : Nat := 1291063579544017466086777

theorem tailTrace_3771506 : CollatzResearch.WordTrace tailWord_3771506 prefixEnd_3771506 1291063579544017466086777 := by
  unfold tailWord_3771506
  simp only [CollatzResearch.WordTrace]
  refine ⟨34389531168621339697185593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91705416449656905859161581 34389531168621339697185593)
  ·
    refine ⟨25792148376466004772889195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34389531168621339697185593 25792148376466004772889195)
    ·
      refine ⟨38688222564699007159333793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25792148376466004772889195 38688222564699007159333793)
      ·
        refine ⟨29016166923524255369500345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38688222564699007159333793 29016166923524255369500345)
        ·
          refine ⟨21762125192643191527125259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29016166923524255369500345 21762125192643191527125259)
          ·
            refine ⟨32643187788964787290687889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21762125192643191527125259 32643187788964787290687889)
            ·
              refine ⟨24482390841723590468015917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32643187788964787290687889 24482390841723590468015917)
              ·
                refine ⟨9180896565646346425505969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24482390841723590468015917 9180896565646346425505969)
                ·
                  refine ⟨6885672424234759819129477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9180896565646346425505969 6885672424234759819129477)
                  ·
                    refine ⟨1291063579544017466086777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6885672424234759819129477 1291063579544017466086777)
                    ·
                      rfl

theorem cell22_3771506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 2, 3, 2, 4].length) (baseStart_3771506 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3771506 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3771506 prefixEnd_3771506 := by exact prefixLift 3771506
  have htrace : WordTrace (prefixWord ++ tailWord_3771506) baseStart_3771506 baseEnd_3771506 := by
    simpa [prefixWord, tailWord_3771506, baseEnd_3771506] using wordTrace_append hprefix tailTrace_3771506
  have hstable : (prefixWord ++ tailWord_3771506).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3771506).length < 2 ^ (prefixWord ++ tailWord_3771506).sum := by decide
  have hdescent : baseEnd_3771506 < baseStart_3771506 := by decide
  rcases family_descends (prefixWord ++ tailWord_3771506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3771521 : List Nat := [1, 2, 4, 2, 2, 3, 8]
def baseStart_3771521 : Nat := 118140960795 + 3771521 * 2 ^ 59
def prefixEnd_3771521 : Nat := 4983230072969 + 3 ^ 40 * 3771521 * 2
def baseEnd_3771521 : Nat := 47817359790761571368953

theorem tailTrace_3771521 : CollatzResearch.WordTrace tailWord_3771521 prefixEnd_3771521 47817359790761571368953 := by
  unfold tailWord_3771521
  simp only [CollatzResearch.WordTrace]
  refine ⟨137558671769431016350538417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91705781179620677567025611 137558671769431016350538417)
  ·
    refine ⟨103169003827073262262903813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137558671769431016350538417 103169003827073262262903813)
    ·
      refine ⟨19344188217576236674294465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 103169003827073262262903813 19344188217576236674294465)
      ·
        refine ⟨14508141163182177505720849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19344188217576236674294465 14508141163182177505720849)
        ·
          refine ⟨10881105872386633129290637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14508141163182177505720849 10881105872386633129290637)
          ·
            refine ⟨4080414702144987423483989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10881105872386633129290637 4080414702144987423483989)
            ·
              refine ⟨47817359790761571368953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4080414702144987423483989 47817359790761571368953)
              ·
                rfl

theorem cell22_3771521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 3, 8].length) (baseStart_3771521 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3771521 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3771521 prefixEnd_3771521 := by exact prefixLift 3771521
  have htrace : WordTrace (prefixWord ++ tailWord_3771521) baseStart_3771521 baseEnd_3771521 := by
    simpa [prefixWord, tailWord_3771521, baseEnd_3771521] using wordTrace_append hprefix tailTrace_3771521
  have hstable : (prefixWord ++ tailWord_3771521).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3771521).length < 2 ^ (prefixWord ++ tailWord_3771521).sum := by decide
  have hdescent : baseEnd_3771521 < baseStart_3771521 := by decide
  rcases family_descends (prefixWord ++ tailWord_3771521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3771536 : List Nat := [2, 1, 1, 1, 1, 1, 4, 5, 3, 3]
def baseStart_3771536 : Nat := 118140960795 + 3771536 * 2 ^ 59
def prefixEnd_3771536 : Nat := 4983230072969 + 3 ^ 40 * 3771536 * 2
def baseEnd_3771536 : Nat := 1291073849157107387836685

theorem tailTrace_3771536 : CollatzResearch.WordTrace tailWord_3771536 prefixEnd_3771536 1291073849157107387836685 := by
  unfold tailWord_3771536
  simp only [CollatzResearch.WordTrace]
  refine ⟨68779609432188336956167231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91706145909584449274889641 68779609432188336956167231)
  ·
    refine ⟨103169414148282505434250847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68779609432188336956167231 103169414148282505434250847)
    ·
      refine ⟨154754121222423758151376271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103169414148282505434250847 154754121222423758151376271)
      ·
        refine ⟨232131181833635637227064407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154754121222423758151376271 232131181833635637227064407)
        ·
          refine ⟨348196772750453455840596611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 232131181833635637227064407 348196772750453455840596611)
          ·
            refine ⟨522295159125680183760894917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 348196772750453455840596611 522295159125680183760894917)
            ·
              refine ⟨97930342336065034455167797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 522295159125680183760894917 97930342336065034455167797)
              ·
                refine ⟨9180969594006096980171981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 97930342336065034455167797 9180969594006096980171981)
                ·
                  refine ⟨3442863597752286367564493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9180969594006096980171981 3442863597752286367564493)
                  ·
                    refine ⟨1291073849157107387836685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3442863597752286367564493 1291073849157107387836685)
                    ·
                      rfl

theorem cell22_3771536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 5, 3, 3].length) (baseStart_3771536 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3771536 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3771536 prefixEnd_3771536 := by exact prefixLift 3771536
  have htrace : WordTrace (prefixWord ++ tailWord_3771536) baseStart_3771536 baseEnd_3771536 := by
    simpa [prefixWord, tailWord_3771536, baseEnd_3771536] using wordTrace_append hprefix tailTrace_3771536
  have hstable : (prefixWord ++ tailWord_3771536).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3771536).length < 2 ^ (prefixWord ++ tailWord_3771536).sum := by decide
  have hdescent : baseEnd_3771536 < baseStart_3771536 := by decide
  rcases family_descends (prefixWord ++ tailWord_3771536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3771564 : List Nat := [2, 2, 1, 1, 1, 1, 1, 3, 3, 7]
def baseStart_3771564 : Nat := 118140960795 + 3771564 * 2 ^ 59
def prefixEnd_3771564 : Nat := 4983230072969 + 3 ^ 40 * 3771564 * 2
def baseEnd_3771564 : Nat := 1291083434129324648136599

theorem tailTrace_3771564 : CollatzResearch.WordTrace tailWord_3771564 prefixEnd_3771564 1291083434129324648136599 := by
  unfold tailWord_3771564
  simp only [CollatzResearch.WordTrace]
  refine ⟨68780120054137617347176873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91706826738850156462902497 68780120054137617347176873)
  ·
    refine ⟨51585090040603213010382655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68780120054137617347176873 51585090040603213010382655)
    ·
      refine ⟨77377635060904819515573983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51585090040603213010382655 77377635060904819515573983)
      ·
        refine ⟨116066452591357229273360975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77377635060904819515573983 116066452591357229273360975)
        ·
          refine ⟨174099678887035843910041463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116066452591357229273360975 174099678887035843910041463)
          ·
            refine ⟨261149518330553765865062195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 174099678887035843910041463 261149518330553765865062195)
            ·
              refine ⟨391724277495830648797593293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 261149518330553765865062195 391724277495830648797593293)
              ·
                refine ⟨146896604060936493299097485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 391724277495830648797593293 146896604060936493299097485)
                ·
                  refine ⟨55086226522851184987161557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 146896604060936493299097485 55086226522851184987161557)
                  ·
                    refine ⟨1291083434129324648136599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 55086226522851184987161557 1291083434129324648136599)
                    ·
                      rfl

theorem cell22_3771564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 7].length) (baseStart_3771564 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3771564 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3771564 prefixEnd_3771564 := by exact prefixLift 3771564
  have htrace : WordTrace (prefixWord ++ tailWord_3771564) baseStart_3771564 baseEnd_3771564 := by
    simpa [prefixWord, tailWord_3771564, baseEnd_3771564] using wordTrace_append hprefix tailTrace_3771564
  have hstable : (prefixWord ++ tailWord_3771564).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3771564).length < 2 ^ (prefixWord ++ tailWord_3771564).sum := by decide
  have hdescent : baseEnd_3771564 < baseStart_3771564 := by decide
  rcases family_descends (prefixWord ++ tailWord_3771564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3771598 : List Nat := [4, 1, 1, 1, 5, 1, 1, 1, 2, 5]
def baseStart_3771598 : Nat := 118140960795 + 3771598 * 2 ^ 59
def prefixEnd_3771598 : Nat := 4983230072969 + 3 ^ 40 * 3771598 * 2
def baseEnd_3771598 : Nat := 1291095073024159892786495

theorem tailTrace_3771598 : CollatzResearch.WordTrace tailWord_3771598 prefixEnd_3771598 1291095073024159892786495 := by
  unfold tailWord_3771598
  simp only [CollatzResearch.WordTrace]
  refine ⟨17195185023769007312636431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 91707653460101372334060965 17195185023769007312636431)
  ·
    refine ⟨25792777535653510968954647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17195185023769007312636431 25792777535653510968954647)
    ·
      refine ⟨38689166303480266453431971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25792777535653510968954647 38689166303480266453431971)
      ·
        refine ⟨58033749455220399680147957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38689166303480266453431971 58033749455220399680147957)
        ·
          refine ⟨5440664011426912470013871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 58033749455220399680147957 5440664011426912470013871)
          ·
            refine ⟨8160996017140368705020807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5440664011426912470013871 8160996017140368705020807)
            ·
              refine ⟨12241494025710553057531211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8160996017140368705020807 12241494025710553057531211)
              ·
                refine ⟨18362241038565829586296817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12241494025710553057531211 18362241038565829586296817)
                ·
                  refine ⟨13771680778924372189722613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18362241038565829586296817 13771680778924372189722613)
                  ·
                    refine ⟨1291095073024159892786495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13771680778924372189722613 1291095073024159892786495)
                    ·
                      rfl

theorem cell22_3771598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 1, 1, 2, 5].length) (baseStart_3771598 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3771598 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3771598 prefixEnd_3771598 := by exact prefixLift 3771598
  have htrace : WordTrace (prefixWord ++ tailWord_3771598) baseStart_3771598 baseEnd_3771598 := by
    simpa [prefixWord, tailWord_3771598, baseEnd_3771598] using wordTrace_append hprefix tailTrace_3771598
  have hstable : (prefixWord ++ tailWord_3771598).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3771598).length < 2 ^ (prefixWord ++ tailWord_3771598).sum := by decide
  have hdescent : baseEnd_3771598 < baseStart_3771598 := by decide
  rcases family_descends (prefixWord ++ tailWord_3771598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3771628 : List Nat := [2, 2, 1, 1, 2, 4, 1, 5, 4]
def baseStart_3771628 : Nat := 118140960795 + 3771628 * 2 ^ 59
def prefixEnd_3771628 : Nat := 4983230072969 + 3 ^ 40 * 3771628 * 2
def baseEnd_3771628 : Nat := 430368447545749938178801

theorem tailTrace_3771628 : CollatzResearch.WordTrace tailWord_3771628 prefixEnd_3771628 430368447545749938178801 := by
  unfold tailWord_3771628
  simp only [CollatzResearch.WordTrace]
  refine ⟨68781287190021686812341769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91708382920028915749789025 68781287190021686812341769)
  ·
    refine ⟨51585965392516265109256327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68781287190021686812341769 51585965392516265109256327)
    ·
      refine ⟨77378948088774397663884491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51585965392516265109256327 77378948088774397663884491)
      ·
        refine ⟨116068422133161596495826737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77378948088774397663884491 116068422133161596495826737)
        ·
          refine ⟨87051316599871197371870053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116068422133161596495826737 87051316599871197371870053)
          ·
            refine ⟨16322121862475849507225635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 87051316599871197371870053 16322121862475849507225635)
            ·
              refine ⟨24483182793713774260838453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16322121862475849507225635 24483182793713774260838453)
              ·
                refine ⟨2295298386910666336953605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24483182793713774260838453 2295298386910666336953605)
                ·
                  refine ⟨430368447545749938178801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2295298386910666336953605 430368447545749938178801)
                  ·
                    rfl

theorem cell22_3771628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 1, 5, 4].length) (baseStart_3771628 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3771628 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3771628 prefixEnd_3771628 := by exact prefixLift 3771628
  have htrace : WordTrace (prefixWord ++ tailWord_3771628) baseStart_3771628 baseEnd_3771628 := by
    simpa [prefixWord, tailWord_3771628, baseEnd_3771628] using wordTrace_append hprefix tailTrace_3771628
  have hstable : (prefixWord ++ tailWord_3771628).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3771628).length < 2 ^ (prefixWord ++ tailWord_3771628).sum := by decide
  have hdescent : baseEnd_3771628 < baseStart_3771628 := by decide
  rcases family_descends (prefixWord ++ tailWord_3771628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3771630 : List Nat := [4, 1, 2, 1, 1, 1, 6, 1, 1, 4]
def baseStart_3771630 : Nat := 118140960795 + 3771630 * 2 ^ 59
def prefixEnd_3771630 : Nat := 4983230072969 + 3 ^ 40 * 3771630 * 2
def baseEnd_3771630 : Nat := 1291106027278122475986397

theorem tailTrace_3771630 : CollatzResearch.WordTrace tailWord_3771630 prefixEnd_3771630 1291106027278122475986397 := by
  unfold tailWord_3771630
  simp only [CollatzResearch.WordTrace]
  refine ⟨17195330915754515995782043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 91708431550690751977504229 17195330915754515995782043)
  ·
    refine ⟨25792996373631773993673065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17195330915754515995782043 25792996373631773993673065)
    ·
      refine ⟨19344747280223830495254799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25792996373631773993673065 19344747280223830495254799)
      ·
        refine ⟨29017120920335745742882199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19344747280223830495254799 29017120920335745742882199)
        ·
          refine ⟨43525681380503618614323299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29017120920335745742882199 43525681380503618614323299)
          ·
            refine ⟨65288522070755427921484949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43525681380503618614323299 65288522070755427921484949)
            ·
              refine ⟨3060399472066660683819607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 65288522070755427921484949 3060399472066660683819607)
              ·
                refine ⟨4590599208099991025729411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3060399472066660683819607 4590599208099991025729411)
                ·
                  refine ⟨6885898812149986538594117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4590599208099991025729411 6885898812149986538594117)
                  ·
                    refine ⟨1291106027278122475986397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6885898812149986538594117 1291106027278122475986397)
                    ·
                      rfl

theorem cell22_3771630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 6, 1, 1, 4].length) (baseStart_3771630 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3771630 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3771630 prefixEnd_3771630 := by exact prefixLift 3771630
  have htrace : WordTrace (prefixWord ++ tailWord_3771630) baseStart_3771630 baseEnd_3771630 := by
    simpa [prefixWord, tailWord_3771630, baseEnd_3771630] using wordTrace_append hprefix tailTrace_3771630
  have hstable : (prefixWord ++ tailWord_3771630).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3771630).length < 2 ^ (prefixWord ++ tailWord_3771630).sum := by decide
  have hdescent : baseEnd_3771630 < baseStart_3771630 := by decide
  rcases family_descends (prefixWord ++ tailWord_3771630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3771641 : List Nat := [1, 2, 1, 3, 1, 1, 4, 1, 4, 4]
def baseStart_3771641 : Nat := 118140960795 + 3771641 * 2 ^ 59
def prefixEnd_3771641 : Nat := 4983230072969 + 3 ^ 40 * 3771641 * 2
def baseEnd_3771641 : Nat := 1291109792802922113961363

theorem tailTrace_3771641 : CollatzResearch.WordTrace tailWord_3771641 prefixEnd_3771641 1291109792802922113961363 := by
  unfold tailWord_3771641
  simp only [CollatzResearch.WordTrace]
  refine ⟨137563048528996276844906777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91708699019330851229937851 137563048528996276844906777)
  ·
    refine ⟨103172286396747207633680083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137563048528996276844906777 103172286396747207633680083)
    ·
      refine ⟨154758429595120811450520125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103172286396747207633680083 154758429595120811450520125)
      ·
        refine ⟨58034411098170304293945047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 154758429595120811450520125 58034411098170304293945047)
        ·
          refine ⟨87051616647255456440917571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58034411098170304293945047 87051616647255456440917571)
          ·
            refine ⟨130577424970883184661376357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87051616647255456440917571 130577424970883184661376357)
            ·
              refine ⟨24483267182040597124008067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 130577424970883184661376357 24483267182040597124008067)
              ·
                refine ⟨36724900773060895686012101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24483267182040597124008067 36724900773060895686012101)
                ·
                  refine ⟨6885918894948917941127269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36724900773060895686012101 6885918894948917941127269)
                  ·
                    refine ⟨1291109792802922113961363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6885918894948917941127269 1291109792802922113961363)
                    ·
                      rfl

theorem cell22_3771641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 4, 1, 4, 4].length) (baseStart_3771641 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3771641 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3771641 prefixEnd_3771641 := by exact prefixLift 3771641
  have htrace : WordTrace (prefixWord ++ tailWord_3771641) baseStart_3771641 baseEnd_3771641 := by
    simpa [prefixWord, tailWord_3771641, baseEnd_3771641] using wordTrace_append hprefix tailTrace_3771641
  have hstable : (prefixWord ++ tailWord_3771641).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3771641).length < 2 ^ (prefixWord ++ tailWord_3771641).sum := by decide
  have hdescent : baseEnd_3771641 < baseStart_3771641 := by decide
  rcases family_descends (prefixWord ++ tailWord_3771641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3771671 : List Nat := [1, 1, 3, 4, 1, 1, 1, 1, 2, 7]
def baseStart_3771671 : Nat := 118140960795 + 3771671 * 2 ^ 59
def prefixEnd_3771671 : Nat := 4983230072969 + 3 ^ 40 * 3771671 * 2
def baseEnd_3771671 : Nat := 1291120062416012035711271

theorem tailTrace_3771671 : CollatzResearch.WordTrace tailWord_3771671 prefixEnd_3771671 1291120062416012035711271 := by
  unfold tailWord_3771671
  simp only [CollatzResearch.WordTrace]
  refine ⟨137564142718887591968498867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91709428479258394645665911 137564142718887591968498867)
  ·
    refine ⟨206346214078331387952748301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137564142718887591968498867 206346214078331387952748301)
    ·
      refine ⟨77379830279374270482280613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 206346214078331387952748301 77379830279374270482280613)
      ·
        refine ⟨14508718177382675715427615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 77379830279374270482280613 14508718177382675715427615)
        ·
          refine ⟨21763077266074013573141423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14508718177382675715427615 21763077266074013573141423)
          ·
            refine ⟨32644615899111020359712135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21763077266074013573141423 32644615899111020359712135)
            ·
              refine ⟨48966923848666530539568203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32644615899111020359712135 48966923848666530539568203)
              ·
                refine ⟨73450385772999795809352305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48966923848666530539568203 73450385772999795809352305)
                ·
                  refine ⟨55087789329749846857014229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 73450385772999795809352305 55087789329749846857014229)
                  ·
                    refine ⟨1291120062416012035711271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 55087789329749846857014229 1291120062416012035711271)
                    ·
                      rfl

theorem cell22_3771671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 1, 2, 7].length) (baseStart_3771671 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3771671 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3771671 prefixEnd_3771671 := by exact prefixLift 3771671
  have htrace : WordTrace (prefixWord ++ tailWord_3771671) baseStart_3771671 baseEnd_3771671 := by
    simpa [prefixWord, tailWord_3771671, baseEnd_3771671] using wordTrace_append hprefix tailTrace_3771671
  have hstable : (prefixWord ++ tailWord_3771671).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3771671).length < 2 ^ (prefixWord ++ tailWord_3771671).sum := by decide
  have hdescent : baseEnd_3771671 < baseStart_3771671 := by decide
  rcases family_descends (prefixWord ++ tailWord_3771671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3771829 : List Nat := [1, 3, 3, 2, 2, 2, 3, 1, 2, 3]
def baseStart_3771829 : Nat := 118140960795 + 3771829 * 2 ^ 59
def prefixEnd_3771829 : Nat := 4983230072969 + 3 ^ 40 * 3771829 * 2
def baseEnd_3771829 : Nat := 1291174149044952290260787

theorem tailTrace_3771829 : CollatzResearch.WordTrace tailWord_3771829 prefixEnd_3771829 1291174149044952290260787 := by
  unfold tailWord_3771829
  simp only [CollatzResearch.WordTrace]
  refine ⟨137569905452315184952750541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91713270301543456635167027 137569905452315184952750541)
  ·
    refine ⟨51588714544618194357281453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137569905452315184952750541 51588714544618194357281453)
    ·
      refine ⟨19345767954231822883980545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51588714544618194357281453 19345767954231822883980545)
      ·
        refine ⟨14509325965673867162985409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19345767954231822883980545 14509325965673867162985409)
        ·
          refine ⟨10881994474255400372239057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14509325965673867162985409 10881994474255400372239057)
          ·
            refine ⟨8161495855691550279179293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10881994474255400372239057 8161495855691550279179293)
            ·
              refine ⟨3060560945884331354692235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8161495855691550279179293 3060560945884331354692235)
              ·
                refine ⟨4590841418826497032038353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3060560945884331354692235 4590841418826497032038353)
                ·
                  refine ⟨3443131064119872774028765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4590841418826497032038353 3443131064119872774028765)
                  ·
                    refine ⟨1291174149044952290260787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3443131064119872774028765 1291174149044952290260787)
                    ·
                      rfl

theorem cell22_3771829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 3, 1, 2, 3].length) (baseStart_3771829 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3771829 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3771829 prefixEnd_3771829 := by exact prefixLift 3771829
  have htrace : WordTrace (prefixWord ++ tailWord_3771829) baseStart_3771829 baseEnd_3771829 := by
    simpa [prefixWord, tailWord_3771829, baseEnd_3771829] using wordTrace_append hprefix tailTrace_3771829
  have hstable : (prefixWord ++ tailWord_3771829).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3771829).length < 2 ^ (prefixWord ++ tailWord_3771829).sum := by decide
  have hdescent : baseEnd_3771829 < baseStart_3771829 := by decide
  rcases family_descends (prefixWord ++ tailWord_3771829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3771840 : List Nat := [2, 1, 1, 2, 3, 1, 4, 2, 3, 3]
def baseStart_3771840 : Nat := 118140960795 + 3771840 * 2 ^ 59
def prefixEnd_3771840 : Nat := 4983230072969 + 3 ^ 40 * 3771840 * 2
def baseEnd_3771840 : Nat := 1291177914569751928235753

theorem tailTrace_3771840 : CollatzResearch.WordTrace tailWord_3771840 prefixEnd_3771840 1291177914569751928235753 := by
  unfold tailWord_3771840
  simp only [CollatzResearch.WordTrace]
  refine ⟨68785153327637666915700487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91713537770183555887600649 68785153327637666915700487)
  ·
    refine ⟨103177729991456500373550731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68785153327637666915700487 103177729991456500373550731)
    ·
      refine ⟨154766594987184750560326097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103177729991456500373550731 154766594987184750560326097)
      ·
        refine ⟨116074946240388562920244573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154766594987184750560326097 116074946240388562920244573)
        ·
          refine ⟨43528104840145711095091715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 116074946240388562920244573 43528104840145711095091715)
          ·
            refine ⟨65292157260218566642637573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43528104840145711095091715 65292157260218566642637573)
            ·
              refine ⟨12242279486290981245494545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 65292157260218566642637573 12242279486290981245494545)
              ·
                refine ⟨9181709614718235934120909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12242279486290981245494545 9181709614718235934120909)
                ·
                  refine ⟨3443141105519338475295341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9181709614718235934120909 3443141105519338475295341)
                  ·
                    refine ⟨1291177914569751928235753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3443141105519338475295341 1291177914569751928235753)
                    ·
                      rfl

theorem cell22_3771840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 4, 2, 3, 3].length) (baseStart_3771840 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3771840 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3771840 prefixEnd_3771840 := by exact prefixLift 3771840
  have htrace : WordTrace (prefixWord ++ tailWord_3771840) baseStart_3771840 baseEnd_3771840 := by
    simpa [prefixWord, tailWord_3771840, baseEnd_3771840] using wordTrace_append hprefix tailTrace_3771840
  have hstable : (prefixWord ++ tailWord_3771840).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3771840).length < 2 ^ (prefixWord ++ tailWord_3771840).sum := by decide
  have hdescent : baseEnd_3771840 < baseStart_3771840 := by decide
  rcases family_descends (prefixWord ++ tailWord_3771840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3771898 : List Nat := [3, 1, 1, 1, 1, 2, 4, 1, 8]
def baseStart_3771898 : Nat := 118140960795 + 3771898 * 2 ^ 59
def prefixEnd_3771898 : Nat := 4983230072969 + 3 ^ 40 * 3771898 * 2
def baseEnd_3771898 : Nat := 430399256385019703428525

theorem tailTrace_3771898 : CollatzResearch.WordTrace tailWord_3771898 prefixEnd_3771898 430399256385019703428525 := by
  unfold tailWord_3771898
  simp only [CollatzResearch.WordTrace]
  refine ⟨34393105522266302434253087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91714948059376806491341565 34393105522266302434253087)
  ·
    refine ⟨51589658283399453651379631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34393105522266302434253087 51589658283399453651379631)
    ·
      refine ⟨77384487425099180477069447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51589658283399453651379631 77384487425099180477069447)
      ·
        refine ⟨116076731137648770715604171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77384487425099180477069447 116076731137648770715604171)
        ·
          refine ⟨174115096706473156073406257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116076731137648770715604171 174115096706473156073406257)
          ·
            refine ⟨130586322529854867055054693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 174115096706473156073406257 130586322529854867055054693)
            ·
              refine ⟨24484935474347787572822755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 130586322529854867055054693 24484935474347787572822755)
              ·
                refine ⟨36727403211521681359234133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24484935474347787572822755 36727403211521681359234133)
                ·
                  refine ⟨430399256385019703428525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 36727403211521681359234133 430399256385019703428525)
                  ·
                    rfl

theorem cell22_3771898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 4, 1, 8].length) (baseStart_3771898 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3771898 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3771898 prefixEnd_3771898 := by exact prefixLift 3771898
  have htrace : WordTrace (prefixWord ++ tailWord_3771898) baseStart_3771898 baseEnd_3771898 := by
    simpa [prefixWord, tailWord_3771898, baseEnd_3771898] using wordTrace_append hprefix tailTrace_3771898
  have hstable : (prefixWord ++ tailWord_3771898).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3771898).length < 2 ^ (prefixWord ++ tailWord_3771898).sum := by decide
  have hdescent : baseEnd_3771898 < baseStart_3771898 := by decide
  rcases family_descends (prefixWord ++ tailWord_3771898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3771932 : List Nat := [2, 2, 3, 1, 2, 1, 3, 4, 4]
def baseStart_3771932 : Nat := 118140960795 + 3771932 * 2 ^ 59
def prefixEnd_3771932 : Nat := 4983230072969 + 3 ^ 40 * 3771932 * 2
def baseEnd_3771932 : Nat := 430403136016631451645157

theorem tailTrace_3771932 : CollatzResearch.WordTrace tailWord_3771932 prefixEnd_3771932 430403136016631451645157 := by
  unfold tailWord_3771932
  simp only [CollatzResearch.WordTrace]
  refine ⟨68786831085471016771875025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91715774780628022362500033 68786831085471016771875025)
  ·
    refine ⟨51590123314103262578906269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68786831085471016771875025 51590123314103262578906269)
    ·
      refine ⟨19346296242788723467089851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51590123314103262578906269 19346296242788723467089851)
      ·
        refine ⟨29019444364183085200634777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19346296242788723467089851 29019444364183085200634777)
        ·
          refine ⟨21764583273137313900476083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29019444364183085200634777 21764583273137313900476083)
          ·
            refine ⟨32646874909705970850714125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21764583273137313900476083 32646874909705970850714125)
            ·
              refine ⟨12242578091139739069017797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32646874909705970850714125 12242578091139739069017797)
              ·
                refine ⟨2295483392088701075440837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12242578091139739069017797 2295483392088701075440837)
                ·
                  refine ⟨430403136016631451645157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2295483392088701075440837 430403136016631451645157)
                  ·
                    rfl

theorem cell22_3771932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 3, 4, 4].length) (baseStart_3771932 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3771932 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3771932 prefixEnd_3771932 := by exact prefixLift 3771932
  have htrace : WordTrace (prefixWord ++ tailWord_3771932) baseStart_3771932 baseEnd_3771932 := by
    simpa [prefixWord, tailWord_3771932, baseEnd_3771932] using wordTrace_append hprefix tailTrace_3771932
  have hstable : (prefixWord ++ tailWord_3771932).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3771932).length < 2 ^ (prefixWord ++ tailWord_3771932).sum := by decide
  have hdescent : baseEnd_3771932 < baseStart_3771932 := by decide
  rcases family_descends (prefixWord ++ tailWord_3771932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3772022 : List Nat := [5, 1, 1, 2, 2, 1, 1, 2, 7]
def baseStart_3772022 : Nat := 118140960795 + 3772022 * 2 ^ 59
def prefixEnd_3772022 : Nat := 4983230072969 + 3 ^ 40 * 3772022 * 2
def baseEnd_3772022 : Nat := 430413405629721373395065

theorem tailTrace_3772022 : CollatzResearch.WordTrace tailWord_3772022 prefixEnd_3772022 430413405629721373395065 := by
  unfold tailWord_3772022
  simp only [CollatzResearch.WordTrace]
  refine ⟨8598559046288498682157895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 91717963160410652609684213 8598559046288498682157895)
  ·
    refine ⟨12897838569432748023236843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8598559046288498682157895 12897838569432748023236843)
    ·
      refine ⟨19346757854149122034855265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12897838569432748023236843 19346757854149122034855265)
      ·
        refine ⟨14510068390611841526141449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19346757854149122034855265 14510068390611841526141449)
        ·
          refine ⟨10882551292958881144606087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14510068390611841526141449 10882551292958881144606087)
          ·
            refine ⟨16323826939438321716909131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10882551292958881144606087 16323826939438321716909131)
            ·
              refine ⟨24485740409157482575363697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16323826939438321716909131 24485740409157482575363697)
              ·
                refine ⟨18364305306868111931522773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24485740409157482575363697 18364305306868111931522773)
                ·
                  refine ⟨430413405629721373395065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18364305306868111931522773 430413405629721373395065)
                  ·
                    rfl

theorem cell22_3772022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 1, 2, 7].length) (baseStart_3772022 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3772022 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3772022 prefixEnd_3772022 := by exact prefixLift 3772022
  have htrace : WordTrace (prefixWord ++ tailWord_3772022) baseStart_3772022 baseEnd_3772022 := by
    simpa [prefixWord, tailWord_3772022, baseEnd_3772022] using wordTrace_append hprefix tailTrace_3772022
  have hstable : (prefixWord ++ tailWord_3772022).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3772022).length < 2 ^ (prefixWord ++ tailWord_3772022).sum := by decide
  have hdescent : baseEnd_3772022 < baseStart_3772022 := by decide
  rcases family_descends (prefixWord ++ tailWord_3772022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3772035 : List Nat := [1, 1, 1, 3, 3, 1, 1, 2, 5, 4]
def baseStart_3772035 : Nat := 118140960795 + 3772035 * 2 ^ 59
def prefixEnd_3772035 : Nat := 4983230072969 + 3 ^ 40 * 3772035 * 2
def baseEnd_3772035 : Nat := 1291244667054836419610155

theorem tailTrace_3772035 : CollatzResearch.WordTrace tailWord_3772035 prefixEnd_3772035 1291244667054836419610155 := by
  unfold tailWord_3772035
  simp only [CollatzResearch.WordTrace]
  refine ⟨137577418889568882134749559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91718279259712588089833039 137577418889568882134749559)
  ·
    refine ⟨206366128334353323202124339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137577418889568882134749559 206366128334353323202124339)
    ·
      refine ⟨309549192501529984803186509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206366128334353323202124339 309549192501529984803186509)
      ·
        refine ⟨116080947188073744301194941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 309549192501529984803186509 116080947188073744301194941)
        ·
          refine ⟨43530355195527654112948103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 116080947188073744301194941 43530355195527654112948103)
          ·
            refine ⟨65295532793291481169422155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43530355195527654112948103 65295532793291481169422155)
            ·
              refine ⟨97943299189937221754133233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65295532793291481169422155 97943299189937221754133233)
              ·
                refine ⟨73457474392452916315599925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 97943299189937221754133233 73457474392452916315599925)
                ·
                  refine ⟨6886638224292460904587493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 73457474392452916315599925 6886638224292460904587493)
                  ·
                    refine ⟨1291244667054836419610155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6886638224292460904587493 1291244667054836419610155)
                    ·
                      rfl

theorem cell22_3772035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 2, 5, 4].length) (baseStart_3772035 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3772035 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3772035 prefixEnd_3772035 := by exact prefixLift 3772035
  have htrace : WordTrace (prefixWord ++ tailWord_3772035) baseStart_3772035 baseEnd_3772035 := by
    simpa [prefixWord, tailWord_3772035, baseEnd_3772035] using wordTrace_append hprefix tailTrace_3772035
  have hstable : (prefixWord ++ tailWord_3772035).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3772035).length < 2 ^ (prefixWord ++ tailWord_3772035).sum := by decide
  have hdescent : baseEnd_3772035 < baseStart_3772035 := by decide
  rcases family_descends (prefixWord ++ tailWord_3772035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3772080 : List Nat := [2, 1, 1, 1, 2, 1, 4, 3, 1, 6]
def baseStart_3772080 : Nat := 118140960795 + 3772080 * 2 ^ 59
def prefixEnd_3772080 : Nat := 4983230072969 + 3 ^ 40 * 3772080 * 2
def baseEnd_3772080 : Nat := 1291260071474471302235017

theorem tailTrace_3772080 : CollatzResearch.WordTrace tailWord_3772080 prefixEnd_3772080 1291260071474471302235017 := by
  unfold tailWord_3772080
  simp only [CollatzResearch.WordTrace]
  refine ⟨68789530087202927410068847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91719373449603903213425129 68789530087202927410068847)
  ·
    refine ⟨103184295130804391115103271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68789530087202927410068847 103184295130804391115103271)
    ·
      refine ⟨154776442696206586672654907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103184295130804391115103271 154776442696206586672654907)
      ·
        refine ⟨232164664044309880008982361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154776442696206586672654907 232164664044309880008982361)
        ·
          refine ⟨174123498033232410006736771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 232164664044309880008982361 174123498033232410006736771)
          ·
            refine ⟨261185247049848615010105157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 174123498033232410006736771 261185247049848615010105157)
            ·
              refine ⟨48972233821846615314394717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 261185247049848615010105157 48972233821846615314394717)
              ·
                refine ⟨18364587683192480742898019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48972233821846615314394717 18364587683192480742898019)
                ·
                  refine ⟨27546881524788721114347029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18364587683192480742898019 27546881524788721114347029)
                  ·
                    refine ⟨1291260071474471302235017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27546881524788721114347029 1291260071474471302235017)
                    ·
                      rfl

theorem cell22_3772080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 3, 1, 6].length) (baseStart_3772080 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3772080 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3772080 prefixEnd_3772080 := by exact prefixLift 3772080
  have htrace : WordTrace (prefixWord ++ tailWord_3772080) baseStart_3772080 baseEnd_3772080 := by
    simpa [prefixWord, tailWord_3772080, baseEnd_3772080] using wordTrace_append hprefix tailTrace_3772080
  have hstable : (prefixWord ++ tailWord_3772080).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3772080).length < 2 ^ (prefixWord ++ tailWord_3772080).sum := by decide
  have hdescent : baseEnd_3772080 < baseStart_3772080 := by decide
  rcases family_descends (prefixWord ++ tailWord_3772080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3772082 : List Nat := [3, 2, 1, 1, 1, 2, 2, 1, 6, 3]
def baseStart_3772082 : Nat := 118140960795 + 3772082 * 2 ^ 59
def prefixEnd_3772082 : Nat := 4983230072969 + 3 ^ 40 * 3772082 * 2
def baseEnd_3772082 : Nat := 1291260756115343963685011

theorem tailTrace_3772082 : CollatzResearch.WordTrace tailWord_3772082 prefixEnd_3772082 1291260756115343963685011 := by
  unfold tailWord_3772082
  simp only [CollatzResearch.WordTrace]
  refine ⟨34394783280099652290427625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91719422080265739441140333 34394783280099652290427625)
  ·
    refine ⟨25796087460074739217820719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34394783280099652290427625 25796087460074739217820719)
    ·
      refine ⟨38694131190112108826731079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25796087460074739217820719 38694131190112108826731079)
      ·
        refine ⟨58041196785168163240096619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38694131190112108826731079 58041196785168163240096619)
        ·
          refine ⟨87061795177752244860144929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58041196785168163240096619 87061795177752244860144929)
          ·
            refine ⟨65296346383314183645108697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87061795177752244860144929 65296346383314183645108697)
            ·
              refine ⟨48972259787485637733831523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65296346383314183645108697 48972259787485637733831523)
              ·
                refine ⟨73458389681228456600747285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48972259787485637733831523 73458389681228456600747285)
                ·
                  refine ⟨3443362016307583903160029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 73458389681228456600747285 3443362016307583903160029)
                  ·
                    refine ⟨1291260756115343963685011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3443362016307583903160029 1291260756115343963685011)
                    ·
                      rfl

theorem cell22_3772082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 1, 6, 3].length) (baseStart_3772082 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3772082 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3772082 prefixEnd_3772082 := by exact prefixLift 3772082
  have htrace : WordTrace (prefixWord ++ tailWord_3772082) baseStart_3772082 baseEnd_3772082 := by
    simpa [prefixWord, tailWord_3772082, baseEnd_3772082] using wordTrace_append hprefix tailTrace_3772082
  have hstable : (prefixWord ++ tailWord_3772082).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3772082).length < 2 ^ (prefixWord ++ tailWord_3772082).sum := by decide
  have hdescent : baseEnd_3772082 < baseStart_3772082 := by decide
  rcases family_descends (prefixWord ++ tailWord_3772082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3772116 : List Nat := [2, 4, 1, 3, 1, 1, 2, 3, 2, 3]
def baseStart_3772116 : Nat := 118140960795 + 3772116 * 2 ^ 59
def prefixEnd_3772116 : Nat := 4983230072969 + 3 ^ 40 * 3772116 * 2
def baseEnd_3772116 : Nat := 1291272395010179208334907

theorem tailTrace_3772116 : CollatzResearch.WordTrace tailWord_3772116 prefixEnd_3772116 1291272395010179208334907 := by
  unfold tailWord_3772116
  simp only [CollatzResearch.WordTrace]
  refine ⟨68790186601137716484224101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91720248801516955312298801 68790186601137716484224101)
  ·
    refine ⟨12898159987713321840792019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 68790186601137716484224101 12898159987713321840792019)
    ·
      refine ⟨19347239981569982761188029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12898159987713321840792019 19347239981569982761188029)
      ·
        refine ⟨7255214993088743535445511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19347239981569982761188029 7255214993088743535445511)
        ·
          refine ⟨10882822489633115303168267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7255214993088743535445511 10882822489633115303168267)
          ·
            refine ⟨16324233734449672954752401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10882822489633115303168267 16324233734449672954752401)
            ·
              refine ⟨12243175300837254716064301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16324233734449672954752401 12243175300837254716064301)
              ·
                refine ⟨4591190737813970518524113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12243175300837254716064301 4591190737813970518524113)
                ·
                  refine ⟨3443393053360477888893085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4591190737813970518524113 3443393053360477888893085)
                  ·
                    refine ⟨1291272395010179208334907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3443393053360477888893085 1291272395010179208334907)
                    ·
                      rfl

theorem cell22_3772116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 2, 3, 2, 3].length) (baseStart_3772116 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3772116 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3772116 prefixEnd_3772116 := by exact prefixLift 3772116
  have htrace : WordTrace (prefixWord ++ tailWord_3772116) baseStart_3772116 baseEnd_3772116 := by
    simpa [prefixWord, tailWord_3772116, baseEnd_3772116] using wordTrace_append hprefix tailTrace_3772116
  have hstable : (prefixWord ++ tailWord_3772116).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3772116).length < 2 ^ (prefixWord ++ tailWord_3772116).sum := by decide
  have hdescent : baseEnd_3772116 < baseStart_3772116 := by decide
  rcases family_descends (prefixWord ++ tailWord_3772116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3772129 : List Nat := [1, 2, 3, 1, 5, 1, 3, 6]
def baseStart_3772129 : Nat := 118140960795 + 3772129 * 2 ^ 59
def prefixEnd_3772129 : Nat := 4983230072969 + 3 ^ 40 * 3772129 * 2
def baseEnd_3772129 : Nat := 143475205019539056417763

theorem tailTrace_3772129 : CollatzResearch.WordTrace tailWord_3772129 prefixEnd_3772129 143475205019539056417763 := by
  unfold tailWord_3772129
  simp only [CollatzResearch.WordTrace]
  refine ⟨137580847351228336188671441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91720564900818890792447627 137580847351228336188671441)
  ·
    refine ⟨103185635513421252141503581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137580847351228336188671441 103185635513421252141503581)
    ·
      refine ⟨38694613317532969553063843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103185635513421252141503581 38694613317532969553063843)
      ·
        refine ⟨58041919976299454329595765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38694613317532969553063843 58041919976299454329595765)
        ·
          refine ⟨5441429997778073843399603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 58041919976299454329595765 5441429997778073843399603)
          ·
            refine ⟨8162144996667110765099405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5441429997778073843399603 8162144996667110765099405)
            ·
              refine ⟨3060804373750166536912277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8162144996667110765099405 3060804373750166536912277)
              ·
                refine ⟨143475205019539056417763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3060804373750166536912277 143475205019539056417763)
                ·
                  rfl

theorem cell22_3772129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 3, 6].length) (baseStart_3772129 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3772129 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3772129 prefixEnd_3772129 := by exact prefixLift 3772129
  have htrace : WordTrace (prefixWord ++ tailWord_3772129) baseStart_3772129 baseEnd_3772129 := by
    simpa [prefixWord, tailWord_3772129, baseEnd_3772129] using wordTrace_append hprefix tailTrace_3772129
  have hstable : (prefixWord ++ tailWord_3772129).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3772129).length < 2 ^ (prefixWord ++ tailWord_3772129).sum := by decide
  have hdescent : baseEnd_3772129 < baseStart_3772129 := by decide
  rcases family_descends (prefixWord ++ tailWord_3772129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3772131 : List Nat := [1, 1, 1, 7, 2, 2, 1, 1, 2, 4]
def baseStart_3772131 : Nat := 118140960795 + 3772131 * 2 ^ 59
def prefixEnd_3772131 : Nat := 4983230072969 + 3 ^ 40 * 3772131 * 2
def baseEnd_3772131 : Nat := 1291277529816724169209861

theorem tailTrace_3772131 : CollatzResearch.WordTrace tailWord_3772131 prefixEnd_3772131 1291277529816724169209861 := by
  unfold tailWord_3772131
  simp only [CollatzResearch.WordTrace]
  refine ⟨137580920297221090530244247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91720613531480727020162831 137580920297221090530244247)
  ·
    refine ⟨206371380445831635795366371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137580920297221090530244247 206371380445831635795366371)
    ·
      refine ⟨309557070668747453693049557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206371380445831635795366371 309557070668747453693049557)
      ·
        refine ⟨7255243843798768445930849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 309557070668747453693049557 7255243843798768445930849)
        ·
          refine ⟨5441432882849076334448137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7255243843798768445930849 5441432882849076334448137)
          ·
            refine ⟨4081074662136807250836103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5441432882849076334448137 4081074662136807250836103)
            ·
              refine ⟨6121611993205210876254155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4081074662136807250836103 6121611993205210876254155)
              ·
                refine ⟨9182417989807816314381233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6121611993205210876254155 9182417989807816314381233)
                ·
                  refine ⟨6886813492355862235785925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9182417989807816314381233 6886813492355862235785925)
                  ·
                    refine ⟨1291277529816724169209861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6886813492355862235785925 1291277529816724169209861)
                    ·
                      rfl

theorem cell22_3772131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 2, 1, 1, 2, 4].length) (baseStart_3772131 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3772131 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3772131 prefixEnd_3772131 := by exact prefixLift 3772131
  have htrace : WordTrace (prefixWord ++ tailWord_3772131) baseStart_3772131 baseEnd_3772131 := by
    simpa [prefixWord, tailWord_3772131, baseEnd_3772131] using wordTrace_append hprefix tailTrace_3772131
  have hstable : (prefixWord ++ tailWord_3772131).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3772131).length < 2 ^ (prefixWord ++ tailWord_3772131).sum := by decide
  have hdescent : baseEnd_3772131 < baseStart_3772131 := by decide
  rcases family_descends (prefixWord ++ tailWord_3772131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3772157 : List Nat := [1, 4, 1, 1, 1, 1, 2, 6, 5]
def baseStart_3772157 : Nat := 118140960795 + 3772157 * 2 ^ 59
def prefixEnd_3772157 : Nat := 4983230072969 + 3 ^ 40 * 3772157 * 2
def baseEnd_3772157 : Nat := 430428810049356256019927

theorem tailTrace_3772157 : CollatzResearch.WordTrace tailWord_3772157 prefixEnd_3772157 430428810049356256019927 := by
  unfold tailWord_3772157
  simp only [CollatzResearch.WordTrace]
  refine ⟨137581868595126896970690725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91721245730084597980460483 137581868595126896970690725)
  ·
    refine ⟨25796600361586293182004511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 137581868595126896970690725 25796600361586293182004511)
    ·
      refine ⟨38694900542379439773006767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25796600361586293182004511 38694900542379439773006767)
      ·
        refine ⟨58042350813569159659510151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38694900542379439773006767 58042350813569159659510151)
        ·
          refine ⟨87063526220353739489265227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58042350813569159659510151 87063526220353739489265227)
          ·
            refine ⟨130595289330530609233897841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87063526220353739489265227 130595289330530609233897841)
            ·
              refine ⟨97946466997897956925423381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 130595289330530609233897841 97946466997897956925423381)
              ·
                refine ⟨4591240640526466730879221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 97946466997897956925423381 4591240640526466730879221)
                ·
                  refine ⟨430428810049356256019927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4591240640526466730879221 430428810049356256019927)
                  ·
                    rfl

theorem cell22_3772157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 6, 5].length) (baseStart_3772157 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3772157 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3772157 prefixEnd_3772157 := by exact prefixLift 3772157
  have htrace : WordTrace (prefixWord ++ tailWord_3772157) baseStart_3772157 baseEnd_3772157 := by
    simpa [prefixWord, tailWord_3772157, baseEnd_3772157] using wordTrace_append hprefix tailTrace_3772157
  have hstable : (prefixWord ++ tailWord_3772157).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3772157).length < 2 ^ (prefixWord ++ tailWord_3772157).sum := by decide
  have hdescent : baseEnd_3772157 < baseStart_3772157 := by decide
  rcases family_descends (prefixWord ++ tailWord_3772157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3772161 : List Nat := [1, 2, 4, 1, 1, 1, 4, 4, 1, 3]
def baseStart_3772161 : Nat := 118140960795 + 3772161 * 2 ^ 59
def prefixEnd_3772161 : Nat := 4983230072969 + 3 ^ 40 * 3772161 * 2
def baseEnd_3772161 : Nat := 1291287799429814090959769

theorem tailTrace_3772161 : CollatzResearch.WordTrace tailWord_3772161 prefixEnd_3772161 1291287799429814090959769 := by
  unfold tailWord_3772161
  simp only [CollatzResearch.WordTrace]
  refine ⟨137582014487112405653836337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91721342991408270435890891 137582014487112405653836337)
  ·
    refine ⟨103186510865334304240377253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137582014487112405653836337 103186510865334304240377253)
    ·
      refine ⟨19347470787250182045070735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 103186510865334304240377253 19347470787250182045070735)
      ·
        refine ⟨29021206180875273067606103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19347470787250182045070735 29021206180875273067606103)
        ·
          refine ⟨43531809271312909601409155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29021206180875273067606103 43531809271312909601409155)
          ·
            refine ⟨65297713906969364402113733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43531809271312909601409155 65297713906969364402113733)
            ·
              refine ⟨12243321357556755825396325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 65297713906969364402113733 12243321357556755825396325)
              ·
                refine ⟨2295622754541891717261811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12243321357556755825396325 2295622754541891717261811)
                ·
                  refine ⟨3443434131812837575892717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2295622754541891717261811 3443434131812837575892717)
                  ·
                    refine ⟨1291287799429814090959769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3443434131812837575892717 1291287799429814090959769)
                    ·
                      rfl

theorem cell22_3772161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 4, 4, 1, 3].length) (baseStart_3772161 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3772161 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3772161 prefixEnd_3772161 := by exact prefixLift 3772161
  have htrace : WordTrace (prefixWord ++ tailWord_3772161) baseStart_3772161 baseEnd_3772161 := by
    simpa [prefixWord, tailWord_3772161, baseEnd_3772161] using wordTrace_append hprefix tailTrace_3772161
  have hstable : (prefixWord ++ tailWord_3772161).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3772161).length < 2 ^ (prefixWord ++ tailWord_3772161).sum := by decide
  have hdescent : baseEnd_3772161 < baseStart_3772161 := by decide
  rcases family_descends (prefixWord ++ tailWord_3772161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3772172 : List Nat := [2, 2, 1, 2, 2, 1, 4, 1, 2, 5]
def baseStart_3772172 : Nat := 118140960795 + 3772172 * 2 ^ 59
def prefixEnd_3772172 : Nat := 4983230072969 + 3 ^ 40 * 3772172 * 2
def baseEnd_3772172 : Nat := 1291291564954613728934735

theorem tailTrace_3772172 : CollatzResearch.WordTrace tailWord_3772172 prefixEnd_3772172 1291291564954613728934735 := by
  unfold tailWord_3772172
  simp only [CollatzResearch.WordTrace]
  refine ⟨68791207845036277266243385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91721610460048369688324513 68791207845036277266243385)
  ·
    refine ⟨51593405883777207949682539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68791207845036277266243385 51593405883777207949682539)
    ·
      refine ⟨77390108825665811924523809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51593405883777207949682539 77390108825665811924523809)
      ·
        refine ⟨58042581619249358943392857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77390108825665811924523809 58042581619249358943392857)
        ·
          refine ⟨43531936214437019207544643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58042581619249358943392857 43531936214437019207544643)
          ·
            refine ⟨65297904321655528811316965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43531936214437019207544643 65297904321655528811316965)
            ·
              refine ⟨12243357060310411652121931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 65297904321655528811316965 12243357060310411652121931)
              ·
                refine ⟨18365035590465617478182897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12243357060310411652121931 18365035590465617478182897)
                ·
                  refine ⟨13773776692849213108637173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18365035590465617478182897 13773776692849213108637173)
                  ·
                    refine ⟨1291291564954613728934735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13773776692849213108637173 1291291564954613728934735)
                    ·
                      rfl

theorem cell22_3772172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 4, 1, 2, 5].length) (baseStart_3772172 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3772172 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3772172 prefixEnd_3772172 := by exact prefixLift 3772172
  have htrace : WordTrace (prefixWord ++ tailWord_3772172) baseStart_3772172 baseEnd_3772172 := by
    simpa [prefixWord, tailWord_3772172, baseEnd_3772172] using wordTrace_append hprefix tailTrace_3772172
  have hstable : (prefixWord ++ tailWord_3772172).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3772172).length < 2 ^ (prefixWord ++ tailWord_3772172).sum := by decide
  have hdescent : baseEnd_3772172 < baseStart_3772172 := by decide
  rcases family_descends (prefixWord ++ tailWord_3772172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3772180 : List Nat := [2, 4, 4, 1, 1, 2, 2, 6]
def baseStart_3772180 : Nat := 118140960795 + 3772180 * 2 ^ 59
def prefixEnd_3772180 : Nat := 4983230072969 + 3 ^ 40 * 3772180 * 2
def baseEnd_3772180 : Nat := 143477144835344930526079

theorem tailTrace_3772180 : CollatzResearch.WordTrace tailWord_3772180 prefixEnd_3772180 143477144835344930526079 := by
  unfold tailWord_3772180
  simp only [CollatzResearch.WordTrace]
  refine ⟨68791353737021785949388997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91721804982695714599185329 68791353737021785949388997)
  ·
    refine ⟨12898378825691584865510437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 68791353737021785949388997 12898378825691584865510437)
    ·
      refine ⟨2418446029817172162283207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12898378825691584865510437 2418446029817172162283207)
      ·
        refine ⟨3627669044725758243424811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2418446029817172162283207 3627669044725758243424811)
        ·
          refine ⟨5441503567088637365137217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3627669044725758243424811 5441503567088637365137217)
          ·
            refine ⟨4081127675316478023852913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5441503567088637365137217 4081127675316478023852913)
            ·
              refine ⟨3060845756487358517889685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4081127675316478023852913 3060845756487358517889685)
              ·
                refine ⟨143477144835344930526079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3060845756487358517889685 143477144835344930526079)
                ·
                  rfl

theorem cell22_3772180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 2, 2, 6].length) (baseStart_3772180 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3772180 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3772180 prefixEnd_3772180 := by exact prefixLift 3772180
  have htrace : WordTrace (prefixWord ++ tailWord_3772180) baseStart_3772180 baseEnd_3772180 := by
    simpa [prefixWord, tailWord_3772180, baseEnd_3772180] using wordTrace_append hprefix tailTrace_3772180
  have hstable : (prefixWord ++ tailWord_3772180).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3772180).length < 2 ^ (prefixWord ++ tailWord_3772180).sum := by decide
  have hdescent : baseEnd_3772180 < baseStart_3772180 := by decide
  rcases family_descends (prefixWord ++ tailWord_3772180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3772204 : List Nat := [2, 2, 1, 1, 1, 5, 2, 3, 1, 4]
def baseStart_3772204 : Nat := 118140960795 + 3772204 * 2 ^ 59
def prefixEnd_3772204 : Nat := 4983230072969 + 3 ^ 40 * 3772204 * 2
def baseEnd_3772204 : Nat := 1291302519208576312134637

theorem tailTrace_3772204 : CollatzResearch.WordTrace tailWord_3772204 prefixEnd_3772204 1291302519208576312134637 := by
  unfold tailWord_3772204
  simp only [CollatzResearch.WordTrace]
  refine ⟨68791791412978311998825833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91722388550637749331767777 68791791412978311998825833)
  ·
    refine ⟨51593843559733733999119375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68791791412978311998825833 51593843559733733999119375)
    ·
      refine ⟨77390765339600600998679063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51593843559733733999119375 77390765339600600998679063)
      ·
        refine ⟨116086148009400901498018595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77390765339600600998679063 116086148009400901498018595)
        ·
          refine ⟨174129222014101352247027893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116086148009400901498018595 174129222014101352247027893)
          ·
            refine ⟨16324614563822001773158865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 174129222014101352247027893 16324614563822001773158865)
            ·
              refine ⟨12243460922866501329869149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16324614563822001773158865 12243460922866501329869149)
              ·
                refine ⟨4591297846074937998700931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12243460922866501329869149 4591297846074937998700931)
                ·
                  refine ⟨6886946769112406998051397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4591297846074937998700931 6886946769112406998051397)
                  ·
                    refine ⟨1291302519208576312134637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6886946769112406998051397 1291302519208576312134637)
                    ·
                      rfl

theorem cell22_3772204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 4].length) (baseStart_3772204 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3772204 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3772204 prefixEnd_3772204 := by exact prefixLift 3772204
  have htrace : WordTrace (prefixWord ++ tailWord_3772204) baseStart_3772204 baseEnd_3772204 := by
    simpa [prefixWord, tailWord_3772204, baseEnd_3772204] using wordTrace_append hprefix tailTrace_3772204
  have hstable : (prefixWord ++ tailWord_3772204).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3772204).length < 2 ^ (prefixWord ++ tailWord_3772204).sum := by decide
  have hdescent : baseEnd_3772204 < baseStart_3772204 := by decide
  rcases family_descends (prefixWord ++ tailWord_3772204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3772249 : List Nat := [1, 2, 1, 2, 2, 3, 4, 1, 2, 4]
def baseStart_3772249 : Nat := 118140960795 + 3772249 * 2 ^ 59
def prefixEnd_3772249 : Nat := 4983230072969 + 3 ^ 40 * 3772249 * 2
def baseEnd_3772249 : Nat := 1291317923628211194759499

theorem tailTrace_3772249 : CollatzResearch.WordTrace tailWord_3772249 prefixEnd_3772249 1291317923628211194759499 := by
  unfold tailWord_3772249
  simp only [CollatzResearch.WordTrace]
  refine ⟨137585224110793596683039801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91723482740529064455359867 137585224110793596683039801)
  ·
    refine ⟨103188918083095197512279851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137585224110793596683039801 103188918083095197512279851)
    ·
      refine ⟨154783377124642796268419777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103188918083095197512279851 154783377124642796268419777)
      ·
        refine ⟨116087532843482097201314833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154783377124642796268419777 116087532843482097201314833)
        ·
          refine ⟨87065649632611572900986125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116087532843482097201314833 87065649632611572900986125)
          ·
            refine ⟨32649618612229339837869797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87065649632611572900986125 32649618612229339837869797)
            ·
              refine ⟨6121803489793001219600587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32649618612229339837869797 6121803489793001219600587)
              ·
                refine ⟨9182705234689501829400881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6121803489793001219600587 9182705234689501829400881)
                ·
                  refine ⟨6887028926017126372050661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9182705234689501829400881 6887028926017126372050661)
                  ·
                    refine ⟨1291317923628211194759499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6887028926017126372050661 1291317923628211194759499)
                    ·
                      rfl

theorem cell22_3772249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 4, 1, 2, 4].length) (baseStart_3772249 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3772249 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3772249 prefixEnd_3772249 := by exact prefixLift 3772249
  have htrace : WordTrace (prefixWord ++ tailWord_3772249) baseStart_3772249 baseEnd_3772249 := by
    simpa [prefixWord, tailWord_3772249, baseEnd_3772249] using wordTrace_append hprefix tailTrace_3772249
  have hstable : (prefixWord ++ tailWord_3772249).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3772249).length < 2 ^ (prefixWord ++ tailWord_3772249).sum := by decide
  have hdescent : baseEnd_3772249 < baseStart_3772249 := by decide
  rcases family_descends (prefixWord ++ tailWord_3772249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3772270 : List Nat := [4, 1, 2, 3, 1, 3, 2, 2, 4]
def baseStart_3772270 : Nat := 118140960795 + 3772270 * 2 ^ 59
def prefixEnd_3772270 : Nat := 4983230072969 + 3 ^ 40 * 3772270 * 2
def baseEnd_3772270 : Nat := 430441704119124713328145

theorem tailTrace_3772270 : CollatzResearch.WordTrace tailWord_3772270 prefixEnd_3772270 430441704119124713328145 := by
  unfold tailWord_3772270
  simp only [CollatzResearch.WordTrace]
  refine ⟨17198248755464689658694283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 91723993362478344846369509 17198248755464689658694283)
  ·
    refine ⟨25797373133197034488041425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17198248755464689658694283 25797373133197034488041425)
    ·
      refine ⟨19348029849897775866031069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25797373133197034488041425 19348029849897775866031069)
      ·
        refine ⟨7255511193711665949761651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19348029849897775866031069 7255511193711665949761651)
        ·
          refine ⟨10883266790567498924642477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7255511193711665949761651 10883266790567498924642477)
          ·
            refine ⟨4081225046462812096740929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10883266790567498924642477 4081225046462812096740929)
            ·
              refine ⟨3060918784847109072555697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4081225046462812096740929 3060918784847109072555697)
              ·
                refine ⟨2295689088635331804416773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3060918784847109072555697 2295689088635331804416773)
                ·
                  refine ⟨430441704119124713328145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2295689088635331804416773 430441704119124713328145)
                  ·
                    rfl

theorem cell22_3772270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 3, 2, 2, 4].length) (baseStart_3772270 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3772270 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3772270 prefixEnd_3772270 := by exact prefixLift 3772270
  have htrace : WordTrace (prefixWord ++ tailWord_3772270) baseStart_3772270 baseEnd_3772270 := by
    simpa [prefixWord, tailWord_3772270, baseEnd_3772270] using wordTrace_append hprefix tailTrace_3772270
  have hstable : (prefixWord ++ tailWord_3772270).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3772270).length < 2 ^ (prefixWord ++ tailWord_3772270).sum := by decide
  have hdescent : baseEnd_3772270 < baseStart_3772270 := by decide
  rcases family_descends (prefixWord ++ tailWord_3772270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3772324 : List Nat := [2, 3, 1, 2, 1, 3, 1, 2, 2, 5]
def baseStart_3772324 : Nat := 118140960795 + 3772324 * 2 ^ 59
def prefixEnd_3772324 : Nat := 4983230072969 + 3 ^ 40 * 3772324 * 2
def baseEnd_3772324 : Nat := 1291343597660935999134269

theorem tailTrace_3772324 : CollatzResearch.WordTrace tailWord_3772324 prefixEnd_3772324 1291343597660935999134269 := by
  unfold tailWord_3772324
  simp only [CollatzResearch.WordTrace]
  refine ⟨68793979792760942246010013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91725306390347922994680017 68793979792760942246010013)
  ·
    refine ⟨25797742422285353342253755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68793979792760942246010013 25797742422285353342253755)
    ·
      refine ⟨38696613633428030013380633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25797742422285353342253755 38696613633428030013380633)
      ·
        refine ⟨29022460225071022510035475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38696613633428030013380633 29022460225071022510035475)
        ·
          refine ⟨43533690337606533765053213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29022460225071022510035475 43533690337606533765053213)
          ·
            refine ⟨16325133876602450161894955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43533690337606533765053213 16325133876602450161894955)
            ·
              refine ⟨24487700814903675242842433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16325133876602450161894955 24487700814903675242842433)
              ·
                refine ⟨18365775611177756432131825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24487700814903675242842433 18365775611177756432131825)
                ·
                  refine ⟨13774331708383317324098869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18365775611177756432131825 13774331708383317324098869)
                  ·
                    refine ⟨1291343597660935999134269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13774331708383317324098869 1291343597660935999134269)
                    ·
                      rfl

theorem cell22_3772324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 1, 2, 2, 5].length) (baseStart_3772324 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3772324 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3772324 prefixEnd_3772324 := by exact prefixLift 3772324
  have htrace : WordTrace (prefixWord ++ tailWord_3772324) baseStart_3772324 baseEnd_3772324 := by
    simpa [prefixWord, tailWord_3772324, baseEnd_3772324] using wordTrace_append hprefix tailTrace_3772324
  have hstable : (prefixWord ++ tailWord_3772324).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3772324).length < 2 ^ (prefixWord ++ tailWord_3772324).sum := by decide
  have hdescent : baseEnd_3772324 < baseStart_3772324 := by decide
  rcases family_descends (prefixWord ++ tailWord_3772324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3772388 : List Nat := [2, 3, 1, 1, 1, 1, 7, 2, 4]
def baseStart_3772388 : Nat := 118140960795 + 3772388 * 2 ^ 59
def prefixEnd_3772388 : Nat := 4983230072969 + 3 ^ 40 * 3772388 * 2
def baseEnd_3772388 : Nat := 430455168722953721844691

theorem tailTrace_3772388 : CollatzResearch.WordTrace tailWord_3772388 prefixEnd_3772388 430455168722953721844691 := by
  unfold tailWord_3772388
  simp only [CollatzResearch.WordTrace]
  refine ⟨68795146928645011711174909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91726862571526682281566545 68795146928645011711174909)
  ·
    refine ⟨25798180098241879391690591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68795146928645011711174909 25798180098241879391690591)
    ·
      refine ⟨38697270147362819087535887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25798180098241879391690591 38697270147362819087535887)
      ·
        refine ⟨58045905221044228631303831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38697270147362819087535887 58045905221044228631303831)
        ·
          refine ⟨87068857831566342946955747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58045905221044228631303831 87068857831566342946955747)
          ·
            refine ⟨130603286747349514420433621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87068857831566342946955747 130603286747349514420433621)
            ·
              refine ⟨3061014533141004244228913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 130603286747349514420433621 3061014533141004244228913)
              ·
                refine ⟨2295760899855753183171685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3061014533141004244228913 2295760899855753183171685)
                ·
                  refine ⟨430455168722953721844691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2295760899855753183171685 430455168722953721844691)
                  ·
                    rfl

theorem cell22_3772388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 7, 2, 4].length) (baseStart_3772388 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3772388 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3772388 prefixEnd_3772388 := by exact prefixLift 3772388
  have htrace : WordTrace (prefixWord ++ tailWord_3772388) baseStart_3772388 baseEnd_3772388 := by
    simpa [prefixWord, tailWord_3772388, baseEnd_3772388] using wordTrace_append hprefix tailTrace_3772388
  have hstable : (prefixWord ++ tailWord_3772388).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3772388).length < 2 ^ (prefixWord ++ tailWord_3772388).sum := by decide
  have hdescent : baseEnd_3772388 < baseStart_3772388 := by decide
  rcases family_descends (prefixWord ++ tailWord_3772388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3772399 : List Nat := [1, 1, 2, 1, 4, 2, 4, 7]
def baseStart_3772399 : Nat := 118140960795 + 3772399 * 2 ^ 59
def prefixEnd_3772399 : Nat := 4983230072969 + 3 ^ 40 * 3772399 * 2
def baseEnd_3772399 : Nat := 143485474632628978167671

theorem tailTrace_3772399 : CollatzResearch.WordTrace tailWord_3772399 prefixEnd_3772399 143485474632628978167671 := by
  unfold tailWord_3772399
  simp only [CollatzResearch.WordTrace]
  refine ⟨137590695060250172301000251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91727130040166781534000167 137590695060250172301000251)
  ·
    refine ⟨206386042590375258451500377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137590695060250172301000251 206386042590375258451500377)
    ·
      refine ⟨154789531942781443838625283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 206386042590375258451500377 154789531942781443838625283)
      ·
        refine ⟨232184297914172165757937925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154789531942781443838625283 232184297914172165757937925)
        ·
          refine ⟨43534555858907281079613361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 232184297914172165757937925 43534555858907281079613361)
          ·
            refine ⟨32650916894180460809710021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43534555858907281079613361 32650916894180460809710021)
            ·
              refine ⟨6122046917658836401820629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32650916894180460809710021 6122046917658836401820629)
              ·
                refine ⟨143485474632628978167671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6122046917658836401820629 143485474632628978167671)
                ·
                  rfl

theorem cell22_3772399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 4, 7].length) (baseStart_3772399 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3772399 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3772399 prefixEnd_3772399 := by exact prefixLift 3772399
  have htrace : WordTrace (prefixWord ++ tailWord_3772399) baseStart_3772399 baseEnd_3772399 := by
    simpa [prefixWord, tailWord_3772399, baseEnd_3772399] using wordTrace_append hprefix tailTrace_3772399
  have hstable : (prefixWord ++ tailWord_3772399).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3772399).length < 2 ^ (prefixWord ++ tailWord_3772399).sum := by decide
  have hdescent : baseEnd_3772399 < baseStart_3772399 := by decide
  rcases family_descends (prefixWord ++ tailWord_3772399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3772489 : List Nat := [1, 2, 1, 1, 2, 2, 3, 2, 8]
def baseStart_3772489 : Nat := 118140960795 + 3772489 * 2 ^ 59
def prefixEnd_3772489 : Nat := 4983230072969 + 3 ^ 40 * 3772489 * 2
def baseEnd_3772489 : Nat := 430466693510976856252921

theorem tailTrace_3772489 : CollatzResearch.WordTrace tailWord_3772489 prefixEnd_3772489 430466693510976856252921 := by
  unfold tailWord_3772489
  simp only [CollatzResearch.WordTrace]
  refine ⟨137593977629924117671776521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91729318419949411781184347 137593977629924117671776521)
  ·
    refine ⟨103195483222443088253832391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137593977629924117671776521 103195483222443088253832391)
    ·
      refine ⟨154793224833664632380748587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103195483222443088253832391 154793224833664632380748587)
      ·
        refine ⟨232189837250496948571122881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154793224833664632380748587 232189837250496948571122881)
        ·
          refine ⟨174142377937872711428342161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 232189837250496948571122881 174142377937872711428342161)
          ·
            refine ⟨130606783453404533571256621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 174142377937872711428342161 130606783453404533571256621)
            ·
              refine ⟨48977543795026700089221233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 130606783453404533571256621 48977543795026700089221233)
              ·
                refine ⟨36733157846270025066915925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48977543795026700089221233 36733157846270025066915925)
                ·
                  refine ⟨430466693510976856252921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 36733157846270025066915925 430466693510976856252921)
                  ·
                    rfl

theorem cell22_3772489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 2, 8].length) (baseStart_3772489 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3772489 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3772489 prefixEnd_3772489 := by exact prefixLift 3772489
  have htrace : WordTrace (prefixWord ++ tailWord_3772489) baseStart_3772489 baseEnd_3772489 := by
    simpa [prefixWord, tailWord_3772489, baseEnd_3772489] using wordTrace_append hprefix tailTrace_3772489
  have hstable : (prefixWord ++ tailWord_3772489).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3772489).length < 2 ^ (prefixWord ++ tailWord_3772489).sum := by decide
  have hdescent : baseEnd_3772489 < baseStart_3772489 := by decide
  rcases family_descends (prefixWord ++ tailWord_3772489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3772491 : List Nat := [1, 1, 1, 1, 3, 1, 2, 7, 1, 4]
def baseStart_3772491 : Nat := 118140960795 + 3772491 * 2 ^ 59
def prefixEnd_3772491 : Nat := 4983230072969 + 3 ^ 40 * 3772491 * 2
def baseEnd_3772491 : Nat := 1291400765173803230208757

theorem tailTrace_3772491 : CollatzResearch.WordTrace tailWord_3772491 prefixEnd_3772491 1291400765173803230208757 := by
  unfold tailWord_3772491
  simp only [CollatzResearch.WordTrace]
  refine ⟨137594050575916872013349327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91729367050611248008899551 137594050575916872013349327)
  ·
    refine ⟨206391075863875308020023991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137594050575916872013349327 206391075863875308020023991)
    ·
      refine ⟨309586613795812962030035987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206391075863875308020023991 309586613795812962030035987)
      ·
        refine ⟨464379920693719443045053981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 309586613795812962030035987 464379920693719443045053981)
        ·
          refine ⟨174142470260144791141895243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 464379920693719443045053981 174142470260144791141895243)
          ·
            refine ⟨261213705390217186712842865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 174142470260144791141895243 261213705390217186712842865)
            ·
              refine ⟨195910279042662890034632149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 261213705390217186712842865 195910279042662890034632149)
              ·
                refine ⟨4591647165062411485186691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 195910279042662890034632149 4591647165062411485186691)
                ·
                  refine ⟨6887470747593617227780037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4591647165062411485186691 6887470747593617227780037)
                  ·
                    refine ⟨1291400765173803230208757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6887470747593617227780037 1291400765173803230208757)
                    ·
                      rfl

theorem cell22_3772491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 7, 1, 4].length) (baseStart_3772491 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3772491 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3772491 prefixEnd_3772491 := by exact prefixLift 3772491
  have htrace : WordTrace (prefixWord ++ tailWord_3772491) baseStart_3772491 baseEnd_3772491 := by
    simpa [prefixWord, tailWord_3772491, baseEnd_3772491] using wordTrace_append hprefix tailTrace_3772491
  have hstable : (prefixWord ++ tailWord_3772491).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3772491).length < 2 ^ (prefixWord ++ tailWord_3772491).sum := by decide
  have hdescent : baseEnd_3772491 < baseStart_3772491 := by decide
  rcases family_descends (prefixWord ++ tailWord_3772491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3772506 : List Nat := [3, 1, 1, 2, 1, 1, 6, 1, 6]
def baseStart_3772506 : Nat := 118140960795 + 3772506 * 2 ^ 59
def prefixEnd_3772506 : Nat := 4983230072969 + 3 ^ 40 * 3772506 * 2
def baseEnd_3772506 : Nat := 430468633326782730361237

theorem tailTrace_3772506 : CollatzResearch.WordTrace tailWord_3772506 prefixEnd_3772506 430468633326782730361237 := by
  unfold tailWord_3772506
  simp only [CollatzResearch.WordTrace]
  refine ⟨34398649417715632393786343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91729731780575019716763581 34398649417715632393786343)
  ·
    refine ⟨51597974126573448590679515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34398649417715632393786343 51597974126573448590679515)
    ·
      refine ⟨77396961189860172886019273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51597974126573448590679515 77396961189860172886019273)
      ·
        refine ⟨58047720892395129664514455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77396961189860172886019273 58047720892395129664514455)
        ·
          refine ⟨87071581338592694496771683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58047720892395129664514455 87071581338592694496771683)
          ·
            refine ⟨130607372007889041745157525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87071581338592694496771683 130607372007889041745157525)
            ·
              refine ⟨6122220562869798831804259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 130607372007889041745157525 6122220562869798831804259)
              ·
                refine ⟨9183330844304698247706389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6122220562869798831804259 9183330844304698247706389)
                ·
                  refine ⟨430468633326782730361237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9183330844304698247706389 430468633326782730361237)
                  ·
                    rfl

theorem cell22_3772506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 6, 1, 6].length) (baseStart_3772506 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3772506 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3772506 prefixEnd_3772506 := by exact prefixLift 3772506
  have htrace : WordTrace (prefixWord ++ tailWord_3772506) baseStart_3772506 baseEnd_3772506 := by
    simpa [prefixWord, tailWord_3772506, baseEnd_3772506] using wordTrace_append hprefix tailTrace_3772506
  have hstable : (prefixWord ++ tailWord_3772506).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3772506).length < 2 ^ (prefixWord ++ tailWord_3772506).sum := by decide
  have hdescent : baseEnd_3772506 < baseStart_3772506 := by decide
  rcases family_descends (prefixWord ++ tailWord_3772506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3772536 : List Nat := [2, 1, 2, 1, 1, 1, 3, 5, 2, 4]
def baseStart_3772536 : Nat := 118140960795 + 3772536 * 2 ^ 59
def prefixEnd_3772536 : Nat := 4983230072969 + 3 ^ 40 * 3772536 * 2
def baseEnd_3772536 : Nat := 1291416169593438112833619

theorem tailTrace_3772536 : CollatzResearch.WordTrace tailWord_3772536 prefixEnd_3772536 1291416169593438112833619 := by
  unfold tailWord_3772536
  simp only [CollatzResearch.WordTrace]
  refine ⟨68797845930376922349368731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91730461240502563132491641 68797845930376922349368731)
  ·
    refine ⟨103196768895565383524053097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68797845930376922349368731 103196768895565383524053097)
    ·
      refine ⟨77397576671674037643039823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103196768895565383524053097 77397576671674037643039823)
      ·
        refine ⟨116096365007511056464559735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77397576671674037643039823 116096365007511056464559735)
        ·
          refine ⟨174144547511266584696839603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116096365007511056464559735 174144547511266584696839603)
          ·
            refine ⟨261216821266899877045259405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 174144547511266584696839603 261216821266899877045259405)
            ·
              refine ⟨97956307975087453891972277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 261216821266899877045259405 97956307975087453891972277)
              ·
                refine ⟨9183403872664448802372401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 97956307975087453891972277 9183403872664448802372401)
                ·
                  refine ⟨6887552904498336601779301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9183403872664448802372401 6887552904498336601779301)
                  ·
                    refine ⟨1291416169593438112833619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6887552904498336601779301 1291416169593438112833619)
                    ·
                      rfl

theorem cell22_3772536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 5, 2, 4].length) (baseStart_3772536 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3772536 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3772536 prefixEnd_3772536 := by exact prefixLift 3772536
  have htrace : WordTrace (prefixWord ++ tailWord_3772536) baseStart_3772536 baseEnd_3772536 := by
    simpa [prefixWord, tailWord_3772536, baseEnd_3772536] using wordTrace_append hprefix tailTrace_3772536
  have hstable : (prefixWord ++ tailWord_3772536).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3772536).length < 2 ^ (prefixWord ++ tailWord_3772536).sum := by decide
  have hdescent : baseEnd_3772536 < baseStart_3772536 := by decide
  rcases family_descends (prefixWord ++ tailWord_3772536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3772540 : List Nat := [2, 2, 2, 1, 1, 6, 1, 3, 4]
def baseStart_3772540 : Nat := 118140960795 + 3772540 * 2 ^ 59
def prefixEnd_3772540 : Nat := 4983230072969 + 3 ^ 40 * 3772540 * 2
def baseEnd_3772540 : Nat := 430472512958394478577869

theorem tailTrace_3772540 : CollatzResearch.WordTrace tailWord_3772540 prefixEnd_3772540 430472512958394478577869 := by
  unfold tailWord_3772540
  simp only [CollatzResearch.WordTrace]
  refine ⟨68797918876369676690941537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91730558501826235587922049 68797918876369676690941537)
  ·
    refine ⟨51598439157277257518206153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68797918876369676690941537 51598439157277257518206153)
    ·
      refine ⟨38698829367957943138654615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51598439157277257518206153 38698829367957943138654615)
      ·
        refine ⟨58048244051936914707981923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38698829367957943138654615 58048244051936914707981923)
        ·
          refine ⟨87072366077905372061972885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58048244051936914707981923 87072366077905372061972885)
          ·
            refine ⟨4081517159901814315404979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 87072366077905372061972885 4081517159901814315404979)
            ·
              refine ⟨6122275739852721473107469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4081517159901814315404979 6122275739852721473107469)
              ·
                refine ⟨2295853402444770552415301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6122275739852721473107469 2295853402444770552415301)
                ·
                  refine ⟨430472512958394478577869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2295853402444770552415301 430472512958394478577869)
                  ·
                    rfl

theorem cell22_3772540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 6, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 6, 1, 3, 4].length) (baseStart_3772540 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3772540 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3772540 prefixEnd_3772540 := by exact prefixLift 3772540
  have htrace : WordTrace (prefixWord ++ tailWord_3772540) baseStart_3772540 baseEnd_3772540 := by
    simpa [prefixWord, tailWord_3772540, baseEnd_3772540] using wordTrace_append hprefix tailTrace_3772540
  have hstable : (prefixWord ++ tailWord_3772540).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3772540).length < 2 ^ (prefixWord ++ tailWord_3772540).sum := by decide
  have hdescent : baseEnd_3772540 < baseStart_3772540 := by decide
  rcases family_descends (prefixWord ++ tailWord_3772540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3772568 : List Nat := [2, 1, 2, 4, 3, 1, 2, 7]
def baseStart_3772568 : Nat := 118140960795 + 3772568 * 2 ^ 59
def prefixEnd_3772568 : Nat := 4983230072969 + 3 ^ 40 * 3772568 * 2
def baseEnd_3772568 : Nat := 143491902649711188448169

theorem tailTrace_3772568 : CollatzResearch.WordTrace tailWord_3772568 prefixEnd_3772568 143491902649711188448169 := by
  unfold tailWord_3772568
  simp only [CollatzResearch.WordTrace]
  refine ⟨68798429498318957081951179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91731239331091942775934905 68798429498318957081951179)
  ·
    refine ⟨103197644247478435622926769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68798429498318957081951179 103197644247478435622926769)
    ·
      refine ⟨77398233185608826717195077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103197644247478435622926769 77398233185608826717195077)
      ·
        refine ⟨14512168722301655009474077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 77398233185608826717195077 14512168722301655009474077)
        ·
          refine ⟨5442063270863120628552779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14512168722301655009474077 5442063270863120628552779)
          ·
            refine ⟨8163094906294680942829169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5442063270863120628552779 8163094906294680942829169)
            ·
              refine ⟨6122321179721010707121877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8163094906294680942829169 6122321179721010707121877)
              ·
                refine ⟨143491902649711188448169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6122321179721010707121877 143491902649711188448169)
                ·
                  rfl

theorem cell22_3772568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 2, 7].length) (baseStart_3772568 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3772568 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3772568 prefixEnd_3772568 := by exact prefixLift 3772568
  have htrace : WordTrace (prefixWord ++ tailWord_3772568) baseStart_3772568 baseEnd_3772568 := by
    simpa [prefixWord, tailWord_3772568, baseEnd_3772568] using wordTrace_append hprefix tailTrace_3772568
  have hstable : (prefixWord ++ tailWord_3772568).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3772568).length < 2 ^ (prefixWord ++ tailWord_3772568).sum := by decide
  have hdescent : baseEnd_3772568 < baseStart_3772568 := by decide
  rcases family_descends (prefixWord ++ tailWord_3772568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3772600 : List Nat := [2, 1, 2, 1, 2, 1, 4, 5, 1, 3]
def baseStart_3772600 : Nat := 118140960795 + 3772600 * 2 ^ 59
def prefixEnd_3772600 : Nat := 4983230072969 + 3 ^ 40 * 3772600 * 2
def baseEnd_3772600 : Nat := 1291438078101363279233423

theorem tailTrace_3772600 : CollatzResearch.WordTrace tailWord_3772600 prefixEnd_3772600 1291438078101363279233423 := by
  unfold tailWord_3772600
  simp only [CollatzResearch.WordTrace]
  refine ⟨68799013066260991814533627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91732017421681322419378169 68799013066260991814533627)
  ·
    refine ⟨103198519599391487721800441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68799013066260991814533627 103198519599391487721800441)
    ·
      refine ⟨77398889699543615791350331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103198519599391487721800441 77398889699543615791350331)
      ·
        refine ⟨116098334549315423687025497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77398889699543615791350331 116098334549315423687025497)
        ·
          refine ⟨87073750911986567765269123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116098334549315423687025497 87073750911986567765269123)
          ·
            refine ⟨130610626367979851647903685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87073750911986567765269123 130610626367979851647903685)
            ·
              refine ⟨24489492443996222183981941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 130610626367979851647903685 24489492443996222183981941)
              ·
                refine ⟨2295889916624645829748307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24489492443996222183981941 2295889916624645829748307)
                ·
                  refine ⟨3443834874936968744622461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2295889916624645829748307 3443834874936968744622461)
                  ·
                    refine ⟨1291438078101363279233423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3443834874936968744622461 1291438078101363279233423)
                    ·
                      rfl

theorem cell22_3772600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 4, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 4, 5, 1, 3].length) (baseStart_3772600 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3772600 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3772600 prefixEnd_3772600 := by exact prefixLift 3772600
  have htrace : WordTrace (prefixWord ++ tailWord_3772600) baseStart_3772600 baseEnd_3772600 := by
    simpa [prefixWord, tailWord_3772600, baseEnd_3772600] using wordTrace_append hprefix tailTrace_3772600
  have hstable : (prefixWord ++ tailWord_3772600).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3772600).length < 2 ^ (prefixWord ++ tailWord_3772600).sum := by decide
  have hdescent : baseEnd_3772600 < baseStart_3772600 := by decide
  rcases family_descends (prefixWord ++ tailWord_3772600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3772703 : List Nat := [1, 1, 2, 4, 3, 2, 1, 8]
def baseStart_3772703 : Nat := 118140960795 + 3772703 * 2 ^ 59
def prefixEnd_3772703 : Nat := 4983230072969 + 3 ^ 40 * 3772703 * 2
def baseEnd_3772703 : Nat := 143497037456256149323123

theorem tailTrace_3772703 : CollatzResearch.WordTrace tailWord_3772703 prefixEnd_3772703 143497037456256149323123 := by
  unfold tailWord_3772703
  simp only [CollatzResearch.WordTrace]
  refine ⟨137601782851148832220066763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91734521900765888146711175 137601782851148832220066763)
  ·
    refine ⟨206402674276723248330100145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137601782851148832220066763 206402674276723248330100145)
    ·
      refine ⟨154802005707542436247575109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 206402674276723248330100145 154802005707542436247575109)
      ·
        refine ⟨29025376070164206796420333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 154802005707542436247575109 29025376070164206796420333)
        ·
          refine ⟨10884516026311577548657625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29025376070164206796420333 10884516026311577548657625)
          ·
            refine ⟨8163387019733683161493219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10884516026311577548657625 8163387019733683161493219)
            ·
              refine ⟨12245080529600524742239829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8163387019733683161493219 12245080529600524742239829)
              ·
                refine ⟨143497037456256149323123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12245080529600524742239829 143497037456256149323123)
                ·
                  rfl

theorem cell22_3772703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 1, 8].length) (baseStart_3772703 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3772703 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3772703 prefixEnd_3772703 := by exact prefixLift 3772703
  have htrace : WordTrace (prefixWord ++ tailWord_3772703) baseStart_3772703 baseEnd_3772703 := by
    simpa [prefixWord, tailWord_3772703, baseEnd_3772703] using wordTrace_append hprefix tailTrace_3772703
  have hstable : (prefixWord ++ tailWord_3772703).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3772703).length < 2 ^ (prefixWord ++ tailWord_3772703).sum := by decide
  have hdescent : baseEnd_3772703 < baseStart_3772703 := by decide
  rcases family_descends (prefixWord ++ tailWord_3772703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3772709 : List Nat := [1, 3, 1, 2, 6, 1, 1, 3, 4]
def baseStart_3772709 : Nat := 118140960795 + 3772709 * 2 ^ 59
def prefixEnd_3772709 : Nat := 4983230072969 + 3 ^ 40 * 3772709 * 2
def baseEnd_3772709 : Nat := 430491797009641109419363

theorem tailTrace_3772709 : CollatzResearch.WordTrace tailWord_3772709 prefixEnd_3772709 430491797009641109419363 := by
  unfold tailWord_3772709
  simp only [CollatzResearch.WordTrace]
  refine ⟨137602001689127095244785181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91734667792751396829856787 137602001689127095244785181)
  ·
    refine ⟨51600750633422660716794443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137602001689127095244785181 51600750633422660716794443)
    ·
      refine ⟨77401125950133991075191665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51600750633422660716794443 77401125950133991075191665)
      ·
        refine ⟨58050844462600493306393749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77401125950133991075191665 58050844462600493306393749)
        ·
          refine ⟨2721133334184398123737207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 58050844462600493306393749 2721133334184398123737207)
          ·
            refine ⟨4081700001276597185605811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2721133334184398123737207 4081700001276597185605811)
            ·
              refine ⟨6122550001914895778408717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4081700001276597185605811 6122550001914895778408717)
              ·
                refine ⟨2295956250718085916903269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6122550001914895778408717 2295956250718085916903269)
                ·
                  refine ⟨430491797009641109419363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2295956250718085916903269 430491797009641109419363)
                  ·
                    rfl

theorem cell22_3772709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 6, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 6, 1, 1, 3, 4].length) (baseStart_3772709 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3772709 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3772709 prefixEnd_3772709 := by exact prefixLift 3772709
  have htrace : WordTrace (prefixWord ++ tailWord_3772709) baseStart_3772709 baseEnd_3772709 := by
    simpa [prefixWord, tailWord_3772709, baseEnd_3772709] using wordTrace_append hprefix tailTrace_3772709
  have hstable : (prefixWord ++ tailWord_3772709).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3772709).length < 2 ^ (prefixWord ++ tailWord_3772709).sum := by decide
  have hdescent : baseEnd_3772709 < baseStart_3772709 := by decide
  rcases family_descends (prefixWord ++ tailWord_3772709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3772786 : List Nat := [3, 2, 1, 2, 1, 5, 2, 2, 1, 3]
def baseStart_3772786 : Nat := 118140960795 + 3772786 * 2 ^ 59
def prefixEnd_3772786 : Nat := 4983230072969 + 3 ^ 40 * 3772786 * 2
def baseEnd_3772786 : Nat := 1291501749702520794082853

theorem tailTrace_3772786 : CollatzResearch.WordTrace tailWord_3772786 prefixEnd_3772786 1291501749702520794082853 := by
  unfold tailWord_3772786
  simp only [CollatzResearch.WordTrace]
  refine ⟨34401202527462034348834553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91736540073232091596892141 34401202527462034348834553)
  ·
    refine ⟨25800901895596525761625915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34401202527462034348834553 25800901895596525761625915)
    ·
      refine ⟨38701352843394788642438873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25800901895596525761625915 38701352843394788642438873)
      ·
        refine ⟨29026014632546091481829155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38701352843394788642438873 29026014632546091481829155)
        ·
          refine ⟨43539021948819137222743733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29026014632546091481829155 43539021948819137222743733)
          ·
            refine ⟨4081783307701794114632225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 43539021948819137222743733 4081783307701794114632225)
            ·
              refine ⟨3061337480776345585974169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4081783307701794114632225 3061337480776345585974169)
              ·
                refine ⟨2296003110582259189480627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3061337480776345585974169 2296003110582259189480627)
                ·
                  refine ⟨3444004665873388784220941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2296003110582259189480627 3444004665873388784220941)
                  ·
                    refine ⟨1291501749702520794082853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3444004665873388784220941 1291501749702520794082853)
                    ·
                      rfl

theorem cell22_3772786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 5, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 5, 2, 2, 1, 3].length) (baseStart_3772786 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3772786 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3772786 prefixEnd_3772786 := by exact prefixLift 3772786
  have htrace : WordTrace (prefixWord ++ tailWord_3772786) baseStart_3772786 baseEnd_3772786 := by
    simpa [prefixWord, tailWord_3772786, baseEnd_3772786] using wordTrace_append hprefix tailTrace_3772786
  have hstable : (prefixWord ++ tailWord_3772786).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3772786).length < 2 ^ (prefixWord ++ tailWord_3772786).sum := by decide
  have hdescent : baseEnd_3772786 < baseStart_3772786 := by decide
  rcases family_descends (prefixWord ++ tailWord_3772786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3772793 : List Nat := [1, 2, 1, 3, 2, 1, 1, 5, 6]
def baseStart_3772793 : Nat := 118140960795 + 3772793 * 2 ^ 59
def prefixEnd_3772793 : Nat := 4983230072969 + 3 ^ 40 * 3772793 * 2
def baseEnd_3772793 : Nat := 430501381981858369719277

theorem tailTrace_3772793 : CollatzResearch.WordTrace tailWord_3772793 prefixEnd_3772793 430501381981858369719277 := by
  unfold tailWord_3772793
  simp only [CollatzResearch.WordTrace]
  refine ⟨137605065420822777590843033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91736710280548518393895355 137605065420822777590843033)
  ·
    refine ⟨103203799065617083193132275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137605065420822777590843033 103203799065617083193132275)
    ·
      refine ⟨154805698598425624789698413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103203799065617083193132275 154805698598425624789698413)
      ·
        refine ⟨58052136974409609296136905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 154805698598425624789698413 58052136974409609296136905)
        ·
          refine ⟨43539102730807206972102679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58052136974409609296136905 43539102730807206972102679)
          ·
            refine ⟨65308654096210810458154019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43539102730807206972102679 65308654096210810458154019)
            ·
              refine ⟨97962981144316215687231029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65308654096210810458154019 97962981144316215687231029)
              ·
                refine ⟨9184029482279645220677909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 97962981144316215687231029 9184029482279645220677909)
                ·
                  refine ⟨430501381981858369719277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9184029482279645220677909 430501381981858369719277)
                  ·
                    rfl

theorem cell22_3772793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 5, 6].length) (baseStart_3772793 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3772793 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3772793 prefixEnd_3772793 := by exact prefixLift 3772793
  have htrace : WordTrace (prefixWord ++ tailWord_3772793) baseStart_3772793 baseEnd_3772793 := by
    simpa [prefixWord, tailWord_3772793, baseEnd_3772793] using wordTrace_append hprefix tailTrace_3772793
  have hstable : (prefixWord ++ tailWord_3772793).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3772793).length < 2 ^ (prefixWord ++ tailWord_3772793).sum := by decide
  have hdescent : baseEnd_3772793 < baseStart_3772793 := by decide
  rcases family_descends (prefixWord ++ tailWord_3772793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3772825 : List Nat := [1, 2, 1, 2, 1, 4, 2, 2, 4, 3]
def baseStart_3772825 : Nat := 118140960795 + 3772825 * 2 ^ 59
def prefixEnd_3772825 : Nat := 4983230072969 + 3 ^ 40 * 3772825 * 2
def baseEnd_3772825 : Nat := 1291515100199537692357733

theorem tailTrace_3772825 : CollatzResearch.WordTrace tailWord_3772825 prefixEnd_3772825 1291515100199537692357733 := by
  unfold tailWord_3772825
  simp only [CollatzResearch.WordTrace]
  refine ⟨137606232556706847056007929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91737488371137898037338619 137606232556706847056007929)
  ·
    refine ⟨103204674417530135292005947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137606232556706847056007929 103204674417530135292005947)
    ·
      refine ⟨154807011626295202938008921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103204674417530135292005947 154807011626295202938008921)
      ·
        refine ⟨116105258719721402203506691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154807011626295202938008921 116105258719721402203506691)
        ·
          refine ⟨174157888079582103305260037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116105258719721402203506691 174157888079582103305260037)
          ·
            refine ⟨32654604014921644369736257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 174157888079582103305260037 32654604014921644369736257)
            ·
              refine ⟨24490953011191233277302193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32654604014921644369736257 24490953011191233277302193)
              ·
                refine ⟨18368214758393424957976645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24490953011191233277302193 18368214758393424957976645)
                ·
                  refine ⟨3444040267198767179620621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18368214758393424957976645 3444040267198767179620621)
                  ·
                    refine ⟨1291515100199537692357733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3444040267198767179620621 1291515100199537692357733)
                    ·
                      rfl

theorem cell22_3772825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 2, 2, 4, 3].length) (baseStart_3772825 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3772825 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3772825 prefixEnd_3772825 := by exact prefixLift 3772825
  have htrace : WordTrace (prefixWord ++ tailWord_3772825) baseStart_3772825 baseEnd_3772825 := by
    simpa [prefixWord, tailWord_3772825, baseEnd_3772825] using wordTrace_append hprefix tailTrace_3772825
  have hstable : (prefixWord ++ tailWord_3772825).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3772825).length < 2 ^ (prefixWord ++ tailWord_3772825).sum := by decide
  have hdescent : baseEnd_3772825 < baseStart_3772825 := by decide
  rcases family_descends (prefixWord ++ tailWord_3772825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3772872 : List Nat := [2, 1, 3, 1, 3, 4, 2, 6]
def baseStart_3772872 : Nat := 118140960795 + 3772872 * 2 ^ 59
def prefixEnd_3772872 : Nat := 4983230072969 + 3 ^ 40 * 3772872 * 2
def baseEnd_3772872 : Nat := 143503465473338359603621

theorem tailTrace_3772872 : CollatzResearch.WordTrace tailWord_3772872 prefixEnd_3772872 143503465473338359603621 := by
  unfold tailWord_3772872
  simp only [CollatzResearch.WordTrace]
  refine ⟨68803973393768287041484435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91738631191691049388645913 68803973393768287041484435)
  ·
    refine ⟨103205960090652430562226653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68803973393768287041484435 103205960090652430562226653)
    ·
      refine ⟨38702235033994661460834995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103205960090652430562226653 38702235033994661460834995)
      ·
        refine ⟨58053352550991992191252493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38702235033994661460834995 58053352550991992191252493)
        ·
          refine ⟨21770007206621997071719685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58053352550991992191252493 21770007206621997071719685)
          ·
            refine ⟨4081876351241624450947441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21770007206621997071719685 4081876351241624450947441)
            ·
              refine ⟨3061407263431218338210581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4081876351241624450947441 3061407263431218338210581)
              ·
                refine ⟨143503465473338359603621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3061407263431218338210581 143503465473338359603621)
                ·
                  rfl

theorem cell22_3772872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 4, 2, 6].length) (baseStart_3772872 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3772872 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3772872 prefixEnd_3772872 := by exact prefixLift 3772872
  have htrace : WordTrace (prefixWord ++ tailWord_3772872) baseStart_3772872 baseEnd_3772872 := by
    simpa [prefixWord, tailWord_3772872, baseEnd_3772872] using wordTrace_append hprefix tailTrace_3772872
  have hstable : (prefixWord ++ tailWord_3772872).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3772872).length < 2 ^ (prefixWord ++ tailWord_3772872).sum := by decide
  have hdescent : baseEnd_3772872 < baseStart_3772872 := by decide
  rcases family_descends (prefixWord ++ tailWord_3772872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3772904 : List Nat := [2, 1, 4, 1, 1, 5, 1, 1, 3, 3]
def baseStart_3772904 : Nat := 118140960795 + 3772904 * 2 ^ 59
def prefixEnd_3772904 : Nat := 4983230072969 + 3 ^ 40 * 3772904 * 2
def baseEnd_3772904 : Nat := 1291542143514007819632491

theorem tailTrace_3772904 : CollatzResearch.WordTrace tailWord_3772904 prefixEnd_3772904 1291542143514007819632491 := by
  unfold tailWord_3772904
  simp only [CollatzResearch.WordTrace]
  refine ⟨68804556961710321774066883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91739409282280429032089177 68804556961710321774066883)
  ·
    refine ⟨103206835442565482661100325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68804556961710321774066883 103206835442565482661100325)
    ·
      refine ⟨19351281645481027998956311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 103206835442565482661100325 19351281645481027998956311)
      ·
        refine ⟨29026922468221541998434467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19351281645481027998956311 29026922468221541998434467)
        ·
          refine ⟨43540383702332312997651701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29026922468221541998434467 43540383702332312997651701)
          ·
            refine ⟨4081910972093654343529847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 43540383702332312997651701 4081910972093654343529847)
            ·
              refine ⟨6122866458140481515294771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4081910972093654343529847 6122866458140481515294771)
              ·
                refine ⟨9184299687210722272942157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6122866458140481515294771 9184299687210722272942157)
                ·
                  refine ⟨3444112382704020852353309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9184299687210722272942157 3444112382704020852353309)
                  ·
                    refine ⟨1291542143514007819632491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3444112382704020852353309 1291542143514007819632491)
                    ·
                      rfl

theorem cell22_3772904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 5, 1, 1, 3, 3].length) (baseStart_3772904 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3772904 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3772904 prefixEnd_3772904 := by exact prefixLift 3772904
  have htrace : WordTrace (prefixWord ++ tailWord_3772904) baseStart_3772904 baseEnd_3772904 := by
    simpa [prefixWord, tailWord_3772904, baseEnd_3772904] using wordTrace_append hprefix tailTrace_3772904
  have hstable : (prefixWord ++ tailWord_3772904).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3772904).length < 2 ^ (prefixWord ++ tailWord_3772904).sum := by decide
  have hdescent : baseEnd_3772904 < baseStart_3772904 := by decide
  rcases family_descends (prefixWord ++ tailWord_3772904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3772992 : List Nat := [2, 1, 1, 2, 2, 2, 5, 1, 2, 4]
def baseStart_3772992 : Nat := 118140960795 + 3772992 * 2 ^ 59
def prefixEnd_3772992 : Nat := 4983230072969 + 3 ^ 40 * 3772992 * 2
def baseEnd_3772992 : Nat := 1291572267712404923432221

theorem tailTrace_3772992 : CollatzResearch.WordTrace tailWord_3772992 prefixEnd_3772992 1291572267712404923432221 := by
  unfold tailWord_3772992
  simp only [CollatzResearch.WordTrace]
  refine ⟨68806161773550917288668615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91741549031401223051558153 68806161773550917288668615)
  ·
    refine ⟨103209242660326375933002923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68806161773550917288668615 103209242660326375933002923)
    ·
      refine ⟨154813863990489563899504385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103209242660326375933002923 154813863990489563899504385)
      ·
        refine ⟨116110397992867172924628289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154813863990489563899504385 116110397992867172924628289)
        ·
          refine ⟨87082798494650379693471217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116110397992867172924628289 87082798494650379693471217)
          ·
            refine ⟨65312098870987784770103413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87082798494650379693471217 65312098870987784770103413)
            ·
              refine ⟨6123009269155104822197195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 65312098870987784770103413 6123009269155104822197195)
              ·
                refine ⟨9184513903732657233295793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6123009269155104822197195 9184513903732657233295793)
                ·
                  refine ⟨6888385427799492924971845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9184513903732657233295793 6888385427799492924971845)
                  ·
                    refine ⟨1291572267712404923432221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6888385427799492924971845 1291572267712404923432221)
                    ·
                      rfl

theorem cell22_3772992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 5, 1, 2, 4].length) (baseStart_3772992 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3772992 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3772992 prefixEnd_3772992 := by exact prefixLift 3772992
  have htrace : WordTrace (prefixWord ++ tailWord_3772992) baseStart_3772992 baseEnd_3772992 := by
    simpa [prefixWord, tailWord_3772992, baseEnd_3772992] using wordTrace_append hprefix tailTrace_3772992
  have hstable : (prefixWord ++ tailWord_3772992).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3772992).length < 2 ^ (prefixWord ++ tailWord_3772992).sum := by decide
  have hdescent : baseEnd_3772992 < baseStart_3772992 := by decide
  rcases family_descends (prefixWord ++ tailWord_3772992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3772998 : List Nat := [6, 1, 1, 1, 2, 1, 4, 1, 1, 4]
def baseStart_3772998 : Nat := 118140960795 + 3772998 * 2 ^ 59
def prefixEnd_3772998 : Nat := 4983230072969 + 3 ^ 40 * 3772998 * 2
def baseEnd_3772998 : Nat := 1291574321635022907782203

theorem tailTrace_3772998 : CollatzResearch.WordTrace tailWord_3772998 prefixEnd_3772998 1291574321635022907782203 := by
  unfold tailWord_3772998
  simp only [CollatzResearch.WordTrace]
  refine ⟨4300391949533753050064239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 91741694923386731734703765 4300391949533753050064239)
  ·
    refine ⟨6450587924300629575096359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4300391949533753050064239 6450587924300629575096359)
    ·
      refine ⟨9675881886450944362644539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6450587924300629575096359 9675881886450944362644539)
      ·
        refine ⟨14513822829676416543966809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9675881886450944362644539 14513822829676416543966809)
        ·
          refine ⟨10885367122257312407975107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14513822829676416543966809 10885367122257312407975107)
          ·
            refine ⟨16328050683385968611962661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10885367122257312407975107 16328050683385968611962661)
            ·
              refine ⟨3061509503134869114742999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16328050683385968611962661 3061509503134869114742999)
              ·
                refine ⟨4592264254702303672114499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3061509503134869114742999 4592264254702303672114499)
                ·
                  refine ⟨6888396382053455508171749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4592264254702303672114499 6888396382053455508171749)
                  ·
                    refine ⟨1291574321635022907782203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6888396382053455508171749 1291574321635022907782203)
                    ·
                      rfl

theorem cell22_3772998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 4, 1, 1, 4].length) (baseStart_3772998 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3772998 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3772998 prefixEnd_3772998 := by exact prefixLift 3772998
  have htrace : WordTrace (prefixWord ++ tailWord_3772998) baseStart_3772998 baseEnd_3772998 := by
    simpa [prefixWord, tailWord_3772998, baseEnd_3772998] using wordTrace_append hprefix tailTrace_3772998
  have hstable : (prefixWord ++ tailWord_3772998).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3772998).length < 2 ^ (prefixWord ++ tailWord_3772998).sum := by decide
  have hdescent : baseEnd_3772998 < baseStart_3772998 := by decide
  rcases family_descends (prefixWord ++ tailWord_3772998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3773056 : List Nat := [2, 1, 1, 2, 1, 5, 3, 3, 1, 3]
def baseStart_3773056 : Nat := 118140960795 + 3773056 * 2 ^ 59
def prefixEnd_3773056 : Nat := 4983230072969 + 3 ^ 40 * 3773056 * 2
def baseEnd_3773056 : Nat := 1291594176220330089832025

theorem tailTrace_3773056 : CollatzResearch.WordTrace tailWord_3773056 prefixEnd_3773056 1291594176220330089832025 := by
  unfold tailWord_3773056
  simp only [CollatzResearch.WordTrace]
  refine ⟨68807328909434986753833511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91743105212579982338444681 68807328909434986753833511)
  ·
    refine ⟨103210993364152480130750267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68807328909434986753833511 103210993364152480130750267)
    ·
      refine ⟨154816490046228720196125401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103210993364152480130750267 154816490046228720196125401)
      ·
        refine ⟨116112367534671540147094051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154816490046228720196125401 116112367534671540147094051)
        ·
          refine ⟨174168551302007310220641077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116112367534671540147094051 174168551302007310220641077)
          ·
            refine ⟨16328301684563185333185101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 174168551302007310220641077 16328301684563185333185101)
            ·
              refine ⟨6123113131711194499944413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16328301684563185333185101 6123113131711194499944413)
              ·
                refine ⟨2296167424391697937479155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6123113131711194499944413 2296167424391697937479155)
                ·
                  refine ⟨3444251136587546906218733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2296167424391697937479155 3444251136587546906218733)
                  ·
                    refine ⟨1291594176220330089832025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3444251136587546906218733 1291594176220330089832025)
                    ·
                      rfl

theorem cell22_3773056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 3, 3, 1, 3].length) (baseStart_3773056 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3773056 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3773056 prefixEnd_3773056 := by exact prefixLift 3773056
  have htrace : WordTrace (prefixWord ++ tailWord_3773056) baseStart_3773056 baseEnd_3773056 := by
    simpa [prefixWord, tailWord_3773056, baseEnd_3773056] using wordTrace_append hprefix tailTrace_3773056
  have hstable : (prefixWord ++ tailWord_3773056).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3773056).length < 2 ^ (prefixWord ++ tailWord_3773056).sum := by decide
  have hdescent : baseEnd_3773056 < baseStart_3773056 := by decide
  rcases family_descends (prefixWord ++ tailWord_3773056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3773058 : List Nat := [3, 4, 3, 1, 1, 2, 8]
def baseStart_3773058 : Nat := 118140960795 + 3773058 * 2 ^ 59
def prefixEnd_3773058 : Nat := 4983230072969 + 3 ^ 40 * 3773058 * 2
def baseEnd_3773058 : Nat := 47836846698563064862297

theorem tailTrace_3773058 : CollatzResearch.WordTrace tailWord_3773058 prefixEnd_3773058 47836846698563064862297 := by
  unfold tailWord_3773058
  simp only [CollatzResearch.WordTrace]
  refine ⟨34403682691215681962309957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91743153843241818566159885 34403682691215681962309957)
  ·
    refine ⟨6450690504602940367933117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34403682691215681962309957 6450690504602940367933117)
    ·
      refine ⟨2419008939226102637974919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6450690504602940367933117 2419008939226102637974919)
      ·
        refine ⟨3628513408839153956962379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2419008939226102637974919 3628513408839153956962379)
        ·
          refine ⟨5442770113258730935443569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3628513408839153956962379 5442770113258730935443569)
          ·
            refine ⟨4082077584944048201582677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5442770113258730935443569 4082077584944048201582677)
            ·
              refine ⟨47836846698563064862297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4082077584944048201582677 47836846698563064862297)
              ·
                rfl

theorem cell22_3773058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 2, 8].length) (baseStart_3773058 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3773058 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3773058 prefixEnd_3773058 := by exact prefixLift 3773058
  have htrace : WordTrace (prefixWord ++ tailWord_3773058) baseStart_3773058 baseEnd_3773058 := by
    simpa [prefixWord, tailWord_3773058, baseEnd_3773058] using wordTrace_append hprefix tailTrace_3773058
  have hstable : (prefixWord ++ tailWord_3773058).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3773058).length < 2 ^ (prefixWord ++ tailWord_3773058).sum := by decide
  have hdescent : baseEnd_3773058 < baseStart_3773058 := by decide
  rcases family_descends (prefixWord ++ tailWord_3773058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3773114 : List Nat := [3, 1, 1, 1, 2, 3, 2, 5, 4]
def baseStart_3773114 : Nat := 118140960795 + 3773114 * 2 ^ 59
def prefixEnd_3773114 : Nat := 4983230072969 + 3 ^ 40 * 3773114 * 2
def baseEnd_3773114 : Nat := 430538010268545757293949

theorem tailTrace_3773114 : CollatzResearch.WordTrace tailWord_3773114 prefixEnd_3773114 430538010268545757293949 := by
  unfold tailWord_3773114
  simp only [CollatzResearch.WordTrace]
  refine ⟨34404193313164962353319599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91744515501773232942185597 34404193313164962353319599)
  ·
    refine ⟨51606289969747443529979399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34404193313164962353319599 51606289969747443529979399)
    ·
      refine ⟨77409434954621165294969099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51606289969747443529979399 77409434954621165294969099)
      ·
        refine ⟨116114152431931747942453649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77409434954621165294969099 116114152431931747942453649)
        ·
          refine ⟨87085614323948810956840237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116114152431931747942453649 87085614323948810956840237)
          ·
            refine ⟨32657105371480804108815089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87085614323948810956840237 32657105371480804108815089)
            ·
              refine ⟨24492829028610603081611317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32657105371480804108815089 24492829028610603081611317)
              ·
                refine ⟨2296202721432244038901061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24492829028610603081611317 2296202721432244038901061)
                ·
                  refine ⟨430538010268545757293949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2296202721432244038901061 430538010268545757293949)
                  ·
                    rfl

theorem cell22_3773114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 2, 5, 4].length) (baseStart_3773114 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3773114 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3773114 prefixEnd_3773114 := by exact prefixLift 3773114
  have htrace : WordTrace (prefixWord ++ tailWord_3773114) baseStart_3773114 baseEnd_3773114 := by
    simpa [prefixWord, tailWord_3773114, baseEnd_3773114] using wordTrace_append hprefix tailTrace_3773114
  have hstable : (prefixWord ++ tailWord_3773114).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3773114).length < 2 ^ (prefixWord ++ tailWord_3773114).sum := by decide
  have hdescent : baseEnd_3773114 < baseStart_3773114 := by decide
  rcases family_descends (prefixWord ++ tailWord_3773114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3773116 : List Nat := [2, 2, 2, 3, 1, 1, 5, 1, 1, 4]
def baseStart_3773116 : Nat := 118140960795 + 3773116 * 2 ^ 59
def prefixEnd_3773116 : Nat := 4983230072969 + 3 ^ 40 * 3773116 * 2
def baseEnd_3773116 : Nat := 1291614715446509933331841

theorem tailTrace_3773116 : CollatzResearch.WordTrace tailWord_3773116 prefixEnd_3773116 1291614715446509933331841 := by
  unfold tailWord_3773116
  simp only [CollatzResearch.WordTrace]
  refine ⟨68808423099326301877425601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91744564132435069169900801 68808423099326301877425601)
  ·
    refine ⟨51606317324494726408069201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68808423099326301877425601 51606317324494726408069201)
    ·
      refine ⟨38704737993371044806051901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51606317324494726408069201 38704737993371044806051901)
      ·
        refine ⟨14514276747514141802269463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38704737993371044806051901 14514276747514141802269463)
        ·
          refine ⟨21771415121271212703404195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14514276747514141802269463 21771415121271212703404195)
          ·
            refine ⟨32657122681906819055106293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21771415121271212703404195 32657122681906819055106293)
            ·
              refine ⟨3061605251428764286416215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 32657122681906819055106293 3061605251428764286416215)
              ·
                refine ⟨4592407877143146429624323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3061605251428764286416215 4592407877143146429624323)
                ·
                  refine ⟨6888611815714719644436485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4592407877143146429624323 6888611815714719644436485)
                  ·
                    refine ⟨1291614715446509933331841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6888611815714719644436485 1291614715446509933331841)
                    ·
                      rfl

theorem cell22_3773116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 5, 1, 1, 4].length) (baseStart_3773116 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3773116 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3773116 prefixEnd_3773116 := by exact prefixLift 3773116
  have htrace : WordTrace (prefixWord ++ tailWord_3773116) baseStart_3773116 baseEnd_3773116 := by
    simpa [prefixWord, tailWord_3773116, baseEnd_3773116] using wordTrace_append hprefix tailTrace_3773116
  have hstable : (prefixWord ++ tailWord_3773116).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3773116).length < 2 ^ (prefixWord ++ tailWord_3773116).sum := by decide
  have hdescent : baseEnd_3773116 < baseStart_3773116 := by decide
  rcases family_descends (prefixWord ++ tailWord_3773116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3773127 : List Nat := [1, 1, 4, 1, 1, 1, 2, 3, 4, 4]
def baseStart_3773127 : Nat := 118140960795 + 3773127 * 2 ^ 59
def prefixEnd_3773127 : Nat := 4983230072969 + 3 ^ 40 * 3773127 * 2
def baseEnd_3773127 : Nat := 1291618480971309571306807

theorem tailTrace_3773127 : CollatzResearch.WordTrace tailWord_3773127 prefixEnd_3773127 1291618480971309571306807 := by
  unfold tailWord_3773127
  simp only [CollatzResearch.WordTrace]
  refine ⟨137617247401612752633501635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91744831601075168422334423 137617247401612752633501635)
  ·
    refine ⟨206425871102419128950252453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137617247401612752633501635 206425871102419128950252453)
    ·
      refine ⟨38704850831703586678172335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 206425871102419128950252453 38704850831703586678172335)
      ·
        refine ⟨58057276247555380017258503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38704850831703586678172335 58057276247555380017258503)
        ·
          refine ⟨87085914371333070025887755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58057276247555380017258503 87085914371333070025887755)
          ·
            refine ⟨130628871556999605038831633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87085914371333070025887755 130628871556999605038831633)
            ·
              refine ⟨97971653667749703779123725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 130628871556999605038831633 97971653667749703779123725)
              ·
                refine ⟨36739370125406138917171397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 97971653667749703779123725 36739370125406138917171397)
                ·
                  refine ⟨6888631898513651046969637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36739370125406138917171397 6888631898513651046969637)
                  ·
                    refine ⟨1291618480971309571306807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6888631898513651046969637 1291618480971309571306807)
                    ·
                      rfl

theorem cell22_3773127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 3, 4, 4].length) (baseStart_3773127 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3773127 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3773127 prefixEnd_3773127 := by exact prefixLift 3773127
  have htrace : WordTrace (prefixWord ++ tailWord_3773127) baseStart_3773127 baseEnd_3773127 := by
    simpa [prefixWord, tailWord_3773127, baseEnd_3773127] using wordTrace_append hprefix tailTrace_3773127
  have hstable : (prefixWord ++ tailWord_3773127).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3773127).length < 2 ^ (prefixWord ++ tailWord_3773127).sum := by decide
  have hdescent : baseEnd_3773127 < baseStart_3773127 := by decide
  rcases family_descends (prefixWord ++ tailWord_3773127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3773191 : List Nat := [1, 1, 4, 4, 1, 1, 1, 3, 3, 3]
def baseStart_3773191 : Nat := 118140960795 + 3773191 * 2 ^ 59
def prefixEnd_3773191 : Nat := 4983230072969 + 3 ^ 40 * 3773191 * 2
def baseEnd_3773191 : Nat := 1291640389479234737706611

theorem tailTrace_3773191 : CollatzResearch.WordTrace tailWord_3773191 prefixEnd_3773191 1291640389479234737706611 := by
  unfold tailWord_3773191
  simp only [CollatzResearch.WordTrace]
  refine ⟨137619581673380891563831427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91746387782253927709220951 137619581673380891563831427)
  ·
    refine ⟨206429372510071337345747141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137619581673380891563831427 206429372510071337345747141)
    ·
      refine ⟨38705507345638375752327589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 206429372510071337345747141 38705507345638375752327589)
      ·
        refine ⟨7257282627307195453561423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38705507345638375752327589 7257282627307195453561423)
        ·
          refine ⟨10885923940960793180342135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7257282627307195453561423 10885923940960793180342135)
          ·
            refine ⟨16328885911441189770513203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10885923940960793180342135 16328885911441189770513203)
            ·
              refine ⟨24493328867161784655769805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16328885911441189770513203 24493328867161784655769805)
              ·
                refine ⟨9184998325185669245913677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24493328867161784655769805 9184998325185669245913677)
                ·
                  refine ⟨3444374371944625967217629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9184998325185669245913677 3444374371944625967217629)
                  ·
                    refine ⟨1291640389479234737706611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3444374371944625967217629 1291640389479234737706611)
                    ·
                      rfl

theorem cell22_3773191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 1, 3, 3, 3].length) (baseStart_3773191 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3773191 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3773191 prefixEnd_3773191 := by exact prefixLift 3773191
  have htrace : WordTrace (prefixWord ++ tailWord_3773191) baseStart_3773191 baseEnd_3773191 := by
    simpa [prefixWord, tailWord_3773191, baseEnd_3773191] using wordTrace_append hprefix tailTrace_3773191
  have hstable : (prefixWord ++ tailWord_3773191).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3773191).length < 2 ^ (prefixWord ++ tailWord_3773191).sum := by decide
  have hdescent : baseEnd_3773191 < baseStart_3773191 := by decide
  rcases family_descends (prefixWord ++ tailWord_3773191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3773232 : List Nat := [2, 1, 1, 1, 2, 2, 1, 4, 8]
def baseStart_3773232 : Nat := 118140960795 + 3773232 * 2 ^ 59
def prefixEnd_3773232 : Nat := 4983230072969 + 3 ^ 40 * 3773232 * 2
def baseEnd_3773232 : Nat := 430551474872374765810495

theorem tailTrace_3773232 : CollatzResearch.WordTrace tailWord_3773232 prefixEnd_3773232 430551474872374765810495 := by
  unfold tailWord_3773232
  simp only [CollatzResearch.WordTrace]
  refine ⟨68810538533116177783036975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91747384710821570377382633 68810538533116177783036975)
  ·
    refine ⟨103215807799674266674555463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68810538533116177783036975 103215807799674266674555463)
    ·
      refine ⟨154823711699511400011833195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103215807799674266674555463 154823711699511400011833195)
      ·
        refine ⟨232235567549267100017749793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154823711699511400011833195 232235567549267100017749793)
        ·
          refine ⟨174176675661950325013312345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 232235567549267100017749793 174176675661950325013312345)
          ·
            refine ⟨130632506746462743759984259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 174176675661950325013312345 130632506746462743759984259)
            ·
              refine ⟨195948760119694115639976389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 130632506746462743759984259 195948760119694115639976389)
              ·
                refine ⟨36740392522442646682495573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 195948760119694115639976389 36740392522442646682495573)
                ·
                  refine ⟨430551474872374765810495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 36740392522442646682495573 430551474872374765810495)
                  ·
                    rfl

theorem cell22_3773232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 4, 8].length) (baseStart_3773232 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3773232 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3773232 prefixEnd_3773232 := by exact prefixLift 3773232
  have htrace : WordTrace (prefixWord ++ tailWord_3773232) baseStart_3773232 baseEnd_3773232 := by
    simpa [prefixWord, tailWord_3773232, baseEnd_3773232] using wordTrace_append hprefix tailTrace_3773232
  have hstable : (prefixWord ++ tailWord_3773232).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3773232).length < 2 ^ (prefixWord ++ tailWord_3773232).sum := by decide
  have hdescent : baseEnd_3773232 < baseStart_3773232 := by decide
  rcases family_descends (prefixWord ++ tailWord_3773232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3773294 : List Nat := [4, 1, 2, 3, 12]
def baseStart_3773294 : Nat := 118140960795 + 3773294 * 2 ^ 59
def prefixEnd_3773294 : Nat := 4983230072969 + 3 ^ 40 * 3773294 * 2
def baseEnd_3773294 : Nat := 5315537648083032108565

theorem tailTrace_3773294 : CollatzResearch.WordTrace tailWord_3773294 prefixEnd_3773294 5315537648083032108565 := by
  unfold tailWord_3773294
  simp only [CollatzResearch.WordTrace]
  refine ⟨17202917299000967519353867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 91748892261338493436553957 17202917299000967519353867)
  ·
    refine ⟨25804375948501451279030801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17202917299000967519353867 25804375948501451279030801)
    ·
      refine ⟨19353281961376088459273101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25804375948501451279030801 19353281961376088459273101)
      ·
        refine ⟨7257480735516033172227413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19353281961376088459273101 7257480735516033172227413)
        ·
          refine ⟨5315537648083032108565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 7257480735516033172227413 5315537648083032108565)
          ·
            rfl

theorem cell22_3773294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 12].length) (baseStart_3773294 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3773294 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3773294 prefixEnd_3773294 := by exact prefixLift 3773294
  have htrace : WordTrace (prefixWord ++ tailWord_3773294) baseStart_3773294 baseEnd_3773294 := by
    simpa [prefixWord, tailWord_3773294, baseEnd_3773294] using wordTrace_append hprefix tailTrace_3773294
  have hstable : (prefixWord ++ tailWord_3773294).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3773294).length < 2 ^ (prefixWord ++ tailWord_3773294).sum := by decide
  have hdescent : baseEnd_3773294 < baseStart_3773294 := by decide
  rcases family_descends (prefixWord ++ tailWord_3773294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3773330 : List Nat := [3, 2, 3, 2, 2, 2, 1, 1, 2, 4]
def baseStart_3773330 : Nat := 118140960795 + 3773330 * 2 ^ 59
def prefixEnd_3773330 : Nat := 4983230072969 + 3 ^ 40 * 3773330 * 2
def baseEnd_3773330 : Nat := 1291687972019884708481185

theorem tailTrace_3773330 : CollatzResearch.WordTrace tailWord_3773330 prefixEnd_3773330 1291687972019884708481185 := by
  unfold tailWord_3773330
  simp only [CollatzResearch.WordTrace]
  refine ⟨34406162854969329575785361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91749767613251545535427629 34406162854969329575785361)
  ·
    refine ⟨25804622141226997181839021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34406162854969329575785361 25804622141226997181839021)
    ·
      refine ⟨9676733302960123943189633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25804622141226997181839021 9676733302960123943189633)
      ·
        refine ⟨7257549977220092957392225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9676733302960123943189633 7257549977220092957392225)
        ·
          refine ⟨5443162482915069718044169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7257549977220092957392225 5443162482915069718044169)
          ·
            refine ⟨4082371862186302288533127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5443162482915069718044169 4082371862186302288533127)
            ·
              refine ⟨6123557793279453432799691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4082371862186302288533127 6123557793279453432799691)
              ·
                refine ⟨9185336689919180149199537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6123557793279453432799691 9185336689919180149199537)
                ·
                  refine ⟨6889002517439385111899653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9185336689919180149199537 6889002517439385111899653)
                  ·
                    refine ⟨1291687972019884708481185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6889002517439385111899653 1291687972019884708481185)
                    ·
                      rfl

theorem cell22_3773330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 2, 1, 1, 2, 4].length) (baseStart_3773330 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3773330 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3773330 prefixEnd_3773330 := by exact prefixLift 3773330
  have htrace : WordTrace (prefixWord ++ tailWord_3773330) baseStart_3773330 baseEnd_3773330 := by
    simpa [prefixWord, tailWord_3773330, baseEnd_3773330] using wordTrace_append hprefix tailTrace_3773330
  have hstable : (prefixWord ++ tailWord_3773330).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3773330).length < 2 ^ (prefixWord ++ tailWord_3773330).sum := by decide
  have hdescent : baseEnd_3773330 < baseStart_3773330 := by decide
  rcases family_descends (prefixWord ++ tailWord_3773330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3773366 : List Nat := [5, 1, 4, 1, 1, 1, 3, 1, 2, 3]
def baseStart_3773366 : Nat := 118140960795 + 3773366 * 2 ^ 59
def prefixEnd_3773366 : Nat := 4983230072969 + 3 ^ 40 * 3773366 * 2
def baseEnd_3773366 : Nat := 1291700295555592614581075

theorem tailTrace_3773366 : CollatzResearch.WordTrace tailWord_3773366 prefixEnd_3773366 1291700295555592614581075 := by
  unfold tailWord_3773366
  simp only [CollatzResearch.WordTrace]
  refine ⟨8601622777984181028215747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 91750642965164597634301301 8601622777984181028215747)
  ·
    refine ⟨12902434166976271542323621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8601622777984181028215747 12902434166976271542323621)
    ·
      refine ⟨2419206406308050914185679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12902434166976271542323621 2419206406308050914185679)
      ·
        refine ⟨3628809609462076371278519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2419206406308050914185679 3628809609462076371278519)
        ·
          refine ⟨5443214414193114556917779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3628809609462076371278519 5443214414193114556917779)
          ·
            refine ⟨8164821621289671835376669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5443214414193114556917779 8164821621289671835376669)
            ·
              refine ⟨3061808107983626938266251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8164821621289671835376669 3061808107983626938266251)
              ·
                refine ⟨4592712161975440407399377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3061808107983626938266251 4592712161975440407399377)
                ·
                  refine ⟨3444534121481580305549533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4592712161975440407399377 3444534121481580305549533)
                  ·
                    refine ⟨1291700295555592614581075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3444534121481580305549533 1291700295555592614581075)
                    ·
                      rfl

theorem cell22_3773366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 3, 1, 2, 3].length) (baseStart_3773366 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3773366 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3773366 prefixEnd_3773366 := by exact prefixLift 3773366
  have htrace : WordTrace (prefixWord ++ tailWord_3773366) baseStart_3773366 baseEnd_3773366 := by
    simpa [prefixWord, tailWord_3773366, baseEnd_3773366] using wordTrace_append hprefix tailTrace_3773366
  have hstable : (prefixWord ++ tailWord_3773366).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3773366).length < 2 ^ (prefixWord ++ tailWord_3773366).sum := by decide
  have hdescent : baseEnd_3773366 < baseStart_3773366 := by decide
  rcases family_descends (prefixWord ++ tailWord_3773366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3773418 : List Nat := [3, 1, 3, 1, 2, 4, 1, 1, 6]
def baseStart_3773418 : Nat := 118140960795 + 3773418 * 2 ^ 59
def prefixEnd_3773418 : Nat := 4983230072969 + 3 ^ 40 * 3773418 * 2
def baseEnd_3773418 : Nat := 430572698739427270760305

theorem tailTrace_3773418 : CollatzResearch.WordTrace tailWord_3773418 prefixEnd_3773418 430572698739427270760305 := by
  unfold tailWord_3773418
  simp only [CollatzResearch.WordTrace]
  refine ⟨34406965260889627333086227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91751907362372339554896605 34406965260889627333086227)
  ·
    refine ⟨51610447891334440999629341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34406965260889627333086227 51610447891334440999629341)
    ·
      refine ⟨19353917959250415374861003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51610447891334440999629341 19353917959250415374861003)
      ·
        refine ⟨29030876938875623062291505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19353917959250415374861003 29030876938875623062291505)
        ·
          refine ⟨21773157704156717296718629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29030876938875623062291505 21773157704156717296718629)
          ·
            refine ⟨4082467069529384493134743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21773157704156717296718629 4082467069529384493134743)
            ·
              refine ⟨6123700604294076739702115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4082467069529384493134743 6123700604294076739702115)
              ·
                refine ⟨9185550906441115109553173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6123700604294076739702115 9185550906441115109553173)
                ·
                  refine ⟨430572698739427270760305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9185550906441115109553173 430572698739427270760305)
                  ·
                    rfl

theorem cell22_3773418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 4, 1, 1, 6].length) (baseStart_3773418 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3773418 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3773418 prefixEnd_3773418 := by exact prefixLift 3773418
  have htrace : WordTrace (prefixWord ++ tailWord_3773418) baseStart_3773418 baseEnd_3773418 := by
    simpa [prefixWord, tailWord_3773418, baseEnd_3773418] using wordTrace_append hprefix tailTrace_3773418
  have hstable : (prefixWord ++ tailWord_3773418).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3773418).length < 2 ^ (prefixWord ++ tailWord_3773418).sum := by decide
  have hdescent : baseEnd_3773418 < baseStart_3773418 := by decide
  rcases family_descends (prefixWord ++ tailWord_3773418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3773433 : List Nat := [1, 2, 1, 3, 1, 3, 3, 3, 2, 3]
def baseStart_3773433 : Nat := 118140960795 + 3773433 * 2 ^ 59
def prefixEnd_3773433 : Nat := 4983230072969 + 3 ^ 40 * 3773433 * 2
def baseEnd_3773433 : Nat := 1291723231024826773155869

theorem tailTrace_3773433 : CollatzResearch.WordTrace tailWord_3773433 prefixEnd_3773433 1291723231024826773155869 := by
  unfold tailWord_3773433
  simp only [CollatzResearch.WordTrace]
  refine ⟨137628408138504166894140953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91752272092336111262760635 137628408138504166894140953)
  ·
    refine ⟨103221306103878125170605715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137628408138504166894140953 103221306103878125170605715)
    ·
      refine ⟨154831959155817187755908573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103221306103878125170605715 154831959155817187755908573)
      ·
        refine ⟨58061984683431445408465715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 154831959155817187755908573 58061984683431445408465715)
        ·
          refine ⟨87092977025147168112698573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58061984683431445408465715 87092977025147168112698573)
          ·
            refine ⟨32659866384430188042261965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87092977025147168112698573 32659866384430188042261965)
            ·
              refine ⟨12247449894161320515848237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32659866384430188042261965 12247449894161320515848237)
              ·
                refine ⟨4592793710310495193443089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12247449894161320515848237 4592793710310495193443089)
                ·
                  refine ⟨3444595282732871395082317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4592793710310495193443089 3444595282732871395082317)
                  ·
                    refine ⟨1291723231024826773155869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3444595282732871395082317 1291723231024826773155869)
                    ·
                      rfl

theorem cell22_3773433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 3, 3, 2, 3].length) (baseStart_3773433 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3773433 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3773433 prefixEnd_3773433 := by exact prefixLift 3773433
  have htrace : WordTrace (prefixWord ++ tailWord_3773433) baseStart_3773433 baseEnd_3773433 := by
    simpa [prefixWord, tailWord_3773433, baseEnd_3773433] using wordTrace_append hprefix tailTrace_3773433
  have hstable : (prefixWord ++ tailWord_3773433).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3773433).length < 2 ^ (prefixWord ++ tailWord_3773433).sum := by decide
  have hdescent : baseEnd_3773433 < baseStart_3773433 := by decide
  rcases family_descends (prefixWord ++ tailWord_3773433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3773448 : List Nat := [2, 1, 3, 2, 1, 4, 2, 1, 2, 4]
def baseStart_3773448 : Nat := 118140960795 + 3773448 * 2 ^ 59
def prefixEnd_3773448 : Nat := 4983230072969 + 3 ^ 40 * 3773448 * 2
def baseEnd_3773448 : Nat := 1291728365831371734030823

theorem tailTrace_3773448 : CollatzResearch.WordTrace tailWord_3773448 prefixEnd_3773448 1291728365831371734030823 := by
  unfold tailWord_3773448
  simp only [CollatzResearch.WordTrace]
  refine ⟨68814477616724912227968499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91752636822299882970624665 68814477616724912227968499)
  ·
    refine ⟨103221716425087368341952749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68814477616724912227968499 103221716425087368341952749)
    ·
      refine ⟨38708143659407763128232281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103221716425087368341952749 38708143659407763128232281)
      ·
        refine ⟨29031107744555822346174211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38708143659407763128232281 29031107744555822346174211)
        ·
          refine ⟨43546661616833733519261317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29031107744555822346174211 43546661616833733519261317)
          ·
            refine ⟨8164999053156325034861497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43546661616833733519261317 8164999053156325034861497)
            ·
              refine ⟨6123749289867243776146123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8164999053156325034861497 6123749289867243776146123)
              ·
                refine ⟨9185623934800865664219185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6123749289867243776146123 9185623934800865664219185)
                ·
                  refine ⟨6889217951100649248164389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9185623934800865664219185 6889217951100649248164389)
                  ·
                    refine ⟨1291728365831371734030823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6889217951100649248164389 1291728365831371734030823)
                    ·
                      rfl

theorem cell22_3773448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 2, 1, 2, 4].length) (baseStart_3773448 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3773448 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3773448 prefixEnd_3773448 := by exact prefixLift 3773448
  have htrace : WordTrace (prefixWord ++ tailWord_3773448) baseStart_3773448 baseEnd_3773448 := by
    simpa [prefixWord, tailWord_3773448, baseEnd_3773448] using wordTrace_append hprefix tailTrace_3773448
  have hstable : (prefixWord ++ tailWord_3773448).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3773448).length < 2 ^ (prefixWord ++ tailWord_3773448).sum := by decide
  have hdescent : baseEnd_3773448 < baseStart_3773448 := by decide
  rcases family_descends (prefixWord ++ tailWord_3773448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3773469 : List Nat := [1, 4, 2, 2, 4, 1, 2, 2, 4]
def baseStart_3773469 : Nat := 118140960795 + 3773469 * 2 ^ 59
def prefixEnd_3773469 : Nat := 4983230072969 + 3 ^ 40 * 3773469 * 2
def baseEnd_3773469 : Nat := 430578518186844893085253

theorem tailTrace_3773469 : CollatzResearch.WordTrace tailWord_3773469 prefixEnd_3773469 430578518186844893085253 := by
  unfold tailWord_3773469
  simp only [CollatzResearch.WordTrace]
  refine ⟨137629721166373745042451461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91753147444249163361634307 137629721166373745042451461)
  ·
    refine ⟨25805572718695077195459649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 137629721166373745042451461 25805572718695077195459649)
    ·
      refine ⟨19354179539021307896594737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25805572718695077195459649 19354179539021307896594737)
      ·
        refine ⟨14515634654265980922446053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19354179539021307896594737 14515634654265980922446053)
        ·
          refine ⟨2721681497674871422958635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14515634654265980922446053 2721681497674871422958635)
          ·
            refine ⟨4082522246512307134437953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2721681497674871422958635 4082522246512307134437953)
            ·
              refine ⟨3061891684884230350828465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4082522246512307134437953 3061891684884230350828465)
              ·
                refine ⟨2296418763663172763121349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3061891684884230350828465 2296418763663172763121349)
                ·
                  refine ⟨430578518186844893085253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2296418763663172763121349 430578518186844893085253)
                  ·
                    rfl

theorem cell22_3773469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 4, 1, 2, 2, 4].length) (baseStart_3773469 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3773469 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3773469 prefixEnd_3773469 := by exact prefixLift 3773469
  have htrace : WordTrace (prefixWord ++ tailWord_3773469) baseStart_3773469 baseEnd_3773469 := by
    simpa [prefixWord, tailWord_3773469, baseEnd_3773469] using wordTrace_append hprefix tailTrace_3773469
  have hstable : (prefixWord ++ tailWord_3773469).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3773469).length < 2 ^ (prefixWord ++ tailWord_3773469).sum := by decide
  have hdescent : baseEnd_3773469 < baseStart_3773469 := by decide
  rcases family_descends (prefixWord ++ tailWord_3773469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3773568 : List Nat := [2, 1, 1, 2, 1, 3, 3, 2, 4, 3]
def baseStart_3773568 : Nat := 118140960795 + 3773568 * 2 ^ 59
def prefixEnd_3773568 : Nat := 4983230072969 + 3 ^ 40 * 3773568 * 2
def baseEnd_3773568 : Nat := 1291769444283731421030455

theorem tailTrace_3773568 : CollatzResearch.WordTrace tailWord_3773568 prefixEnd_3773568 1291769444283731421030455 := by
  unfold tailWord_3773568
  simp only [CollatzResearch.WordTrace]
  refine ⟨68816665996507542475152679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91755554662010056633536905 68816665996507542475152679)
  ·
    refine ⟨103224998994761313712729019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68816665996507542475152679 103224998994761313712729019)
    ·
      refine ⟨154837498492141970569093529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103224998994761313712729019 154837498492141970569093529)
      ·
        refine ⟨116128123869106477926820147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154837498492141970569093529 116128123869106477926820147)
        ·
          refine ⟨174192185803659716890230221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116128123869106477926820147 174192185803659716890230221)
          ·
            refine ⟨65322069676372393833836333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 174192185803659716890230221 65322069676372393833836333)
            ·
              refine ⟨24495776128639647687688625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65322069676372393833836333 24495776128639647687688625)
              ·
                refine ⟨18371832096479735765766469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24495776128639647687688625 18371832096479735765766469)
                ·
                  refine ⟨3444718518089950456081213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18371832096479735765766469 3444718518089950456081213)
                  ·
                    refine ⟨1291769444283731421030455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3444718518089950456081213 1291769444283731421030455)
                    ·
                      rfl

theorem cell22_3773568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 3, 2, 4, 3].length) (baseStart_3773568 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3773568 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3773568 prefixEnd_3773568 := by exact prefixLift 3773568
  have htrace : WordTrace (prefixWord ++ tailWord_3773568) baseStart_3773568 baseEnd_3773568 := by
    simpa [prefixWord, tailWord_3773568, baseEnd_3773568] using wordTrace_append hprefix tailTrace_3773568
  have hstable : (prefixWord ++ tailWord_3773568).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3773568).length < 2 ^ (prefixWord ++ tailWord_3773568).sum := by decide
  have hdescent : baseEnd_3773568 < baseStart_3773568 := by decide
  rcases family_descends (prefixWord ++ tailWord_3773568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3773690 : List Nat := [3, 1, 1, 1, 1, 4, 3, 3, 1, 4]
def baseStart_3773690 : Nat := 118140960795 + 3773690 * 2 ^ 59
def prefixEnd_3773690 : Nat := 4983230072969 + 3 ^ 40 * 3773690 * 2
def baseEnd_3773690 : Nat := 1291811207376963769480081

theorem tailTrace_3773690 : CollatzResearch.WordTrace tailWord_3773690 prefixEnd_3773690 1291811207376963769480081 := by
  unfold tailWord_3773690
  simp only [CollatzResearch.WordTrace]
  refine ⟨34409445424643274946561631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91758521132382066524164349 34409445424643274946561631)
  ·
    refine ⟨51614168136964912419842447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34409445424643274946561631 51614168136964912419842447)
    ·
      refine ⟨77421252205447368629763671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51614168136964912419842447 77421252205447368629763671)
      ·
        refine ⟨116131878308171052944645507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77421252205447368629763671 116131878308171052944645507)
        ·
          refine ⟨174197817462256579416968261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116131878308171052944645507 174197817462256579416968261)
          ·
            refine ⟨32662090774173108640681549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 174197817462256579416968261 32662090774173108640681549)
            ·
              refine ⟨12248284040314915740255581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32662090774173108640681549 12248284040314915740255581)
              ·
                refine ⟨4593106515118093402595843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12248284040314915740255581 4593106515118093402595843)
                ·
                  refine ⟨6889659772677140103893765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4593106515118093402595843 6889659772677140103893765)
                  ·
                    refine ⟨1291811207376963769480081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6889659772677140103893765 1291811207376963769480081)
                    ·
                      rfl

theorem cell22_3773690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 3, 3, 1, 4].length) (baseStart_3773690 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3773690 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3773690 prefixEnd_3773690 := by exact prefixLift 3773690
  have htrace : WordTrace (prefixWord ++ tailWord_3773690) baseStart_3773690 baseEnd_3773690 := by
    simpa [prefixWord, tailWord_3773690, baseEnd_3773690] using wordTrace_append hprefix tailTrace_3773690
  have hstable : (prefixWord ++ tailWord_3773690).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3773690).length < 2 ^ (prefixWord ++ tailWord_3773690).sum := by decide
  have hdescent : baseEnd_3773690 < baseStart_3773690 := by decide
  rcases family_descends (prefixWord ++ tailWord_3773690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3773705 : List Nat := [1, 2, 1, 1, 3, 3, 1, 6, 4]
def baseStart_3773705 : Nat := 118140960795 + 3773705 * 2 ^ 59
def prefixEnd_3773705 : Nat := 4983230072969 + 3 ^ 40 * 3773705 * 2
def baseEnd_3773705 : Nat := 430605447394502910118345

theorem tailTrace_3773705 : CollatzResearch.WordTrace tailWord_3773705 prefixEnd_3773705 430605447394502910118345 := by
  unfold tailWord_3773705
  simp only [CollatzResearch.WordTrace]
  refine ⟨137638328793518757348042569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91758885862345838232028379 137638328793518757348042569)
  ·
    refine ⟨103228746595139068011031927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137638328793518757348042569 103228746595139068011031927)
    ·
      refine ⟨154843119892708602016547891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103228746595139068011031927 154843119892708602016547891)
      ·
        refine ⟨232264679839062903024821837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154843119892708602016547891 232264679839062903024821837)
        ·
          refine ⟨87099254939648588634308189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 232264679839062903024821837 87099254939648588634308189)
          ·
            refine ⟨32662220602368220737865571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87099254939648588634308189 32662220602368220737865571)
            ·
              refine ⟨48993330903552331106798357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32662220602368220737865571 48993330903552331106798357)
              ·
                refine ⟨2296562386104015520631173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 48993330903552331106798357 2296562386104015520631173)
                ·
                  refine ⟨430605447394502910118345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2296562386104015520631173 430605447394502910118345)
                  ·
                    rfl

theorem cell22_3773705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 6, 4].length) (baseStart_3773705 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3773705 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3773705 prefixEnd_3773705 := by exact prefixLift 3773705
  have htrace : WordTrace (prefixWord ++ tailWord_3773705) baseStart_3773705 baseEnd_3773705 := by
    simpa [prefixWord, tailWord_3773705, baseEnd_3773705] using wordTrace_append hprefix tailTrace_3773705
  have hstable : (prefixWord ++ tailWord_3773705).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3773705).length < 2 ^ (prefixWord ++ tailWord_3773705).sum := by decide
  have hdescent : baseEnd_3773705 < baseStart_3773705 := by decide
  rcases family_descends (prefixWord ++ tailWord_3773705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3773720 : List Nat := [2, 1, 2, 3, 1, 3, 3, 1, 1, 5]
def baseStart_3773720 : Nat := 118140960795 + 3773720 * 2 ^ 59
def prefixEnd_3773720 : Nat := 4983230072969 + 3 ^ 40 * 3773720 * 2
def baseEnd_3773720 : Nat := 1291821476990053691229989

theorem tailTrace_3773720 : CollatzResearch.WordTrace tailWord_3773720 prefixEnd_3773720 1291821476990053691229989 := by
  unfold tailWord_3773720
  simp only [CollatzResearch.WordTrace]
  refine ⟨68819437944232207454919307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91759250592309609939892409 68819437944232207454919307)
  ·
    refine ⟨103229156916348311182378961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68819437944232207454919307 103229156916348311182378961)
    ·
      refine ⟨77421867687261233386784221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103229156916348311182378961 77421867687261233386784221)
      ·
        refine ⟨29033200382722962520044083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77421867687261233386784221 29033200382722962520044083)
        ·
          refine ⟨43549800574084443780066125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29033200382722962520044083 43549800574084443780066125)
          ·
            refine ⟨16331175215281666417524797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43549800574084443780066125 16331175215281666417524797)
            ·
              refine ⟨6124190705730624906571799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16331175215281666417524797 6124190705730624906571799)
              ·
                refine ⟨9186286058595937359857699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6124190705730624906571799 9186286058595937359857699)
                ·
                  refine ⟨13779429087893906039786549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9186286058595937359857699 13779429087893906039786549)
                  ·
                    refine ⟨1291821476990053691229989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13779429087893906039786549 1291821476990053691229989)
                    ·
                      rfl

theorem cell22_3773720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 3, 1, 1, 5].length) (baseStart_3773720 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3773720 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3773720 prefixEnd_3773720 := by exact prefixLift 3773720
  have htrace : WordTrace (prefixWord ++ tailWord_3773720) baseStart_3773720 baseEnd_3773720 := by
    simpa [prefixWord, tailWord_3773720, baseEnd_3773720] using wordTrace_append hprefix tailTrace_3773720
  have hstable : (prefixWord ++ tailWord_3773720).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3773720).length < 2 ^ (prefixWord ++ tailWord_3773720).sum := by decide
  have hdescent : baseEnd_3773720 < baseStart_3773720 := by decide
  rcases family_descends (prefixWord ++ tailWord_3773720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3773763 : List Nat := [1, 1, 1, 3, 1, 3, 1, 3, 2, 6]
def baseStart_3773763 : Nat := 118140960795 + 3773763 * 2 ^ 59
def prefixEnd_3773763 : Nat := 4983230072969 + 3 ^ 40 * 3773763 * 2
def baseEnd_3773763 : Nat := 1291836196768815912404857

theorem tailTrace_3773763 : CollatzResearch.WordTrace tailWord_3773763 prefixEnd_3773763 1291836196768815912404857 := by
  unfold tailWord_3773763
  simp only [CollatzResearch.WordTrace]
  refine ⟨137640444227308633253653943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91760296151539088835769295 137640444227308633253653943)
  ·
    refine ⟨206460666340962949880480915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137640444227308633253653943 206460666340962949880480915)
    ·
      refine ⟨309690999511444424820721373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206460666340962949880480915 309690999511444424820721373)
      ·
        refine ⟨116134124816791659307770515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 309690999511444424820721373 116134124816791659307770515)
        ·
          refine ⟨174201187225187488961655773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116134124816791659307770515 174201187225187488961655773)
          ·
            refine ⟨65325445209445308360620915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 174201187225187488961655773 65325445209445308360620915)
            ·
              refine ⟨97988167814167962540931373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65325445209445308360620915 97988167814167962540931373)
              ·
                refine ⟨36745562930312985952849265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 97988167814167962540931373 36745562930312985952849265)
                ·
                  refine ⟨27559172197734739464636949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36745562930312985952849265 27559172197734739464636949)
                  ·
                    refine ⟨1291836196768815912404857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27559172197734739464636949 1291836196768815912404857)
                    ·
                      rfl

theorem cell22_3773763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 3, 2, 6].length) (baseStart_3773763 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3773763 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3773763 prefixEnd_3773763 := by exact prefixLift 3773763
  have htrace : WordTrace (prefixWord ++ tailWord_3773763) baseStart_3773763 baseEnd_3773763 := by
    simpa [prefixWord, tailWord_3773763, baseEnd_3773763] using wordTrace_append hprefix tailTrace_3773763
  have hstable : (prefixWord ++ tailWord_3773763).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3773763).length < 2 ^ (prefixWord ++ tailWord_3773763).sum := by decide
  have hdescent : baseEnd_3773763 < baseStart_3773763 := by decide
  rcases family_descends (prefixWord ++ tailWord_3773763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3773810 : List Nat := [3, 2, 1, 2, 1, 2, 2, 2, 2, 5]
def baseStart_3773810 : Nat := 118140960795 + 3773810 * 2 ^ 59
def prefixEnd_3773810 : Nat := 4983230072969 + 3 ^ 40 * 3773810 * 2
def baseEnd_3773810 : Nat := 1291852285829323456479713

theorem tailTrace_3773810 : CollatzResearch.WordTrace tailWord_3773810 prefixEnd_3773810 1291852285829323456479713 := by
  unfold tailWord_3773810
  simp only [CollatzResearch.WordTrace]
  refine ⟨34410539614534590070153721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91761438972092240187076589 34410539614534590070153721)
  ·
    refine ⟨25807904710900942552615291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34410539614534590070153721 25807904710900942552615291)
    ·
      refine ⟨38711857066351413828922937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25807904710900942552615291 38711857066351413828922937)
      ·
        refine ⟨29033892799763560371692203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38711857066351413828922937 29033892799763560371692203)
        ·
          refine ⟨43550839199645340557538305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29033892799763560371692203 43550839199645340557538305)
          ·
            refine ⟨32663129399734005418153729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43550839199645340557538305 32663129399734005418153729)
            ·
              refine ⟨24497347049800504063615297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32663129399734005418153729 24497347049800504063615297)
              ·
                refine ⟨18373010287350378047711473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24497347049800504063615297 18373010287350378047711473)
                ·
                  refine ⟨13779757715512783535783605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18373010287350378047711473 13779757715512783535783605)
                  ·
                    refine ⟨1291852285829323456479713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13779757715512783535783605 1291852285829323456479713)
                    ·
                      rfl

theorem cell22_3773810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 2, 2, 2, 5].length) (baseStart_3773810 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3773810 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3773810 prefixEnd_3773810 := by exact prefixLift 3773810
  have htrace : WordTrace (prefixWord ++ tailWord_3773810) baseStart_3773810 baseEnd_3773810 := by
    simpa [prefixWord, tailWord_3773810, baseEnd_3773810] using wordTrace_append hprefix tailTrace_3773810
  have hstable : (prefixWord ++ tailWord_3773810).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3773810).length < 2 ^ (prefixWord ++ tailWord_3773810).sum := by decide
  have hdescent : baseEnd_3773810 < baseStart_3773810 := by decide
  rcases family_descends (prefixWord ++ tailWord_3773810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3773872 : List Nat := [2, 1, 1, 1, 2, 1, 1, 8, 2, 3]
def baseStart_3773872 : Nat := 118140960795 + 3773872 * 2 ^ 59
def prefixEnd_3773872 : Nat := 4983230072969 + 3 ^ 40 * 3773872 * 2
def baseEnd_3773872 : Nat := 1291873509696375961429523

theorem tailTrace_3773872 : CollatzResearch.WordTrace tailWord_3773872 prefixEnd_3773872 1291873509696375961429523 := by
  unfold tailWord_3773872
  simp only [CollatzResearch.WordTrace]
  refine ⟨68822209891956872434685935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91762946522609163246247913 68822209891956872434685935)
  ·
    refine ⟨103233314837935308652028903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68822209891956872434685935 103233314837935308652028903)
    ·
      refine ⟨154849972256902962978043355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103233314837935308652028903 154849972256902962978043355)
      ·
        refine ⟨232274958385354444467065033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154849972256902962978043355 232274958385354444467065033)
        ·
          refine ⟨174206218789015833350298775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 232274958385354444467065033 174206218789015833350298775)
          ·
            refine ⟨261309328183523750025448163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 174206218789015833350298775 261309328183523750025448163)
            ·
              refine ⟨391963992275285625038172245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 261309328183523750025448163 391963992275285625038172245)
              ·
                refine ⟨4593328034476003418416081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 391963992275285625038172245 4593328034476003418416081)
                ·
                  refine ⟨3444996025857002563812061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4593328034476003418416081 3444996025857002563812061)
                  ·
                    refine ⟨1291873509696375961429523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3444996025857002563812061 1291873509696375961429523)
                    ·
                      rfl

theorem cell22_3773872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 8, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 8, 2, 3].length) (baseStart_3773872 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3773872 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3773872 prefixEnd_3773872 := by exact prefixLift 3773872
  have htrace : WordTrace (prefixWord ++ tailWord_3773872) baseStart_3773872 baseEnd_3773872 := by
    simpa [prefixWord, tailWord_3773872, baseEnd_3773872] using wordTrace_append hprefix tailTrace_3773872
  have hstable : (prefixWord ++ tailWord_3773872).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3773872).length < 2 ^ (prefixWord ++ tailWord_3773872).sum := by decide
  have hdescent : baseEnd_3773872 < baseStart_3773872 := by decide
  rcases family_descends (prefixWord ++ tailWord_3773872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3773885 : List Nat := [1, 4, 1, 2, 2, 1, 2, 9]
def baseStart_3773885 : Nat := 118140960795 + 3773885 * 2 ^ 59
def prefixEnd_3773885 : Nat := 4983230072969 + 3 ^ 40 * 3773885 * 2
def baseEnd_3773885 : Nat := 143541995540227584539387

theorem tailTrace_3773885 : CollatzResearch.WordTrace tailWord_3773885 prefixEnd_3773885 143541995540227584539387 := by
  unfold tailWord_3773885
  simp only [CollatzResearch.WordTrace]
  refine ⟨137644893932866648089595109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91763262621911098726396739 137644893932866648089595109)
  ·
    refine ⟨25808417612412496516799083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 137644893932866648089595109 25808417612412496516799083)
    ·
      refine ⟨38712626418618744775198625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25808417612412496516799083 38712626418618744775198625)
      ·
        refine ⟨29034469813964058581398969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38712626418618744775198625 29034469813964058581398969)
        ·
          refine ⟨21775852360473043936049227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29034469813964058581398969 21775852360473043936049227)
          ·
            refine ⟨32663778540709565904073841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21775852360473043936049227 32663778540709565904073841)
            ·
              refine ⟨24497833905532174428055381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32663778540709565904073841 24497833905532174428055381)
              ·
                refine ⟨143541995540227584539387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 24497833905532174428055381 143541995540227584539387)
                ·
                  rfl

theorem cell22_3773885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 2, 9].length) (baseStart_3773885 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3773885 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3773885 prefixEnd_3773885 := by exact prefixLift 3773885
  have htrace : WordTrace (prefixWord ++ tailWord_3773885) baseStart_3773885 baseEnd_3773885 := by
    simpa [prefixWord, tailWord_3773885, baseEnd_3773885] using wordTrace_append hprefix tailTrace_3773885
  have hstable : (prefixWord ++ tailWord_3773885).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3773885).length < 2 ^ (prefixWord ++ tailWord_3773885).sum := by decide
  have hdescent : baseEnd_3773885 < baseStart_3773885 := by decide
  rcases family_descends (prefixWord ++ tailWord_3773885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3773902 : List Nat := [4, 1, 1, 1, 2, 1, 6, 6]
def baseStart_3773902 : Nat := 118140960795 + 3773902 * 2 ^ 59
def prefixEnd_3773902 : Nat := 4983230072969 + 3 ^ 40 * 3773902 * 2
def baseEnd_3773902 : Nat := 143542642145496209242159

theorem tailTrace_3773902 : CollatzResearch.WordTrace tailWord_3773902 prefixEnd_3773902 143542642145496209242159 := by
  unfold tailWord_3773902
  simp only [CollatzResearch.WordTrace]
  refine ⟨17205689246725632499120495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 91763675982536706661975973 17205689246725632499120495)
  ·
    refine ⟨25808533870088448748680743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17205689246725632499120495 25808533870088448748680743)
    ·
      refine ⟨38712800805132673123021115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25808533870088448748680743 38712800805132673123021115)
      ·
        refine ⟨58069201207699009684531673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38712800805132673123021115 58069201207699009684531673)
        ·
          refine ⟨43551900905774257263398755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58069201207699009684531673 43551900905774257263398755)
          ·
            refine ⟨65327851358661385895098133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43551900905774257263398755 65327851358661385895098133)
            ·
              refine ⟨3062243032437252463832725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 65327851358661385895098133 3062243032437252463832725)
              ·
                refine ⟨143542642145496209242159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3062243032437252463832725 143542642145496209242159)
                ·
                  rfl

theorem cell22_3773902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 6, 6].length) (baseStart_3773902 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3773902 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3773902 prefixEnd_3773902 := by exact prefixLift 3773902
  have htrace : WordTrace (prefixWord ++ tailWord_3773902) baseStart_3773902 baseEnd_3773902 := by
    simpa [prefixWord, tailWord_3773902, baseEnd_3773902] using wordTrace_append hprefix tailTrace_3773902
  have hstable : (prefixWord ++ tailWord_3773902).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3773902).length < 2 ^ (prefixWord ++ tailWord_3773902).sum := by decide
  have hdescent : baseEnd_3773902 < baseStart_3773902 := by decide
  rcases family_descends (prefixWord ++ tailWord_3773902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3773908 : List Nat := [2, 4, 1, 2, 4, 1, 1, 3, 4]
def baseStart_3773908 : Nat := 118140960795 + 3773908 * 2 ^ 59
def prefixEnd_3773908 : Nat := 4983230072969 + 3 ^ 40 * 3773908 * 2
def baseEnd_3773908 : Nat := 430628611077361289176471

theorem tailTrace_3773908 : CollatzResearch.WordTrace tailWord_3773908 prefixEnd_3773908 430628611077361289176471 := by
  unfold tailWord_3773908
  simp only [CollatzResearch.WordTrace]
  refine ⟨68822866405891661508841189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91763821874522215345121585 68822866405891661508841189)
  ·
    refine ⟨12904287451104686532907723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 68822866405891661508841189 12904287451104686532907723)
    ·
      refine ⟨19356431176657029799361585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12904287451104686532907723 19356431176657029799361585)
      ·
        refine ⟨14517323382492772349521189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19356431176657029799361585 14517323382492772349521189)
        ·
          refine ⟨2721998134217394815535223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14517323382492772349521189 2721998134217394815535223)
          ·
            refine ⟨4082997201326092223302835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2721998134217394815535223 4082997201326092223302835)
            ·
              refine ⟨6124495801989138334954253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4082997201326092223302835 6124495801989138334954253)
              ·
                refine ⟨2296685925745926875607845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6124495801989138334954253 2296685925745926875607845)
                ·
                  refine ⟨430628611077361289176471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2296685925745926875607845 430628611077361289176471)
                  ·
                    rfl

theorem cell22_3773908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 4, 1, 1, 3, 4].length) (baseStart_3773908 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3773908 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3773908 prefixEnd_3773908 := by exact prefixLift 3773908
  have htrace : WordTrace (prefixWord ++ tailWord_3773908) baseStart_3773908 baseEnd_3773908 := by
    simpa [prefixWord, tailWord_3773908, baseEnd_3773908] using wordTrace_append hprefix tailTrace_3773908
  have hstable : (prefixWord ++ tailWord_3773908).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3773908).length < 2 ^ (prefixWord ++ tailWord_3773908).sum := by decide
  have hdescent : baseEnd_3773908 < baseStart_3773908 := by decide
  rcases family_descends (prefixWord ++ tailWord_3773908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3773945 : List Nat := [1, 2, 1, 3, 1, 2, 1, 3, 1, 7]
def baseStart_3773945 : Nat := 118140960795 + 3773945 * 2 ^ 59
def prefixEnd_3773945 : Nat := 4983230072969 + 3 ^ 40 * 3773945 * 2
def baseEnd_3773945 : Nat := 1291898499088228104354299

theorem tailTrace_3773945 : CollatzResearch.WordTrace tailWord_3773945 prefixEnd_3773945 1291898499088228104354299 := by
  unfold tailWord_3773945
  simp only [CollatzResearch.WordTrace]
  refine ⟨137647082312649278336779289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91764721541766185557852859 137647082312649278336779289)
  ·
    refine ⟨103235311734486958752584467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137647082312649278336779289 103235311734486958752584467)
    ·
      refine ⟨154852967601730438128876701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103235311734486958752584467 154852967601730438128876701)
      ·
        refine ⟨58069862850648914298328763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 154852967601730438128876701 58069862850648914298328763)
        ·
          refine ⟨87104794275973371447493145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58069862850648914298328763 87104794275973371447493145)
          ·
            refine ⟨65328595706980028585619859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87104794275973371447493145 65328595706980028585619859)
            ·
              refine ⟨97992893560470042878429789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65328595706980028585619859 97992893560470042878429789)
              ·
                refine ⟨36747335085176266079411171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 97992893560470042878429789 36747335085176266079411171)
                ·
                  refine ⟨55121002627764399119116757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36747335085176266079411171 55121002627764399119116757)
                  ·
                    refine ⟨1291898499088228104354299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 55121002627764399119116757 1291898499088228104354299)
                    ·
                      rfl

theorem cell22_3773945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 3, 1, 7].length) (baseStart_3773945 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3773945 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3773945 prefixEnd_3773945 := by exact prefixLift 3773945
  have htrace : WordTrace (prefixWord ++ tailWord_3773945) baseStart_3773945 baseEnd_3773945 := by
    simpa [prefixWord, tailWord_3773945, baseEnd_3773945] using wordTrace_append hprefix tailTrace_3773945
  have hstable : (prefixWord ++ tailWord_3773945).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3773945).length < 2 ^ (prefixWord ++ tailWord_3773945).sum := by decide
  have hdescent : baseEnd_3773945 < baseStart_3773945 := by decide
  rcases family_descends (prefixWord ++ tailWord_3773945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3774007 : List Nat := [1, 1, 3, 1, 2, 4, 1, 3, 1, 5]
def baseStart_3774007 : Nat := 118140960795 + 3774007 * 2 ^ 59
def prefixEnd_3774007 : Nat := 4983230072969 + 3 ^ 40 * 3774007 * 2
def baseEnd_3774007 : Nat := 1291919722955280609304109

theorem tailTrace_3774007 : CollatzResearch.WordTrace tailWord_3774007 prefixEnd_3774007 1291919722955280609304109 := by
  unfold tailWord_3774007
  simp only [CollatzResearch.WordTrace]
  refine ⟨137649343638424662925536275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91766229092283108617024183 137649343638424662925536275)
  ·
    refine ⟨206474015457636994388304413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137649343638424662925536275 206474015457636994388304413)
    ·
      refine ⟨77427755796613872895614155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 206474015457636994388304413 77427755796613872895614155)
      ·
        refine ⟨116141633694920809343421233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77427755796613872895614155 116141633694920809343421233)
        ·
          refine ⟨87106225271190607007565925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116141633694920809343421233 87106225271190607007565925)
          ·
            refine ⟨16332417238348238813918611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 87106225271190607007565925 16332417238348238813918611)
            ·
              refine ⟨24498625857522358220877917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16332417238348238813918611 24498625857522358220877917)
              ·
                refine ⟨9186984696570884332829219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24498625857522358220877917 9186984696570884332829219)
                ·
                  refine ⟨13780477044856326499243829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9186984696570884332829219 13780477044856326499243829)
                  ·
                    refine ⟨1291919722955280609304109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13780477044856326499243829 1291919722955280609304109)
                    ·
                      rfl

theorem cell22_3774007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 1, 3, 1, 5].length) (baseStart_3774007 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3774007 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3774007 prefixEnd_3774007 := by exact prefixLift 3774007
  have htrace : WordTrace (prefixWord ++ tailWord_3774007) baseStart_3774007 baseEnd_3774007 := by
    simpa [prefixWord, tailWord_3774007, baseEnd_3774007] using wordTrace_append hprefix tailTrace_3774007
  have hstable : (prefixWord ++ tailWord_3774007).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3774007).length < 2 ^ (prefixWord ++ tailWord_3774007).sum := by decide
  have hdescent : baseEnd_3774007 < baseStart_3774007 := by decide
  rcases family_descends (prefixWord ++ tailWord_3774007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3774058 : List Nat := [3, 1, 3, 2, 1, 3, 3, 1, 2, 3]
def baseStart_3774058 : Nat := 118140960795 + 3774058 * 2 ^ 59
def prefixEnd_3774058 : Nat := 4983230072969 + 3 ^ 40 * 3774058 * 2
def baseEnd_3774058 : Nat := 1291937181297533476278953

theorem tailTrace_3774058 : CollatzResearch.WordTrace tailWord_3774058 prefixEnd_3774058 1291937181297533476278953 := by
  unfold tailWord_3774058
  simp only [CollatzResearch.WordTrace]
  refine ⟨34412800940309974658910707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91767469174159932423761885 34412800940309974658910707)
  ·
    refine ⟨51619201410464961988366061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34412800940309974658910707 51619201410464961988366061)
    ·
      refine ⟨19357200528924360745637273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51619201410464961988366061 19357200528924360745637273)
      ·
        refine ⟨14517900396693270559227955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19357200528924360745637273 14517900396693270559227955)
        ·
          refine ⟨21776850595039905838841933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14517900396693270559227955 21776850595039905838841933)
          ·
            refine ⟨8166318973139964689565725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21776850595039905838841933 8166318973139964689565725)
            ·
              refine ⟨3062369614927486758587147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8166318973139964689565725 3062369614927486758587147)
              ·
                refine ⟨4593554422391230137880721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3062369614927486758587147 4593554422391230137880721)
                ·
                  refine ⟨3445165816793422603410541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4593554422391230137880721 3445165816793422603410541)
                  ·
                    refine ⟨1291937181297533476278953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3445165816793422603410541 1291937181297533476278953)
                    ·
                      rfl

theorem cell22_3774058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 3, 1, 2, 3].length) (baseStart_3774058 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3774058 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3774058 prefixEnd_3774058 := by exact prefixLift 3774058
  have htrace : WordTrace (prefixWord ++ tailWord_3774058) baseStart_3774058 baseEnd_3774058 := by
    simpa [prefixWord, tailWord_3774058, baseEnd_3774058] using wordTrace_append hprefix tailTrace_3774058
  have hstable : (prefixWord ++ tailWord_3774058).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3774058).length < 2 ^ (prefixWord ++ tailWord_3774058).sum := by decide
  have hdescent : baseEnd_3774058 < baseStart_3774058 := by decide
  rcases family_descends (prefixWord ++ tailWord_3774058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3774097 : List Nat := [1, 2, 2, 1, 1, 1, 1, 6, 2, 5]
def baseStart_3774097 : Nat := 118140960795 + 3774097 * 2 ^ 59
def prefixEnd_3774097 : Nat := 4983230072969 + 3 ^ 40 * 3774097 * 2
def baseEnd_3774097 : Nat := 1291950531794550374553833

theorem tailTrace_3774097 : CollatzResearch.WordTrace tailWord_3774097 prefixEnd_3774097 1291950531794550374553833 := by
  unfold tailWord_3774097
  simp only [CollatzResearch.WordTrace]
  refine ⟨137652626208098608296312545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91768417472065738864208363 137652626208098608296312545)
  ·
    refine ⟨103239469656073956222234409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137652626208098608296312545 103239469656073956222234409)
    ·
      refine ⟨77429602242055467166675807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103239469656073956222234409 77429602242055467166675807)
      ·
        refine ⟨116144403363083200750013711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77429602242055467166675807 116144403363083200750013711)
        ·
          refine ⟨174216605044624801125020567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116144403363083200750013711 174216605044624801125020567)
          ·
            refine ⟨261324907566937201687530851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 174216605044624801125020567 261324907566937201687530851)
            ·
              refine ⟨391987361350405802531296277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 261324907566937201687530851 391987361350405802531296277)
              ·
                refine ⟨18374407563300271993654513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 391987361350405802531296277 18374407563300271993654513)
                ·
                  refine ⟨13780805672475203995240885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18374407563300271993654513 13780805672475203995240885)
                  ·
                    refine ⟨1291950531794550374553833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13780805672475203995240885 1291950531794550374553833)
                    ·
                      rfl

theorem cell22_3774097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 5].length) (baseStart_3774097 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3774097 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3774097 prefixEnd_3774097 := by exact prefixLift 3774097
  have htrace : WordTrace (prefixWord ++ tailWord_3774097) baseStart_3774097 baseEnd_3774097 := by
    simpa [prefixWord, tailWord_3774097, baseEnd_3774097] using wordTrace_append hprefix tailTrace_3774097
  have hstable : (prefixWord ++ tailWord_3774097).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3774097).length < 2 ^ (prefixWord ++ tailWord_3774097).sum := by decide
  have hdescent : baseEnd_3774097 < baseStart_3774097 := by decide
  rcases family_descends (prefixWord ++ tailWord_3774097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3774116 : List Nat := [2, 3, 1, 2, 2, 2, 4, 1, 5]
def baseStart_3774116 : Nat := 118140960795 + 3774116 * 2 ^ 59
def prefixEnd_3774116 : Nat := 4983230072969 + 3 ^ 40 * 3774116 * 2
def baseEnd_3774116 : Nat := 430652345294280219442925

theorem tailTrace_3774116 : CollatzResearch.WordTrace tailWord_3774116 prefixEnd_3774116 430652345294280219442925 := by
  unfold tailWord_3774116
  simp only [CollatzResearch.WordTrace]
  refine ⟨68826659597514887270627101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91768879463353183027502801 68826659597514887270627101)
  ·
    refine ⟨25809997349068082726485163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68826659597514887270627101 25809997349068082726485163)
    ·
      refine ⟨38714996023602124089727745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25809997349068082726485163 38714996023602124089727745)
      ·
        refine ⟨29036247017701593067295809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38714996023602124089727745 29036247017701593067295809)
        ·
          refine ⟨21777185263276194800471857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29036247017701593067295809 21777185263276194800471857)
          ·
            refine ⟨16332888947457146100353893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21777185263276194800471857 16332888947457146100353893)
            ·
              refine ⟨3062416677648214893816355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16332888947457146100353893 3062416677648214893816355)
              ·
                refine ⟨4593625016472322340724533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3062416677648214893816355 4593625016472322340724533)
                ·
                  refine ⟨430652345294280219442925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4593625016472322340724533 430652345294280219442925)
                  ·
                    rfl

theorem cell22_3774116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 4, 1, 5].length) (baseStart_3774116 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3774116 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3774116 prefixEnd_3774116 := by exact prefixLift 3774116
  have htrace : WordTrace (prefixWord ++ tailWord_3774116) baseStart_3774116 baseEnd_3774116 := by
    simpa [prefixWord, tailWord_3774116, baseEnd_3774116] using wordTrace_append hprefix tailTrace_3774116
  have hstable : (prefixWord ++ tailWord_3774116).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3774116).length < 2 ^ (prefixWord ++ tailWord_3774116).sum := by decide
  have hdescent : baseEnd_3774116 < baseStart_3774116 := by decide
  rcases family_descends (prefixWord ++ tailWord_3774116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3774127 : List Nat := [1, 1, 2, 1, 2, 4, 2, 1, 8]
def baseStart_3774127 : Nat := 118140960795 + 3774127 * 2 ^ 59
def prefixEnd_3774127 : Nat := 4983230072969 + 3 ^ 40 * 3774127 * 2
def baseEnd_3774127 : Nat := 430653600469213432101247

theorem tailTrace_3774127 : CollatzResearch.WordTrace tailWord_3774127 prefixEnd_3774127 430653600469213432101247 := by
  unfold tailWord_3774127
  simp only [CollatzResearch.WordTrace]
  refine ⟨137653720397989923419904635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91769146931993282279936423 137653720397989923419904635)
  ·
    refine ⟨206480580596984885129856953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137653720397989923419904635 206480580596984885129856953)
    ·
      refine ⟨154860435447738663847392715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 206480580596984885129856953 154860435447738663847392715)
      ·
        refine ⟨232290653171607995771089073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154860435447738663847392715 232290653171607995771089073)
        ·
          refine ⟨174217989878705996828316805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 232290653171607995771089073 174217989878705996828316805)
          ·
            refine ⟨32665873102257374405309401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 174217989878705996828316805 32665873102257374405309401)
            ·
              refine ⟨24499404826693030803982051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32665873102257374405309401 24499404826693030803982051)
              ·
                refine ⟨36749107240039546205973077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24499404826693030803982051 36749107240039546205973077)
                ·
                  refine ⟨430653600469213432101247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 36749107240039546205973077 430653600469213432101247)
                  ·
                    rfl

theorem cell22_3774127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 2, 1, 8].length) (baseStart_3774127 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3774127 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3774127 prefixEnd_3774127 := by exact prefixLift 3774127
  have htrace : WordTrace (prefixWord ++ tailWord_3774127) baseStart_3774127 baseEnd_3774127 := by
    simpa [prefixWord, tailWord_3774127, baseEnd_3774127] using wordTrace_append hprefix tailTrace_3774127
  have hstable : (prefixWord ++ tailWord_3774127).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3774127).length < 2 ^ (prefixWord ++ tailWord_3774127).sum := by decide
  have hdescent : baseEnd_3774127 < baseStart_3774127 := by decide
  rcases family_descends (prefixWord ++ tailWord_3774127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3774150 : List Nat := [6, 1, 2, 1, 1, 2, 2, 2, 5]
def baseStart_3774150 : Nat := 118140960795 + 3774150 * 2 ^ 59
def prefixEnd_3774150 : Nat := 4983230072969 + 3 ^ 40 * 3774150 * 2
def baseEnd_3774150 : Nat := 430656224925891967659557

theorem tailTrace_3774150 : CollatzResearch.WordTrace tailWord_3774150 prefixEnd_3774150 430656224925891967659557 := by
  unfold tailWord_3774150
  simp only [CollatzResearch.WordTrace]
  refine ⟨4301704977403331198374747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 91769706184604398898661269 4301704977403331198374747)
  ·
    refine ⟨6452557466104996797562121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4301704977403331198374747 6452557466104996797562121)
    ·
      refine ⟨4839418099578747598171591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6452557466104996797562121 4839418099578747598171591)
      ·
        refine ⟨7259127149368121397257387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4839418099578747598171591 7259127149368121397257387)
        ·
          refine ⟨10888690724052182095886081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7259127149368121397257387 10888690724052182095886081)
          ·
            refine ⟨8166518043039136571914561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10888690724052182095886081 8166518043039136571914561)
            ·
              refine ⟨6124888532279352428935921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8166518043039136571914561 6124888532279352428935921)
              ·
                refine ⟨4593666399209514321701941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6124888532279352428935921 4593666399209514321701941)
                ·
                  refine ⟨430656224925891967659557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4593666399209514321701941 430656224925891967659557)
                  ·
                    rfl

theorem cell22_3774150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 2, 2, 5].length) (baseStart_3774150 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3774150 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3774150 prefixEnd_3774150 := by exact prefixLift 3774150
  have htrace : WordTrace (prefixWord ++ tailWord_3774150) baseStart_3774150 baseEnd_3774150 := by
    simpa [prefixWord, tailWord_3774150, baseEnd_3774150] using wordTrace_append hprefix tailTrace_3774150
  have hstable : (prefixWord ++ tailWord_3774150).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3774150).length < 2 ^ (prefixWord ++ tailWord_3774150).sum := by decide
  have hdescent : baseEnd_3774150 < baseStart_3774150 := by decide
  rcases family_descends (prefixWord ++ tailWord_3774150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3774159 : List Nat := [1, 1, 2, 1, 1, 3, 1, 5, 4, 3]
def baseStart_3774159 : Nat := 118140960795 + 3774159 * 2 ^ 59
def prefixEnd_3774159 : Nat := 4983230072969 + 3 ^ 40 * 3774159 * 2
def baseEnd_3774159 : Nat := 1291971755661602879503643

theorem tailTrace_3774159 : CollatzResearch.WordTrace tailWord_3774159 prefixEnd_3774159 1291971755661602879503643 := by
  unfold tailWord_3774159
  simp only [CollatzResearch.WordTrace]
  refine ⟨137654887533873992885069531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91769925022582661923379687 137654887533873992885069531)
  ·
    refine ⟨206482331300810989327604297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137654887533873992885069531 206482331300810989327604297)
    ·
      refine ⟨154861748475608241995703223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 206482331300810989327604297 154861748475608241995703223)
      ·
        refine ⟨232292622713412362993554835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154861748475608241995703223 232292622713412362993554835)
        ·
          refine ⟨348438934070118544490332253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 232292622713412362993554835 348438934070118544490332253)
          ·
            refine ⟨130664600276294454183874595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 348438934070118544490332253 130664600276294454183874595)
            ·
              refine ⟨195996900414441681275811893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 130664600276294454183874595 195996900414441681275811893)
              ·
                refine ⟨18374709413853907619607365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 195996900414441681275811893 18374709413853907619607365)
                ·
                  refine ⟨3445258015097607678676381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18374709413853907619607365 3445258015097607678676381)
                  ·
                    refine ⟨1291971755661602879503643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3445258015097607678676381 1291971755661602879503643)
                    ·
                      rfl

theorem cell22_3774159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 5, 4, 3].length) (baseStart_3774159 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3774159 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3774159 prefixEnd_3774159 := by exact prefixLift 3774159
  have htrace : WordTrace (prefixWord ++ tailWord_3774159) baseStart_3774159 baseEnd_3774159 := by
    simpa [prefixWord, tailWord_3774159, baseEnd_3774159] using wordTrace_append hprefix tailTrace_3774159
  have hstable : (prefixWord ++ tailWord_3774159).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3774159).length < 2 ^ (prefixWord ++ tailWord_3774159).sum := by decide
  have hdescent : baseEnd_3774159 < baseStart_3774159 := by decide
  rcases family_descends (prefixWord ++ tailWord_3774159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3774161 : List Nat := [1, 2, 2, 1, 2, 5, 1, 4, 4]
def baseStart_3774161 : Nat := 118140960795 + 3774161 * 2 ^ 59
def prefixEnd_3774161 : Nat := 4983230072969 + 3 ^ 40 * 3774161 * 2
def baseEnd_3774161 : Nat := 430657480100825180317879

theorem tailTrace_3774161 : CollatzResearch.WordTrace tailWord_3774161 prefixEnd_3774161 430657480100825180317879 := by
  unfold tailWord_3774161
  simp only [CollatzResearch.WordTrace]
  refine ⟨137654960479866747226642337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91769973653244498151094891 137654960479866747226642337)
  ·
    refine ⟨103241220359900060419981753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137654960479866747226642337 103241220359900060419981753)
    ·
      refine ⟨77430915269925045314986315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103241220359900060419981753 77430915269925045314986315)
      ·
        refine ⟨116146372904887567972479473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77430915269925045314986315 116146372904887567972479473)
        ·
          refine ⟨87109779678665675979359605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116146372904887567972479473 87109779678665675979359605)
          ·
            refine ⟨8166541844874907123064963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 87109779678665675979359605 8166541844874907123064963)
            ·
              refine ⟨12249812767312360684597445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8166541844874907123064963 12249812767312360684597445)
              ·
                refine ⟨2296839893871067628362021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12249812767312360684597445 2296839893871067628362021)
                ·
                  refine ⟨430657480100825180317879, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2296839893871067628362021 430657480100825180317879)
                  ·
                    rfl

theorem cell22_3774161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 1, 4, 4].length) (baseStart_3774161 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3774161 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3774161 prefixEnd_3774161 := by exact prefixLift 3774161
  have htrace : WordTrace (prefixWord ++ tailWord_3774161) baseStart_3774161 baseEnd_3774161 := by
    simpa [prefixWord, tailWord_3774161, baseEnd_3774161] using wordTrace_append hprefix tailTrace_3774161
  have hstable : (prefixWord ++ tailWord_3774161).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3774161).length < 2 ^ (prefixWord ++ tailWord_3774161).sum := by decide
  have hdescent : baseEnd_3774161 < baseStart_3774161 := by decide
  rcases family_descends (prefixWord ++ tailWord_3774161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3774176 : List Nat := [2, 1, 1, 3, 1, 2, 4, 3, 2, 3]
def baseStart_3774176 : Nat := 118140960795 + 3774176 * 2 ^ 59
def prefixEnd_3774176 : Nat := 4983230072969 + 3 ^ 40 * 3774176 * 2
def baseEnd_3774176 : Nat := 1291977575109020501828591

theorem tailTrace_3774176 : CollatzResearch.WordTrace tailWord_3774176 prefixEnd_3774176 1291977575109020501828591 := by
  unfold tailWord_3774176
  simp only [CollatzResearch.WordTrace]
  refine ⟨68827753787406202394219191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91770338383208269858958921 68827753787406202394219191)
  ·
    refine ⟨103241630681109303591328787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68827753787406202394219191 103241630681109303591328787)
    ·
      refine ⟨154862446021663955386993181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103241630681109303591328787 154862446021663955386993181)
      ·
        refine ⟨58073417258123983270122443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 154862446021663955386993181 58073417258123983270122443)
        ·
          refine ⟨87110125887185974905183665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58073417258123983270122443 87110125887185974905183665)
          ·
            refine ⟨65332594415389481178887749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87110125887185974905183665 65332594415389481178887749)
            ·
              refine ⟨12249861452885527721041453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 65332594415389481178887749 12249861452885527721041453)
              ·
                refine ⟨4593698044832072895390545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12249861452885527721041453 4593698044832072895390545)
                ·
                  refine ⟨3445273533624054671542909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4593698044832072895390545 3445273533624054671542909)
                  ·
                    refine ⟨1291977575109020501828591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3445273533624054671542909 1291977575109020501828591)
                    ·
                      rfl

theorem cell22_3774176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 4, 3, 2, 3].length) (baseStart_3774176 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3774176 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3774176 prefixEnd_3774176 := by exact prefixLift 3774176
  have htrace : WordTrace (prefixWord ++ tailWord_3774176) baseStart_3774176 baseEnd_3774176 := by
    simpa [prefixWord, tailWord_3774176, baseEnd_3774176] using wordTrace_append hprefix tailTrace_3774176
  have hstable : (prefixWord ++ tailWord_3774176).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3774176).length < 2 ^ (prefixWord ++ tailWord_3774176).sum := by decide
  have hdescent : baseEnd_3774176 < baseStart_3774176 := by decide
  rcases family_descends (prefixWord ++ tailWord_3774176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3774206 : List Nat := [4, 2, 2, 1, 3, 1, 9]
def baseStart_3774206 : Nat := 118140960795 + 3774206 * 2 ^ 59
def prefixEnd_3774206 : Nat := 4983230072969 + 3 ^ 40 * 3774206 * 2
def baseEnd_3774206 : Nat := 47851401656374460132537

theorem tailTrace_3774206 : CollatzResearch.WordTrace tailWord_3774206 prefixEnd_3774206 47851401656374460132537 := by
  unfold tailWord_3774206
  simp only [CollatzResearch.WordTrace]
  refine ⟨17207075220587964989003809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 91771067843135813274686981 17207075220587964989003809)
  ·
    refine ⟨12905306415440973741752857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17207075220587964989003809 12905306415440973741752857)
    ·
      refine ⟨9678979811580730306314643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12905306415440973741752857 9678979811580730306314643)
      ·
        refine ⟨14518469717371095459471965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9678979811580730306314643 14518469717371095459471965)
        ·
          refine ⟨5444426144014160797301987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14518469717371095459471965 5444426144014160797301987)
          ·
            refine ⟨8166639216021241195952981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5444426144014160797301987 8166639216021241195952981)
            ·
              refine ⟨47851401656374460132537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8166639216021241195952981 47851401656374460132537)
              ·
                rfl

theorem cell22_3774206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 9].length) (baseStart_3774206 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3774206 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3774206 prefixEnd_3774206 := by exact prefixLift 3774206
  have htrace : WordTrace (prefixWord ++ tailWord_3774206) baseStart_3774206 baseEnd_3774206 := by
    simpa [prefixWord, tailWord_3774206, baseEnd_3774206] using wordTrace_append hprefix tailTrace_3774206
  have hstable : (prefixWord ++ tailWord_3774206).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3774206).length < 2 ^ (prefixWord ++ tailWord_3774206).sum := by decide
  have hdescent : baseEnd_3774206 < baseStart_3774206 := by decide
  rcases family_descends (prefixWord ++ tailWord_3774206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3774285 : List Nat := [1, 6, 1, 2, 1, 1, 4, 1, 5]
def baseStart_3774285 : Nat := 118140960795 + 3774285 * 2 ^ 59
def prefixEnd_3774285 : Nat := 4983230072969 + 3 ^ 40 * 3774285 * 2
def baseEnd_3774285 : Nat := 430671629345526850284419

theorem tailTrace_3774285 : CollatzResearch.WordTrace tailWord_3774285 prefixEnd_3774285 430671629345526850284419 := by
  unfold tailWord_3774285
  simp only [CollatzResearch.WordTrace]
  refine ⟨137659483131417516404156309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91772988754278344269437539 137659483131417516404156309)
  ·
    refine ⟨6452788271785196081444827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 137659483131417516404156309 6452788271785196081444827)
    ·
      refine ⟨9679182407677794122167241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6452788271785196081444827 9679182407677794122167241)
      ·
        refine ⟨7259386805758345591625431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9679182407677794122167241 7259386805758345591625431)
        ·
          refine ⟨10889080208637518387438147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7259386805758345591625431 10889080208637518387438147)
          ·
            refine ⟨16333620312956277581157221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10889080208637518387438147 16333620312956277581157221)
            ·
              refine ⟨3062553808679302046466979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16333620312956277581157221 3062553808679302046466979)
              ·
                refine ⟨4593830713018953069700469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3062553808679302046466979 4593830713018953069700469)
                ·
                  refine ⟨430671629345526850284419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4593830713018953069700469 430671629345526850284419)
                  ·
                    rfl

theorem cell22_3774285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 4, 1, 5].length) (baseStart_3774285 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3774285 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3774285 prefixEnd_3774285 := by exact prefixLift 3774285
  have htrace : WordTrace (prefixWord ++ tailWord_3774285) baseStart_3774285 baseEnd_3774285 := by
    simpa [prefixWord, tailWord_3774285, baseEnd_3774285] using wordTrace_append hprefix tailTrace_3774285
  have hstable : (prefixWord ++ tailWord_3774285).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3774285).length < 2 ^ (prefixWord ++ tailWord_3774285).sum := by decide
  have hdescent : baseEnd_3774285 < baseStart_3774285 := by decide
  rcases family_descends (prefixWord ++ tailWord_3774285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3774311 : List Nat := [1, 1, 5, 1, 2, 1, 3, 2, 1, 5]
def baseStart_3774311 : Nat := 118140960795 + 3774311 * 2 ^ 59
def prefixEnd_3774311 : Nat := 4983230072969 + 3 ^ 40 * 3774311 * 2
def baseEnd_3774311 : Nat := 1292023788367925149703177

theorem tailTrace_3774311 : CollatzResearch.WordTrace tailWord_3774311 prefixEnd_3774311 1292023788367925149703177 := by
  unfold tailWord_3774311
  simp only [CollatzResearch.WordTrace]
  refine ⟨137660431429323322844602787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91773620952882215229735191 137660431429323322844602787)
  ·
    refine ⟨206490647143984984266904181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137660431429323322844602787 206490647143984984266904181)
    ·
      refine ⟨19358498169748592275022267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 206490647143984984266904181 19358498169748592275022267)
      ·
        refine ⟨29037747254622888412533401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19358498169748592275022267 29037747254622888412533401)
        ·
          refine ⟨21778310440967166309400051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29037747254622888412533401 21778310440967166309400051)
          ·
            refine ⟨32667465661450749464100077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21778310440967166309400051 32667465661450749464100077)
            ·
              refine ⟨12250299623044031049037529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32667465661450749464100077 12250299623044031049037529)
              ·
                refine ⟨9187724717283023286778147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12250299623044031049037529 9187724717283023286778147)
                ·
                  refine ⟨13781587075924534930167221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9187724717283023286778147 13781587075924534930167221)
                  ·
                    refine ⟨1292023788367925149703177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13781587075924534930167221 1292023788367925149703177)
                    ·
                      rfl

theorem cell22_3774311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 3, 2, 1, 5].length) (baseStart_3774311 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3774311 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3774311 prefixEnd_3774311 := by exact prefixLift 3774311
  have htrace : WordTrace (prefixWord ++ tailWord_3774311) baseStart_3774311 baseEnd_3774311 := by
    simpa [prefixWord, tailWord_3774311, baseEnd_3774311] using wordTrace_append hprefix tailTrace_3774311
  have hstable : (prefixWord ++ tailWord_3774311).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3774311).length < 2 ^ (prefixWord ++ tailWord_3774311).sum := by decide
  have hdescent : baseEnd_3774311 < baseStart_3774311 := by decide
  rcases family_descends (prefixWord ++ tailWord_3774311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3774366 : List Nat := [4, 3, 1, 3, 2, 1, 2, 1, 1, 4]
def baseStart_3774366 : Nat := 118140960795 + 3774366 * 2 ^ 59
def prefixEnd_3774366 : Nat := 4983230072969 + 3 ^ 40 * 3774366 * 2
def baseEnd_3774366 : Nat := 1292042615991923339578009

theorem tailTrace_3774366 : CollatzResearch.WordTrace tailWord_3774366 prefixEnd_3774366 1292042615991923339578009 := by
  unfold tailWord_3774366
  simp only [CollatzResearch.WordTrace]
  refine ⟨17207804680515508404731869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 91774958296082711491903301 17207804680515508404731869)
  ·
    refine ⟨6452926755193315651774451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17207804680515508404731869 6452926755193315651774451)
    ·
      refine ⟨9679390132789973477661677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6452926755193315651774451 9679390132789973477661677)
      ·
        refine ⟨3629771299796240054123129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9679390132789973477661677 3629771299796240054123129)
        ·
          refine ⟨2722328474847180040592347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3629771299796240054123129 2722328474847180040592347)
          ·
            refine ⟨4083492712270770060888521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2722328474847180040592347 4083492712270770060888521)
            ·
              refine ⟨3062619534203077545666391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4083492712270770060888521 3062619534203077545666391)
              ·
                refine ⟨4593929301304616318499587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3062619534203077545666391 4593929301304616318499587)
                ·
                  refine ⟨6890893951956924477749381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4593929301304616318499587 6890893951956924477749381)
                  ·
                    refine ⟨1292042615991923339578009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6890893951956924477749381 1292042615991923339578009)
                    ·
                      rfl

theorem cell22_3774366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 2, 1, 2, 1, 1, 4].length) (baseStart_3774366 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3774366 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3774366 prefixEnd_3774366 := by exact prefixLift 3774366
  have htrace : WordTrace (prefixWord ++ tailWord_3774366) baseStart_3774366 baseEnd_3774366 := by
    simpa [prefixWord, tailWord_3774366, baseEnd_3774366] using wordTrace_append hprefix tailTrace_3774366
  have hstable : (prefixWord ++ tailWord_3774366).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3774366).length < 2 ^ (prefixWord ++ tailWord_3774366).sum := by decide
  have hdescent : baseEnd_3774366 < baseStart_3774366 := by decide
  rcases family_descends (prefixWord ++ tailWord_3774366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3774416 : List Nat := [2, 1, 1, 1, 1, 2, 4, 3, 3, 4]
def baseStart_3774416 : Nat := 118140960795 + 3774416 * 2 ^ 59
def prefixEnd_3774416 : Nat := 4983230072969 + 3 ^ 40 * 3774416 * 2
def baseEnd_3774416 : Nat := 1292059732013739875827855

theorem tailTrace_3774416 : CollatzResearch.WordTrace tailWord_3774416 prefixEnd_3774416 1292059732013739875827855 := by
  unfold tailWord_3774416
  simp only [CollatzResearch.WordTrace]
  refine ⟨68832130546971462888587551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91776174062628617184783401 68832130546971462888587551)
  ·
    refine ⟨103248195820457194332881327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68832130546971462888587551 103248195820457194332881327)
    ·
      refine ⟨154872293730685791499321991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103248195820457194332881327 154872293730685791499321991)
      ·
        refine ⟨232308440596028687248982987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154872293730685791499321991 232308440596028687248982987)
        ·
          refine ⟨348462660894043030873474481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 232308440596028687248982987 348462660894043030873474481)
          ·
            refine ⟨261346995670532273155105861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 348462660894043030873474481 261346995670532273155105861)
            ·
              refine ⟨49002561688224801216582349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 261346995670532273155105861 49002561688224801216582349)
              ·
                refine ⟨18375960633084300456218381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49002561688224801216582349 18375960633084300456218381)
                ·
                  refine ⟨6890985237406612671081893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18375960633084300456218381 6890985237406612671081893)
                  ·
                    refine ⟨1292059732013739875827855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6890985237406612671081893 1292059732013739875827855)
                    ·
                      rfl

theorem cell22_3774416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 3, 3, 4].length) (baseStart_3774416 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3774416 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3774416 prefixEnd_3774416 := by exact prefixLift 3774416
  have htrace : WordTrace (prefixWord ++ tailWord_3774416) baseStart_3774416 baseEnd_3774416 := by
    simpa [prefixWord, tailWord_3774416, baseEnd_3774416] using wordTrace_append hprefix tailTrace_3774416
  have hstable : (prefixWord ++ tailWord_3774416).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3774416).length < 2 ^ (prefixWord ++ tailWord_3774416).sum := by decide
  have hdescent : baseEnd_3774416 < baseStart_3774416 := by decide
  rcases family_descends (prefixWord ++ tailWord_3774416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3774433 : List Nat := [1, 2, 3, 1, 2, 1, 4, 3, 1, 4]
def baseStart_3774433 : Nat := 118140960795 + 3774433 * 2 ^ 59
def prefixEnd_3774433 : Nat := 4983230072969 + 3 ^ 40 * 3774433 * 2
def baseEnd_3774433 : Nat := 1292065551461157498152803

theorem tailTrace_3774433 : CollatzResearch.WordTrace tailWord_3774433 prefixEnd_3774433 1292065551461157498152803 := by
  unfold tailWord_3774433
  simp only [CollatzResearch.WordTrace]
  refine ⟨137664881134881337680543953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91776587423254225120362635 137664881134881337680543953)
  ·
    refine ⟨103248660851161003260407965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137664881134881337680543953 103248660851161003260407965)
    ·
      refine ⟨38718247819185376222652987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103248660851161003260407965 38718247819185376222652987)
      ·
        refine ⟨58077371728778064333979481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38718247819185376222652987 58077371728778064333979481)
        ·
          refine ⟨43558028796583548250484611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58077371728778064333979481 43558028796583548250484611)
          ·
            refine ⟨65337043194875322375726917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43558028796583548250484611 65337043194875322375726917)
            ·
              refine ⟨12250695599039122945448797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 65337043194875322375726917 12250695599039122945448797)
              ·
                refine ⟨4594010849639671104543299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12250695599039122945448797 4594010849639671104543299)
                ·
                  refine ⟨6891016274459506656814949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4594010849639671104543299 6891016274459506656814949)
                  ·
                    refine ⟨1292065551461157498152803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6891016274459506656814949 1292065551461157498152803)
                    ·
                      rfl

theorem cell22_3774433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 4, 3, 1, 4].length) (baseStart_3774433 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3774433 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3774433 prefixEnd_3774433 := by exact prefixLift 3774433
  have htrace : WordTrace (prefixWord ++ tailWord_3774433) baseStart_3774433 baseEnd_3774433 := by
    simpa [prefixWord, tailWord_3774433, baseEnd_3774433] using wordTrace_append hprefix tailTrace_3774433
  have hstable : (prefixWord ++ tailWord_3774433).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3774433).length < 2 ^ (prefixWord ++ tailWord_3774433).sum := by decide
  have hdescent : baseEnd_3774433 < baseStart_3774433 := by decide
  rcases family_descends (prefixWord ++ tailWord_3774433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3774448 : List Nat := [2, 1, 1, 1, 3, 2, 2, 6, 4]
def baseStart_3774448 : Nat := 118140960795 + 3774448 * 2 ^ 59
def prefixEnd_3774448 : Nat := 4983230072969 + 3 ^ 40 * 3774448 * 2
def baseEnd_3774448 : Nat := 430690228755900819675919

theorem tailTrace_3774448 : CollatzResearch.WordTrace tailWord_3774448 prefixEnd_3774448 430690228755900819675919 := by
  unfold tailWord_3774448
  simp only [CollatzResearch.WordTrace]
  refine ⟨68832714114913497621169999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91776952153217996828226665 68832714114913497621169999)
  ·
    refine ⟨103249071172370246431754999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68832714114913497621169999 103249071172370246431754999)
    ·
      refine ⟨154873606758555369647632499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103249071172370246431754999 154873606758555369647632499)
      ·
        refine ⟨232310410137833054471448749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154873606758555369647632499 232310410137833054471448749)
        ·
          refine ⟨87116403801687395426793281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 232310410137833054471448749 87116403801687395426793281)
          ·
            refine ⟨65337302851265546570094961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87116403801687395426793281 65337302851265546570094961)
            ·
              refine ⟨49002977138449159927571221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65337302851265546570094961 49002977138449159927571221)
              ·
                refine ⟨2297014553364804371604901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 49002977138449159927571221 2297014553364804371604901)
                ·
                  refine ⟨430690228755900819675919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2297014553364804371604901 430690228755900819675919)
                  ·
                    rfl

theorem cell22_3774448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 6, 4].length) (baseStart_3774448 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3774448 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3774448 prefixEnd_3774448 := by exact prefixLift 3774448
  have htrace : WordTrace (prefixWord ++ tailWord_3774448) baseStart_3774448 baseEnd_3774448 := by
    simpa [prefixWord, tailWord_3774448, baseEnd_3774448] using wordTrace_append hprefix tailTrace_3774448
  have hstable : (prefixWord ++ tailWord_3774448).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3774448).length < 2 ^ (prefixWord ++ tailWord_3774448).sum := by decide
  have hdescent : baseEnd_3774448 < baseStart_3774448 := by decide
  rcases family_descends (prefixWord ++ tailWord_3774448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3774454 : List Nat := [5, 1, 1, 1, 5, 1, 2, 1, 5]
def baseStart_3774454 : Nat := 118140960795 + 3774454 * 2 ^ 59
def prefixEnd_3774454 : Nat := 4983230072969 + 3 ^ 40 * 3774454 * 2
def baseEnd_3774454 : Nat := 430690913396773481125913

theorem tailTrace_3774454 : CollatzResearch.WordTrace tailWord_3774454 prefixEnd_3774454 430690913396773481125913 := by
  unfold tailWord_3774454
  simp only [CollatzResearch.WordTrace]
  refine ⟨8604102941737828641691151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 91777098045203505511372277 8604102941737828641691151)
  ·
    refine ⟨12906154412606742962536727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8604102941737828641691151 12906154412606742962536727)
    ·
      refine ⟨19359231618910114443805091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12906154412606742962536727 19359231618910114443805091)
      ·
        refine ⟨29038847428365171665707637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19359231618910114443805091 29038847428365171665707637)
        ·
          refine ⟨2722391946409234843660091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 29038847428365171665707637 2722391946409234843660091)
          ·
            refine ⟨4083587919613852265490137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2722391946409234843660091 4083587919613852265490137)
            ·
              refine ⟨3062690939710389199117603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4083587919613852265490137 3062690939710389199117603)
              ·
                refine ⟨4594036409565583798676405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3062690939710389199117603 4594036409565583798676405)
                ·
                  refine ⟨430690913396773481125913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4594036409565583798676405 430690913396773481125913)
                  ·
                    rfl

theorem cell22_3774454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 5, 1, 2, 1, 5].length) (baseStart_3774454 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3774454 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3774454 prefixEnd_3774454 := by exact prefixLift 3774454
  have htrace : WordTrace (prefixWord ++ tailWord_3774454) baseStart_3774454 baseEnd_3774454 := by
    simpa [prefixWord, tailWord_3774454, baseEnd_3774454] using wordTrace_append hprefix tailTrace_3774454
  have hstable : (prefixWord ++ tailWord_3774454).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3774454).length < 2 ^ (prefixWord ++ tailWord_3774454).sum := by decide
  have hdescent : baseEnd_3774454 < baseStart_3774454 := by decide
  rcases family_descends (prefixWord ++ tailWord_3774454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3774461 : List Nat := [1, 4, 1, 1, 1, 2, 2, 1, 3, 6]
def baseStart_3774461 : Nat := 118140960795 + 3774461 * 2 ^ 59
def prefixEnd_3774461 : Nat := 4983230072969 + 3 ^ 40 * 3774461 * 2
def baseEnd_3774461 : Nat := 1292075136433374758452717

theorem tailTrace_3774461 : CollatzResearch.WordTrace tailWord_3774461 prefixEnd_3774461 1292075136433374758452717 := by
  unfold tailWord_3774461
  simp only [CollatzResearch.WordTrace]
  refine ⟨137665902378779898462563237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91777268252519932308375491 137665902378779898462563237)
  ·
    refine ⟨25812356696021230961730607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 137665902378779898462563237 25812356696021230961730607)
    ·
      refine ⟨38718535044031846442595911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25812356696021230961730607 38718535044031846442595911)
      ·
        refine ⟨58077802566047769663893867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38718535044031846442595911 58077802566047769663893867)
        ·
          refine ⟨87116703849071654495840801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58077802566047769663893867 87116703849071654495840801)
          ·
            refine ⟨65337527886803740871880601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87116703849071654495840801 65337527886803740871880601)
            ·
              refine ⟨49003145915102805653910451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65337527886803740871880601 49003145915102805653910451)
              ·
                refine ⟨73504718872654208480865677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49003145915102805653910451 73504718872654208480865677)
                ·
                  refine ⟨27564269577245328180324629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 73504718872654208480865677 27564269577245328180324629)
                  ·
                    refine ⟨1292075136433374758452717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27564269577245328180324629 1292075136433374758452717)
                    ·
                      rfl

theorem cell22_3774461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 1, 3, 6].length) (baseStart_3774461 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3774461 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3774461 prefixEnd_3774461 := by exact prefixLift 3774461
  have htrace : WordTrace (prefixWord ++ tailWord_3774461) baseStart_3774461 baseEnd_3774461 := by
    simpa [prefixWord, tailWord_3774461, baseEnd_3774461] using wordTrace_append hprefix tailTrace_3774461
  have hstable : (prefixWord ++ tailWord_3774461).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3774461).length < 2 ^ (prefixWord ++ tailWord_3774461).sum := by decide
  have hdescent : baseEnd_3774461 < baseStart_3774461 := by decide
  rcases family_descends (prefixWord ++ tailWord_3774461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3774476 : List Nat := [2, 2, 1, 2, 3, 1, 1, 10]
def baseStart_3774476 : Nat := 118140960795 + 3774476 * 2 ^ 59
def prefixEnd_3774476 : Nat := 4983230072969 + 3 ^ 40 * 3774476 * 2
def baseEnd_3774476 : Nat := 143564474582213302147519

theorem tailTrace_3774476 : CollatzResearch.WordTrace tailWord_3774476 prefixEnd_3774476 143564474582213302147519 := by
  unfold tailWord_3774476
  simp only [CollatzResearch.WordTrace]
  refine ⟨68833224736862778012179641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91777632982483704016239521 68833224736862778012179641)
  ·
    refine ⟨51624918552647083509134731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68833224736862778012179641 51624918552647083509134731)
    ·
      refine ⟨77437377828970625263702097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51624918552647083509134731 77437377828970625263702097)
      ·
        refine ⟨58078033371727968947776573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77437377828970625263702097 58078033371727968947776573)
        ·
          refine ⟨21779262514397988355416215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58078033371727968947776573 21779262514397988355416215)
          ·
            refine ⟨32668893771596982533124323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21779262514397988355416215 32668893771596982533124323)
            ·
              refine ⟨49003340657395473799686485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32668893771596982533124323 49003340657395473799686485)
              ·
                refine ⟨143564474582213302147519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 49003340657395473799686485 143564474582213302147519)
                ·
                  rfl

theorem cell22_3774476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 10].length) (baseStart_3774476 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3774476 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3774476 prefixEnd_3774476 := by exact prefixLift 3774476
  have htrace : WordTrace (prefixWord ++ tailWord_3774476) baseStart_3774476 baseEnd_3774476 := by
    simpa [prefixWord, tailWord_3774476, baseEnd_3774476] using wordTrace_append hprefix tailTrace_3774476
  have hstable : (prefixWord ++ tailWord_3774476).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3774476).length < 2 ^ (prefixWord ++ tailWord_3774476).sum := by decide
  have hdescent : baseEnd_3774476 < baseStart_3774476 := by decide
  rcases family_descends (prefixWord ++ tailWord_3774476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3774497 : List Nat := [1, 2, 3, 2, 4, 1, 2, 2, 2, 3]
def baseStart_3774497 : Nat := 118140960795 + 3774497 * 2 ^ 59
def prefixEnd_3774497 : Nat := 4983230072969 + 3 ^ 40 * 3774497 * 2
def baseEnd_3774497 : Nat := 1292087459969082664552607

theorem tailTrace_3774497 : CollatzResearch.WordTrace tailWord_3774497 prefixEnd_3774497 1292087459969082664552607 := by
  unfold tailWord_3774497
  simp only [CollatzResearch.WordTrace]
  refine ⟨137667215406649476610873745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91778143604432984407249163 137667215406649476610873745)
  ·
    refine ⟨103250411554987107458155309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137667215406649476610873745 103250411554987107458155309)
    ·
      refine ⟨38718904333120165296808241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103250411554987107458155309 38718904333120165296808241)
      ·
        refine ⟨29039178249840123972606181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38718904333120165296808241 29039178249840123972606181)
        ·
          refine ⟨5444845921845023244863659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29039178249840123972606181 5444845921845023244863659)
          ·
            refine ⟨8167268882767534867295489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5444845921845023244863659 8167268882767534867295489)
            ·
              refine ⟨6125451662075651150471617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8167268882767534867295489 6125451662075651150471617)
              ·
                refine ⟨4594088746556738362853713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6125451662075651150471617 4594088746556738362853713)
                ·
                  refine ⟨3445566559917553772140285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4594088746556738362853713 3445566559917553772140285)
                  ·
                    refine ⟨1292087459969082664552607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3445566559917553772140285 1292087459969082664552607)
                    ·
                      rfl

theorem cell22_3774497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 2, 2, 2, 3].length) (baseStart_3774497 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3774497 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3774497 prefixEnd_3774497 := by exact prefixLift 3774497
  have htrace : WordTrace (prefixWord ++ tailWord_3774497) baseStart_3774497 baseEnd_3774497 := by
    simpa [prefixWord, tailWord_3774497, baseEnd_3774497] using wordTrace_append hprefix tailTrace_3774497
  have hstable : (prefixWord ++ tailWord_3774497).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3774497).length < 2 ^ (prefixWord ++ tailWord_3774497).sum := by decide
  have hdescent : baseEnd_3774497 < baseStart_3774497 := by decide
  rcases family_descends (prefixWord ++ tailWord_3774497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3774510 : List Nat := [4, 1, 3, 1, 1, 4, 1, 7]
def baseStart_3774510 : Nat := 118140960795 + 3774510 * 2 ^ 59
def prefixEnd_3774510 : Nat := 4983230072969 + 3 ^ 40 * 3774510 * 2
def baseEnd_3774510 : Nat := 143565767792750551553063

theorem tailTrace_3774510 : CollatzResearch.WordTrace tailWord_3774510 prefixEnd_3774510 143565767792750551553063 := by
  unfold tailWord_3774510
  simp only [CollatzResearch.WordTrace]
  refine ⟨17208461194450297478887123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 91778459703734919887397989 17208461194450297478887123)
  ·
    refine ⟨25812691791675446218330685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17208461194450297478887123 25812691791675446218330685)
    ·
      refine ⟨9679759421878292331874007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25812691791675446218330685 9679759421878292331874007)
      ·
        refine ⟨14519639132817438497811011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9679759421878292331874007 14519639132817438497811011)
        ·
          refine ⟨21779458699226157746716517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14519639132817438497811011 21779458699226157746716517)
          ·
            refine ⟨4083648506104904577509347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21779458699226157746716517 4083648506104904577509347)
            ·
              refine ⟨6125472759157356866264021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4083648506104904577509347 6125472759157356866264021)
              ·
                refine ⟨143565767792750551553063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6125472759157356866264021 143565767792750551553063)
                ·
                  rfl

theorem cell22_3774510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 4, 1, 7].length) (baseStart_3774510 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3774510 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3774510 prefixEnd_3774510 := by exact prefixLift 3774510
  have htrace : WordTrace (prefixWord ++ tailWord_3774510) baseStart_3774510 baseEnd_3774510 := by
    simpa [prefixWord, tailWord_3774510, baseEnd_3774510] using wordTrace_append hprefix tailTrace_3774510
  have hstable : (prefixWord ++ tailWord_3774510).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3774510).length < 2 ^ (prefixWord ++ tailWord_3774510).sum := by decide
  have hdescent : baseEnd_3774510 < baseStart_3774510 := by decide
  rcases family_descends (prefixWord ++ tailWord_3774510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3774525 : List Nat := [1, 4, 1, 3, 1, 1, 3, 2, 3, 3]
def baseStart_3774525 : Nat := 118140960795 + 3774525 * 2 ^ 59
def prefixEnd_3774525 : Nat := 4983230072969 + 3 ^ 40 * 3774525 * 2
def baseEnd_3774525 : Nat := 1292097044941299924852521

theorem tailTrace_3774525 : CollatzResearch.WordTrace tailWord_3774525 prefixEnd_3774525 1292097044941299924852521 := by
  unfold tailWord_3774525
  simp only [CollatzResearch.WordTrace]
  refine ⟨137668236650548037392893029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91778824433698691595262019 137668236650548037392893029)
  ·
    refine ⟨25812794371977757011167443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 137668236650548037392893029 25812794371977757011167443)
    ·
      refine ⟨38719191557966635516751165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25812794371977757011167443 38719191557966635516751165)
      ·
        refine ⟨14519696834237488318781687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38719191557966635516751165 14519696834237488318781687)
        ·
          refine ⟨21779545251356232478172531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14519696834237488318781687 21779545251356232478172531)
          ·
            refine ⟨32669317877034348717258797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21779545251356232478172531 32669317877034348717258797)
            ·
              refine ⟨12250994203887880768972049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32669317877034348717258797 12250994203887880768972049)
              ·
                refine ⟨9188245652915910576729037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12250994203887880768972049 9188245652915910576729037)
                ·
                  refine ⟨3445592119843466466273389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9188245652915910576729037 3445592119843466466273389)
                  ·
                    refine ⟨1292097044941299924852521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3445592119843466466273389 1292097044941299924852521)
                    ·
                      rfl

theorem cell22_3774525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 3, 2, 3, 3].length) (baseStart_3774525 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3774525 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3774525 prefixEnd_3774525 := by exact prefixLift 3774525
  have htrace : WordTrace (prefixWord ++ tailWord_3774525) baseStart_3774525 baseEnd_3774525 := by
    simpa [prefixWord, tailWord_3774525, baseEnd_3774525] using wordTrace_append hprefix tailTrace_3774525
  have hstable : (prefixWord ++ tailWord_3774525).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3774525).length < 2 ^ (prefixWord ++ tailWord_3774525).sum := by decide
  have hdescent : baseEnd_3774525 < baseStart_3774525 := by decide
  rcases family_descends (prefixWord ++ tailWord_3774525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3774542 : List Nat := [4, 1, 1, 1, 1, 4, 1, 5, 1, 3]
def baseStart_3774542 : Nat := 118140960795 + 3774542 * 2 ^ 59
def prefixEnd_3774542 : Nat := 4983230072969 + 3 ^ 40 * 3774542 * 2
def baseEnd_3774542 : Nat := 1292102864388717547177469

theorem tailTrace_3774542 : CollatzResearch.WordTrace tailWord_3774542 prefixEnd_3774542 1292102864388717547177469 := by
  unfold tailWord_3774542
  simp only [CollatzResearch.WordTrace]
  refine ⟨17208607086435806162032735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 91779237794324299530841253 17208607086435806162032735)
  ·
    refine ⟨25812910629653709243049103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17208607086435806162032735 25812910629653709243049103)
    ·
      refine ⟨38719365944480563864573655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25812910629653709243049103 38719365944480563864573655)
      ·
        refine ⟨58079048916720845796860483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38719365944480563864573655 58079048916720845796860483)
        ·
          refine ⟨87118573375081268695290725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58079048916720845796860483 87118573375081268695290725)
          ·
            refine ⟨16334732507827737880367011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 87118573375081268695290725 16334732507827737880367011)
            ·
              refine ⟨24502098761741606820550517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16334732507827737880367011 24502098761741606820550517)
              ·
                refine ⟨2297071758913275639426611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24502098761741606820550517 2297071758913275639426611)
                ·
                  refine ⟨3445607638369913459139917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2297071758913275639426611 3445607638369913459139917)
                  ·
                    refine ⟨1292102864388717547177469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3445607638369913459139917 1292102864388717547177469)
                    ·
                      rfl

theorem cell22_3774542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 1, 5, 1, 3].length) (baseStart_3774542 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3774542 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3774542 prefixEnd_3774542 := by exact prefixLift 3774542
  have htrace : WordTrace (prefixWord ++ tailWord_3774542) baseStart_3774542 baseEnd_3774542 := by
    simpa [prefixWord, tailWord_3774542, baseEnd_3774542] using wordTrace_append hprefix tailTrace_3774542
  have hstable : (prefixWord ++ tailWord_3774542).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3774542).length < 2 ^ (prefixWord ++ tailWord_3774542).sum := by decide
  have hdescent : baseEnd_3774542 < baseStart_3774542 := by decide
  rcases family_descends (prefixWord ++ tailWord_3774542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3774583 : List Nat := [1, 1, 3, 1, 1, 5, 2, 2, 6]
def baseStart_3774583 : Nat := 118140960795 + 3774583 * 2 ^ 59
def prefixEnd_3774583 : Nat := 4983230072969 + 3 ^ 40 * 3774583 * 2
def baseEnd_3774583 : Nat := 430705633175535702300781

theorem tailTrace_3774583 : CollatzResearch.WordTrace tailWord_3774583 prefixEnd_3774583 430705633175535702300781 := by
  unfold tailWord_3774583
  simp only [CollatzResearch.WordTrace]
  refine ⟨137670352084337913298504403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91780234722891942199002935 137670352084337913298504403)
  ·
    refine ⟨206505528126506869947756605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137670352084337913298504403 206505528126506869947756605)
    ·
      refine ⟨77439573047440076230408727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 206505528126506869947756605 77439573047440076230408727)
      ·
        refine ⟨116159359571160114345613091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77439573047440076230408727 116159359571160114345613091)
        ·
          refine ⟨174239039356740171518419637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116159359571160114345613091 174239039356740171518419637)
          ·
            refine ⟨16334909939694391079851841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 174239039356740171518419637 16334909939694391079851841)
            ·
              refine ⟨12251182454770793309888881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16334909939694391079851841 12251182454770793309888881)
              ·
                refine ⟨9188386841078094982416661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12251182454770793309888881 9188386841078094982416661)
                ·
                  refine ⟨430705633175535702300781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9188386841078094982416661 430705633175535702300781)
                  ·
                    rfl

theorem cell22_3774583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 2, 2, 6].length) (baseStart_3774583 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3774583 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3774583 prefixEnd_3774583 := by exact prefixLift 3774583
  have htrace : WordTrace (prefixWord ++ tailWord_3774583) baseStart_3774583 baseEnd_3774583 := by
    simpa [prefixWord, tailWord_3774583, baseEnd_3774583] using wordTrace_append hprefix tailTrace_3774583
  have hstable : (prefixWord ++ tailWord_3774583).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3774583).length < 2 ^ (prefixWord ++ tailWord_3774583).sum := by decide
  have hdescent : baseEnd_3774583 < baseStart_3774583 := by decide
  rcases family_descends (prefixWord ++ tailWord_3774583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3774585 : List Nat := [1, 2, 1, 3, 4, 1, 1, 4, 1, 4]
def baseStart_3774585 : Nat := 118140960795 + 3774585 * 2 ^ 59
def prefixEnd_3774585 : Nat := 4983230072969 + 3 ^ 40 * 3774585 * 2
def baseEnd_3774585 : Nat := 1292117584167479768352337

theorem tailTrace_3774585 : CollatzResearch.WordTrace tailWord_3774585 prefixEnd_3774585 1292117584167479768352337 := by
  unfold tailWord_3774585
  simp only [CollatzResearch.WordTrace]
  refine ⟨137670425030330667640077209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91780283353553778426718139 137670425030330667640077209)
  ·
    refine ⟨103252818772748000730057907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137670425030330667640077209 103252818772748000730057907)
    ·
      refine ⟨154879228159122001095086861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103252818772748000730057907 154879228159122001095086861)
      ·
        refine ⟨58079710559670750410657573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 154879228159122001095086861 58079710559670750410657573)
        ·
          refine ⟨10889945729938265701998295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 58079710559670750410657573 10889945729938265701998295)
          ·
            refine ⟨16334918594907398552997443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10889945729938265701998295 16334918594907398552997443)
            ·
              refine ⟨24502377892361097829496165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16334918594907398552997443 24502377892361097829496165)
              ·
                refine ⟨4594195854817705843030531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24502377892361097829496165 4594195854817705843030531)
                ·
                  refine ⟨6891293782226558764545797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4594195854817705843030531 6891293782226558764545797)
                  ·
                    refine ⟨1292117584167479768352337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6891293782226558764545797 1292117584167479768352337)
                    ·
                      rfl

theorem cell22_3774585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 1, 4, 1, 4].length) (baseStart_3774585 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3774585 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3774585 prefixEnd_3774585 := by exact prefixLift 3774585
  have htrace : WordTrace (prefixWord ++ tailWord_3774585) baseStart_3774585 baseEnd_3774585 := by
    simpa [prefixWord, tailWord_3774585, baseEnd_3774585] using wordTrace_append hprefix tailTrace_3774585
  have hstable : (prefixWord ++ tailWord_3774585).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3774585).length < 2 ^ (prefixWord ++ tailWord_3774585).sum := by decide
  have hdescent : baseEnd_3774585 < baseStart_3774585 := by decide
  rcases family_descends (prefixWord ++ tailWord_3774585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3774668 : List Nat := [2, 2, 1, 6, 2, 1, 2, 2, 4]
def baseStart_3774668 : Nat := 118140960795 + 3774668 * 2 ^ 59
def prefixEnd_3774668 : Nat := 4983230072969 + 3 ^ 40 * 3774668 * 2
def baseEnd_3774668 : Nat := 430715332254565072842361

theorem tailTrace_3774668 : CollatzResearch.WordTrace tailWord_3774668 prefixEnd_3774668 430715332254565072842361 := by
  unfold tailWord_3774668
  simp only [CollatzResearch.WordTrace]
  refine ⟨68836726144514986407674329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91782301526019981876899105 68836726144514986407674329)
  ·
    refine ⟨51627544608386239805755747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68836726144514986407674329 51627544608386239805755747)
    ·
      refine ⟨77441316912579359708633621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51627544608386239805755747 77441316912579359708633621)
      ·
        refine ⟨3630061730277157486342201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 77441316912579359708633621 3630061730277157486342201)
        ·
          refine ⟨2722546297707868114756651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3630061730277157486342201 2722546297707868114756651)
          ·
            refine ⟨4083819446561802172134977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2722546297707868114756651 4083819446561802172134977)
            ·
              refine ⟨3062864584921351629101233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4083819446561802172134977 3062864584921351629101233)
              ·
                refine ⟨2297148438691013721825925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3062864584921351629101233 2297148438691013721825925)
                ·
                  refine ⟨430715332254565072842361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2297148438691013721825925 430715332254565072842361)
                  ·
                    rfl

theorem cell22_3774668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 2, 1, 2, 2, 4].length) (baseStart_3774668 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3774668 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3774668 prefixEnd_3774668 := by exact prefixLift 3774668
  have htrace : WordTrace (prefixWord ++ tailWord_3774668) baseStart_3774668 baseEnd_3774668 := by
    simpa [prefixWord, tailWord_3774668, baseEnd_3774668] using wordTrace_append hprefix tailTrace_3774668
  have hstable : (prefixWord ++ tailWord_3774668).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3774668).length < 2 ^ (prefixWord ++ tailWord_3774668).sum := by decide
  have hdescent : baseEnd_3774668 < baseStart_3774668 := by decide
  rcases family_descends (prefixWord ++ tailWord_3774668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3774673 : List Nat := [1, 2, 2, 1, 2, 2, 2, 3, 7]
def baseStart_3774673 : Nat := 118140960795 + 3774673 * 2 ^ 59
def prefixEnd_3774673 : Nat := 4983230072969 + 3 ^ 40 * 3774673 * 2
def baseEnd_3774673 : Nat := 430715902788625624050689

theorem tailTrace_3774673 : CollatzResearch.WordTrace tailWord_3774673 prefixEnd_3774673 430715902788625624050689 := by
  unfold tailWord_3774673
  simp only [CollatzResearch.WordTrace]
  refine ⟨137673634654011858669280673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91782423102674572446187115 137673634654011858669280673)
  ·
    refine ⟨103255225990508894001960505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137673634654011858669280673 103255225990508894001960505)
    ·
      refine ⟨77441419492881670501470379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103255225990508894001960505 77441419492881670501470379)
      ·
        refine ⟨116162129239322505752205569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77441419492881670501470379 116162129239322505752205569)
        ·
          refine ⟨87121596929491879314154177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116162129239322505752205569 87121596929491879314154177)
          ·
            refine ⟨65341197697118909485615633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87121596929491879314154177 65341197697118909485615633)
            ·
              refine ⟨49005898272839182114211725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65341197697118909485615633 49005898272839182114211725)
              ·
                refine ⟨18377211852314693292829397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49005898272839182114211725 18377211852314693292829397)
                ·
                  refine ⟨430715902788625624050689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18377211852314693292829397 430715902788625624050689)
                  ·
                    rfl

theorem cell22_3774673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 3, 7].length) (baseStart_3774673 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3774673 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3774673 prefixEnd_3774673 := by exact prefixLift 3774673
  have htrace : WordTrace (prefixWord ++ tailWord_3774673) baseStart_3774673 baseEnd_3774673 := by
    simpa [prefixWord, tailWord_3774673, baseEnd_3774673] using wordTrace_append hprefix tailTrace_3774673
  have hstable : (prefixWord ++ tailWord_3774673).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3774673).length < 2 ^ (prefixWord ++ tailWord_3774673).sum := by decide
  have hdescent : baseEnd_3774673 < baseStart_3774673 := by decide
  rcases family_descends (prefixWord ++ tailWord_3774673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3774722 : List Nat := [3, 4, 1, 1, 2, 1, 1, 2, 2, 5]
def baseStart_3774722 : Nat := 118140960795 + 3774722 * 2 ^ 59
def prefixEnd_3774722 : Nat := 4983230072969 + 3 ^ 40 * 3774722 * 2
def baseEnd_3774722 : Nat := 1292164482067257077676917

theorem tailTrace_3774722 : CollatzResearch.WordTrace tailWord_3774722 prefixEnd_3774722 1292164482067257077676917 := by
  unfold tailWord_3774722
  simp only [CollatzResearch.WordTrace]
  refine ⟨34418855457708585009453605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91783614553889560025209613 34418855457708585009453605)
  ·
    refine ⟨6453535398320359689272551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34418855457708585009453605 6453535398320359689272551)
    ·
      refine ⟨9680303097480539533908827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6453535398320359689272551 9680303097480539533908827)
      ·
        refine ⟨14520454646220809300863241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9680303097480539533908827 14520454646220809300863241)
        ·
          refine ⟨10890340984665606975647431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14520454646220809300863241 10890340984665606975647431)
          ·
            refine ⟨16335511476998410463471147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10890340984665606975647431 16335511476998410463471147)
            ·
              refine ⟨24503267215497615695206721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16335511476998410463471147 24503267215497615695206721)
              ·
                refine ⟨18377450411623211771405041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24503267215497615695206721 18377450411623211771405041)
                ·
                  refine ⟨13783087808717408828553781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18377450411623211771405041 13783087808717408828553781)
                  ·
                    refine ⟨1292164482067257077676917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13783087808717408828553781 1292164482067257077676917)
                    ·
                      rfl

theorem cell22_3774722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 1, 2, 2, 5].length) (baseStart_3774722 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3774722 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3774722 prefixEnd_3774722 := by exact prefixLift 3774722
  have htrace : WordTrace (prefixWord ++ tailWord_3774722) baseStart_3774722 baseEnd_3774722 := by
    simpa [prefixWord, tailWord_3774722, baseEnd_3774722] using wordTrace_append hprefix tailTrace_3774722
  have hstable : (prefixWord ++ tailWord_3774722).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3774722).length < 2 ^ (prefixWord ++ tailWord_3774722).sum := by decide
  have hdescent : baseEnd_3774722 < baseStart_3774722 := by decide
  rcases family_descends (prefixWord ++ tailWord_3774722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3774724 : List Nat := [2, 3, 2, 2, 3, 2, 1, 2, 5]
def baseStart_3774724 : Nat := 118140960795 + 3774724 * 2 ^ 59
def prefixEnd_3774724 : Nat := 4983230072969 + 3 ^ 40 * 3774724 * 2
def baseEnd_3774724 : Nat := 430721722236043246375637

theorem tailTrace_3774724 : CollatzResearch.WordTrace tailWord_3774724 prefixEnd_3774724 430721722236043246375637 := by
  unfold tailWord_3774724
  simp only [CollatzResearch.WordTrace]
  refine ⟨68837747388413547189693613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91783663184551396252924817 68837747388413547189693613)
  ·
    refine ⟨25814155270655080196135105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68837747388413547189693613 25814155270655080196135105)
    ·
      refine ⟨19360616452991310147101329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25814155270655080196135105 19360616452991310147101329)
      ·
        refine ⟨14520462339743482610325997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19360616452991310147101329 14520462339743482610325997)
        ·
          refine ⟨5445173377403805978872249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14520462339743482610325997 5445173377403805978872249)
          ·
            refine ⟨4083880033052854484154187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5445173377403805978872249 4083880033052854484154187)
            ·
              refine ⟨6125820049579281726231281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4083880033052854484154187 6125820049579281726231281)
              ·
                refine ⟨4594365037184461294673461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6125820049579281726231281 4594365037184461294673461)
                ·
                  refine ⟨430721722236043246375637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4594365037184461294673461 430721722236043246375637)
                  ·
                    rfl

theorem cell22_3774724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 2, 1, 2, 5].length) (baseStart_3774724 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3774724 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3774724 prefixEnd_3774724 := by exact prefixLift 3774724
  have htrace : WordTrace (prefixWord ++ tailWord_3774724) baseStart_3774724 baseEnd_3774724 := by
    simpa [prefixWord, tailWord_3774724, baseEnd_3774724] using wordTrace_append hprefix tailTrace_3774724
  have hstable : (prefixWord ++ tailWord_3774724).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3774724).length < 2 ^ (prefixWord ++ tailWord_3774724).sum := by decide
  have hdescent : baseEnd_3774724 < baseStart_3774724 := by decide
  rcases family_descends (prefixWord ++ tailWord_3774724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3774754 : List Nat := [3, 3, 1, 1, 3, 2, 2, 2, 1, 4]
def baseStart_3774754 : Nat := 118140960795 + 3774754 * 2 ^ 59
def prefixEnd_3774754 : Nat := 4983230072969 + 3 ^ 40 * 3774754 * 2
def baseEnd_3774754 : Nat := 1292175436321219660876819

theorem tailTrace_3774754 : CollatzResearch.WordTrace tailWord_3774754 prefixEnd_3774754 1292175436321219660876819 := by
  unfold tailWord_3774754
  simp only [CollatzResearch.WordTrace]
  refine ⟨34419147241679602375744829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91784392644478939668652877 34419147241679602375744829)
  ·
    refine ⟨12907180215629850890904311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34419147241679602375744829 12907180215629850890904311)
    ·
      refine ⟨19360770323444776336356467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12907180215629850890904311 19360770323444776336356467)
      ·
        refine ⟨29041155485167164504534701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19360770323444776336356467 29041155485167164504534701)
        ·
          refine ⟨10890433306937686689200513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29041155485167164504534701 10890433306937686689200513)
          ·
            refine ⟨8167824980203265016900385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10890433306937686689200513 8167824980203265016900385)
            ·
              refine ⟨6125868735152448762675289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8167824980203265016900385 6125868735152448762675289)
              ·
                refine ⟨4594401551364336572006467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6125868735152448762675289 4594401551364336572006467)
                ·
                  refine ⟨6891602327046504858009701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4594401551364336572006467 6891602327046504858009701)
                  ·
                    refine ⟨1292175436321219660876819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6891602327046504858009701 1292175436321219660876819)
                    ·
                      rfl

theorem cell22_3774754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 2, 2, 1, 4].length) (baseStart_3774754 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3774754 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3774754 prefixEnd_3774754 := by exact prefixLift 3774754
  have htrace : WordTrace (prefixWord ++ tailWord_3774754) baseStart_3774754 baseEnd_3774754 := by
    simpa [prefixWord, tailWord_3774754, baseEnd_3774754] using wordTrace_append hprefix tailTrace_3774754
  have hstable : (prefixWord ++ tailWord_3774754).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3774754).length < 2 ^ (prefixWord ++ tailWord_3774754).sum := by decide
  have hdescent : baseEnd_3774754 < baseStart_3774754 := by decide
  rcases family_descends (prefixWord ++ tailWord_3774754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3774782 : List Nat := [4, 2, 1, 2, 1, 2, 1, 1, 4, 4]
def baseStart_3774782 : Nat := 118140960795 + 3774782 * 2 ^ 59
def prefixEnd_3774782 : Nat := 4983230072969 + 3 ^ 40 * 3774782 * 2
def baseEnd_3774782 : Nat := 1292185021293436921176733

theorem tailTrace_3774782 : CollatzResearch.WordTrace tailWord_3774782 prefixEnd_3774782 1292185021293436921176733 := by
  unfold tailWord_3774782
  simp only [CollatzResearch.WordTrace]
  refine ⟨17209701276327121285624825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 91785073473744646856665733 17209701276327121285624825)
  ·
    refine ⟨12907275957245340964218619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17209701276327121285624825 12907275957245340964218619)
    ·
      refine ⟨19360913935868011446327929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12907275957245340964218619 19360913935868011446327929)
      ·
        refine ⟨14520685451901008584745947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19360913935868011446327929 14520685451901008584745947)
        ·
          refine ⟨21781028177851512877118921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14520685451901008584745947 21781028177851512877118921)
          ·
            refine ⟨16335771133388634657839191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21781028177851512877118921 16335771133388634657839191)
            ·
              refine ⟨24503656700082951986758787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16335771133388634657839191 24503656700082951986758787)
              ·
                refine ⟨36755485050124427980138181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24503656700082951986758787 36755485050124427980138181)
                ·
                  refine ⟨6891653446898330246275909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36755485050124427980138181 6891653446898330246275909)
                  ·
                    refine ⟨1292185021293436921176733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6891653446898330246275909 1292185021293436921176733)
                    ·
                      rfl

theorem cell22_3774782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 1, 1, 4, 4].length) (baseStart_3774782 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3774782 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3774782 prefixEnd_3774782 := by exact prefixLift 3774782
  have htrace : WordTrace (prefixWord ++ tailWord_3774782) baseStart_3774782 baseEnd_3774782 := by
    simpa [prefixWord, tailWord_3774782, baseEnd_3774782] using wordTrace_append hprefix tailTrace_3774782
  have hstable : (prefixWord ++ tailWord_3774782).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3774782).length < 2 ^ (prefixWord ++ tailWord_3774782).sum := by decide
  have hdescent : baseEnd_3774782 < baseStart_3774782 := by decide
  rcases family_descends (prefixWord ++ tailWord_3774782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3774801 : List Nat := [1, 2, 2, 1, 4, 4, 2, 1, 2, 3]
def baseStart_3774801 : Nat := 118140960795 + 3774801 * 2 ^ 59
def prefixEnd_3774801 : Nat := 4983230072969 + 3 ^ 40 * 3774801 * 2
def baseEnd_3774801 : Nat := 1292191525381727204951675

theorem tailTrace_3774801 : CollatzResearch.WordTrace tailWord_3774801 prefixEnd_3774801 1292191525381727204951675 := by
  unfold tailWord_3774801
  simp only [CollatzResearch.WordTrace]
  refine ⟨137678303197548136529940257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91785535465032091019960171 137678303197548136529940257)
  ·
    refine ⟨103258727398161102397455193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137678303197548136529940257 103258727398161102397455193)
    ·
      refine ⟨77444045548620826798091395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103258727398161102397455193 77444045548620826798091395)
      ·
        refine ⟨116166068322931240197137093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77444045548620826798091395 116166068322931240197137093)
        ·
          refine ⟨21781137810549607536963205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 116166068322931240197137093 21781137810549607536963205)
          ·
            refine ⟨4083963339478051413180601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21781137810549607536963205 4083963339478051413180601)
            ·
              refine ⟨3062972504608538559885451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4083963339478051413180601 3062972504608538559885451)
              ·
                refine ⟨4594458756912807839828177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3062972504608538559885451 4594458756912807839828177)
                ·
                  refine ⟨3445844067684605879871133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4594458756912807839828177 3445844067684605879871133)
                  ·
                    refine ⟨1292191525381727204951675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3445844067684605879871133 1292191525381727204951675)
                    ·
                      rfl

theorem cell22_3774801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 4, 2, 1, 2, 3].length) (baseStart_3774801 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3774801 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3774801 prefixEnd_3774801 := by exact prefixLift 3774801
  have htrace : WordTrace (prefixWord ++ tailWord_3774801) baseStart_3774801 baseEnd_3774801 := by
    simpa [prefixWord, tailWord_3774801, baseEnd_3774801] using wordTrace_append hprefix tailTrace_3774801
  have hstable : (prefixWord ++ tailWord_3774801).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3774801).length < 2 ^ (prefixWord ++ tailWord_3774801).sum := by decide
  have hdescent : baseEnd_3774801 < baseStart_3774801 := by decide
  rcases family_descends (prefixWord ++ tailWord_3774801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3774857 : List Nat := [1, 2, 1, 1, 6, 2, 1, 1, 2, 5]
def baseStart_3774857 : Nat := 118140960795 + 3774857 * 2 ^ 59
def prefixEnd_3774857 : Nat := 4983230072969 + 3 ^ 40 * 3774857 * 2
def baseEnd_3774857 : Nat := 1292210695326161725551503

theorem tailTrace_3774857 : CollatzResearch.WordTrace tailWord_3774857 prefixEnd_3774857 1292210695326161725551503 := by
  unfold tailWord_3774857
  simp only [CollatzResearch.WordTrace]
  refine ⟨137680345685345258093978825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91786897123563505395985883 137680345685345258093978825)
  ·
    refine ⟨103260259264008943570484119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137680345685345258093978825 103260259264008943570484119)
    ·
      refine ⟨154890388896013415355726179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103260259264008943570484119 154890388896013415355726179)
      ·
        refine ⟨232335583344020123033589269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154890388896013415355726179 232335583344020123033589269)
        ·
          refine ⟨10890730469250943267199497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 232335583344020123033589269 10890730469250943267199497)
          ·
            refine ⟨8168047851938207450399623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10890730469250943267199497 8168047851938207450399623)
            ·
              refine ⟨12252071777907311175599435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8168047851938207450399623 12252071777907311175599435)
              ·
                refine ⟨18378107666860966763399153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12252071777907311175599435 18378107666860966763399153)
                ·
                  refine ⟨13783580750145725072549365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18378107666860966763399153 13783580750145725072549365)
                  ·
                    refine ⟨1292210695326161725551503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13783580750145725072549365 1292210695326161725551503)
                    ·
                      rfl

theorem cell22_3774857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 1, 1, 2, 5].length) (baseStart_3774857 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3774857 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3774857 prefixEnd_3774857 := by exact prefixLift 3774857
  have htrace : WordTrace (prefixWord ++ tailWord_3774857) baseStart_3774857 baseEnd_3774857 := by
    simpa [prefixWord, tailWord_3774857, baseEnd_3774857] using wordTrace_append hprefix tailTrace_3774857
  have hstable : (prefixWord ++ tailWord_3774857).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3774857).length < 2 ^ (prefixWord ++ tailWord_3774857).sum := by decide
  have hdescent : baseEnd_3774857 < baseStart_3774857 := by decide
  rcases family_descends (prefixWord ++ tailWord_3774857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3774893 : List Nat := [1, 5, 2, 2, 3, 1, 1, 2, 5]
def baseStart_3774893 : Nat := 118140960795 + 3774893 * 2 ^ 59
def prefixEnd_3774893 : Nat := 4983230072969 + 3 ^ 40 * 3774893 * 2
def baseEnd_3774893 : Nat := 430741006287289877217131

theorem tailTrace_3774893 : CollatzResearch.WordTrace tailWord_3774893 prefixEnd_3774893 430741006287289877217131 := by
  unfold tailWord_3774893
  simp only [CollatzResearch.WordTrace]
  refine ⟨137681658713214836242289333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91787772475476557494859555 137681658713214836242289333)
  ·
    refine ⟨12907655504363890897714625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 137681658713214836242289333 12907655504363890897714625)
    ·
      refine ⟨9680741628272918173285969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12907655504363890897714625 9680741628272918173285969)
      ·
        refine ⟨7260556221204688629964477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9680741628272918173285969 7260556221204688629964477)
        ·
          refine ⟨2722708582951758236236679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7260556221204688629964477 2722708582951758236236679)
          ·
            refine ⟨4084062874427637354355019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2722708582951758236236679 4084062874427637354355019)
            ·
              refine ⟨6126094311641456031532529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4084062874427637354355019 6126094311641456031532529)
              ·
                refine ⟨4594570733731092023649397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6126094311641456031532529 4594570733731092023649397)
                ·
                  refine ⟨430741006287289877217131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4594570733731092023649397 430741006287289877217131)
                  ·
                    rfl

theorem cell22_3774893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 3, 1, 1, 2, 5].length) (baseStart_3774893 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3774893 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3774893 prefixEnd_3774893 := by exact prefixLift 3774893
  have htrace : WordTrace (prefixWord ++ tailWord_3774893) baseStart_3774893 baseEnd_3774893 := by
    simpa [prefixWord, tailWord_3774893, baseEnd_3774893] using wordTrace_append hprefix tailTrace_3774893
  have hstable : (prefixWord ++ tailWord_3774893).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3774893).length < 2 ^ (prefixWord ++ tailWord_3774893).sum := by decide
  have hdescent : baseEnd_3774893 < baseStart_3774893 := by decide
  rcases family_descends (prefixWord ++ tailWord_3774893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3774915 : List Nat := [1, 1, 1, 3, 1, 1, 3, 11]
def baseStart_3774915 : Nat := 118140960795 + 3774915 * 2 ^ 59
def prefixEnd_3774915 : Nat := 4983230072969 + 3 ^ 40 * 3774915 * 2
def baseEnd_3774915 : Nat := 143581172212385434177925

theorem tailTrace_3774915 : CollatzResearch.WordTrace tailWord_3774915 prefixEnd_3774915 143581172212385434177925 := by
  unfold tailWord_3774915
  simp only [CollatzResearch.WordTrace]
  refine ⟨137682461119135133999590199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91788307412756755999726799 137682461119135133999590199)
  ·
    refine ⟨206523691678702700999385299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137682461119135133999590199 206523691678702700999385299)
    ·
      refine ⟨309785537518054051499077949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206523691678702700999385299 309785537518054051499077949)
      ·
        refine ⟨116169576569270269312154231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 309785537518054051499077949 116169576569270269312154231)
        ·
          refine ⟨174254364853905403968231347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116169576569270269312154231 174254364853905403968231347)
          ·
            refine ⟨261381547280858105952347021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 174254364853905403968231347 261381547280858105952347021)
            ·
              refine ⟨98018080230321789732130133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 261381547280858105952347021 98018080230321789732130133)
              ·
                refine ⟨143581172212385434177925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 98018080230321789732130133 143581172212385434177925)
                ·
                  rfl

theorem cell22_3774915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 11].length) (baseStart_3774915 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3774915 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3774915 prefixEnd_3774915 := by exact prefixLift 3774915
  have htrace : WordTrace (prefixWord ++ tailWord_3774915) baseStart_3774915 baseEnd_3774915 := by
    simpa [prefixWord, tailWord_3774915, baseEnd_3774915] using wordTrace_append hprefix tailTrace_3774915
  have hstable : (prefixWord ++ tailWord_3774915).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3774915).length < 2 ^ (prefixWord ++ tailWord_3774915).sum := by decide
  have hdescent : baseEnd_3774915 < baseStart_3774915 := by decide
  rcases family_descends (prefixWord ++ tailWord_3774915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3774919 : List Nat := [1, 1, 4, 1, 1, 6, 1, 1, 1, 5]
def baseStart_3774919 : Nat := 118140960795 + 3774919 * 2 ^ 59
def prefixEnd_3774919 : Nat := 4983230072969 + 3 ^ 40 * 3774919 * 2
def baseEnd_3774919 : Nat := 1292231919193214230501313

theorem tailTrace_3774919 : CollatzResearch.WordTrace tailWord_3774919 prefixEnd_3774919 1292231919193214230501313 := by
  unfold tailWord_3774919
  simp only [CollatzResearch.WordTrace]
  refine ⟨137682607011120642682735811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91788404674080428455157207 137682607011120642682735811)
  ·
    refine ⟨206523910516680964024103717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137682607011120642682735811 206523910516680964024103717)
    ·
      refine ⟨38723233221877680754519447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 206523910516680964024103717 38723233221877680754519447)
      ·
        refine ⟨58084849832816521131779171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38723233221877680754519447 58084849832816521131779171)
        ·
          refine ⟨87127274749224781697668757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58084849832816521131779171 87127274749224781697668757)
          ·
            refine ⟨4084091003869911642078223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 87127274749224781697668757 4084091003869911642078223)
            ·
              refine ⟨6126136505804867463117335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4084091003869911642078223 6126136505804867463117335)
              ·
                refine ⟨9189204758707301194676003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6126136505804867463117335 9189204758707301194676003)
                ·
                  refine ⟨13783807138060951792014005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9189204758707301194676003 13783807138060951792014005)
                  ·
                    refine ⟨1292231919193214230501313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13783807138060951792014005 1292231919193214230501313)
                    ·
                      rfl

theorem cell22_3774919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 6, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 6, 1, 1, 1, 5].length) (baseStart_3774919 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3774919 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3774919 prefixEnd_3774919 := by exact prefixLift 3774919
  have htrace : WordTrace (prefixWord ++ tailWord_3774919) baseStart_3774919 baseEnd_3774919 := by
    simpa [prefixWord, tailWord_3774919, baseEnd_3774919] using wordTrace_append hprefix tailTrace_3774919
  have hstable : (prefixWord ++ tailWord_3774919).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3774919).length < 2 ^ (prefixWord ++ tailWord_3774919).sum := by decide
  have hdescent : baseEnd_3774919 < baseStart_3774919 := by decide
  rcases family_descends (prefixWord ++ tailWord_3774919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3774934 : List Nat := [5, 2, 1, 1, 1, 1, 1, 3, 1, 6]
def baseStart_3774934 : Nat := 118140960795 + 3774934 * 2 ^ 59
def prefixEnd_3774934 : Nat := 4983230072969 + 3 ^ 40 * 3774934 * 2
def baseEnd_3774934 : Nat := 1292237053999759191376267

theorem tailTrace_3774934 : CollatzResearch.WordTrace tailWord_3774934 prefixEnd_3774934 1292237053999759191376267 := by
  unfold tailWord_3774934
  simp only [CollatzResearch.WordTrace]
  refine ⟨8605197131629143765283241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 91788769404044200163021237 8605197131629143765283241)
  ·
    refine ⟨6453897848721857823962431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8605197131629143765283241 6453897848721857823962431)
    ·
      refine ⟨9680846773082786735943647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6453897848721857823962431 9680846773082786735943647)
      ·
        refine ⟨14521270159624180103915471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9680846773082786735943647 14521270159624180103915471)
        ·
          refine ⟨21781905239436270155873207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14521270159624180103915471 21781905239436270155873207)
          ·
            refine ⟨32672857859154405233809811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21781905239436270155873207 32672857859154405233809811)
            ·
              refine ⟨49009286788731607850714717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32672857859154405233809811 49009286788731607850714717)
              ·
                refine ⟨18378482545774352944018019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49009286788731607850714717 18378482545774352944018019)
                ·
                  refine ⟨27567723818661529416027029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18378482545774352944018019 27567723818661529416027029)
                  ·
                    refine ⟨1292237053999759191376267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27567723818661529416027029 1292237053999759191376267)
                    ·
                      rfl

theorem cell22_3774934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 3, 1, 6].length) (baseStart_3774934 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3774934 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3774934 prefixEnd_3774934 := by exact prefixLift 3774934
  have htrace : WordTrace (prefixWord ++ tailWord_3774934) baseStart_3774934 baseEnd_3774934 := by
    simpa [prefixWord, tailWord_3774934, baseEnd_3774934] using wordTrace_append hprefix tailTrace_3774934
  have hstable : (prefixWord ++ tailWord_3774934).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3774934).length < 2 ^ (prefixWord ++ tailWord_3774934).sum := by decide
  have hdescent : baseEnd_3774934 < baseStart_3774934 := by decide
  rcases family_descends (prefixWord ++ tailWord_3774934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3774949 : List Nat := [1, 3, 1, 5, 2, 2, 8]
def baseStart_3774949 : Nat := 118140960795 + 3774949 * 2 ^ 59
def prefixEnd_3774949 : Nat := 4983230072969 + 3 ^ 40 * 3774949 * 2
def baseEnd_3774949 : Nat := 47860821807640894527823

theorem tailTrace_3774949 : CollatzResearch.WordTrace tailWord_3774949 prefixEnd_3774949 47860821807640894527823 := by
  unfold tailWord_3774949
  simp only [CollatzResearch.WordTrace]
  refine ⟨137683701201011957806327901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91789134134007971870885267 137683701201011957806327901)
  ·
    refine ⟨51631387950379484177372963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137683701201011957806327901 51631387950379484177372963)
    ·
      refine ⟨77447081925569226266059445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51631387950379484177372963 77447081925569226266059445)
      ·
        refine ⟨7260663930522114962443073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 77447081925569226266059445 7260663930522114962443073)
        ·
          refine ⟨5445497947891586221832305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7260663930522114962443073 5445497947891586221832305)
          ·
            refine ⟨4084123460918689666374229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5445497947891586221832305 4084123460918689666374229)
            ·
              refine ⟨47860821807640894527823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4084123460918689666374229 47860821807640894527823)
              ·
                rfl

theorem cell22_3774949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 2, 8].length) (baseStart_3774949 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3774949 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3774949 prefixEnd_3774949 := by exact prefixLift 3774949
  have htrace : WordTrace (prefixWord ++ tailWord_3774949) baseStart_3774949 baseEnd_3774949 := by
    simpa [prefixWord, tailWord_3774949, baseEnd_3774949] using wordTrace_append hprefix tailTrace_3774949
  have hstable : (prefixWord ++ tailWord_3774949).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3774949).length < 2 ^ (prefixWord ++ tailWord_3774949).sum := by decide
  have hdescent : baseEnd_3774949 < baseStart_3774949 := by decide
  rcases family_descends (prefixWord ++ tailWord_3774949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3775054 : List Nat := [4, 1, 1, 1, 1, 2, 4, 2, 1, 5]
def baseStart_3775054 : Nat := 118140960795 + 3775054 * 2 ^ 59
def prefixEnd_3775054 : Nat := 4983230072969 + 3 ^ 40 * 3775054 * 2
def baseEnd_3775054 : Nat := 1292278132452118878375899

theorem tailTrace_3775054 : CollatzResearch.WordTrace tailWord_3775054 prefixEnd_3775054 1292278132452118878375899 := by
  unfold tailWord_3775054
  simp only [CollatzResearch.WordTrace]
  refine ⟨17210941358203945092362527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 91791687243754373825933477 17210941358203945092362527)
  ·
    refine ⟨25816412037305917638543791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17210941358203945092362527 25816412037305917638543791)
    ·
      refine ⟨38724618055958876457815687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25816412037305917638543791 38724618055958876457815687)
      ·
        refine ⟨58086927083938314686723531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38724618055958876457815687 58086927083938314686723531)
        ·
          refine ⟨87130390625907472030085297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58086927083938314686723531 87130390625907472030085297)
          ·
            refine ⟨65347792969430604022563973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87130390625907472030085297 65347792969430604022563973)
            ·
              refine ⟨12252711181768238254230745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 65347792969430604022563973 12252711181768238254230745)
              ·
                refine ⟨9189533386326178690673059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12252711181768238254230745 9189533386326178690673059)
                ·
                  refine ⟨13784300079489268036009589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9189533386326178690673059 13784300079489268036009589)
                  ·
                    refine ⟨1292278132452118878375899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13784300079489268036009589 1292278132452118878375899)
                    ·
                      rfl

theorem cell22_3775054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 4, 2, 1, 5].length) (baseStart_3775054 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3775054 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3775054 prefixEnd_3775054 := by exact prefixLift 3775054
  have htrace : WordTrace (prefixWord ++ tailWord_3775054) baseStart_3775054 baseEnd_3775054 := by
    simpa [prefixWord, tailWord_3775054, baseEnd_3775054] using wordTrace_append hprefix tailTrace_3775054
  have hstable : (prefixWord ++ tailWord_3775054).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3775054).length < 2 ^ (prefixWord ++ tailWord_3775054).sum := by decide
  have hdescent : baseEnd_3775054 < baseStart_3775054 := by decide
  rcases family_descends (prefixWord ++ tailWord_3775054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3775088 : List Nat := [2, 1, 1, 1, 8, 1, 1, 1, 1, 5]
def baseStart_3775088 : Nat := 118140960795 + 3775088 * 2 ^ 59
def prefixEnd_3775088 : Nat := 4983230072969 + 3 ^ 40 * 3775088 * 2
def baseEnd_3775088 : Nat := 1292289771346954123025795

theorem tailTrace_3775088 : CollatzResearch.WordTrace tailWord_3775088 prefixEnd_3775088 1292289771346954123025795 := by
  unfold tailWord_3775088
  simp only [CollatzResearch.WordTrace]
  refine ⟨68844385473754192272818959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91792513965005589697091945 68844385473754192272818959)
  ·
    refine ⟨103266578210631288409228439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68844385473754192272818959 103266578210631288409228439)
    ·
      refine ⟨154899867315946932613842659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103266578210631288409228439 154899867315946932613842659)
      ·
        refine ⟨232349800973920398920763989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154899867315946932613842659 232349800973920398920763989)
        ·
          refine ⟨2722849230163129674852703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 232349800973920398920763989 2722849230163129674852703)
          ·
            refine ⟨4084273845244694512279055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2722849230163129674852703 4084273845244694512279055)
            ·
              refine ⟨6126410767867041768418583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4084273845244694512279055 6126410767867041768418583)
              ·
                refine ⟨9189616151800562652627875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6126410767867041768418583 9189616151800562652627875)
                ·
                  refine ⟨13784424227700843978941813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9189616151800562652627875 13784424227700843978941813)
                  ·
                    refine ⟨1292289771346954123025795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13784424227700843978941813 1292289771346954123025795)
                    ·
                      rfl

theorem cell22_3775088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 8, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 8, 1, 1, 1, 1, 5].length) (baseStart_3775088 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3775088 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3775088 prefixEnd_3775088 := by exact prefixLift 3775088
  have htrace : WordTrace (prefixWord ++ tailWord_3775088) baseStart_3775088 baseEnd_3775088 := by
    simpa [prefixWord, tailWord_3775088, baseEnd_3775088] using wordTrace_append hprefix tailTrace_3775088
  have hstable : (prefixWord ++ tailWord_3775088).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3775088).length < 2 ^ (prefixWord ++ tailWord_3775088).sum := by decide
  have hdescent : baseEnd_3775088 < baseStart_3775088 := by decide
  rcases family_descends (prefixWord ++ tailWord_3775088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3775099 : List Nat := [1, 1, 1, 1, 1, 4, 2, 3, 5, 3]
def baseStart_3775099 : Nat := 118140960795 + 3775099 * 2 ^ 59
def prefixEnd_3775099 : Nat := 4983230072969 + 3 ^ 40 * 3775099 * 2
def baseEnd_3775099 : Nat := 1292293536871753761000761

theorem tailTrace_3775099 : CollatzResearch.WordTrace tailWord_3775099 prefixEnd_3775099 1292293536871753761000761 := by
  unfold tailWord_3775099
  simp only [CollatzResearch.WordTrace]
  refine ⟨137689172150468533424288351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91792781433645688949525567 137689172150468533424288351)
  ·
    refine ⟨206533758225702800136432527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137689172150468533424288351 206533758225702800136432527)
    ·
      refine ⟨309800637338554200204648791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206533758225702800136432527 309800637338554200204648791)
      ·
        refine ⟨464700956007831300306973187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 309800637338554200204648791 464700956007831300306973187)
        ·
          refine ⟨697051434011746950460459781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 464700956007831300306973187 697051434011746950460459781)
          ·
            refine ⟨130697143877202553211336209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 697051434011746950460459781 130697143877202553211336209)
            ·
              refine ⟨98022857907901914908502157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 130697143877202553211336209 98022857907901914908502157)
              ·
                refine ⟨36758571715463218090688309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 98022857907901914908502157 36758571715463218090688309)
                ·
                  refine ⟨3446116098324676696002029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 36758571715463218090688309 3446116098324676696002029)
                  ·
                    refine ⟨1292293536871753761000761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3446116098324676696002029 1292293536871753761000761)
                    ·
                      rfl

theorem cell22_3775099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 3, 5, 3].length) (baseStart_3775099 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3775099 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3775099 prefixEnd_3775099 := by exact prefixLift 3775099
  have htrace : WordTrace (prefixWord ++ tailWord_3775099) baseStart_3775099 baseEnd_3775099 := by
    simpa [prefixWord, tailWord_3775099, baseEnd_3775099] using wordTrace_append hprefix tailTrace_3775099
  have hstable : (prefixWord ++ tailWord_3775099).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3775099).length < 2 ^ (prefixWord ++ tailWord_3775099).sum := by decide
  have hdescent : baseEnd_3775099 < baseStart_3775099 := by decide
  rcases family_descends (prefixWord ++ tailWord_3775099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3775129 : List Nat := [1, 2, 1, 2, 1, 2, 4, 4, 5]
def baseStart_3775129 : Nat := 118140960795 + 3775129 * 2 ^ 59
def prefixEnd_3775129 : Nat := 4983230072969 + 3 ^ 40 * 3775129 * 2
def baseEnd_3775129 : Nat := 430767935494947894250223

theorem tailTrace_3775129 : CollatzResearch.WordTrace tailWord_3775129 prefixEnd_3775129 430767935494947894250223 := by
  unfold tailWord_3775129
  simp only [CollatzResearch.WordTrace]
  refine ⟨137690266340359848547880441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91793510893573232365253627 137690266340359848547880441)
  ·
    refine ⟨103267699755269886410910331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137690266340359848547880441 103267699755269886410910331)
    ·
      refine ⟨154901549632904829616365497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103267699755269886410910331 154901549632904829616365497)
      ·
        refine ⟨116176162224678622212274123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154901549632904829616365497 116176162224678622212274123)
        ·
          refine ⟨174264243337017933318411185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116176162224678622212274123 174264243337017933318411185)
          ·
            refine ⟨130698182502763449988808389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 174264243337017933318411185 130698182502763449988808389)
            ·
              refine ⟨24505909219268146872901573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 130698182502763449988808389 24505909219268146872901573)
              ·
                refine ⟨4594857978612777538669045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24505909219268146872901573 4594857978612777538669045)
                ·
                  refine ⟨430767935494947894250223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4594857978612777538669045 430767935494947894250223)
                  ·
                    rfl

theorem cell22_3775129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 4, 4, 5].length) (baseStart_3775129 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3775129 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3775129 prefixEnd_3775129 := by exact prefixLift 3775129
  have htrace : WordTrace (prefixWord ++ tailWord_3775129) baseStart_3775129 baseEnd_3775129 := by
    simpa [prefixWord, tailWord_3775129, baseEnd_3775129] using wordTrace_append hprefix tailTrace_3775129
  have hstable : (prefixWord ++ tailWord_3775129).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3775129).length < 2 ^ (prefixWord ++ tailWord_3775129).sum := by decide
  have hdescent : baseEnd_3775129 < baseStart_3775129 := by decide
  rcases family_descends (prefixWord ++ tailWord_3775129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3775133 : List Nat := [1, 4, 2, 1, 1, 1, 2, 6, 1, 3]
def baseStart_3775133 : Nat := 118140960795 + 3775133 * 2 ^ 59
def prefixEnd_3775133 : Nat := 4983230072969 + 3 ^ 40 * 3775133 * 2
def baseEnd_3775133 : Nat := 1292305175766589005650657

theorem tailTrace_3775133 : CollatzResearch.WordTrace tailWord_3775133 prefixEnd_3775133 1292305175766589005650657 := by
  unfold tailWord_3775133
  simp only [CollatzResearch.WordTrace]
  refine ⟨137690412232345357231026053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91793608154896904820684035 137690412232345357231026053)
  ·
    refine ⟨25816952293564754480817385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 137690412232345357231026053 25816952293564754480817385)
    ·
      refine ⟨19362714220173565860613039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25816952293564754480817385 19362714220173565860613039)
      ·
        refine ⟨29044071330260348790919559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19362714220173565860613039 29044071330260348790919559)
        ·
          refine ⟨43566106995390523186379339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29044071330260348790919559 43566106995390523186379339)
          ·
            refine ⟨65349160493085784779569009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43566106995390523186379339 65349160493085784779569009)
            ·
              refine ⟨49011870369814338584676757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65349160493085784779569009 49011870369814338584676757)
              ·
                refine ⟨2297431423585047121156723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 49011870369814338584676757 2297431423585047121156723)
                ·
                  refine ⟨3446147135377570681735085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2297431423585047121156723 3446147135377570681735085)
                  ·
                    refine ⟨1292305175766589005650657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3446147135377570681735085 1292305175766589005650657)
                    ·
                      rfl

theorem cell22_3775133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 6, 1, 3].length) (baseStart_3775133 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3775133 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3775133 prefixEnd_3775133 := by exact prefixLift 3775133
  have htrace : WordTrace (prefixWord ++ tailWord_3775133) baseStart_3775133 baseEnd_3775133 := by
    simpa [prefixWord, tailWord_3775133, baseEnd_3775133] using wordTrace_append hprefix tailTrace_3775133
  have hstable : (prefixWord ++ tailWord_3775133).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3775133).length < 2 ^ (prefixWord ++ tailWord_3775133).sum := by decide
  have hdescent : baseEnd_3775133 < baseStart_3775133 := by decide
  rcases family_descends (prefixWord ++ tailWord_3775133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3775240 : List Nat := [2, 1, 3, 2, 2, 4, 1, 2, 2, 3]
def baseStart_3775240 : Nat := 118140960795 + 3775240 * 2 ^ 59
def prefixEnd_3775240 : Nat := 4983230072969 + 3 ^ 40 * 3775240 * 2
def baseEnd_3775240 : Nat := 1292341804053276393225329

theorem tailTrace_3775240 : CollatzResearch.WordTrace tailWord_3775240 prefixEnd_3775240 1292341804053276393225329 := by
  unfold tailWord_3775240
  simp only [CollatzResearch.WordTrace]
  refine ⟨68847157421478857252585587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91796209895305143003447449 68847157421478857252585587)
  ·
    refine ⟨103270736132218285878878381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68847157421478857252585587 103270736132218285878878381)
    ·
      refine ⟨38726526049581857204579393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103270736132218285878878381 38726526049581857204579393)
      ·
        refine ⟨29044894537186392903434545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38726526049581857204579393 29044894537186392903434545)
        ·
          refine ⟨21783670902889794677575909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29044894537186392903434545 21783670902889794677575909)
          ·
            refine ⟨4084438294291836502045483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21783670902889794677575909 4084438294291836502045483)
            ·
              refine ⟨6126657441437754753068225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4084438294291836502045483 6126657441437754753068225)
              ·
                refine ⟨4594993081078316064801169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6126657441437754753068225 4594993081078316064801169)
                ·
                  refine ⟨3446244810808737048600877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4594993081078316064801169 3446244810808737048600877)
                  ·
                    refine ⟨1292341804053276393225329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3446244810808737048600877 1292341804053276393225329)
                    ·
                      rfl

theorem cell22_3775240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 4, 1, 2, 2, 3].length) (baseStart_3775240 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3775240 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3775240 prefixEnd_3775240 := by exact prefixLift 3775240
  have htrace : WordTrace (prefixWord ++ tailWord_3775240) baseStart_3775240 baseEnd_3775240 := by
    simpa [prefixWord, tailWord_3775240, baseEnd_3775240] using wordTrace_append hprefix tailTrace_3775240
  have hstable : (prefixWord ++ tailWord_3775240).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3775240).length < 2 ^ (prefixWord ++ tailWord_3775240).sum := by decide
  have hdescent : baseEnd_3775240 < baseStart_3775240 := by decide
  rcases family_descends (prefixWord ++ tailWord_3775240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3775249 : List Nat := [1, 2, 2, 1, 1, 3, 2, 1, 1, 8]
def baseStart_3775249 : Nat := 118140960795 + 3775249 * 2 ^ 59
def prefixEnd_3775249 : Nat := 4983230072969 + 3 ^ 40 * 3775249 * 2
def baseEnd_3775249 : Nat := 1292344884937203369750301

theorem tailTrace_3775249 : CollatzResearch.WordTrace tailWord_3775249 prefixEnd_3775249 1292344884937203369750301 := by
  unfold tailWord_3775249
  simp only [CollatzResearch.WordTrace]
  refine ⟨137694643099925109042248801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91796428733283406028165867 137694643099925109042248801)
  ·
    refine ⟨103270982324943831781686601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137694643099925109042248801 103270982324943831781686601)
    ·
      refine ⟨77453236743707873836264951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103270982324943831781686601 77453236743707873836264951)
      ·
        refine ⟨116179855115561810754397427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77453236743707873836264951 116179855115561810754397427)
        ·
          refine ⟨174269782673342716131596141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116179855115561810754397427 174269782673342716131596141)
          ·
            refine ⟨65351168502503518549348553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 174269782673342716131596141 65351168502503518549348553)
            ·
              refine ⟨49013376376877638912011415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65351168502503518549348553 49013376376877638912011415)
              ·
                refine ⟨73520064565316458368017123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49013376376877638912011415 73520064565316458368017123)
                ·
                  refine ⟨110280096847974687552025685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73520064565316458368017123 110280096847974687552025685)
                  ·
                    refine ⟨1292344884937203369750301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 110280096847974687552025685 1292344884937203369750301)
                    ·
                      rfl

theorem cell22_3775249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 8].length) (baseStart_3775249 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3775249 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3775249 prefixEnd_3775249 := by exact prefixLift 3775249
  have htrace : WordTrace (prefixWord ++ tailWord_3775249) baseStart_3775249 baseEnd_3775249 := by
    simpa [prefixWord, tailWord_3775249, baseEnd_3775249] using wordTrace_append hprefix tailTrace_3775249
  have hstable : (prefixWord ++ tailWord_3775249).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3775249).length < 2 ^ (prefixWord ++ tailWord_3775249).sum := by decide
  have hdescent : baseEnd_3775249 < baseStart_3775249 := by decide
  rcases family_descends (prefixWord ++ tailWord_3775249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3775345 : List Nat := [1, 2, 2, 2, 1, 5, 3, 1, 1, 4]
def baseStart_3775345 : Nat := 118140960795 + 3775345 * 2 ^ 59
def prefixEnd_3775345 : Nat := 4983230072969 + 3 ^ 40 * 3775345 * 2
def baseEnd_3775345 : Nat := 1292377747699091119350007

theorem tailTrace_3775345 : CollatzResearch.WordTrace tailWord_3775345 prefixEnd_3775345 1292377747699091119350007 := by
  unfold tailWord_3775345
  simp only [CollatzResearch.WordTrace]
  refine ⟨137698144507577317437743489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91798763005051544958495659 137698144507577317437743489)
  ·
    refine ⟨103273608380682988078307617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137698144507577317437743489 103273608380682988078307617)
    ·
      refine ⟨77455206285512241058730713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103273608380682988078307617 77455206285512241058730713)
      ·
        refine ⟨58091404714134180794048035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77455206285512241058730713 58091404714134180794048035)
        ·
          refine ⟨87137107071201271191072053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58091404714134180794048035 87137107071201271191072053)
          ·
            refine ⟨8169103787925119174163005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 87137107071201271191072053 8169103787925119174163005)
            ·
              refine ⟨3063413920471919690311127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8169103787925119174163005 3063413920471919690311127)
              ·
                refine ⟨4595120880707879535466691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3063413920471919690311127 4595120880707879535466691)
                ·
                  refine ⟨6892681321061819303200037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4595120880707879535466691 6892681321061819303200037)
                  ·
                    refine ⟨1292377747699091119350007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6892681321061819303200037 1292377747699091119350007)
                    ·
                      rfl

theorem cell22_3775345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 3, 1, 1, 4].length) (baseStart_3775345 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3775345 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3775345 prefixEnd_3775345 := by exact prefixLift 3775345
  have htrace : WordTrace (prefixWord ++ tailWord_3775345) baseStart_3775345 baseEnd_3775345 := by
    simpa [prefixWord, tailWord_3775345, baseEnd_3775345] using wordTrace_append hprefix tailTrace_3775345
  have hstable : (prefixWord ++ tailWord_3775345).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3775345).length < 2 ^ (prefixWord ++ tailWord_3775345).sum := by decide
  have hdescent : baseEnd_3775345 < baseStart_3775345 := by decide
  rcases family_descends (prefixWord ++ tailWord_3775345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3775371 : List Nat := [1, 1, 1, 1, 4, 2, 5, 7]
def baseStart_3775371 : Nat := 118140960795 + 3775371 * 2 ^ 59
def prefixEnd_3775371 : Nat := 4983230072969 + 3 ^ 40 * 3775371 * 2
def baseEnd_3775371 : Nat := 143598516447826190911103

theorem tailTrace_3775371 : CollatzResearch.WordTrace tailWord_3775371 prefixEnd_3775371 143598516447826190911103 := by
  unfold tailWord_3775371
  simp only [CollatzResearch.WordTrace]
  refine ⟨137699092805483123878189967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91799395203655415918793311 137699092805483123878189967)
  ·
    refine ⟨206548639208224685817284951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137699092805483123878189967 206548639208224685817284951)
    ·
      refine ⟨309822958812337028725927427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206548639208224685817284951 309822958812337028725927427)
      ·
        refine ⟨464734438218505543088891141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 309822958812337028725927427 464734438218505543088891141)
        ·
          refine ⟨87137707165969789329167089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 464734438218505543088891141 87137707165969789329167089)
          ·
            refine ⟨65353280374477341996875317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87137707165969789329167089 65353280374477341996875317)
            ·
              refine ⟨6126870035107250812207061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 65353280374477341996875317 6126870035107250812207061)
              ·
                refine ⟨143598516447826190911103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6126870035107250812207061 143598516447826190911103)
                ·
                  rfl

theorem cell22_3775371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 5, 7].length) (baseStart_3775371 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3775371 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3775371 prefixEnd_3775371 := by exact prefixLift 3775371
  have htrace : WordTrace (prefixWord ++ tailWord_3775371) baseStart_3775371 baseEnd_3775371 := by
    simpa [prefixWord, tailWord_3775371, baseEnd_3775371] using wordTrace_append hprefix tailTrace_3775371
  have hstable : (prefixWord ++ tailWord_3775371).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3775371).length < 2 ^ (prefixWord ++ tailWord_3775371).sum := by decide
  have hdescent : baseEnd_3775371 < baseStart_3775371 := by decide
  rcases family_descends (prefixWord ++ tailWord_3775371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3775405 : List Nat := [1, 5, 2, 3, 1, 1, 9]
def baseStart_3775405 : Nat := 118140960795 + 3775405 * 2 ^ 59
def prefixEnd_3775405 : Nat := 4983230072969 + 3 ^ 40 * 3775405 * 2
def baseEnd_3775405 : Nat := 47866603219454480105549

theorem tailTrace_3775405 : CollatzResearch.WordTrace tailWord_3775405 prefixEnd_3775405 47866603219454480105549 := by
  unfold tailWord_3775405
  simp only [CollatzResearch.WordTrace]
  refine ⟨137700332887359947684927669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91800221924906631789951779 137700332887359947684927669)
  ·
    refine ⟨12909406208189995095461969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 137700332887359947684927669 12909406208189995095461969)
    ·
      refine ⟨9682054656142496321596477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12909406208189995095461969 9682054656142496321596477)
      ·
        refine ⟨3630770496053436120598679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9682054656142496321596477 3630770496053436120598679)
        ·
          refine ⟨5446155744080154180898019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3630770496053436120598679 5446155744080154180898019)
          ·
            refine ⟨8169233616120231271347029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5446155744080154180898019 8169233616120231271347029)
            ·
              refine ⟨47866603219454480105549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8169233616120231271347029 47866603219454480105549)
              ·
                rfl

theorem cell22_3775405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 9].length) (baseStart_3775405 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3775405 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3775405 prefixEnd_3775405 := by exact prefixLift 3775405
  have htrace : WordTrace (prefixWord ++ tailWord_3775405) baseStart_3775405 baseEnd_3775405 := by
    simpa [prefixWord, tailWord_3775405, baseEnd_3775405] using wordTrace_append hprefix tailTrace_3775405
  have hstable : (prefixWord ++ tailWord_3775405).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3775405).length < 2 ^ (prefixWord ++ tailWord_3775405).sum := by decide
  have hdescent : baseEnd_3775405 < baseStart_3775405 := by decide
  rcases family_descends (prefixWord ++ tailWord_3775405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3775409 : List Nat := [1, 2, 2, 4, 4, 1, 1, 2, 2, 3]
def baseStart_3775409 : Nat := 118140960795 + 3775409 * 2 ^ 59
def prefixEnd_3775409 : Nat := 4983230072969 + 3 ^ 40 * 3775409 * 2
def baseEnd_3775409 : Nat := 1292399656207016285749811

theorem tailTrace_3775409 : CollatzResearch.WordTrace tailWord_3775409 prefixEnd_3775409 1292399656207016285749811 := by
  unfold tailWord_3775409
  simp only [CollatzResearch.WordTrace]
  refine ⟨137700478779345456368073281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91800319186230304245382187 137700478779345456368073281)
  ·
    refine ⟨103275359084509092276054961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137700478779345456368073281 103275359084509092276054961)
    ·
      refine ⟨77456519313381819207041221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103275359084509092276054961 77456519313381819207041221)
      ·
        refine ⟨14523097371259091101320229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 77456519313381819207041221 14523097371259091101320229)
        ·
          refine ⟨2723080757111079581497543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14523097371259091101320229 2723080757111079581497543)
          ·
            refine ⟨4084621135666619372246315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2723080757111079581497543 4084621135666619372246315)
            ·
              refine ⟨6126931703499929058369473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4084621135666619372246315 6126931703499929058369473)
              ·
                refine ⟨4595198777624946793777105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6126931703499929058369473 4595198777624946793777105)
                ·
                  refine ⟨3446399083218710095332829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4595198777624946793777105 3446399083218710095332829)
                  ·
                    refine ⟨1292399656207016285749811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3446399083218710095332829 1292399656207016285749811)
                    ·
                      rfl

theorem cell22_3775409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 4, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 4, 1, 1, 2, 2, 3].length) (baseStart_3775409 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3775409 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3775409 prefixEnd_3775409 := by exact prefixLift 3775409
  have htrace : WordTrace (prefixWord ++ tailWord_3775409) baseStart_3775409 baseEnd_3775409 := by
    simpa [prefixWord, tailWord_3775409, baseEnd_3775409] using wordTrace_append hprefix tailTrace_3775409
  have hstable : (prefixWord ++ tailWord_3775409).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3775409).length < 2 ^ (prefixWord ++ tailWord_3775409).sum := by decide
  have hdescent : baseEnd_3775409 < baseStart_3775409 := by decide
  rcases family_descends (prefixWord ++ tailWord_3775409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3775493 : List Nat := [1, 3, 1, 1, 2, 3, 2, 3, 1, 5]
def baseStart_3775493 : Nat := 118140960795 + 3775493 * 2 ^ 59
def prefixEnd_3775493 : Nat := 4983230072969 + 3 ^ 40 * 3775493 * 2
def baseEnd_3775493 : Nat := 1292428411123668066649553

theorem tailTrace_3775493 : CollatzResearch.WordTrace tailWord_3775493 prefixEnd_3775493 1292428411123668066649553 := by
  unfold tailWord_3775493
  simp only [CollatzResearch.WordTrace]
  refine ⟨137703542511041138714131133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91802361674027425809420755 137703542511041138714131133)
  ·
    refine ⟨51638828441640427017799175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137703542511041138714131133 51638828441640427017799175)
    ·
      refine ⟨77458242662460640526698763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51638828441640427017799175 77458242662460640526698763)
      ·
        refine ⟨116187363993690960790048145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77458242662460640526698763 116187363993690960790048145)
        ·
          refine ⟨87140522995268220592536109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116187363993690960790048145 87140522995268220592536109)
          ·
            refine ⟨32677696123225582722201041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87140522995268220592536109 32677696123225582722201041)
            ·
              refine ⟨24508272092419187041650781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32677696123225582722201041 24508272092419187041650781)
              ·
                refine ⟨9190602034657195140619043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24508272092419187041650781 9190602034657195140619043)
                ·
                  refine ⟨13785903051985792710928565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9190602034657195140619043 13785903051985792710928565)
                  ·
                    refine ⟨1292428411123668066649553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13785903051985792710928565 1292428411123668066649553)
                    ·
                      rfl

theorem cell22_3775493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 2, 3, 1, 5].length) (baseStart_3775493 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3775493 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3775493 prefixEnd_3775493 := by exact prefixLift 3775493
  have htrace : WordTrace (prefixWord ++ tailWord_3775493) baseStart_3775493 baseEnd_3775493 := by
    simpa [prefixWord, tailWord_3775493, baseEnd_3775493] using wordTrace_append hprefix tailTrace_3775493
  have hstable : (prefixWord ++ tailWord_3775493).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3775493).length < 2 ^ (prefixWord ++ tailWord_3775493).sum := by decide
  have hdescent : baseEnd_3775493 < baseStart_3775493 := by decide
  rcases family_descends (prefixWord ++ tailWord_3775493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3775555 : List Nat := [1, 1, 1, 3, 1, 2, 5, 2, 3, 3]
def baseStart_3775555 : Nat := 118140960795 + 3775555 * 2 ^ 59
def prefixEnd_3775555 : Nat := 4983230072969 + 3 ^ 40 * 3775555 * 2
def baseEnd_3775555 : Nat := 1292449634990720571599363

theorem tailTrace_3775555 : CollatzResearch.WordTrace tailWord_3775555 prefixEnd_3775555 1292449634990720571599363 := by
  unfold tailWord_3775555
  simp only [CollatzResearch.WordTrace]
  refine ⟨137705803836816523302888119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91803869224544348868592079 137705803836816523302888119)
  ·
    refine ⟨206558705755224784954332179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137705803836816523302888119 206558705755224784954332179)
    ·
      refine ⟨309838058632837177431498269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206558705755224784954332179 309838058632837177431498269)
      ·
        refine ⟨116189271987313941536811851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 309838058632837177431498269 116189271987313941536811851)
        ·
          refine ⟨174283907980970912305217777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116189271987313941536811851 174283907980970912305217777)
          ·
            refine ⟨130712930985728184228913333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 174283907980970912305217777 130712930985728184228913333)
            ·
              refine ⟨12254337279912017271460625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 130712930985728184228913333 12254337279912017271460625)
              ·
                refine ⟨9190752959934012953595469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12254337279912017271460625 9190752959934012953595469)
                ·
                  refine ⟨3446532359975254857598301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9190752959934012953595469 3446532359975254857598301)
                  ·
                    refine ⟨1292449634990720571599363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3446532359975254857598301 1292449634990720571599363)
                    ·
                      rfl

theorem cell22_3775555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 5, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 5, 2, 3, 3].length) (baseStart_3775555 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3775555 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3775555 prefixEnd_3775555 := by exact prefixLift 3775555
  have htrace : WordTrace (prefixWord ++ tailWord_3775555) baseStart_3775555 baseEnd_3775555 := by
    simpa [prefixWord, tailWord_3775555, baseEnd_3775555] using wordTrace_append hprefix tailTrace_3775555
  have hstable : (prefixWord ++ tailWord_3775555).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3775555).length < 2 ^ (prefixWord ++ tailWord_3775555).sum := by decide
  have hdescent : baseEnd_3775555 < baseStart_3775555 := by decide
  rcases family_descends (prefixWord ++ tailWord_3775555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3775583 : List Nat := [1, 1, 2, 3, 1, 1, 3, 1, 4, 5]
def baseStart_3775583 : Nat := 118140960795 + 3775583 * 2 ^ 59
def prefixEnd_3775583 : Nat := 4983230072969 + 3 ^ 40 * 3775583 * 2
def baseEnd_3775583 : Nat := 1292459219962937831899277

theorem tailTrace_3775583 : CollatzResearch.WordTrace tailWord_3775583 prefixEnd_3775583 1292459219962937831899277 := by
  unfold tailWord_3775583
  simp only [CollatzResearch.WordTrace]
  refine ⟨137706825080715084084907403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91804550053810056056604935 137706825080715084084907403)
  ·
    refine ⟨206560237621072626127361105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137706825080715084084907403 206560237621072626127361105)
    ·
      refine ⟨154920178215804469595520829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 206560237621072626127361105 154920178215804469595520829)
      ·
        refine ⟨58095066830926676098320311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 154920178215804469595520829 58095066830926676098320311)
        ·
          refine ⟨87142600246390014147480467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58095066830926676098320311 87142600246390014147480467)
          ·
            refine ⟨130713900369585021221220701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87142600246390014147480467 130713900369585021221220701)
            ·
              refine ⟨49017712638594382957957763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 130713900369585021221220701 49017712638594382957957763)
              ·
                refine ⟨73526568957891574436936645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49017712638594382957957763 73526568957891574436936645)
                ·
                  refine ⟨13786231679604670206925621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 73526568957891574436936645 13786231679604670206925621)
                  ·
                    refine ⟨1292459219962937831899277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13786231679604670206925621 1292459219962937831899277)
                    ·
                      rfl

theorem cell22_3775583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 1, 4, 5].length) (baseStart_3775583 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3775583 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3775583 prefixEnd_3775583 := by exact prefixLift 3775583
  have htrace : WordTrace (prefixWord ++ tailWord_3775583) baseStart_3775583 baseEnd_3775583 := by
    simpa [prefixWord, tailWord_3775583, baseEnd_3775583] using wordTrace_append hprefix tailTrace_3775583
  have hstable : (prefixWord ++ tailWord_3775583).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3775583).length < 2 ^ (prefixWord ++ tailWord_3775583).sum := by decide
  have hdescent : baseEnd_3775583 < baseStart_3775583 := by decide
  rcases family_descends (prefixWord ++ tailWord_3775583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3775585 : List Nat := [1, 2, 3, 1, 1, 2, 5, 2, 5]
def baseStart_3775585 : Nat := 118140960795 + 3775585 * 2 ^ 59
def prefixEnd_3775585 : Nat := 4983230072969 + 3 ^ 40 * 3775585 * 2
def baseEnd_3775585 : Nat := 430819968201270164449757

theorem tailTrace_3775585 : CollatzResearch.WordTrace tailWord_3775585 prefixEnd_3775585 430819968201270164449757 := by
  unfold tailWord_3775585
  simp only [CollatzResearch.WordTrace]
  refine ⟨137706898026707838426480209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91804598684471892284320139 137706898026707838426480209)
  ·
    refine ⟨103280173520030878819860157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137706898026707838426480209 103280173520030878819860157)
    ·
      refine ⟨38730065070011579557447559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103280173520030878819860157 38730065070011579557447559)
      ·
        refine ⟨58095097605017369336171339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38730065070011579557447559 58095097605017369336171339)
        ·
          refine ⟨87142646407526054004257009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58095097605017369336171339 87142646407526054004257009)
          ·
            refine ⟨65356984805644540503192757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87142646407526054004257009 65356984805644540503192757)
            ·
              refine ⟨6127217325529175672174321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 65356984805644540503192757 6127217325529175672174321)
              ·
                refine ⟨4595412994146881754130741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6127217325529175672174321 4595412994146881754130741)
                ·
                  refine ⟨430819968201270164449757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4595412994146881754130741 430819968201270164449757)
                  ·
                    rfl

theorem cell22_3775585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 5, 2, 5].length) (baseStart_3775585 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3775585 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3775585 prefixEnd_3775585 := by exact prefixLift 3775585
  have htrace : WordTrace (prefixWord ++ tailWord_3775585) baseStart_3775585 baseEnd_3775585 := by
    simpa [prefixWord, tailWord_3775585, baseEnd_3775585] using wordTrace_append hprefix tailTrace_3775585
  have hstable : (prefixWord ++ tailWord_3775585).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3775585).length < 2 ^ (prefixWord ++ tailWord_3775585).sum := by decide
  have hdescent : baseEnd_3775585 < baseStart_3775585 := by decide
  rcases family_descends (prefixWord ++ tailWord_3775585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3775602 : List Nat := [3, 2, 1, 2, 2, 1, 5, 1, 5]
def baseStart_3775602 : Nat := 118140960795 + 3775602 * 2 ^ 59
def prefixEnd_3775602 : Nat := 4983230072969 + 3 ^ 40 * 3775602 * 2
def baseEnd_3775602 : Nat := 430821908017076038558073

theorem tailTrace_3775602 : CollatzResearch.WordTrace tailWord_3775602 prefixEnd_3775602 430821908017076038558073 := by
  unfold tailWord_3775602
  simp only [CollatzResearch.WordTrace]
  refine ⟨34426879516911562582462265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91805012045097500219899373 34426879516911562582462265)
  ·
    refine ⟨25820159637683671936846699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34426879516911562582462265 25820159637683671936846699)
    ·
      refine ⟨38730239456525507905270049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25820159637683671936846699 38730239456525507905270049)
      ·
        refine ⟨29047679592394130928952537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38730239456525507905270049 29047679592394130928952537)
        ·
          refine ⟨21785759694295598196714403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29047679592394130928952537 21785759694295598196714403)
          ·
            refine ⟨32678639541443397295071605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21785759694295598196714403 32678639541443397295071605)
            ·
              refine ⟨3063622457010318496412963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 32678639541443397295071605 3063622457010318496412963)
              ·
                refine ⟨4595433685515477744619445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3063622457010318496412963 4595433685515477744619445)
                ·
                  refine ⟨430821908017076038558073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4595433685515477744619445 430821908017076038558073)
                  ·
                    rfl

theorem cell22_3775602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 5, 1, 5].length) (baseStart_3775602 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3775602 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3775602 prefixEnd_3775602 := by exact prefixLift 3775602
  have htrace : WordTrace (prefixWord ++ tailWord_3775602) baseStart_3775602 baseEnd_3775602 := by
    simpa [prefixWord, tailWord_3775602, baseEnd_3775602] using wordTrace_append hprefix tailTrace_3775602
  have hstable : (prefixWord ++ tailWord_3775602).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3775602).length < 2 ^ (prefixWord ++ tailWord_3775602).sum := by decide
  have hdescent : baseEnd_3775602 < baseStart_3775602 := by decide
  rcases family_descends (prefixWord ++ tailWord_3775602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3775643 : List Nat := [1, 1, 1, 1, 1, 1, 2, 3, 5, 6]
def baseStart_3775643 : Nat := 118140960795 + 3775643 * 2 ^ 59
def prefixEnd_3775643 : Nat := 4983230072969 + 3 ^ 40 * 3775643 * 2
def baseEnd_3775643 : Nat := 1292479759189117675399093

theorem tailTrace_3775643 : CollatzResearch.WordTrace tailWord_3775643 prefixEnd_3775643 1292479759189117675399093 := by
  unfold tailWord_3775643
  simp only [CollatzResearch.WordTrace]
  refine ⟨137709013460497714332091583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91806008973665142888061055 137709013460497714332091583)
  ·
    refine ⟨206563520190746571498137375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137709013460497714332091583 206563520190746571498137375)
    ·
      refine ⟨309845280286119857247206063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206563520190746571498137375 309845280286119857247206063)
      ·
        refine ⟨464767920429179785870809095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 309845280286119857247206063 464767920429179785870809095)
        ·
          refine ⟨697151880643769678806213643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 464767920429179785870809095 697151880643769678806213643)
          ·
            refine ⟨1045727820965654518209320465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 697151880643769678806213643 1045727820965654518209320465)
            ·
              refine ⟨784295865724240888656990349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1045727820965654518209320465 784295865724240888656990349)
              ·
                refine ⟨294110949646590333246371381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 784295865724240888656990349 294110949646590333246371381)
                ·
                  refine ⟨27572901529367843741847317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 294110949646590333246371381 27572901529367843741847317)
                  ·
                    refine ⟨1292479759189117675399093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27572901529367843741847317 1292479759189117675399093)
                    ·
                      rfl

theorem cell22_3775643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 5, 6].length) (baseStart_3775643 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3775643 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3775643 prefixEnd_3775643 := by exact prefixLift 3775643
  have htrace : WordTrace (prefixWord ++ tailWord_3775643) baseStart_3775643 baseEnd_3775643 := by
    simpa [prefixWord, tailWord_3775643, baseEnd_3775643] using wordTrace_append hprefix tailTrace_3775643
  have hstable : (prefixWord ++ tailWord_3775643).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3775643).length < 2 ^ (prefixWord ++ tailWord_3775643).sum := by decide
  have hdescent : baseEnd_3775643 < baseStart_3775643 := by decide
  rcases family_descends (prefixWord ++ tailWord_3775643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3775709 : List Nat := [1, 4, 3, 2, 2, 2, 1, 7]
def baseStart_3775709 : Nat := 118140960795 + 3775709 * 2 ^ 59
def prefixEnd_3775709 : Nat := 4983230072969 + 3 ^ 40 * 3775709 * 2
def baseEnd_3775709 : Nat := 143611372481990611472099

theorem tailTrace_3775709 : CollatzResearch.WordTrace tailWord_3775709 prefixEnd_3775709 143611372481990611472099 := by
  unfold tailWord_3775709
  simp only [CollatzResearch.WordTrace]
  refine ⟨137711420678258607603994181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91807613785505738402662787 137711420678258607603994181)
  ·
    refine ⟨25820891377173488925748909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 137711420678258607603994181 25820891377173488925748909)
    ·
      refine ⟨9682834266440058347155841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25820891377173488925748909 9682834266440058347155841)
      ·
        refine ⟨7262125699830043760366881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9682834266440058347155841 7262125699830043760366881)
        ·
          refine ⟨5446594274872532820275161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7262125699830043760366881 5446594274872532820275161)
          ·
            refine ⟨4084945706154399615206371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5446594274872532820275161 4084945706154399615206371)
            ·
              refine ⟨6127418559231599422809557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4084945706154399615206371 6127418559231599422809557)
              ·
                refine ⟨143611372481990611472099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6127418559231599422809557 143611372481990611472099)
                ·
                  rfl

theorem cell22_3775709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 2, 1, 7].length) (baseStart_3775709 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3775709 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3775709 prefixEnd_3775709 := by exact prefixLift 3775709
  have htrace : WordTrace (prefixWord ++ tailWord_3775709) baseStart_3775709 baseEnd_3775709 := by
    simpa [prefixWord, tailWord_3775709, baseEnd_3775709] using wordTrace_append hprefix tailTrace_3775709
  have hstable : (prefixWord ++ tailWord_3775709).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3775709).length < 2 ^ (prefixWord ++ tailWord_3775709).sum := by decide
  have hdescent : baseEnd_3775709 < baseStart_3775709 := by decide
  rcases family_descends (prefixWord ++ tailWord_3775709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3775784 : List Nat := [2, 1, 5, 1, 2, 1, 1, 4, 1, 4]
def baseStart_3775784 : Nat := 118140960795 + 3775784 * 2 ^ 59
def prefixEnd_3775784 : Nat := 4983230072969 + 3 ^ 40 * 3775784 * 2
def baseEnd_3775784 : Nat := 1292528026370640307623661

theorem tailTrace_3775784 : CollatzResearch.WordTrace tailWord_3775784 prefixEnd_3775784 1292528026370640307623661 := by
  unfold tailWord_3775784
  simp only [CollatzResearch.WordTrace]
  refine ⟨68857078076493447706487203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91809437435324596941982937 68857078076493447706487203)
  ·
    refine ⟨103285617114740171559730805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68857078076493447706487203 103285617114740171559730805)
    ·
      refine ⟨9683026604506891083724763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 103285617114740171559730805 9683026604506891083724763)
      ·
        refine ⟨14524539906760336625587145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9683026604506891083724763 14524539906760336625587145)
        ·
          refine ⟨10893404930070252469190359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14524539906760336625587145 10893404930070252469190359)
          ·
            refine ⟨16340107395105378703785539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10893404930070252469190359 16340107395105378703785539)
            ·
              refine ⟨24510161092658068055678309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16340107395105378703785539 24510161092658068055678309)
              ·
                refine ⟨4595655204873387760439683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24510161092658068055678309 4595655204873387760439683)
                ·
                  refine ⟨6893482807310081640659525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4595655204873387760439683 6893482807310081640659525)
                  ·
                    refine ⟨1292528026370640307623661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6893482807310081640659525 1292528026370640307623661)
                    ·
                      rfl

theorem cell22_3775784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 1, 4, 1, 4].length) (baseStart_3775784 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3775784 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3775784 prefixEnd_3775784 := by exact prefixLift 3775784
  have htrace : WordTrace (prefixWord ++ tailWord_3775784) baseStart_3775784 baseEnd_3775784 := by
    simpa [prefixWord, tailWord_3775784, baseEnd_3775784] using wordTrace_append hprefix tailTrace_3775784
  have hstable : (prefixWord ++ tailWord_3775784).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3775784).length < 2 ^ (prefixWord ++ tailWord_3775784).sum := by decide
  have hdescent : baseEnd_3775784 < baseStart_3775784 := by decide
  rcases family_descends (prefixWord ++ tailWord_3775784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3775831 : List Nat := [1, 1, 3, 2, 3, 2, 4, 1, 2, 3]
def baseStart_3775831 : Nat := 118140960795 + 3775831 * 2 ^ 59
def prefixEnd_3775831 : Nat := 4983230072969 + 3 ^ 40 * 3775831 * 2
def baseEnd_3775831 : Nat := 1292544115431147851698517

theorem tailTrace_3775831 : CollatzResearch.WordTrace tailWord_3775831 prefixEnd_3775831 1292544115431147851698517 := by
  unfold tailWord_3775831
  simp only [CollatzResearch.WordTrace]
  refine ⟨137715870383816622439935347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91810580255877748293290231 137715870383816622439935347)
  ·
    refine ⟨206573805575724933659903021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137715870383816622439935347 206573805575724933659903021)
    ·
      refine ⟨77465177090896850122463633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 206573805575724933659903021 77465177090896850122463633)
      ·
        refine ⟨58098882818172637591847725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77465177090896850122463633 58098882818172637591847725)
        ·
          refine ⟨21787081056814739096942897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58098882818172637591847725 21787081056814739096942897)
          ·
            refine ⟨16340310792611054322707173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21787081056814739096942897 16340310792611054322707173)
            ·
              refine ⟨3063808273614572685507595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16340310792611054322707173 3063808273614572685507595)
              ·
                refine ⟨4595712410421859028261393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3063808273614572685507595 4595712410421859028261393)
                ·
                  refine ⟨3446784307816394271196045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4595712410421859028261393 3446784307816394271196045)
                  ·
                    refine ⟨1292544115431147851698517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3446784307816394271196045 1292544115431147851698517)
                    ·
                      rfl

theorem cell22_3775831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 4, 1, 2, 3].length) (baseStart_3775831 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3775831 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3775831 prefixEnd_3775831 := by exact prefixLift 3775831
  have htrace : WordTrace (prefixWord ++ tailWord_3775831) baseStart_3775831 baseEnd_3775831 := by
    simpa [prefixWord, tailWord_3775831, baseEnd_3775831] using wordTrace_append hprefix tailTrace_3775831
  have hstable : (prefixWord ++ tailWord_3775831).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3775831).length < 2 ^ (prefixWord ++ tailWord_3775831).sum := by decide
  have hdescent : baseEnd_3775831 < baseStart_3775831 := by decide
  rcases family_descends (prefixWord ++ tailWord_3775831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3775947 : List Nat := [1, 1, 1, 1, 3, 3, 3, 2, 1, 6]
def baseStart_3775947 : Nat := 118140960795 + 3775947 * 2 ^ 59
def prefixEnd_3775947 : Nat := 4983230072969 + 3 ^ 40 * 3775947 * 2
def baseEnd_3775947 : Nat := 1292583824601762215798161

theorem tailTrace_3775947 : CollatzResearch.WordTrace tailWord_3775947 prefixEnd_3775947 1292583824601762215798161 := by
  unfold tailWord_3775947
  simp only [CollatzResearch.WordTrace]
  refine ⟨137720101251396374251158095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91813400834264249500772063 137720101251396374251158095)
  ·
    refine ⟨206580151877094561376737143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137720101251396374251158095 206580151877094561376737143)
    ·
      refine ⟨309870227815641842065105715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206580151877094561376737143 309870227815641842065105715)
      ·
        refine ⟨464805341723462763097658573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 309870227815641842065105715 464805341723462763097658573)
        ·
          refine ⟨174302003146298536161621965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 464805341723462763097658573 174302003146298536161621965)
          ·
            refine ⟨65363251179861951060608237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 174302003146298536161621965 65363251179861951060608237)
            ·
              refine ⟨24511219192448231647728089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65363251179861951060608237 24511219192448231647728089)
              ·
                refine ⟨18383414394336173735796067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24511219192448231647728089 18383414394336173735796067)
                ·
                  refine ⟨27575121591504260603694101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18383414394336173735796067 27575121591504260603694101)
                  ·
                    refine ⟨1292583824601762215798161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27575121591504260603694101 1292583824601762215798161)
                    ·
                      rfl

theorem cell22_3775947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 3, 2, 1, 6].length) (baseStart_3775947 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3775947 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3775947 prefixEnd_3775947 := by exact prefixLift 3775947
  have htrace : WordTrace (prefixWord ++ tailWord_3775947) baseStart_3775947 baseEnd_3775947 := by
    simpa [prefixWord, tailWord_3775947, baseEnd_3775947] using wordTrace_append hprefix tailTrace_3775947
  have hstable : (prefixWord ++ tailWord_3775947).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3775947).length < 2 ^ (prefixWord ++ tailWord_3775947).sum := by decide
  have hdescent : baseEnd_3775947 < baseStart_3775947 := by decide
  rcases family_descends (prefixWord ++ tailWord_3775947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3776028 : List Nat := [2, 2, 3, 1, 2, 1, 2, 5, 1, 3]
def baseStart_3776028 : Nat := 118140960795 + 3776028 * 2 ^ 59
def prefixEnd_3776028 : Nat := 4983230072969 + 3 ^ 40 * 3776028 * 2
def baseEnd_3776028 : Nat := 1292611552557105004522913

theorem tailTrace_3776028 : CollatzResearch.WordTrace tailWord_3776028 prefixEnd_3776028 1292611552557105004522913 := by
  unfold tailWord_3776028
  simp only [CollatzResearch.WordTrace]
  refine ⟨68861527782051462542428369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91815370376068616723237825 68861527782051462542428369)
  ·
    refine ⟨51646145836538596906821277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68861527782051462542428369 51646145836538596906821277)
    ·
      refine ⟨19367304688701973840057979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51646145836538596906821277 19367304688701973840057979)
      ·
        refine ⟨29050957033052960760086969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19367304688701973840057979 29050957033052960760086969)
        ·
          refine ⟨21788217774789720570065227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29050957033052960760086969 21788217774789720570065227)
          ·
            refine ⟨32682326662184580855097841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21788217774789720570065227 32682326662184580855097841)
            ·
              refine ⟨24511744996638435641323381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32682326662184580855097841 24511744996638435641323381)
              ·
                refine ⟨2297976093434853341374067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24511744996638435641323381 2297976093434853341374067)
                ·
                  refine ⟨3446964140152280012061101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2297976093434853341374067 3446964140152280012061101)
                  ·
                    refine ⟨1292611552557105004522913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3446964140152280012061101 1292611552557105004522913)
                    ·
                      rfl

theorem cell22_3776028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 2, 5, 1, 3].length) (baseStart_3776028 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3776028 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3776028 prefixEnd_3776028 := by exact prefixLift 3776028
  have htrace : WordTrace (prefixWord ++ tailWord_3776028) baseStart_3776028 baseEnd_3776028 := by
    simpa [prefixWord, tailWord_3776028, baseEnd_3776028] using wordTrace_append hprefix tailTrace_3776028
  have hstable : (prefixWord ++ tailWord_3776028).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3776028).length < 2 ^ (prefixWord ++ tailWord_3776028).sum := by decide
  have hdescent : baseEnd_3776028 < baseStart_3776028 := by decide
  rcases family_descends (prefixWord ++ tailWord_3776028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3776030 : List Nat := [4, 3, 3, 1, 2, 9]
def baseStart_3776030 : Nat := 118140960795 + 3776030 * 2 ^ 59
def prefixEnd_3776030 : Nat := 4983230072969 + 3 ^ 40 * 3776030 * 2
def baseEnd_3776030 : Nat := 15958175767876267481147

theorem tailTrace_3776030 : CollatzResearch.WordTrace tailWord_3776030 prefixEnd_3776030 15958175767876267481147 := by
  unfold tailWord_3776030
  simp only [CollatzResearch.WordTrace]
  refine ⟨17215391063761959928303693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 91815419006730452950953029 17215391063761959928303693)
  ·
    refine ⟨6455771648910734973113885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17215391063761959928303693 6455771648910734973113885)
    ·
      refine ⟨2420914368341525614917707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6455771648910734973113885 2420914368341525614917707)
      ·
        refine ⟨3631371552512288422376561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2420914368341525614917707 3631371552512288422376561)
        ·
          refine ⟨2723528664384216316782421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3631371552512288422376561 2723528664384216316782421)
          ·
            refine ⟨15958175767876267481147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2723528664384216316782421 15958175767876267481147)
            ·
              rfl

theorem cell22_3776030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 2, 9].length) (baseStart_3776030 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3776030 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3776030 prefixEnd_3776030 := by exact prefixLift 3776030
  have htrace : WordTrace (prefixWord ++ tailWord_3776030) baseStart_3776030 baseEnd_3776030 := by
    simpa [prefixWord, tailWord_3776030, baseEnd_3776030] using wordTrace_append hprefix tailTrace_3776030
  have hstable : (prefixWord ++ tailWord_3776030).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3776030).length < 2 ^ (prefixWord ++ tailWord_3776030).sum := by decide
  have hdescent : baseEnd_3776030 < baseStart_3776030 := by decide
  rcases family_descends (prefixWord ++ tailWord_3776030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3776069 : List Nat := [1, 3, 1, 1, 1, 4, 3, 2, 6]
def baseStart_3776069 : Nat := 118140960795 + 3776069 * 2 ^ 59
def prefixEnd_3776069 : Nat := 4983230072969 + 3 ^ 40 * 3776069 * 2
def baseEnd_3776069 : Nat := 430875195898331521415929

theorem tailTrace_3776069 : CollatzResearch.WordTrace tailWord_3776069 prefixEnd_3776069 430875195898331521415929 := by
  unfold tailWord_3776069
  simp only [CollatzResearch.WordTrace]
  refine ⟨137724550956954389087099261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91816367304636259391399507 137724550956954389087099261)
  ·
    refine ⟨51646706608857895907662223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137724550956954389087099261 51646706608857895907662223)
    ·
      refine ⟨77470059913286843861493335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51646706608857895907662223 77470059913286843861493335)
      ·
        refine ⟨116205089869930265792240003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77470059913286843861493335 116205089869930265792240003)
        ·
          refine ⟨174307634804895398688360005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116205089869930265792240003 174307634804895398688360005)
          ·
            refine ⟨32682681525917887254067501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 174307634804895398688360005 32682681525917887254067501)
            ·
              refine ⟨12256005572219207720275313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32682681525917887254067501 12256005572219207720275313)
              ·
                refine ⟨9192004179164405790206485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12256005572219207720275313 9192004179164405790206485)
                ·
                  refine ⟨430875195898331521415929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9192004179164405790206485 430875195898331521415929)
                  ·
                    rfl

theorem cell22_3776069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 3, 2, 6].length) (baseStart_3776069 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3776069 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3776069 prefixEnd_3776069 := by exact prefixLift 3776069
  have htrace : WordTrace (prefixWord ++ tailWord_3776069) baseStart_3776069 baseEnd_3776069 := by
    simpa [prefixWord, tailWord_3776069, baseEnd_3776069] using wordTrace_append hprefix tailTrace_3776069
  have hstable : (prefixWord ++ tailWord_3776069).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3776069).length < 2 ^ (prefixWord ++ tailWord_3776069).sum := by decide
  have hdescent : baseEnd_3776069 < baseStart_3776069 := by decide
  rcases family_descends (prefixWord ++ tailWord_3776069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3776118 : List Nat := [5, 1, 1, 2, 2, 1, 3, 1, 1, 5]
def baseStart_3776118 : Nat := 118140960795 + 3776118 * 2 ^ 59
def prefixEnd_3776118 : Nat := 4983230072969 + 3 ^ 40 * 3776118 * 2
def baseEnd_3776118 : Nat := 1292642361396374769772637

theorem tailTrace_3776118 : CollatzResearch.WordTrace tailWord_3776118 prefixEnd_3776118 1292642361396374769772637 := by
  unfold tailWord_3776118
  simp only [CollatzResearch.WordTrace]
  refine ⟨8607896133361054403477063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 91817558755851246970422005 8607896133361054403477063)
  ·
    refine ⟨12911844200041581605215595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8607896133361054403477063 12911844200041581605215595)
    ·
      refine ⟨19367766300062372407823393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12911844200041581605215595 19367766300062372407823393)
      ·
        refine ⟨14525824725046779305867545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19367766300062372407823393 14525824725046779305867545)
        ·
          refine ⟨10894368543785084479400659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14525824725046779305867545 10894368543785084479400659)
          ·
            refine ⟨16341552815677626719100989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10894368543785084479400659 16341552815677626719100989)
            ·
              refine ⟨6128082305879110019662871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16341552815677626719100989 6128082305879110019662871)
              ·
                refine ⟨9192123458818665029494307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6128082305879110019662871 9192123458818665029494307)
                ·
                  refine ⟨13788185188227997544241461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9192123458818665029494307 13788185188227997544241461)
                  ·
                    refine ⟨1292642361396374769772637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13788185188227997544241461 1292642361396374769772637)
                    ·
                      rfl

theorem cell22_3776118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 3, 1, 1, 5].length) (baseStart_3776118 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3776118 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3776118 prefixEnd_3776118 := by exact prefixLift 3776118
  have htrace : WordTrace (prefixWord ++ tailWord_3776118) baseStart_3776118 baseEnd_3776118 := by
    simpa [prefixWord, tailWord_3776118, baseEnd_3776118] using wordTrace_append hprefix tailTrace_3776118
  have hstable : (prefixWord ++ tailWord_3776118).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3776118).length < 2 ^ (prefixWord ++ tailWord_3776118).sum := by decide
  have hdescent : baseEnd_3776118 < baseStart_3776118 := by decide
  rcases family_descends (prefixWord ++ tailWord_3776118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3776148 : List Nat := [2, 4, 2, 2, 2, 2, 8]
def baseStart_3776148 : Nat := 118140960795 + 3776148 * 2 ^ 59
def prefixEnd_3776148 : Nat := 4983230072969 + 3 ^ 40 * 3776148 * 2
def baseEnd_3776148 : Nat := 47876023370720914500835

theorem tailTrace_3776148 : CollatzResearch.WordTrace tailWord_3776148 prefixEnd_3776148 47876023370720914500835 := by
  unfold tailWord_3776148
  simp only [CollatzResearch.WordTrace]
  refine ⟨68863716161834092789612549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91818288215778790386150065 68863716161834092789612549)
  ·
    refine ⟨12911946780343892398052353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 68863716161834092789612549 12911946780343892398052353)
    ·
      refine ⟨9683960085257919298539265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12911946780343892398052353 9683960085257919298539265)
      ·
        refine ⟨7262970063943439473904449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9683960085257919298539265 7262970063943439473904449)
        ·
          refine ⟨5447227547957579605428337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7262970063943439473904449 5447227547957579605428337)
          ·
            refine ⟨4085420660968184704071253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5447227547957579605428337 4085420660968184704071253)
            ·
              refine ⟨47876023370720914500835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4085420660968184704071253 47876023370720914500835)
              ·
                rfl

theorem cell22_3776148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 2, 8].length) (baseStart_3776148 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3776148 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3776148 prefixEnd_3776148 := by exact prefixLift 3776148
  have htrace : WordTrace (prefixWord ++ tailWord_3776148) baseStart_3776148 baseEnd_3776148 := by
    simpa [prefixWord, tailWord_3776148, baseEnd_3776148] using wordTrace_append hprefix tailTrace_3776148
  have hstable : (prefixWord ++ tailWord_3776148).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3776148).length < 2 ^ (prefixWord ++ tailWord_3776148).sum := by decide
  have hdescent : baseEnd_3776148 < baseStart_3776148 := by decide
  rcases family_descends (prefixWord ++ tailWord_3776148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3776219 : List Nat := [1, 1, 1, 1, 1, 1, 1, 3, 1, 11]
def baseStart_3776219 : Nat := 118140960795 + 3776219 * 2 ^ 59
def prefixEnd_3776219 : Nat := 4983230072969 + 3 ^ 40 * 3776219 * 2
def baseEnd_3776219 : Nat := 1292676935760444172997327

theorem tailTrace_3776219 : CollatzResearch.WordTrace tailWord_3776219 prefixEnd_3776219 1292676935760444172997327 := by
  unfold tailWord_3776219
  simp only [CollatzResearch.WordTrace]
  refine ⟨137730021906410964705059711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91820014604273976470039807 137730021906410964705059711)
  ·
    refine ⟨206595032859616447057589567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137730021906410964705059711 206595032859616447057589567)
    ·
      refine ⟨309892549289424670586384351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206595032859616447057589567 309892549289424670586384351)
      ·
        refine ⟨464838823934137005879576527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 309892549289424670586384351 464838823934137005879576527)
        ·
          refine ⟨697258235901205508819364791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 464838823934137005879576527 697258235901205508819364791)
          ·
            refine ⟨1045887353851808263229047187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 697258235901205508819364791 1045887353851808263229047187)
            ·
              refine ⟨1568831030777712394843570781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1045887353851808263229047187 1568831030777712394843570781)
              ·
                refine ⟨588311636541642148066339043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1568831030777712394843570781 588311636541642148066339043)
                ·
                  refine ⟨882467454812463222099508565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 588311636541642148066339043 882467454812463222099508565)
                  ·
                    refine ⟨1292676935760444172997327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 11 882467454812463222099508565 1292676935760444172997327)
                    ·
                      rfl

theorem cell22_3776219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 11].length) (baseStart_3776219 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3776219 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3776219 prefixEnd_3776219 := by exact prefixLift 3776219
  have htrace : WordTrace (prefixWord ++ tailWord_3776219) baseStart_3776219 baseEnd_3776219 := by
    simpa [prefixWord, tailWord_3776219, baseEnd_3776219] using wordTrace_append hprefix tailTrace_3776219
  have hstable : (prefixWord ++ tailWord_3776219).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3776219).length < 2 ^ (prefixWord ++ tailWord_3776219).sum := by decide
  have hdescent : baseEnd_3776219 < baseStart_3776219 := by decide
  rcases family_descends (prefixWord ++ tailWord_3776219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3776236 : List Nat := [2, 2, 1, 1, 2, 2, 3, 3, 1, 5]
def baseStart_3776236 : Nat := 118140960795 + 3776236 * 2 ^ 59
def prefixEnd_3776236 : Nat := 4983230072969 + 3 ^ 40 * 3776236 * 2
def baseEnd_3776236 : Nat := 1292682755207861795322275

theorem tailTrace_3776236 : CollatzResearch.WordTrace tailWord_3776236 prefixEnd_3776236 1292682755207861795322275 := by
  unfold tailWord_3776236
  simp only [CollatzResearch.WordTrace]
  refine ⟨68865320973674688304214281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91820427964899584405619041 68865320973674688304214281)
  ·
    refine ⟨51648990730256016228160711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68865320973674688304214281 51648990730256016228160711)
    ·
      refine ⟨77473486095384024342241067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51648990730256016228160711 77473486095384024342241067)
      ·
        refine ⟨116210229143076036513361601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77473486095384024342241067 116210229143076036513361601)
        ·
          refine ⟨87157671857307027385021201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116210229143076036513361601 87157671857307027385021201)
          ·
            refine ⟨65368253892980270538765901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87157671857307027385021201 65368253892980270538765901)
            ·
              refine ⟨24513095209867601452037213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65368253892980270538765901 24513095209867601452037213)
              ·
                refine ⟨9192410703700350544513955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24513095209867601452037213 9192410703700350544513955)
                ·
                  refine ⟨13788616055550525816770933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9192410703700350544513955 13788616055550525816770933)
                  ·
                    refine ⟨1292682755207861795322275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13788616055550525816770933 1292682755207861795322275)
                    ·
                      rfl

theorem cell22_3776236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 5].length) (baseStart_3776236 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3776236 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3776236 prefixEnd_3776236 := by exact prefixLift 3776236
  have htrace : WordTrace (prefixWord ++ tailWord_3776236) baseStart_3776236 baseEnd_3776236 := by
    simpa [prefixWord, tailWord_3776236, baseEnd_3776236] using wordTrace_append hprefix tailTrace_3776236
  have hstable : (prefixWord ++ tailWord_3776236).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3776236).length < 2 ^ (prefixWord ++ tailWord_3776236).sum := by decide
  have hdescent : baseEnd_3776236 < baseStart_3776236 := by decide
  rcases family_descends (prefixWord ++ tailWord_3776236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3776251 : List Nat := [1, 1, 1, 1, 1, 3, 1, 7, 2, 4]
def baseStart_3776251 : Nat := 118140960795 + 3776251 * 2 ^ 59
def prefixEnd_3776251 : Nat := 4983230072969 + 3 ^ 40 * 3776251 * 2
def baseEnd_3776251 : Nat := 1292687890014406756197229

theorem tailTrace_3776251 : CollatzResearch.WordTrace tailWord_3776251 prefixEnd_3776251 1292687890014406756197229 := by
  unfold tailWord_3776251
  simp only [CollatzResearch.WordTrace]
  refine ⟨137731189042295034170224607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91820792694863356113483071 137731189042295034170224607)
  ·
    refine ⟨206596783563442551255336911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137731189042295034170224607 206596783563442551255336911)
    ·
      refine ⟨309895175345163826883005367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206596783563442551255336911 309895175345163826883005367)
      ·
        refine ⟨464842763017745740324508051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 309895175345163826883005367 464842763017745740324508051)
        ·
          refine ⟨697264144526618610486762077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 464842763017745740324508051 697264144526618610486762077)
          ·
            refine ⟨261474054197481978932535779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 697264144526618610486762077 261474054197481978932535779)
            ·
              refine ⟨392211081296222968398803669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 261474054197481978932535779 392211081296222968398803669)
              ·
                refine ⟨9192447217880225821846961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 392211081296222968398803669 9192447217880225821846961)
                ·
                  refine ⟨6894335413410169366385221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9192447217880225821846961 6894335413410169366385221)
                  ·
                    refine ⟨1292687890014406756197229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6894335413410169366385221 1292687890014406756197229)
                    ·
                      rfl

theorem cell22_3776251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 7, 2, 4].length) (baseStart_3776251 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3776251 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3776251 prefixEnd_3776251 := by exact prefixLift 3776251
  have htrace : WordTrace (prefixWord ++ tailWord_3776251) baseStart_3776251 baseEnd_3776251 := by
    simpa [prefixWord, tailWord_3776251, baseEnd_3776251] using wordTrace_append hprefix tailTrace_3776251
  have hstable : (prefixWord ++ tailWord_3776251).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3776251).length < 2 ^ (prefixWord ++ tailWord_3776251).sum := by decide
  have hdescent : baseEnd_3776251 < baseStart_3776251 := by decide
  rcases family_descends (prefixWord ++ tailWord_3776251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3776266 : List Nat := [3, 1, 2, 2, 1, 4, 9]
def baseStart_3776266 : Nat := 118140960795 + 3776266 * 2 ^ 59
def prefixEnd_3776266 : Nat := 4983230072969 + 3 ^ 40 * 3776266 * 2
def baseEnd_3776266 : Nat := 47877519437813026558229

theorem tailTrace_3776266 : CollatzResearch.WordTrace tailWord_3776266 prefixEnd_3776266 47877519437813026558229 := by
  unfold tailWord_3776266
  simp only [CollatzResearch.WordTrace]
  refine ⟨34432934034310172933005163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91821157424827127821347101 34432934034310172933005163)
  ·
    refine ⟨51649401051465259399507745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34432934034310172933005163 51649401051465259399507745)
    ·
      refine ⟨38737050788598944549630809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51649401051465259399507745 38737050788598944549630809)
      ·
        refine ⟨29052788091449208412223107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38737050788598944549630809 29052788091449208412223107)
        ·
          refine ⟨43579182137173812618334661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29052788091449208412223107 43579182137173812618334661)
          ·
            refine ⟨8171096650720089865937749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43579182137173812618334661 8171096650720089865937749)
            ·
              refine ⟨47877519437813026558229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8171096650720089865937749 47877519437813026558229)
              ·
                rfl

theorem cell22_3776266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 9].length) (baseStart_3776266 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3776266 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3776266 prefixEnd_3776266 := by exact prefixLift 3776266
  have htrace : WordTrace (prefixWord ++ tailWord_3776266) baseStart_3776266 baseEnd_3776266 := by
    simpa [prefixWord, tailWord_3776266, baseEnd_3776266] using wordTrace_append hprefix tailTrace_3776266
  have hstable : (prefixWord ++ tailWord_3776266).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3776266).length < 2 ^ (prefixWord ++ tailWord_3776266).sum := by decide
  have hdescent : baseEnd_3776266 < baseStart_3776266 := by decide
  rcases family_descends (prefixWord ++ tailWord_3776266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3776270 : List Nat := [4, 1, 1, 2, 1, 1, 5, 2, 2, 3]
def baseStart_3776270 : Nat := 118140960795 + 3776270 * 2 ^ 59
def prefixEnd_3776270 : Nat := 4983230072969 + 3 ^ 40 * 3776270 * 2
def baseEnd_3776270 : Nat := 1292694394102697039972171

theorem tailTrace_3776270 : CollatzResearch.WordTrace tailWord_3776270 prefixEnd_3776270 1292694394102697039972171 := by
  unfold tailWord_3776270
  simp only [CollatzResearch.WordTrace]
  refine ⟨17216485253653275051895783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 91821254686150800276777509 17216485253653275051895783)
  ·
    refine ⟨25824727880479912577843675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17216485253653275051895783 25824727880479912577843675)
    ·
      refine ⟨38737091820719868866765513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25824727880479912577843675 38737091820719868866765513)
      ·
        refine ⟨29052818865539901650074135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38737091820719868866765513 29052818865539901650074135)
        ·
          refine ⟨43579228298309852475111203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29052818865539901650074135 43579228298309852475111203)
          ·
            refine ⟨65368842447464778712666805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43579228298309852475111203 65368842447464778712666805)
            ·
              refine ⟨6128328979449823004312513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 65368842447464778712666805 6128328979449823004312513)
              ·
                refine ⟨4596246734587367253234385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6128328979449823004312513 4596246734587367253234385)
                ·
                  refine ⟨3447185050940525439925789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4596246734587367253234385 3447185050940525439925789)
                  ·
                    refine ⟨1292694394102697039972171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3447185050940525439925789 1292694394102697039972171)
                    ·
                      rfl

theorem cell22_3776270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 5, 2, 2, 3].length) (baseStart_3776270 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3776270 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3776270 prefixEnd_3776270 := by exact prefixLift 3776270
  have htrace : WordTrace (prefixWord ++ tailWord_3776270) baseStart_3776270 baseEnd_3776270 := by
    simpa [prefixWord, tailWord_3776270, baseEnd_3776270] using wordTrace_append hprefix tailTrace_3776270
  have hstable : (prefixWord ++ tailWord_3776270).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3776270).length < 2 ^ (prefixWord ++ tailWord_3776270).sum := by decide
  have hdescent : baseEnd_3776270 < baseStart_3776270 := by decide
  rcases family_descends (prefixWord ++ tailWord_3776270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3776332 : List Nat := [2, 2, 1, 3, 4, 2, 1, 1, 3, 3]
def baseStart_3776332 : Nat := 118140960795 + 3776332 * 2 ^ 59
def prefixEnd_3776332 : Nat := 4983230072969 + 3 ^ 40 * 3776332 * 2
def baseEnd_3776332 : Nat := 1292715617969749544921981

theorem tailTrace_3776332 : CollatzResearch.WordTrace tailWord_3776332 prefixEnd_3776332 1292715617969749544921981 := by
  unfold tailWord_3776332
  simp only [CollatzResearch.WordTrace]
  refine ⟨68867071677500792501961625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91822762236667723335948833 68867071677500792501961625)
  ·
    refine ⟨51650303758125594376471219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68867071677500792501961625 51650303758125594376471219)
    ·
      refine ⟨77475455637188391564706829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51650303758125594376471219 77475455637188391564706829)
      ·
        refine ⟨29053295863945646836765061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77475455637188391564706829 29053295863945646836765061)
        ·
          refine ⟨5447492974489808781893449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29053295863945646836765061 5447492974489808781893449)
          ·
            refine ⟨4085619730867356586420087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5447492974489808781893449 4085619730867356586420087)
            ·
              refine ⟨6128429596301034879630131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4085619730867356586420087 6128429596301034879630131)
              ·
                refine ⟨9192644394451552319445197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6128429596301034879630131 9192644394451552319445197)
                ·
                  refine ⟨3447241647919332119791949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9192644394451552319445197 3447241647919332119791949)
                  ·
                    refine ⟨1292715617969749544921981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3447241647919332119791949 1292715617969749544921981)
                    ·
                      rfl

theorem cell22_3776332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 2, 1, 1, 3, 3].length) (baseStart_3776332 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3776332 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3776332 prefixEnd_3776332 := by exact prefixLift 3776332
  have htrace : WordTrace (prefixWord ++ tailWord_3776332) baseStart_3776332 baseEnd_3776332 := by
    simpa [prefixWord, tailWord_3776332, baseEnd_3776332] using wordTrace_append hprefix tailTrace_3776332
  have hstable : (prefixWord ++ tailWord_3776332).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3776332).length < 2 ^ (prefixWord ++ tailWord_3776332).sum := by decide
  have hdescent : baseEnd_3776332 < baseStart_3776332 := by decide
  rcases family_descends (prefixWord ++ tailWord_3776332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3776405 : List Nat := [1, 3, 2, 1, 1, 3, 1, 5, 2, 3]
def baseStart_3776405 : Nat := 118140960795 + 3776405 * 2 ^ 59
def prefixEnd_3776405 : Nat := 4983230072969 + 3 ^ 40 * 3776405 * 2
def baseEnd_3776405 : Nat := 1292740607361601687846757

theorem tailTrace_3776405 : CollatzResearch.WordTrace tailWord_3776405 prefixEnd_3776405 1292740607361601687846757 := by
  unfold tailWord_3776405
  simp only [CollatzResearch.WordTrace]
  refine ⟨137736805883737118471330669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91824537255824745647553779 137736805883737118471330669)
  ·
    refine ⟨51651302206401419426749001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137736805883737118471330669 51651302206401419426749001)
    ·
      refine ⟨38738476654801064570061751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51651302206401419426749001 38738476654801064570061751)
      ·
        refine ⟨58107714982201596855092627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38738476654801064570061751 58107714982201596855092627)
        ·
          refine ⟨87161572473302395282638941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58107714982201596855092627 87161572473302395282638941)
          ·
            refine ⟨32685589677488398230989603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87161572473302395282638941 32685589677488398230989603)
            ·
              refine ⟨49028384516232597346484405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32685589677488398230989603 49028384516232597346484405)
              ·
                refine ⟨4596411048396806001232913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 49028384516232597346484405 4596411048396806001232913)
                ·
                  refine ⟨3447308286297604500924685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4596411048396806001232913 3447308286297604500924685)
                  ·
                    refine ⟨1292740607361601687846757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3447308286297604500924685 1292740607361601687846757)
                    ·
                      rfl

theorem cell22_3776405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 5, 2, 3].length) (baseStart_3776405 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3776405 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3776405 prefixEnd_3776405 := by exact prefixLift 3776405
  have htrace : WordTrace (prefixWord ++ tailWord_3776405) baseStart_3776405 baseEnd_3776405 := by
    simpa [prefixWord, tailWord_3776405, baseEnd_3776405] using wordTrace_append hprefix tailTrace_3776405
  have hstable : (prefixWord ++ tailWord_3776405).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3776405).length < 2 ^ (prefixWord ++ tailWord_3776405).sum := by decide
  have hdescent : baseEnd_3776405 < baseStart_3776405 := by decide
  rcases family_descends (prefixWord ++ tailWord_3776405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3776420 : List Nat := [2, 3, 1, 2, 1, 3, 3, 1, 2, 4]
def baseStart_3776420 : Nat := 118140960795 + 3776420 * 2 ^ 59
def prefixEnd_3776420 : Nat := 4983230072969 + 3 ^ 40 * 3776420 * 2
def baseEnd_3776420 : Nat := 1292745742168146648721711

theorem tailTrace_3776420 : CollatzResearch.WordTrace tailWord_3776420 prefixEnd_3776420 1292745742168146648721711 := by
  unfold tailWord_3776420
  simp only [CollatzResearch.WordTrace]
  refine ⟨68868676489341388016563357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91824901985788517355417809 68868676489341388016563357)
  ·
    refine ⟨25825753683503020506211259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68868676489341388016563357 25825753683503020506211259)
    ·
      refine ⟨38738630525254530759316889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25825753683503020506211259 38738630525254530759316889)
      ·
        refine ⟨29053972893940898069487667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38738630525254530759316889 29053972893940898069487667)
        ·
          refine ⟨43580959340911347104231501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29053972893940898069487667 43580959340911347104231501)
          ·
            refine ⟨16342859752841755164086813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43580959340911347104231501 16342859752841755164086813)
            ·
              refine ⟨6128572407315658186532555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16342859752841755164086813 6128572407315658186532555)
              ·
                refine ⟨9192858610973487279798833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6128572407315658186532555 9192858610973487279798833)
                ·
                  refine ⟨6894643958230115459849125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9192858610973487279798833 6894643958230115459849125)
                  ·
                    refine ⟨1292745742168146648721711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6894643958230115459849125 1292745742168146648721711)
                    ·
                      rfl

theorem cell22_3776420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 3, 1, 2, 4].length) (baseStart_3776420 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3776420 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3776420 prefixEnd_3776420 := by exact prefixLift 3776420
  have htrace : WordTrace (prefixWord ++ tailWord_3776420) baseStart_3776420 baseEnd_3776420 := by
    simpa [prefixWord, tailWord_3776420, baseEnd_3776420] using wordTrace_append hprefix tailTrace_3776420
  have hstable : (prefixWord ++ tailWord_3776420).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3776420).length < 2 ^ (prefixWord ++ tailWord_3776420).sum := by decide
  have hdescent : baseEnd_3776420 < baseStart_3776420 := by decide
  rcases family_descends (prefixWord ++ tailWord_3776420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3776540 : List Nat := [2, 2, 3, 1, 3, 1, 1, 1, 3, 5]
def baseStart_3776540 : Nat := 118140960795 + 3776540 * 2 ^ 59
def prefixEnd_3776540 : Nat := 4983230072969 + 3 ^ 40 * 3776540 * 2
def baseEnd_3776540 : Nat := 1292786820620506335721343

theorem tailTrace_3776540 : CollatzResearch.WordTrace tailWord_3776540 prefixEnd_3776540 1292786820620506335721343 := by
  unfold tailWord_3776540
  simp only [CollatzResearch.WordTrace]
  refine ⟨68870864869124018263747537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91827819825498691018330049 68870864869124018263747537)
  ·
    refine ⟨51653148651843013697810653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68870864869124018263747537 51653148651843013697810653)
    ·
      refine ⟨19369930744441130136678995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51653148651843013697810653 19369930744441130136678995)
      ·
        refine ⟨29054896116661695205018493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19369930744441130136678995 29054896116661695205018493)
        ·
          refine ⟨10895586043748135701881935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29054896116661695205018493 10895586043748135701881935)
          ·
            refine ⟨16343379065622203552822903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10895586043748135701881935 16343379065622203552822903)
            ·
              refine ⟨24515068598433305329234355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16343379065622203552822903 24515068598433305329234355)
              ·
                refine ⟨36772602897649957993851533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24515068598433305329234355 36772602897649957993851533)
                ·
                  refine ⟨13789726086618734247694325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36772602897649957993851533 13789726086618734247694325)
                  ·
                    refine ⟨1292786820620506335721343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13789726086618734247694325 1292786820620506335721343)
                    ·
                      rfl

theorem cell22_3776540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 1, 1, 3, 5].length) (baseStart_3776540 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3776540 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3776540 prefixEnd_3776540 := by exact prefixLift 3776540
  have htrace : WordTrace (prefixWord ++ tailWord_3776540) baseStart_3776540 baseEnd_3776540 := by
    simpa [prefixWord, tailWord_3776540, baseEnd_3776540] using wordTrace_append hprefix tailTrace_3776540
  have hstable : (prefixWord ++ tailWord_3776540).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3776540).length < 2 ^ (prefixWord ++ tailWord_3776540).sum := by decide
  have hdescent : baseEnd_3776540 < baseStart_3776540 := by decide
  rcases family_descends (prefixWord ++ tailWord_3776540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3776574 : List Nat := [4, 2, 1, 3, 2, 1, 2, 1, 1, 5]
def baseStart_3776574 : Nat := 118140960795 + 3776574 * 2 ^ 59
def prefixEnd_3776574 : Nat := 4983230072969 + 3 ^ 40 * 3776574 * 2
def baseEnd_3776574 : Nat := 1292798459515341580371239

theorem tailTrace_3776574 : CollatzResearch.WordTrace tailWord_3776574 prefixEnd_3776574 1292798459515341580371239 := by
  unfold tailWord_3776574
  simp only [CollatzResearch.WordTrace]
  refine ⟨17217871227515607541779097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 91828646546749906889488517 17217871227515607541779097)
  ·
    refine ⟨12913403420636705656334323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17217871227515607541779097 12913403420636705656334323)
    ·
      refine ⟨19370105130955058484501485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12913403420636705656334323 19370105130955058484501485)
      ·
        refine ⟨7263789424108146931688057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19370105130955058484501485 7263789424108146931688057)
        ·
          refine ⟨5447842068081110198766043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7263789424108146931688057 5447842068081110198766043)
          ·
            refine ⟨8171763102121665298149065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5447842068081110198766043 8171763102121665298149065)
            ·
              refine ⟨6128822326591248973611799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8171763102121665298149065 6128822326591248973611799)
              ·
                refine ⟨9193233489886873460417699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6128822326591248973611799 9193233489886873460417699)
                ·
                  refine ⟨13789850234830310190626549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9193233489886873460417699 13789850234830310190626549)
                  ·
                    refine ⟨1292798459515341580371239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13789850234830310190626549 1292798459515341580371239)
                    ·
                      rfl

theorem cell22_3776574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 2, 1, 1, 5].length) (baseStart_3776574 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3776574 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3776574 prefixEnd_3776574 := by exact prefixLift 3776574
  have htrace : WordTrace (prefixWord ++ tailWord_3776574) baseStart_3776574 baseEnd_3776574 := by
    simpa [prefixWord, tailWord_3776574, baseEnd_3776574] using wordTrace_append hprefix tailTrace_3776574
  have hstable : (prefixWord ++ tailWord_3776574).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3776574).length < 2 ^ (prefixWord ++ tailWord_3776574).sum := by decide
  have hdescent : baseEnd_3776574 < baseStart_3776574 := by decide
  rcases family_descends (prefixWord ++ tailWord_3776574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3776615 : List Nat := [1, 1, 5, 1, 1, 2, 3, 1, 7]
def baseStart_3776615 : Nat := 118140960795 + 3776615 * 2 ^ 59
def prefixEnd_3776615 : Nat := 4983230072969 + 3 ^ 40 * 3776615 * 2
def baseEnd_3776615 : Nat := 430937498217743713365371

theorem tailTrace_3776615 : CollatzResearch.WordTrace tailWord_3776615 prefixEnd_3776615 430937498217743713365371 := by
  unfold tailWord_3776615
  simp only [CollatzResearch.WordTrace]
  refine ⟨137744465212976324336475299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91829643475317549557650199 137744465212976324336475299)
  ·
    refine ⟨206616697819464486504712949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137744465212976324336475299 206616697819464486504712949)
    ·
      refine ⟨19370315420574795609816839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 206616697819464486504712949 19370315420574795609816839)
      ·
        refine ⟨29055473130862193414725259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19370315420574795609816839 29055473130862193414725259)
        ·
          refine ⟨43583209696293290122087889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29055473130862193414725259 43583209696293290122087889)
          ·
            refine ⟨32687407272219967591565917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43583209696293290122087889 32687407272219967591565917)
            ·
              refine ⟨12257777727082487846837219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32687407272219967591565917 12257777727082487846837219)
              ·
                refine ⟨18386666590623731770255829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12257777727082487846837219 18386666590623731770255829)
                ·
                  refine ⟨430937498217743713365371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18386666590623731770255829 430937498217743713365371)
                  ·
                    rfl

theorem cell22_3776615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 3, 1, 7].length) (baseStart_3776615 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3776615 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3776615 prefixEnd_3776615 := by exact prefixLift 3776615
  have htrace : WordTrace (prefixWord ++ tailWord_3776615) baseStart_3776615 baseEnd_3776615 := by
    simpa [prefixWord, tailWord_3776615, baseEnd_3776615] using wordTrace_append hprefix tailTrace_3776615
  have hstable : (prefixWord ++ tailWord_3776615).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3776615).length < 2 ^ (prefixWord ++ tailWord_3776615).sum := by decide
  have hdescent : baseEnd_3776615 < baseStart_3776615 := by decide
  rcases family_descends (prefixWord ++ tailWord_3776615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3776670 : List Nat := [4, 3, 1, 1, 3, 1, 3, 2, 1, 3]
def baseStart_3776670 : Nat := 118140960795 + 3776670 * 2 ^ 59
def prefixEnd_3776670 : Nat := 4983230072969 + 3 ^ 40 * 3776670 * 2
def baseEnd_3776670 : Nat := 1292831322277229329970945

theorem tailTrace_3776670 : CollatzResearch.WordTrace tailWord_3776670 prefixEnd_3776670 1292831322277229329970945 := by
  unfold tailWord_3776670
  simp only [CollatzResearch.WordTrace]
  refine ⟨17218308903472133591215933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 91830980818518045819818309 17218308903472133591215933)
  ·
    refine ⟨6456865838802050096705975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17218308903472133591215933 6456865838802050096705975)
    ·
      refine ⟨9685298758203075145058963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6456865838802050096705975 9685298758203075145058963)
      ·
        refine ⟨14527948137304612717588445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9685298758203075145058963 14527948137304612717588445)
        ·
          refine ⟨5447980551489229769095667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14527948137304612717588445 5447980551489229769095667)
          ·
            refine ⟨8171970827233844653643501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5447980551489229769095667 8171970827233844653643501)
            ·
              refine ⟨3064489060212691745116313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8171970827233844653643501 3064489060212691745116313)
              ·
                refine ⟨2298366795159518808837235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3064489060212691745116313 2298366795159518808837235)
                ·
                  refine ⟨3447550192739278213255853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2298366795159518808837235 3447550192739278213255853)
                  ·
                    refine ⟨1292831322277229329970945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3447550192739278213255853 1292831322277229329970945)
                    ·
                      rfl

theorem cell22_3776670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 3, 2, 1, 3].length) (baseStart_3776670 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3776670 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3776670 prefixEnd_3776670 := by exact prefixLift 3776670
  have htrace : WordTrace (prefixWord ++ tailWord_3776670) baseStart_3776670 baseEnd_3776670 := by
    simpa [prefixWord, tailWord_3776670, baseEnd_3776670] using wordTrace_append hprefix tailTrace_3776670
  have hstable : (prefixWord ++ tailWord_3776670).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3776670).length < 2 ^ (prefixWord ++ tailWord_3776670).sum := by decide
  have hdescent : baseEnd_3776670 < baseStart_3776670 := by decide
  rcases family_descends (prefixWord ++ tailWord_3776670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3776754 : List Nat := [3, 2, 1, 3, 2, 1, 1, 1, 5, 3]
def baseStart_3776754 : Nat := 118140960795 + 3776754 * 2 ^ 59
def prefixEnd_3776754 : Nat := 4983230072969 + 3 ^ 40 * 3776754 * 2
def baseEnd_3776754 : Nat := 1292860077193881110870687

theorem tailTrace_3776754 : CollatzResearch.WordTrace tailWord_3776754 prefixEnd_3776754 1292860077193881110870687 := by
  unfold tailWord_3776754
  simp only [CollatzResearch.WordTrace]
  refine ⟨34437383739868187768946329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91833023306315167383856877 34437383739868187768946329)
  ·
    refine ⟨25828037804901140826709747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34437383739868187768946329 25828037804901140826709747)
    ·
      refine ⟨38742056707351711240064621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25828037804901140826709747 38742056707351711240064621)
      ·
        refine ⟨14528271265256891715024233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38742056707351711240064621 14528271265256891715024233)
        ·
          refine ⟨10896203448942668786268175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14528271265256891715024233 10896203448942668786268175)
          ·
            refine ⟨16344305173414003179402263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10896203448942668786268175 16344305173414003179402263)
            ·
              refine ⟨24516457760121004769103395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16344305173414003179402263 24516457760121004769103395)
              ·
                refine ⟨36774686640181507153655093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24516457760121004769103395 36774686640181507153655093)
                ·
                  refine ⟨3447626872517016295655165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 36774686640181507153655093 3447626872517016295655165)
                  ·
                    refine ⟨1292860077193881110870687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3447626872517016295655165 1292860077193881110870687)
                    ·
                      rfl

theorem cell22_3776754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 1, 1, 5, 3].length) (baseStart_3776754 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3776754 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3776754 prefixEnd_3776754 := by exact prefixLift 3776754
  have htrace : WordTrace (prefixWord ++ tailWord_3776754) baseStart_3776754 baseEnd_3776754 := by
    simpa [prefixWord, tailWord_3776754, baseEnd_3776754] using wordTrace_append hprefix tailTrace_3776754
  have hstable : (prefixWord ++ tailWord_3776754).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3776754).length < 2 ^ (prefixWord ++ tailWord_3776754).sum := by decide
  have hdescent : baseEnd_3776754 < baseStart_3776754 := by decide
  rcases family_descends (prefixWord ++ tailWord_3776754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3776771 : List Nat := [1, 1, 1, 3, 2, 3, 4, 3, 1, 3]
def baseStart_3776771 : Nat := 118140960795 + 3776771 * 2 ^ 59
def prefixEnd_3776771 : Nat := 4983230072969 + 3 ^ 40 * 3776771 * 2
def baseEnd_3776771 : Nat := 1292865896641298733195635

theorem tailTrace_3776771 : CollatzResearch.WordTrace tailWord_3776771 prefixEnd_3776771 1292865896641298733195635 := by
  unfold tailWord_3776771
  simp only [CollatzResearch.WordTrace]
  refine ⟨137750155000411162979154167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91833436666940775319436111 137750155000411162979154167)
  ·
    refine ⟨206625232500616744468731251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137750155000411162979154167 206625232500616744468731251)
    ·
      refine ⟨309937848750925116703096877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206625232500616744468731251 309937848750925116703096877)
      ·
        refine ⟨116226693281596918763661329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 309937848750925116703096877 116226693281596918763661329)
        ·
          refine ⟨87170019961197689072745997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116226693281596918763661329 87170019961197689072745997)
          ·
            refine ⟨32688757485449133402279749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87170019961197689072745997 32688757485449133402279749)
            ·
              refine ⟨6129142028521712512927453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32688757485449133402279749 6129142028521712512927453)
              ·
                refine ⟨2298428260695642192347795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6129142028521712512927453 2298428260695642192347795)
                ·
                  refine ⟨3447642391043463288521693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2298428260695642192347795 3447642391043463288521693)
                  ·
                    refine ⟨1292865896641298733195635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3447642391043463288521693 1292865896641298733195635)
                    ·
                      rfl

theorem cell22_3776771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 4, 3, 1, 3].length) (baseStart_3776771 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3776771 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3776771 prefixEnd_3776771 := by exact prefixLift 3776771
  have htrace : WordTrace (prefixWord ++ tailWord_3776771) baseStart_3776771 baseEnd_3776771 := by
    simpa [prefixWord, tailWord_3776771, baseEnd_3776771] using wordTrace_append hprefix tailTrace_3776771
  have hstable : (prefixWord ++ tailWord_3776771).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3776771).length < 2 ^ (prefixWord ++ tailWord_3776771).sum := by decide
  have hdescent : baseEnd_3776771 < baseStart_3776771 := by decide
  rcases family_descends (prefixWord ++ tailWord_3776771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3776782 : List Nat := [4, 1, 1, 2, 1, 2, 1, 1, 4, 5]
def baseStart_3776782 : Nat := 118140960795 + 3776782 * 2 ^ 59
def prefixEnd_3776782 : Nat := 4983230072969 + 3 ^ 40 * 3776782 * 2
def baseEnd_3776782 : Nat := 1292869662166098371170601

theorem tailTrace_3776782 : CollatzResearch.WordTrace tailWord_3776782 prefixEnd_3776782 1292869662166098371170601 := by
  unfold tailWord_3776782
  simp only [CollatzResearch.WordTrace]
  refine ⟨17218819525421413982225575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 91833704135580874571869733 17218819525421413982225575)
  ·
    refine ⟨25828229288132120973338363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17218819525421413982225575 25828229288132120973338363)
    ·
      refine ⟨38742343932198181460007545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25828229288132120973338363 38742343932198181460007545)
      ·
        refine ⟨29056757949148636095005659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38742343932198181460007545 29056757949148636095005659)
        ·
          refine ⟨43585136923722954142508489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29056757949148636095005659 43585136923722954142508489)
          ·
            refine ⟨32688852692792215606881367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43585136923722954142508489 32688852692792215606881367)
            ·
              refine ⟨49033279039188323410322051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32688852692792215606881367 49033279039188323410322051)
              ·
                refine ⟨73549918558782485115483077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49033279039188323410322051 73549918558782485115483077)
                ·
                  refine ⟨13790609729771715959153077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 73549918558782485115483077 13790609729771715959153077)
                  ·
                    refine ⟨1292869662166098371170601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13790609729771715959153077 1292869662166098371170601)
                    ·
                      rfl

theorem cell22_3776782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 1, 4, 5].length) (baseStart_3776782 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3776782 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3776782 prefixEnd_3776782 := by exact prefixLift 3776782
  have htrace : WordTrace (prefixWord ++ tailWord_3776782) baseStart_3776782 baseEnd_3776782 := by
    simpa [prefixWord, tailWord_3776782, baseEnd_3776782] using wordTrace_append hprefix tailTrace_3776782
  have hstable : (prefixWord ++ tailWord_3776782).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3776782).length < 2 ^ (prefixWord ++ tailWord_3776782).sum := by decide
  have hdescent : baseEnd_3776782 < baseStart_3776782 := by decide
  rcases family_descends (prefixWord ++ tailWord_3776782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3776812 : List Nat := [2, 2, 1, 1, 1, 3, 4, 2, 6]
def baseStart_3776812 : Nat := 118140960795 + 3776812 * 2 ^ 59
def prefixEnd_3776812 : Nat := 4983230072969 + 3 ^ 40 * 3776812 * 2
def baseEnd_3776812 : Nat := 430959977259729430973503

theorem tailTrace_3776812 : CollatzResearch.WordTrace tailWord_3776812 prefixEnd_3776812 430959977259729430973503 := by
  unfold tailWord_3776812
  simp only [CollatzResearch.WordTrace]
  refine ⟨68875825196631313490698345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91834433595508417987597793 68875825196631313490698345)
  ·
    refine ⟨51656868897473485118023759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68875825196631313490698345 51656868897473485118023759)
    ·
      refine ⟨77485303346210227677035639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51656868897473485118023759 77485303346210227677035639)
      ·
        refine ⟨116227955019315341515553459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77485303346210227677035639 116227955019315341515553459)
        ·
          refine ⟨174341932528973012273330189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116227955019315341515553459 174341932528973012273330189)
          ·
            refine ⟨65378224698364879602498821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 174341932528973012273330189 65378224698364879602498821)
            ·
              refine ⟨12258417130943414925468529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 65378224698364879602498821 12258417130943414925468529)
              ·
                refine ⟨9193812848207561194101397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12258417130943414925468529 9193812848207561194101397)
                ·
                  refine ⟨430959977259729430973503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9193812848207561194101397 430959977259729430973503)
                  ·
                    rfl

theorem cell22_3776812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 6].length) (baseStart_3776812 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3776812 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3776812 prefixEnd_3776812 := by exact prefixLift 3776812
  have htrace : WordTrace (prefixWord ++ tailWord_3776812) baseStart_3776812 baseEnd_3776812 := by
    simpa [prefixWord, tailWord_3776812, baseEnd_3776812] using wordTrace_append hprefix tailTrace_3776812
  have hstable : (prefixWord ++ tailWord_3776812).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3776812).length < 2 ^ (prefixWord ++ tailWord_3776812).sum := by decide
  have hdescent : baseEnd_3776812 < baseStart_3776812 := by decide
  rcases family_descends (prefixWord ++ tailWord_3776812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3776844 : List Nat := [2, 2, 1, 3, 2, 1, 1, 3, 4, 3]
def baseStart_3776844 : Nat := 118140960795 + 3776844 * 2 ^ 59
def prefixEnd_3776844 : Nat := 4983230072969 + 3 ^ 40 * 3776844 * 2
def baseEnd_3776844 : Nat := 1292890886033150876120411

theorem tailTrace_3776844 : CollatzResearch.WordTrace tailWord_3776844 prefixEnd_3776844 1292890886033150876120411 := by
  unfold tailWord_3776844
  simp only [CollatzResearch.WordTrace]
  refine ⟨68876408764573348223280793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91835211686097797631041057 68876408764573348223280793)
  ·
    refine ⟨51657306573430011167460595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68876408764573348223280793 51657306573430011167460595)
    ·
      refine ⟨77485959860145016751190893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51657306573430011167460595 77485959860145016751190893)
      ·
        refine ⟨29057234947554381281696585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77485959860145016751190893 29057234947554381281696585)
        ·
          refine ⟨21792926210665785961272439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29057234947554381281696585 21792926210665785961272439)
          ·
            refine ⟨32689389315998678941908659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21792926210665785961272439 32689389315998678941908659)
            ·
              refine ⟨49034083973998018412862989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32689389315998678941908659 49034083973998018412862989)
              ·
                refine ⟨18387781490249256904823621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49034083973998018412862989 18387781490249256904823621)
                ·
                  refine ⟨3447709029421735669654429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18387781490249256904823621 3447709029421735669654429)
                  ·
                    refine ⟨1292890886033150876120411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3447709029421735669654429 1292890886033150876120411)
                    ·
                      rfl

theorem cell22_3776844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 3, 4, 3].length) (baseStart_3776844 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3776844 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3776844 prefixEnd_3776844 := by exact prefixLift 3776844
  have htrace : WordTrace (prefixWord ++ tailWord_3776844) baseStart_3776844 baseEnd_3776844 := by
    simpa [prefixWord, tailWord_3776844, baseEnd_3776844] using wordTrace_append hprefix tailTrace_3776844
  have hstable : (prefixWord ++ tailWord_3776844).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3776844).length < 2 ^ (prefixWord ++ tailWord_3776844).sum := by decide
  have hdescent : baseEnd_3776844 < baseStart_3776844 := by decide
  rcases family_descends (prefixWord ++ tailWord_3776844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3776874 : List Nat := [3, 1, 3, 3, 1, 1, 2, 8]
def baseStart_3776874 : Nat := 118140960795 + 3776874 * 2 ^ 59
def prefixEnd_3776874 : Nat := 4983230072969 + 3 ^ 40 * 3776874 * 2
def baseEnd_3776874 : Nat := 143655683960693421985591

theorem tailTrace_3776874 : CollatzResearch.WordTrace tailWord_3776874 prefixEnd_3776874 143655683960693421985591 := by
  unfold tailWord_3776874
  simp only [CollatzResearch.WordTrace]
  refine ⟨34438477929759502892538419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91835941146025341046769117 34438477929759502892538419)
  ·
    refine ⟨51657716894639254338807629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34438477929759502892538419 51657716894639254338807629)
    ·
      refine ⟨19371643835489720377052861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51657716894639254338807629 19371643835489720377052861)
      ·
        refine ⟨7264366438308645141394823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19371643835489720377052861 7264366438308645141394823)
        ·
          refine ⟨10896549657462967712092235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7264366438308645141394823 10896549657462967712092235)
          ·
            refine ⟨16344824486194451568138353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10896549657462967712092235 16344824486194451568138353)
            ·
              refine ⟨12258618364645838676103765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16344824486194451568138353 12258618364645838676103765)
              ·
                refine ⟨143655683960693421985591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12258618364645838676103765 143655683960693421985591)
                ·
                  rfl

theorem cell22_3776874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 2, 8].length) (baseStart_3776874 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3776874 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3776874 prefixEnd_3776874 := by exact prefixLift 3776874
  have htrace : WordTrace (prefixWord ++ tailWord_3776874) baseStart_3776874 baseEnd_3776874 := by
    simpa [prefixWord, tailWord_3776874, baseEnd_3776874] using wordTrace_append hprefix tailTrace_3776874
  have hstable : (prefixWord ++ tailWord_3776874).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3776874).length < 2 ^ (prefixWord ++ tailWord_3776874).sum := by decide
  have hdescent : baseEnd_3776874 < baseStart_3776874 := by decide
  rcases family_descends (prefixWord ++ tailWord_3776874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3776876 : List Nat := [2, 2, 1, 1, 6, 1, 2, 1, 2, 4]
def baseStart_3776876 : Nat := 118140960795 + 3776876 * 2 ^ 59
def prefixEnd_3776876 : Nat := 4983230072969 + 3 ^ 40 * 3776876 * 2
def baseEnd_3776876 : Nat := 1292901840287113459320313

theorem tailTrace_3776876 : CollatzResearch.WordTrace tailWord_3776876 prefixEnd_3776876 1292901840287113459320313 := by
  unfold tailWord_3776876
  simp only [CollatzResearch.WordTrace]
  refine ⟨68876992332515382955863241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91835989776687177274484321 68876992332515382955863241)
  ·
    refine ⟨51657744249386537216897431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68876992332515382955863241 51657744249386537216897431)
    ·
      refine ⟨77486616374079805825346147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51657744249386537216897431 77486616374079805825346147)
      ·
        refine ⟨116229924561119708738019221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77486616374079805825346147 116229924561119708738019221)
        ·
          refine ⟨5448277713802486347094651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 116229924561119708738019221 5448277713802486347094651)
          ·
            refine ⟨8172416570703729520641977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5448277713802486347094651 8172416570703729520641977)
            ·
              refine ⟨6129312428027797140481483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8172416570703729520641977 6129312428027797140481483)
              ·
                refine ⟨9193968642041695710722225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6129312428027797140481483 9193968642041695710722225)
                ·
                  refine ⟨6895476481531271783041669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9193968642041695710722225 6895476481531271783041669)
                  ·
                    refine ⟨1292901840287113459320313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6895476481531271783041669 1292901840287113459320313)
                    ·
                      rfl

theorem cell22_3776876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 4].length) (baseStart_3776876 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3776876 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3776876 prefixEnd_3776876 := by exact prefixLift 3776876
  have htrace : WordTrace (prefixWord ++ tailWord_3776876) baseStart_3776876 baseEnd_3776876 := by
    simpa [prefixWord, tailWord_3776876, baseEnd_3776876] using wordTrace_append hprefix tailTrace_3776876
  have hstable : (prefixWord ++ tailWord_3776876).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3776876).length < 2 ^ (prefixWord ++ tailWord_3776876).sum := by decide
  have hdescent : baseEnd_3776876 < baseStart_3776876 := by decide
  rcases family_descends (prefixWord ++ tailWord_3776876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3776919 : List Nat := [1, 1, 3, 3, 1, 1, 4, 3, 5]
def baseStart_3776919 : Nat := 118140960795 + 3776919 * 2 ^ 59
def prefixEnd_3776919 : Nat := 4983230072969 + 3 ^ 40 * 3776919 * 2
def baseEnd_3776919 : Nat := 430972186688625226831727

theorem tailTrace_3776919 : CollatzResearch.WordTrace tailWord_3776919 prefixEnd_3776919 430972186688625226831727 := by
  unfold tailWord_3776919
  simp only [CollatzResearch.WordTrace]
  refine ⟨137755553003874984255541811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91837035335916656170361207 137755553003874984255541811)
  ·
    refine ⟨206633329505812476383312717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137755553003874984255541811 206633329505812476383312717)
    ·
      refine ⟨77487498564679678643742269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 206633329505812476383312717 77487498564679678643742269)
      ·
        refine ⟨29057811961754879491403351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77487498564679678643742269 29057811961754879491403351)
        ·
          refine ⟨43586717942632319237105027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29057811961754879491403351 43586717942632319237105027)
          ·
            refine ⟨65380076913948478855657541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43586717942632319237105027 65380076913948478855657541)
            ·
              refine ⟨12258764421365339785435789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 65380076913948478855657541 12258764421365339785435789)
              ·
                refine ⟨4597036658012002419538421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12258764421365339785435789 4597036658012002419538421)
                ·
                  refine ⟨430972186688625226831727, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4597036658012002419538421 430972186688625226831727)
                  ·
                    rfl

theorem cell22_3776919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 4, 3, 5].length) (baseStart_3776919 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3776919 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3776919 prefixEnd_3776919 := by exact prefixLift 3776919
  have htrace : WordTrace (prefixWord ++ tailWord_3776919) baseStart_3776919 baseEnd_3776919 := by
    simpa [prefixWord, tailWord_3776919, baseEnd_3776919] using wordTrace_append hprefix tailTrace_3776919
  have hstable : (prefixWord ++ tailWord_3776919).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3776919).length < 2 ^ (prefixWord ++ tailWord_3776919).sum := by decide
  have hdescent : baseEnd_3776919 < baseStart_3776919 := by decide
  rcases family_descends (prefixWord ++ tailWord_3776919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3777099 : List Nat := [1, 1, 1, 1, 3, 1, 5, 1, 8]
def baseStart_3777099 : Nat := 118140960795 + 3777099 * 2 ^ 59
def prefixEnd_3777099 : Nat := 4983230072969 + 3 ^ 40 * 3777099 * 2
def baseEnd_3777099 : Nat := 430992725914805070331543

theorem tailTrace_3777099 : CollatzResearch.WordTrace tailWord_3777099 prefixEnd_3777099 430992725914805070331543 := by
  unfold tailWord_3777099
  simp only [CollatzResearch.WordTrace]
  refine ⟨137762118143222874997094351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91841412095481916664729567 137762118143222874997094351)
  ·
    refine ⟨206643177214834312495641527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137762118143222874997094351 206643177214834312495641527)
    ·
      refine ⟨309964765822251468743462291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206643177214834312495641527 309964765822251468743462291)
      ·
        refine ⟨464947148733377203115193437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 309964765822251468743462291 464947148733377203115193437)
        ·
          refine ⟨174355180775016451168197539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 464947148733377203115193437 174355180775016451168197539)
          ·
            refine ⟨261532771162524676752296309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 174355180775016451168197539 261532771162524676752296309)
            ·
              refine ⟨24518697296486688445527779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 261532771162524676752296309 24518697296486688445527779)
              ·
                refine ⟨36778045944730032668291669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24518697296486688445527779 36778045944730032668291669)
                ·
                  refine ⟨430992725914805070331543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 36778045944730032668291669 430992725914805070331543)
                  ·
                    rfl

theorem cell22_3777099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 5, 1, 8].length) (baseStart_3777099 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3777099 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3777099 prefixEnd_3777099 := by exact prefixLift 3777099
  have htrace : WordTrace (prefixWord ++ tailWord_3777099) baseStart_3777099 baseEnd_3777099 := by
    simpa [prefixWord, tailWord_3777099, baseEnd_3777099] using wordTrace_append hprefix tailTrace_3777099
  have hstable : (prefixWord ++ tailWord_3777099).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3777099).length < 2 ^ (prefixWord ++ tailWord_3777099).sum := by decide
  have hdescent : baseEnd_3777099 < baseStart_3777099 := by decide
  rcases family_descends (prefixWord ++ tailWord_3777099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3777122 : List Nat := [3, 3, 2, 3, 1, 2, 1, 2, 5]
def baseStart_3777122 : Nat := 118140960795 + 3777122 * 2 ^ 59
def prefixEnd_3777122 : Nat := 4983230072969 + 3 ^ 40 * 3777122 * 2
def baseEnd_3777122 : Nat := 430995350371483605889853

theorem tailTrace_3777122 : CollatzResearch.WordTrace tailWord_3777122 prefixEnd_3777122 430995350371483605889853 := by
  unfold tailWord_3777122
  simp only [CollatzResearch.WordTrace]
  refine ⟨34440739255534887481295405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91841971348093033283454413 34440739255534887481295405)
  ·
    refine ⟨12915277220825582805485777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34440739255534887481295405 12915277220825582805485777)
    ·
      refine ⟨9686457915619187104114333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12915277220825582805485777 9686457915619187104114333)
      ·
        refine ⟨3632421718357195164042875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9686457915619187104114333 3632421718357195164042875)
        ·
          refine ⟨5448632577535792746064313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3632421718357195164042875 5448632577535792746064313)
          ·
            refine ⟨4086474433151844559548235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5448632577535792746064313 4086474433151844559548235)
            ·
              refine ⟨6129711649727766839322353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4086474433151844559548235 6129711649727766839322353)
              ·
                refine ⟨4597283737295825129491765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6129711649727766839322353 4597283737295825129491765)
                ·
                  refine ⟨430995350371483605889853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4597283737295825129491765 430995350371483605889853)
                  ·
                    rfl

theorem cell22_3777122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 2, 1, 2, 5].length) (baseStart_3777122 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3777122 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3777122 prefixEnd_3777122 := by exact prefixLift 3777122
  have htrace : WordTrace (prefixWord ++ tailWord_3777122) baseStart_3777122 baseEnd_3777122 := by
    simpa [prefixWord, tailWord_3777122, baseEnd_3777122] using wordTrace_append hprefix tailTrace_3777122
  have hstable : (prefixWord ++ tailWord_3777122).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3777122).length < 2 ^ (prefixWord ++ tailWord_3777122).sum := by decide
  have hdescent : baseEnd_3777122 < baseStart_3777122 := by decide
  rcases family_descends (prefixWord ++ tailWord_3777122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3777133 : List Nat := [1, 5, 1, 1, 3, 2, 2, 1, 6]
def baseStart_3777133 : Nat := 118140960795 + 3777133 * 2 ^ 59
def prefixEnd_3777133 : Nat := 4983230072969 + 3 ^ 40 * 3777133 * 2
def baseEnd_3777133 : Nat := 430996605546416818548175

theorem tailTrace_3777133 : CollatzResearch.WordTrace tailWord_3777133 prefixEnd_3777133 430996605546416818548175 := by
  unfold tailWord_3777133
  simp only [CollatzResearch.WordTrace]
  refine ⟨137763358225099698803832053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91842238816733132535888035 137763358225099698803832053)
  ·
    refine ⟨12915314833603096762859255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 137763358225099698803832053 12915314833603096762859255)
    ·
      refine ⟨19372972250404645144288883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12915314833603096762859255 19372972250404645144288883)
      ·
        refine ⟨29059458375606967716433325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19372972250404645144288883 29059458375606967716433325)
        ·
          refine ⟨10897296890852612893662497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29059458375606967716433325 10897296890852612893662497)
          ·
            refine ⟨8172972668139459670246873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10897296890852612893662497 8172972668139459670246873)
            ·
              refine ⟨6129729501104594752685155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8172972668139459670246873 6129729501104594752685155)
              ·
                refine ⟨9194594251656892129027733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6129729501104594752685155 9194594251656892129027733)
                ·
                  refine ⟨430996605546416818548175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9194594251656892129027733 430996605546416818548175)
                  ·
                    rfl

theorem cell22_3777133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 2, 1, 6].length) (baseStart_3777133 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3777133 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3777133 prefixEnd_3777133 := by exact prefixLift 3777133
  have htrace : WordTrace (prefixWord ++ tailWord_3777133) baseStart_3777133 baseEnd_3777133 := by
    simpa [prefixWord, tailWord_3777133, baseEnd_3777133] using wordTrace_append hprefix tailTrace_3777133
  have hstable : (prefixWord ++ tailWord_3777133).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3777133).length < 2 ^ (prefixWord ++ tailWord_3777133).sum := by decide
  have hdescent : baseEnd_3777133 < baseStart_3777133 := by decide
  rcases family_descends (prefixWord ++ tailWord_3777133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3777148 : List Nat := [2, 2, 2, 1, 1, 2, 2, 5, 2, 3]
def baseStart_3777148 : Nat := 118140960795 + 3777148 * 2 ^ 59
def prefixEnd_3777148 : Nat := 4983230072969 + 3 ^ 40 * 3777148 * 2
def baseEnd_3777148 : Nat := 1292994951445795416519479

theorem tailTrace_3777148 : CollatzResearch.WordTrace tailWord_3777148 prefixEnd_3777148 1292994951445795416519479 := by
  unfold tailWord_3777148
  simp only [CollatzResearch.WordTrace]
  refine ⟨68881952660022678182814049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91842603546696904243752065 68881952660022678182814049)
  ·
    refine ⟨51661464495017008637110537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68881952660022678182814049 51661464495017008637110537)
    ·
      refine ⟨38746098371262756477832903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51661464495017008637110537 38746098371262756477832903)
      ·
        refine ⟨58119147556894134716749355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38746098371262756477832903 58119147556894134716749355)
        ·
          refine ⟨87178721335341202075124033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58119147556894134716749355 87178721335341202075124033)
          ·
            refine ⟨65384041001505901556343025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87178721335341202075124033 65384041001505901556343025)
            ·
              refine ⟨49038030751129426167257269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65384041001505901556343025 49038030751129426167257269)
              ·
                refine ⟨4597315382918383703180369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 49038030751129426167257269 4597315382918383703180369)
                ·
                  refine ⟨3447986537188787777385277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4597315382918383703180369 3447986537188787777385277)
                  ·
                    refine ⟨1292994951445795416519479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3447986537188787777385277 1292994951445795416519479)
                    ·
                      rfl

theorem cell22_3777148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 5, 2, 3].length) (baseStart_3777148 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3777148 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3777148 prefixEnd_3777148 := by exact prefixLift 3777148
  have htrace : WordTrace (prefixWord ++ tailWord_3777148) baseStart_3777148 baseEnd_3777148 := by
    simpa [prefixWord, tailWord_3777148, baseEnd_3777148] using wordTrace_append hprefix tailTrace_3777148
  have hstable : (prefixWord ++ tailWord_3777148).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3777148).length < 2 ^ (prefixWord ++ tailWord_3777148).sum := by decide
  have hdescent : baseEnd_3777148 < baseStart_3777148 := by decide
  rcases family_descends (prefixWord ++ tailWord_3777148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3777244 : List Nat := [2, 2, 5, 1, 1, 2, 1, 4, 1, 3]
def baseStart_3777244 : Nat := 118140960795 + 3777244 * 2 ^ 59
def prefixEnd_3777244 : Nat := 4983230072969 + 3 ^ 40 * 3777244 * 2
def baseEnd_3777244 : Nat := 1293027814207683166119185

theorem tailTrace_3777244 : CollatzResearch.WordTrace tailWord_3777244 prefixEnd_3777244 1293027814207683166119185 := by
  unfold tailWord_3777244
  simp only [CollatzResearch.WordTrace]
  refine ⟨68883703363848782380561393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91844937818465043174081857 68883703363848782380561393)
  ·
    refine ⟨51662777522886586785421045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68883703363848782380561393 51662777522886586785421045)
    ·
      refine ⟨4843385392770617511133223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 51662777522886586785421045 4843385392770617511133223)
      ·
        refine ⟨7265078089155926266699835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4843385392770617511133223 7265078089155926266699835)
        ·
          refine ⟨10897617133733889400049753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7265078089155926266699835 10897617133733889400049753)
          ·
            refine ⟨8173212850300417050037315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10897617133733889400049753 8173212850300417050037315)
            ·
              refine ⟨12259819275450625575055973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8173212850300417050037315 12259819275450625575055973)
              ·
                refine ⟨2298716114146992295322995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12259819275450625575055973 2298716114146992295322995)
                ·
                  refine ⟨3448074171220488442984493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2298716114146992295322995 3448074171220488442984493)
                  ·
                    refine ⟨1293027814207683166119185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3448074171220488442984493 1293027814207683166119185)
                    ·
                      rfl

theorem cell22_3777244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 1, 4, 1, 3].length) (baseStart_3777244 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3777244 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3777244 prefixEnd_3777244 := by exact prefixLift 3777244
  have htrace : WordTrace (prefixWord ++ tailWord_3777244) baseStart_3777244 baseEnd_3777244 := by
    simpa [prefixWord, tailWord_3777244, baseEnd_3777244] using wordTrace_append hprefix tailTrace_3777244
  have hstable : (prefixWord ++ tailWord_3777244).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3777244).length < 2 ^ (prefixWord ++ tailWord_3777244).sum := by decide
  have hdescent : baseEnd_3777244 < baseStart_3777244 := by decide
  rcases family_descends (prefixWord ++ tailWord_3777244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3777253 : List Nat := [1, 3, 1, 4, 1, 2, 1, 2, 3, 4]
def baseStart_3777253 : Nat := 118140960795 + 3777253 * 2 ^ 59
def prefixEnd_3777253 : Nat := 4983230072969 + 3 ^ 40 * 3777253 * 2
def baseEnd_3777253 : Nat := 1293030895091610142644157

theorem tailTrace_3777253 : CollatzResearch.WordTrace tailWord_3777253 prefixEnd_3777253 1293030895091610142644157 := by
  unfold tailWord_3777253
  simp only [CollatzResearch.WordTrace]
  refine ⟨137767734984664959298200413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91845156656443306198800275 137767734984664959298200413)
  ·
    refine ⟨51662900619249359736825155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137767734984664959298200413 51662900619249359736825155)
    ·
      refine ⟨77494350928874039605237733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51662900619249359736825155 77494350928874039605237733)
      ·
        refine ⟨14530190799163882425982075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 77494350928874039605237733 14530190799163882425982075)
        ·
          refine ⟨21795286198745823638973113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14530190799163882425982075 21795286198745823638973113)
          ·
            refine ⟨16346464649059367729229835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21795286198745823638973113 16346464649059367729229835)
            ·
              refine ⟨24519696973589051593844753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16346464649059367729229835 24519696973589051593844753)
              ·
                refine ⟨18389772730191788695383565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24519696973589051593844753 18389772730191788695383565)
                ·
                  refine ⟨6896164773821920760768837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18389772730191788695383565 6896164773821920760768837)
                  ·
                    refine ⟨1293030895091610142644157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6896164773821920760768837 1293030895091610142644157)
                    ·
                      rfl

theorem cell22_3777253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 1, 2, 3, 4].length) (baseStart_3777253 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3777253 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3777253 prefixEnd_3777253 := by exact prefixLift 3777253
  have htrace : WordTrace (prefixWord ++ tailWord_3777253) baseStart_3777253 baseEnd_3777253 := by
    simpa [prefixWord, tailWord_3777253, baseEnd_3777253] using wordTrace_append hprefix tailTrace_3777253
  have hstable : (prefixWord ++ tailWord_3777253).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3777253).length < 2 ^ (prefixWord ++ tailWord_3777253).sum := by decide
  have hdescent : baseEnd_3777253 < baseStart_3777253 := by decide
  rcases family_descends (prefixWord ++ tailWord_3777253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3777270 : List Nat := [5, 1, 1, 1, 1, 2, 2, 4, 1, 4]
def baseStart_3777270 : Nat := 118140960795 + 3777270 * 2 ^ 59
def prefixEnd_3777270 : Nat := 4983230072969 + 3 ^ 40 * 3777270 * 2
def baseEnd_3777270 : Nat := 1293036714539027764969105

theorem tailTrace_3777270 : CollatzResearch.WordTrace tailWord_3777270 prefixEnd_3777270 1293036714539027764969105 := by
  unfold tailWord_3777270
  simp only [CollatzResearch.WordTrace]
  refine ⟨8610522189100210700098079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 91845570017068914134379509 8610522189100210700098079)
  ·
    refine ⟨12915783283650316050147119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8610522189100210700098079 12915783283650316050147119)
    ·
      refine ⟨19373674925475474075220679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12915783283650316050147119 19373674925475474075220679)
      ·
        refine ⟨29060512388213211112831019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19373674925475474075220679 29060512388213211112831019)
        ·
          refine ⟨43590768582319816669246529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29060512388213211112831019 43590768582319816669246529)
          ·
            refine ⟨32693076436739862501934897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43590768582319816669246529 32693076436739862501934897)
            ·
              refine ⟨24519807327554896876451173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32693076436739862501934897 24519807327554896876451173)
              ·
                refine ⟨4597463873916543164334595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24519807327554896876451173 4597463873916543164334595)
                ·
                  refine ⟨6896195810874814746501893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4597463873916543164334595 6896195810874814746501893)
                  ·
                    refine ⟨1293036714539027764969105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6896195810874814746501893 1293036714539027764969105)
                    ·
                      rfl

theorem cell22_3777270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 2, 4, 1, 4].length) (baseStart_3777270 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3777270 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3777270 prefixEnd_3777270 := by exact prefixLift 3777270
  have htrace : WordTrace (prefixWord ++ tailWord_3777270) baseStart_3777270 baseEnd_3777270 := by
    simpa [prefixWord, tailWord_3777270, baseEnd_3777270] using wordTrace_append hprefix tailTrace_3777270
  have hstable : (prefixWord ++ tailWord_3777270).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3777270).length < 2 ^ (prefixWord ++ tailWord_3777270).sum := by decide
  have hdescent : baseEnd_3777270 < baseStart_3777270 := by decide
  rcases family_descends (prefixWord ++ tailWord_3777270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3777283 : List Nat := [1, 1, 1, 3, 2, 2, 1, 4, 4, 3]
def baseStart_3777283 : Nat := 118140960795 + 3777283 * 2 ^ 59
def prefixEnd_3777283 : Nat := 4983230072969 + 3 ^ 40 * 3777283 * 2
def baseEnd_3777283 : Nat := 1293041164704700064394065

theorem tailTrace_3777283 : CollatzResearch.WordTrace tailWord_3777283 prefixEnd_3777283 1293041164704700064394065 := by
  unfold tailWord_3777283
  simp only [CollatzResearch.WordTrace]
  refine ⟨137768829174556274421792503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91845886116370849614528335 137768829174556274421792503)
  ·
    refine ⟨206653243761834411632688755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137768829174556274421792503 206653243761834411632688755)
    ·
      refine ⟨309979865642751617449033133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206653243761834411632688755 309979865642751617449033133)
      ·
        refine ⟨116242449616031856543387425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 309979865642751617449033133 116242449616031856543387425)
        ·
          refine ⟨87181837212023892407540569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116242449616031856543387425 87181837212023892407540569)
          ·
            refine ⟨65386377909017919305655427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87181837212023892407540569 65386377909017919305655427)
            ·
              refine ⟨98079566863526878958483141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65386377909017919305655427 98079566863526878958483141)
              ·
                refine ⟨18389918786911289804715589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 98079566863526878958483141 18389918786911289804715589)
                ·
                  refine ⟨3448109772545866838384173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18389918786911289804715589 3448109772545866838384173)
                  ·
                    refine ⟨1293041164704700064394065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3448109772545866838384173 1293041164704700064394065)
                    ·
                      rfl

theorem cell22_3777283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 4, 4, 3].length) (baseStart_3777283 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3777283 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3777283 prefixEnd_3777283 := by exact prefixLift 3777283
  have htrace : WordTrace (prefixWord ++ tailWord_3777283) baseStart_3777283 baseEnd_3777283 := by
    simpa [prefixWord, tailWord_3777283, baseEnd_3777283] using wordTrace_append hprefix tailTrace_3777283
  have hstable : (prefixWord ++ tailWord_3777283).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3777283).length < 2 ^ (prefixWord ++ tailWord_3777283).sum := by decide
  have hdescent : baseEnd_3777283 < baseStart_3777283 := by decide
  rcases family_descends (prefixWord ++ tailWord_3777283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3777287 : List Nat := [1, 1, 4, 4, 1, 1, 4, 1, 1, 4]
def baseStart_3777287 : Nat := 118140960795 + 3777287 * 2 ^ 59
def prefixEnd_3777287 : Nat := 4983230072969 + 3 ^ 40 * 3777287 * 2
def baseEnd_3777287 : Nat := 1293042533986445387294053

theorem tailTrace_3777287 : CollatzResearch.WordTrace tailWord_3777287 prefixEnd_3777287 1293042533986445387294053 := by
  unfold tailWord_3777287
  simp only [CollatzResearch.WordTrace]
  refine ⟨137768975066541783104938115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91845983377694522069958743 137768975066541783104938115)
  ·
    refine ⟨206653462599812674657407173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137768975066541783104938115 206653462599812674657407173)
    ·
      refine ⟨38747524237464876498263845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 206653462599812674657407173 38747524237464876498263845)
      ·
        refine ⟨7265160794524664343424471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38747524237464876498263845 7265160794524664343424471)
        ·
          refine ⟨10897741191786996515136707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7265160794524664343424471 10897741191786996515136707)
          ·
            refine ⟨16346611787680494772705061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10897741191786996515136707 16346611787680494772705061)
            ·
              refine ⟨3064989710190092769882199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16346611787680494772705061 3064989710190092769882199)
              ·
                refine ⟨4597484565285139154823299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3064989710190092769882199 4597484565285139154823299)
                ·
                  refine ⟨6896226847927708732234949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4597484565285139154823299 6896226847927708732234949)
                  ·
                    refine ⟨1293042533986445387294053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6896226847927708732234949 1293042533986445387294053)
                    ·
                      rfl

theorem cell22_3777287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 4, 1, 1, 4].length) (baseStart_3777287 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3777287 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3777287 prefixEnd_3777287 := by exact prefixLift 3777287
  have htrace : WordTrace (prefixWord ++ tailWord_3777287) baseStart_3777287 baseEnd_3777287 := by
    simpa [prefixWord, tailWord_3777287, baseEnd_3777287] using wordTrace_append hprefix tailTrace_3777287
  have hstable : (prefixWord ++ tailWord_3777287).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3777287).length < 2 ^ (prefixWord ++ tailWord_3777287).sum := by decide
  have hdescent : baseEnd_3777287 < baseStart_3777287 := by decide
  rcases family_descends (prefixWord ++ tailWord_3777287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3777317 : List Nat := [1, 3, 1, 2, 3, 1, 5, 1, 2, 3]
def baseStart_3777317 : Nat := 118140960795 + 3777317 * 2 ^ 59
def prefixEnd_3777317 : Nat := 4983230072969 + 3 ^ 40 * 3777317 * 2
def baseEnd_3777317 : Nat := 1293052803599535309043961

theorem tailTrace_3777317 : CollatzResearch.WordTrace tailWord_3777317 prefixEnd_3777317 1293052803599535309043961 := by
  unfold tailWord_3777317
  simp only [CollatzResearch.WordTrace]
  refine ⟨137770069256433098228530205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91846712837622065485686803 137770069256433098228530205)
  ·
    refine ⟨51663775971162411835698827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137770069256433098228530205 51663775971162411835698827)
    ·
      refine ⟨77495663956743617753548241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51663775971162411835698827 77495663956743617753548241)
      ·
        refine ⟨58121747967557713315161181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77495663956743617753548241 58121747967557713315161181)
        ·
          refine ⟨21795655487834142493185443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58121747967557713315161181 21795655487834142493185443)
          ·
            refine ⟨32693483231751213739778165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21795655487834142493185443 32693483231751213739778165)
            ·
              refine ⟨3065014052976676288104203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 32693483231751213739778165 3065014052976676288104203)
              ·
                refine ⟨4597521079465014432156305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3065014052976676288104203 4597521079465014432156305)
                ·
                  refine ⟨3448140809598760824117229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4597521079465014432156305 3448140809598760824117229)
                  ·
                    refine ⟨1293052803599535309043961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3448140809598760824117229 1293052803599535309043961)
                    ·
                      rfl

theorem cell22_3777317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 5, 1, 2, 3].length) (baseStart_3777317 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3777317 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3777317 prefixEnd_3777317 := by exact prefixLift 3777317
  have htrace : WordTrace (prefixWord ++ tailWord_3777317) baseStart_3777317 baseEnd_3777317 := by
    simpa [prefixWord, tailWord_3777317, baseEnd_3777317] using wordTrace_append hprefix tailTrace_3777317
  have hstable : (prefixWord ++ tailWord_3777317).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3777317).length < 2 ^ (prefixWord ++ tailWord_3777317).sum := by decide
  have hdescent : baseEnd_3777317 < baseStart_3777317 := by decide
  rcases family_descends (prefixWord ++ tailWord_3777317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3777405 : List Nat := [1, 4, 1, 1, 2, 1, 2, 5, 1, 4]
def baseStart_3777405 : Nat := 118140960795 + 3777405 * 2 ^ 59
def prefixEnd_3777405 : Nat := 4983230072969 + 3 ^ 40 * 3777405 * 2
def baseEnd_3777405 : Nat := 1293082927797932412843691

theorem tailTrace_3777405 : CollatzResearch.WordTrace tailWord_3777405 prefixEnd_3777405 1293082927797932412843691 := by
  unfold tailWord_3777405
  simp only [CollatzResearch.WordTrace]
  refine ⟨137773278880114289257733669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91848852586742859505155779 137773278880114289257733669)
  ·
    refine ⟨25832489790021429235825063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 137773278880114289257733669 25832489790021429235825063)
    ·
      refine ⟨38748734685032143853737595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25832489790021429235825063 38748734685032143853737595)
      ·
        refine ⟨58123102027548215780606393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38748734685032143853737595 58123102027548215780606393)
        ·
          refine ⟨43592326520661161835454795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58123102027548215780606393 43592326520661161835454795)
          ·
            refine ⟨65388489780991742753182193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43592326520661161835454795 65388489780991742753182193)
            ·
              refine ⟨49041367335743807064886645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65388489780991742753182193 49041367335743807064886645)
              ·
                refine ⟨4597628187725981912333123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 49041367335743807064886645 4597628187725981912333123)
                ·
                  refine ⟨6896442281588972868499685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4597628187725981912333123 6896442281588972868499685)
                  ·
                    refine ⟨1293082927797932412843691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6896442281588972868499685 1293082927797932412843691)
                    ·
                      rfl

theorem cell22_3777405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 5, 1, 4].length) (baseStart_3777405 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3777405 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3777405 prefixEnd_3777405 := by exact prefixLift 3777405
  have htrace : WordTrace (prefixWord ++ tailWord_3777405) baseStart_3777405 baseEnd_3777405 := by
    simpa [prefixWord, tailWord_3777405, baseEnd_3777405] using wordTrace_append hprefix tailTrace_3777405
  have hstable : (prefixWord ++ tailWord_3777405).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3777405).length < 2 ^ (prefixWord ++ tailWord_3777405).sum := by decide
  have hdescent : baseEnd_3777405 < baseStart_3777405 := by decide
  rcases family_descends (prefixWord ++ tailWord_3777405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3777433 : List Nat := [1, 2, 1, 2, 1, 3, 1, 4, 1, 6]
def baseStart_3777433 : Nat := 118140960795 + 3777433 * 2 ^ 59
def prefixEnd_3777433 : Nat := 4983230072969 + 3 ^ 40 * 3777433 * 2
def baseEnd_3777433 : Nat := 1293092512770149673143605

theorem tailTrace_3777433 : CollatzResearch.WordTrace tailWord_3777433 prefixEnd_3777433 1293092512770149673143605 := by
  unfold tailWord_3777433
  simp only [CollatzResearch.WordTrace]
  refine ⟨137774300124012850039752953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91849533416008566693168635 137774300124012850039752953)
  ·
    refine ⟨103330725093009637529814715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137774300124012850039752953 103330725093009637529814715)
    ·
      refine ⟨154996087639514456294722073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103330725093009637529814715 154996087639514456294722073)
      ·
        refine ⟨116247065729635842221041555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154996087639514456294722073 116247065729635842221041555)
        ·
          refine ⟨174370598594453763331562333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116247065729635842221041555 174370598594453763331562333)
          ·
            refine ⟨65388974472920161249335875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 174370598594453763331562333 65388974472920161249335875)
            ·
              refine ⟨98083461709380241874003813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65388974472920161249335875 98083461709380241874003813)
              ·
                refine ⟨18390649070508795351375715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 98083461709380241874003813 18390649070508795351375715)
                ·
                  refine ⟨27585973605763193027063573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18390649070508795351375715 27585973605763193027063573)
                  ·
                    refine ⟨1293092512770149673143605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27585973605763193027063573 1293092512770149673143605)
                    ·
                      rfl

theorem cell22_3777433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 4, 1, 6].length) (baseStart_3777433 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3777433 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3777433 prefixEnd_3777433 := by exact prefixLift 3777433
  have htrace : WordTrace (prefixWord ++ tailWord_3777433) baseStart_3777433 baseEnd_3777433 := by
    simpa [prefixWord, tailWord_3777433, baseEnd_3777433] using wordTrace_append hprefix tailTrace_3777433
  have hstable : (prefixWord ++ tailWord_3777433).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3777433).length < 2 ^ (prefixWord ++ tailWord_3777433).sum := by decide
  have hdescent : baseEnd_3777433 < baseStart_3777433 := by decide
  rcases family_descends (prefixWord ++ tailWord_3777433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3777497 : List Nat := [1, 2, 1, 2, 5, 1, 2, 2, 3, 3]
def baseStart_3777497 : Nat := 118140960795 + 3777497 * 2 ^ 59
def prefixEnd_3777497 : Nat := 4983230072969 + 3 ^ 40 * 3777497 * 2
def baseEnd_3777497 : Nat := 1293114421278074839543409

theorem tailTrace_3777497 : CollatzResearch.WordTrace tailWord_3777497 prefixEnd_3777497 1293114421278074839543409 := by
  unfold tailWord_3777497
  simp only [CollatzResearch.WordTrace]
  refine ⟨137776634395780988970082745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91851089597187325980055163 137776634395780988970082745)
  ·
    refine ⟨103332475796835741727562059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137776634395780988970082745 103332475796835741727562059)
    ·
      refine ⟨154998713695253612591343089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103332475796835741727562059 154998713695253612591343089)
      ·
        refine ⟨116249035271440209443507317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154998713695253612591343089 116249035271440209443507317)
        ·
          refine ⟨10898347056697519635328811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 116249035271440209443507317 10898347056697519635328811)
          ·
            refine ⟨16347520585046279452993217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10898347056697519635328811 16347520585046279452993217)
            ·
              refine ⟨12260640438784709589744913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16347520585046279452993217 12260640438784709589744913)
              ·
                refine ⟨9195480329088532192308685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12260640438784709589744913 9195480329088532192308685)
                ·
                  refine ⟨3448305123408199572115757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9195480329088532192308685 3448305123408199572115757)
                  ·
                    refine ⟨1293114421278074839543409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3448305123408199572115757 1293114421278074839543409)
                    ·
                      rfl

theorem cell22_3777497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 2, 2, 3, 3].length) (baseStart_3777497 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3777497 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3777497 prefixEnd_3777497 := by exact prefixLift 3777497
  have htrace : WordTrace (prefixWord ++ tailWord_3777497) baseStart_3777497 baseEnd_3777497 := by
    simpa [prefixWord, tailWord_3777497, baseEnd_3777497] using wordTrace_append hprefix tailTrace_3777497
  have hstable : (prefixWord ++ tailWord_3777497).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3777497).length < 2 ^ (prefixWord ++ tailWord_3777497).sum := by decide
  have hdescent : baseEnd_3777497 < baseStart_3777497 := by decide
  rcases family_descends (prefixWord ++ tailWord_3777497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3777544 : List Nat := [2, 1, 3, 2, 1, 5, 2, 1, 5]
def baseStart_3777544 : Nat := 118140960795 + 3777544 * 2 ^ 59
def prefixEnd_3777544 : Nat := 4983230072969 + 3 ^ 40 * 3777544 * 2
def baseEnd_3777544 : Nat := 431043503446194127872755

theorem tailTrace_3777544 : CollatzResearch.WordTrace tailWord_3777544 prefixEnd_3777544 431043503446194127872755 := by
  unfold tailWord_3777544
  simp only [CollatzResearch.WordTrace]
  refine ⟨68889174313305357998521843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91852232417740477331362457 68889174313305357998521843)
  ·
    refine ⟨103333761469958036997782765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68889174313305357998521843 103333761469958036997782765)
    ·
      refine ⟨38750160551234263874168537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103333761469958036997782765 38750160551234263874168537)
      ·
        refine ⟨29062620413425697905626403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38750160551234263874168537 29062620413425697905626403)
        ·
          refine ⟨43593930620138546858439605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29062620413425697905626403 43593930620138546858439605)
          ·
            refine ⟨4086930995637988767978713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 43593930620138546858439605 4086930995637988767978713)
            ·
              refine ⟨3065198246728491575984035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4086930995637988767978713 3065198246728491575984035)
              ·
                refine ⟨4597797370092737363976053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3065198246728491575984035 4597797370092737363976053)
                ·
                  refine ⟨431043503446194127872755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4597797370092737363976053 431043503446194127872755)
                  ·
                    rfl

theorem cell22_3777544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 5, 2, 1, 5].length) (baseStart_3777544 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3777544 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3777544 prefixEnd_3777544 := by exact prefixLift 3777544
  have htrace : WordTrace (prefixWord ++ tailWord_3777544) baseStart_3777544 baseEnd_3777544 := by
    simpa [prefixWord, tailWord_3777544, baseEnd_3777544] using wordTrace_append hprefix tailTrace_3777544
  have hstable : (prefixWord ++ tailWord_3777544).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3777544).length < 2 ^ (prefixWord ++ tailWord_3777544).sum := by decide
  have hdescent : baseEnd_3777544 < baseStart_3777544 := by decide
  rcases family_descends (prefixWord ++ tailWord_3777544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3777557 : List Nat := [1, 3, 2, 1, 4, 2, 1, 1, 3, 4]
def baseStart_3777557 : Nat := 118140960795 + 3777557 * 2 ^ 59
def prefixEnd_3777557 : Nat := 4983230072969 + 3 ^ 40 * 3777557 * 2
def baseEnd_3777557 : Nat := 1293134960504254683043225

theorem tailTrace_3777557 : CollatzResearch.WordTrace tailWord_3777557 prefixEnd_3777557 1293134960504254683043225 := by
  unfold tailWord_3777557
  simp only [CollatzResearch.WordTrace]
  refine ⟨137778822775563619217266925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91852548517042412811511283 137778822775563619217266925)
  ·
    refine ⟨51667058540836357206475097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137778822775563619217266925 51667058540836357206475097)
    ·
      refine ⟨38750293905627267904856323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51667058540836357206475097 38750293905627267904856323)
      ·
        refine ⟨58125440858440901857284485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38750293905627267904856323 58125440858440901857284485)
        ·
          refine ⟨10898520160957669098240841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 58125440858440901857284485 10898520160957669098240841)
          ·
            refine ⟨8173890120718251823680631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10898520160957669098240841 8173890120718251823680631)
            ·
              refine ⟨12260835181077377735520947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8173890120718251823680631 12260835181077377735520947)
              ·
                refine ⟨18391252771616066603281421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12260835181077377735520947 18391252771616066603281421)
                ·
                  refine ⟨6896719789356024976230533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18391252771616066603281421 6896719789356024976230533)
                  ·
                    refine ⟨1293134960504254683043225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6896719789356024976230533 1293134960504254683043225)
                    ·
                      rfl

theorem cell22_3777557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 1, 1, 3, 4].length) (baseStart_3777557 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3777557 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3777557 prefixEnd_3777557 := by exact prefixLift 3777557
  have htrace : WordTrace (prefixWord ++ tailWord_3777557) baseStart_3777557 baseEnd_3777557 := by
    simpa [prefixWord, tailWord_3777557, baseEnd_3777557] using wordTrace_append hprefix tailTrace_3777557
  have hstable : (prefixWord ++ tailWord_3777557).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3777557).length < 2 ^ (prefixWord ++ tailWord_3777557).sum := by decide
  have hdescent : baseEnd_3777557 < baseStart_3777557 := by decide
  rcases family_descends (prefixWord ++ tailWord_3777557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3777632 : List Nat := [2, 1, 1, 3, 2, 2, 1, 2, 5, 3]
def baseStart_3777632 : Nat := 118140960795 + 3777632 * 2 ^ 59
def prefixEnd_3777632 : Nat := 4983230072969 + 3 ^ 40 * 3777632 * 2
def baseEnd_3777632 : Nat := 1293160634536979487417995

theorem tailTrace_3777632 : CollatzResearch.WordTrace tailWord_3777632 prefixEnd_3777632 1293160634536979487417995 := by
  unfold tailWord_3777632
  simp only [CollatzResearch.WordTrace]
  refine ⟨68890779125145953513123575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91854372166861271350831433 68890779125145953513123575)
  ·
    refine ⟨103336168687718930269685363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68890779125145953513123575 103336168687718930269685363)
    ·
      refine ⟨155004253031578395404528045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103336168687718930269685363 155004253031578395404528045)
      ·
        refine ⟨58126594886841898276698017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 155004253031578395404528045 58126594886841898276698017)
        ·
          refine ⟨43594946165131423707523513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58126594886841898276698017 43594946165131423707523513)
          ·
            refine ⟨32696209623848567780642635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43594946165131423707523513 32696209623848567780642635)
            ·
              refine ⟨49044314435772851670963953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32696209623848567780642635 49044314435772851670963953)
              ·
                refine ⟨36783235826829638753222965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49044314435772851670963953 36783235826829638753222965)
                ·
                  refine ⟨3448428358765278633114653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 36783235826829638753222965 3448428358765278633114653)
                  ·
                    refine ⟨1293160634536979487417995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3448428358765278633114653 1293160634536979487417995)
                    ·
                      rfl

theorem cell22_3777632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 2, 5, 3].length) (baseStart_3777632 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3777632 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3777632 prefixEnd_3777632 := by exact prefixLift 3777632
  have htrace : WordTrace (prefixWord ++ tailWord_3777632) baseStart_3777632 baseEnd_3777632 := by
    simpa [prefixWord, tailWord_3777632, baseEnd_3777632] using wordTrace_append hprefix tailTrace_3777632
  have hstable : (prefixWord ++ tailWord_3777632).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3777632).length < 2 ^ (prefixWord ++ tailWord_3777632).sum := by decide
  have hdescent : baseEnd_3777632 < baseStart_3777632 := by decide
  rcases family_descends (prefixWord ++ tailWord_3777632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3777675 : List Nat := [1, 1, 1, 1, 4, 1, 1, 2, 2, 8]
def baseStart_3777675 : Nat := 118140960795 + 3777675 * 2 ^ 59
def prefixEnd_3777675 : Nat := 4983230072969 + 3 ^ 40 * 3777675 * 2
def baseEnd_3777675 : Nat := 1293175354315741708592863

theorem tailTrace_3777675 : CollatzResearch.WordTrace tailWord_3777675 prefixEnd_3777675 1293175354315741708592863 := by
  unfold tailWord_3777675
  simp only [CollatzResearch.WordTrace]
  refine ⟨137783126589136125370062479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91855417726090750246708319 137783126589136125370062479)
  ·
    refine ⟨206674689883704188055093719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137783126589136125370062479 206674689883704188055093719)
    ·
      refine ⟨310012034825556282082640579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206674689883704188055093719 310012034825556282082640579)
      ·
        refine ⟨465018052238334423123960869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 310012034825556282082640579 465018052238334423123960869)
        ·
          refine ⟨87190884794687704335742663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 465018052238334423123960869 87190884794687704335742663)
          ·
            refine ⟨130786327192031556503613995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87190884794687704335742663 130786327192031556503613995)
            ·
              refine ⟨196179490788047334755420993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 130786327192031556503613995 196179490788047334755420993)
              ·
                refine ⟨147134618091035501066565745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 196179490788047334755420993 147134618091035501066565745)
                ·
                  refine ⟨110350963568276625799924309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 147134618091035501066565745 110350963568276625799924309)
                  ·
                    refine ⟨1293175354315741708592863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 110350963568276625799924309 1293175354315741708592863)
                    ·
                      rfl

theorem cell22_3777675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 2, 2, 8].length) (baseStart_3777675 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3777675 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3777675 prefixEnd_3777675 := by exact prefixLift 3777675
  have htrace : WordTrace (prefixWord ++ tailWord_3777675) baseStart_3777675 baseEnd_3777675 := by
    simpa [prefixWord, tailWord_3777675, baseEnd_3777675] using wordTrace_append hprefix tailTrace_3777675
  have hstable : (prefixWord ++ tailWord_3777675).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3777675).length < 2 ^ (prefixWord ++ tailWord_3777675).sum := by decide
  have hdescent : baseEnd_3777675 < baseStart_3777675 := by decide
  rcases family_descends (prefixWord ++ tailWord_3777675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3777722 : List Nat := [3, 1, 1, 1, 2, 2, 1, 5, 1, 5]
def baseStart_3777722 : Nat := 118140960795 + 3777722 * 2 ^ 59
def prefixEnd_3777722 : Nat := 4983230072969 + 3 ^ 40 * 3777722 * 2
def baseEnd_3777722 : Nat := 1293191443376249252667719

theorem tailTrace_3777722 : CollatzResearch.WordTrace tailWord_3777722 prefixEnd_3777722 1293191443376249252667719 := by
  unfold tailWord_3777722
  simp only [CollatzResearch.WordTrace]
  refine ⟨34446210204991463099255855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91856560546643901598015613 34446210204991463099255855)
  ·
    refine ⟨51669315307487194648883783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34446210204991463099255855 51669315307487194648883783)
    ·
      refine ⟨77503972961230791973325675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51669315307487194648883783 77503972961230791973325675)
      ·
        refine ⟨116255959441846187959988513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77503972961230791973325675 116255959441846187959988513)
        ·
          refine ⟨87191969581384640969991385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116255959441846187959988513 87191969581384640969991385)
          ·
            refine ⟨65393977186038480727493539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87191969581384640969991385 65393977186038480727493539)
            ·
              refine ⟨98090965779057721091240309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65393977186038480727493539 98090965779057721091240309)
              ·
                refine ⟨9196028041786661352303779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 98090965779057721091240309 9196028041786661352303779)
                ·
                  refine ⟨13794042062679992028455669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9196028041786661352303779 13794042062679992028455669)
                  ·
                    refine ⟨1293191443376249252667719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13794042062679992028455669 1293191443376249252667719)
                    ·
                      rfl

theorem cell22_3777722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 5, 1, 5].length) (baseStart_3777722 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3777722 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3777722 prefixEnd_3777722 := by exact prefixLift 3777722
  have htrace : WordTrace (prefixWord ++ tailWord_3777722) baseStart_3777722 baseEnd_3777722 := by
    simpa [prefixWord, tailWord_3777722, baseEnd_3777722] using wordTrace_append hprefix tailTrace_3777722
  have hstable : (prefixWord ++ tailWord_3777722).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3777722).length < 2 ^ (prefixWord ++ tailWord_3777722).sum := by decide
  have hdescent : baseEnd_3777722 < baseStart_3777722 := by decide
  rcases family_descends (prefixWord ++ tailWord_3777722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3777726 : List Nat := [4, 2, 1, 1, 3, 1, 3, 2, 1, 4]
def baseStart_3777726 : Nat := 118140960795 + 3777726 * 2 ^ 59
def prefixEnd_3777726 : Nat := 4983230072969 + 3 ^ 40 * 3777726 * 2
def baseEnd_3777726 : Nat := 1293192812657994575567707

theorem tailTrace_3777726 : CollatzResearch.WordTrace tailWord_3777726 prefixEnd_3777726 1293192812657994575567707 := by
  unfold tailWord_3777726
  simp only [CollatzResearch.WordTrace]
  refine ⟨17223123338993920135021129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 91856657807967574053446021 17223123338993920135021129)
  ·
    refine ⟨12917342504245440101265847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17223123338993920135021129 12917342504245440101265847)
    ·
      refine ⟨19376013756368160151898771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12917342504245440101265847 19376013756368160151898771)
      ·
        refine ⟨29064020634552240227848157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19376013756368160151898771 29064020634552240227848157)
        ·
          refine ⟨10899007737957090085443059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29064020634552240227848157 10899007737957090085443059)
          ·
            refine ⟨16348511606935635128164589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10899007737957090085443059 16348511606935635128164589)
            ·
              refine ⟨6130691852600863173061721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16348511606935635128164589 6130691852600863173061721)
              ·
                refine ⟨4598018889450647379796291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6130691852600863173061721 4598018889450647379796291)
                ·
                  refine ⟨6897028334175971069694437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4598018889450647379796291 6897028334175971069694437)
                  ·
                    refine ⟨1293192812657994575567707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6897028334175971069694437 1293192812657994575567707)
                    ·
                      rfl

theorem cell22_3777726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 3, 2, 1, 4].length) (baseStart_3777726 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3777726 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3777726 prefixEnd_3777726 := by exact prefixLift 3777726
  have htrace : WordTrace (prefixWord ++ tailWord_3777726) baseStart_3777726 baseEnd_3777726 := by
    simpa [prefixWord, tailWord_3777726, baseEnd_3777726] using wordTrace_append hprefix tailTrace_3777726
  have hstable : (prefixWord ++ tailWord_3777726).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3777726).length < 2 ^ (prefixWord ++ tailWord_3777726).sum := by decide
  have hdescent : baseEnd_3777726 < baseStart_3777726 := by decide
  rcases family_descends (prefixWord ++ tailWord_3777726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3777752 : List Nat := [2, 1, 2, 2, 5, 10]
def baseStart_3777752 : Nat := 118140960795 + 3777752 * 2 ^ 59
def prefixEnd_3777752 : Nat := 4983230072969 + 3 ^ 40 * 3777752 * 2
def baseEnd_3777752 : Nat := 15965453246781965116267

theorem tailTrace_3777752 : CollatzResearch.WordTrace tailWord_3777752 prefixEnd_3777752 15965453246781965116267 := by
  unfold tailWord_3777752
  simp only [CollatzResearch.WordTrace]
  refine ⟨68892967504928583760307755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91857290006571445013743673 68892967504928583760307755)
  ·
    refine ⟨103339451257392875640461633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68892967504928583760307755 103339451257392875640461633)
    ·
      refine ⟨77504588443044656730346225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103339451257392875640461633 77504588443044656730346225)
      ·
        refine ⟨58128441332283492547759669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77504588443044656730346225 58128441332283492547759669)
        ·
          refine ⟨5449541374901577426352469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 58128441332283492547759669 5449541374901577426352469)
          ·
            refine ⟨15965453246781965116267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 5449541374901577426352469 15965453246781965116267)
            ·
              rfl

theorem cell22_3777752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 10].length) (baseStart_3777752 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3777752 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3777752 prefixEnd_3777752 := by exact prefixLift 3777752
  have htrace : WordTrace (prefixWord ++ tailWord_3777752) baseStart_3777752 baseEnd_3777752 := by
    simpa [prefixWord, tailWord_3777752, baseEnd_3777752] using wordTrace_append hprefix tailTrace_3777752
  have hstable : (prefixWord ++ tailWord_3777752).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3777752).length < 2 ^ (prefixWord ++ tailWord_3777752).sum := by decide
  have hdescent : baseEnd_3777752 < baseStart_3777752 := by decide
  rcases family_descends (prefixWord ++ tailWord_3777752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3777788 : List Nat := [2, 2, 2, 1, 6, 1, 1, 1, 2, 4]
def baseStart_3777788 : Nat := 118140960795 + 3777788 * 2 ^ 59
def prefixEnd_3777788 : Nat := 4983230072969 + 3 ^ 40 * 3777788 * 2
def baseEnd_3777788 : Nat := 1293214036525047080517517

theorem tailTrace_3777788 : CollatzResearch.WordTrace tailWord_3777788 prefixEnd_3777788 1293214036525047080517517 := by
  unfold tailWord_3777788
  simp only [CollatzResearch.WordTrace]
  refine ⟨68893624018863372834463009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91858165358484497112617345 68893624018863372834463009)
  ·
    refine ⟨51670218014147529625847257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68893624018863372834463009 51670218014147529625847257)
    ·
      refine ⟨38752663510610647219385443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51670218014147529625847257 38752663510610647219385443)
      ·
        refine ⟨58128995265915970829078165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38752663510610647219385443 58128995265915970829078165)
        ·
          refine ⟨2724796653089811132613039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 58128995265915970829078165 2724796653089811132613039)
          ·
            refine ⟨4087194979634716698919559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2724796653089811132613039 4087194979634716698919559)
            ·
              refine ⟨6130792469452075048379339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4087194979634716698919559 6130792469452075048379339)
              ·
                refine ⟨9196188704178112572569009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6130792469452075048379339 9196188704178112572569009)
                ·
                  refine ⟨6897141528133584429426757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9196188704178112572569009 6897141528133584429426757)
                  ·
                    refine ⟨1293214036525047080517517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6897141528133584429426757 1293214036525047080517517)
                    ·
                      rfl

theorem cell22_3777788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 6, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 6, 1, 1, 1, 2, 4].length) (baseStart_3777788 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3777788 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3777788 prefixEnd_3777788 := by exact prefixLift 3777788
  have htrace : WordTrace (prefixWord ++ tailWord_3777788) baseStart_3777788 baseEnd_3777788 := by
    simpa [prefixWord, tailWord_3777788, baseEnd_3777788] using wordTrace_append hprefix tailTrace_3777788
  have hstable : (prefixWord ++ tailWord_3777788).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3777788).length < 2 ^ (prefixWord ++ tailWord_3777788).sum := by decide
  have hdescent : baseEnd_3777788 < baseStart_3777788 := by decide
  rcases family_descends (prefixWord ++ tailWord_3777788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3777797 : List Nat := [1, 3, 1, 1, 2, 1, 4, 2, 7]
def baseStart_3777797 : Nat := 118140960795 + 3777797 * 2 ^ 59
def prefixEnd_3777797 : Nat := 4983230072969 + 3 ^ 40 * 3777797 * 2
def baseEnd_3777797 : Nat := 431072372469658019014163

theorem tailTrace_3777797 : CollatzResearch.WordTrace tailWord_3777797 prefixEnd_3777797 431072372469658019014163 := by
  unfold tailWord_3777797
  simp only [CollatzResearch.WordTrace]
  refine ⟨137787576294694140206003645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91858384196462760137335763 137787576294694140206003645)
  ·
    refine ⟨51670341110510302577251367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137787576294694140206003645 51670341110510302577251367)
    ·
      refine ⟨77505511665765453865877051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51670341110510302577251367 77505511665765453865877051)
      ·
        refine ⟨116258267498648180798815577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77505511665765453865877051 116258267498648180798815577)
        ·
          refine ⟨87193700623986135599111683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116258267498648180798815577 87193700623986135599111683)
          ·
            refine ⟨130790550935979203398667525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87193700623986135599111683 130790550935979203398667525)
            ·
              refine ⟨24523228300496100637250161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 130790550935979203398667525 24523228300496100637250161)
              ·
                refine ⟨18392421225372075477937621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24523228300496100637250161 18392421225372075477937621)
                ·
                  refine ⟨431072372469658019014163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18392421225372075477937621 431072372469658019014163)
                  ·
                    rfl

theorem cell22_3777797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 4, 2, 7].length) (baseStart_3777797 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3777797 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3777797 prefixEnd_3777797 := by exact prefixLift 3777797
  have htrace : WordTrace (prefixWord ++ tailWord_3777797) baseStart_3777797 baseEnd_3777797 := by
    simpa [prefixWord, tailWord_3777797, baseEnd_3777797] using wordTrace_append hprefix tailTrace_3777797
  have hstable : (prefixWord ++ tailWord_3777797).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3777797).length < 2 ^ (prefixWord ++ tailWord_3777797).sum := by decide
  have hdescent : baseEnd_3777797 < baseStart_3777797 := by decide
  rcases family_descends (prefixWord ++ tailWord_3777797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3777818 : List Nat := [3, 1, 1, 3, 3, 1, 2, 4, 1, 3]
def baseStart_3777818 : Nat := 118140960795 + 3777818 * 2 ^ 59
def prefixEnd_3777818 : Nat := 4983230072969 + 3 ^ 40 * 3777818 * 2
def baseEnd_3777818 : Nat := 1293224306138137002267425

theorem tailTrace_3777818 : CollatzResearch.WordTrace tailWord_3777818 prefixEnd_3777818 1293224306138137002267425 := by
  unfold tailWord_3777818
  simp only [CollatzResearch.WordTrace]
  refine ⟨34447085556904515198129527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91858894818412040528345405 34447085556904515198129527)
  ·
    refine ⟨51670628335356772797194291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34447085556904515198129527 51670628335356772797194291)
    ·
      refine ⟨77505942503035159195791437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51670628335356772797194291 77505942503035159195791437)
      ·
        refine ⟨29064728438638184698421789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77505942503035159195791437 29064728438638184698421789)
        ·
          refine ⟨10899273164489319261908171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29064728438638184698421789 10899273164489319261908171)
          ·
            refine ⟨16348909746733978892862257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10899273164489319261908171 16348909746733978892862257)
            ·
              refine ⟨12261682310050484169646693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16348909746733978892862257 12261682310050484169646693)
              ·
                refine ⟨2299065433134465781808755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12261682310050484169646693 2299065433134465781808755)
                ·
                  refine ⟨3448598149701698672713133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2299065433134465781808755 3448598149701698672713133)
                  ·
                    refine ⟨1293224306138137002267425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3448598149701698672713133 1293224306138137002267425)
                    ·
                      rfl

theorem cell22_3777818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 2, 4, 1, 3].length) (baseStart_3777818 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3777818 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3777818 prefixEnd_3777818 := by exact prefixLift 3777818
  have htrace : WordTrace (prefixWord ++ tailWord_3777818) baseStart_3777818 baseEnd_3777818 := by
    simpa [prefixWord, tailWord_3777818, baseEnd_3777818] using wordTrace_append hprefix tailTrace_3777818
  have hstable : (prefixWord ++ tailWord_3777818).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3777818).length < 2 ^ (prefixWord ++ tailWord_3777818).sum := by decide
  have hdescent : baseEnd_3777818 < baseStart_3777818 := by decide
  rcases family_descends (prefixWord ++ tailWord_3777818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3777829 : List Nat := [1, 3, 1, 2, 4, 1, 2, 1, 2, 5]
def baseStart_3777829 : Nat := 118140960795 + 3777829 * 2 ^ 59
def prefixEnd_3777829 : Nat := 4983230072969 + 3 ^ 40 * 3777829 * 2
def baseEnd_3777829 : Nat := 1293228071662936640242391

theorem tailTrace_3777829 : CollatzResearch.WordTrace tailWord_3777829 prefixEnd_3777829 1293228071662936640242391 := by
  unfold tailWord_3777829
  simp only [CollatzResearch.WordTrace]
  refine ⟨137788743430578209671168541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91859162287052139780779027 137788743430578209671168541)
  ·
    refine ⟨51670778786466828626688203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137788743430578209671168541 51670778786466828626688203)
    ·
      refine ⟨77506168179700242940032305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51670778786466828626688203 77506168179700242940032305)
      ·
        refine ⟨58129626134775182205024229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77506168179700242940032305 58129626134775182205024229)
        ·
          refine ⟨10899304900270346663442043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 58129626134775182205024229 10899304900270346663442043)
          ·
            refine ⟨16348957350405519995163065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10899304900270346663442043 16348957350405519995163065)
            ·
              refine ⟨12261718012804139996372299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16348957350405519995163065 12261718012804139996372299)
              ·
                refine ⟨18392577019206209994558449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12261718012804139996372299 18392577019206209994558449)
                ·
                  refine ⟨13794432764404657495918837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18392577019206209994558449 13794432764404657495918837)
                  ·
                    refine ⟨1293228071662936640242391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13794432764404657495918837 1293228071662936640242391)
                    ·
                      rfl

theorem cell22_3777829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 2, 1, 2, 5].length) (baseStart_3777829 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3777829 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3777829 prefixEnd_3777829 := by exact prefixLift 3777829
  have htrace : WordTrace (prefixWord ++ tailWord_3777829) baseStart_3777829 baseEnd_3777829 := by
    simpa [prefixWord, tailWord_3777829, baseEnd_3777829] using wordTrace_append hprefix tailTrace_3777829
  have hstable : (prefixWord ++ tailWord_3777829).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3777829).length < 2 ^ (prefixWord ++ tailWord_3777829).sum := by decide
  have hdescent : baseEnd_3777829 < baseStart_3777829 := by decide
  rcases family_descends (prefixWord ++ tailWord_3777829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3777869 : List Nat := [1, 6, 1, 3, 1, 1, 3, 2, 1, 3]
def baseStart_3777869 : Nat := 118140960795 + 3777869 * 2 ^ 59
def prefixEnd_3777869 : Nat := 4983230072969 + 3 ^ 40 * 3777869 * 2
def baseEnd_3777869 : Nat := 1293241764480389869242269

theorem tailTrace_3777869 : CollatzResearch.WordTrace tailWord_3777869 prefixEnd_3777869 1293241764480389869242269 := by
  unfold tailWord_3777869
  simp only [CollatzResearch.WordTrace]
  refine ⟨137790202350433296502624661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91860134900288864335083107 137790202350433296502624661)
  ·
    refine ⟨6458915735176560773560531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 137790202350433296502624661 6458915735176560773560531)
    ·
      refine ⟨9688373602764841160340797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6458915735176560773560531 9688373602764841160340797)
      ·
        refine ⟨3633140101036815435127799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9688373602764841160340797 3633140101036815435127799)
        ·
          refine ⟨5449710151555223152691699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3633140101036815435127799 5449710151555223152691699)
          ·
            refine ⟨8174565227332834729037549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5449710151555223152691699 8174565227332834729037549)
            ·
              refine ⟨3065461960249813023389081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8174565227332834729037549 3065461960249813023389081)
              ·
                refine ⟨2299096470187359767541811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3065461960249813023389081 2299096470187359767541811)
                ·
                  refine ⟨3448644705281039651312717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2299096470187359767541811 3448644705281039651312717)
                  ·
                    refine ⟨1293241764480389869242269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3448644705281039651312717 1293241764480389869242269)
                    ·
                      rfl

theorem cell22_3777869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 3, 2, 1, 3].length) (baseStart_3777869 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3777869 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3777869 prefixEnd_3777869 := by exact prefixLift 3777869
  have htrace : WordTrace (prefixWord ++ tailWord_3777869) baseStart_3777869 baseEnd_3777869 := by
    simpa [prefixWord, tailWord_3777869, baseEnd_3777869] using wordTrace_append hprefix tailTrace_3777869
  have hstable : (prefixWord ++ tailWord_3777869).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3777869).length < 2 ^ (prefixWord ++ tailWord_3777869).sum := by decide
  have hdescent : baseEnd_3777869 < baseStart_3777869 := by decide
  rcases family_descends (prefixWord ++ tailWord_3777869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3777895 : List Nat := [1, 1, 5, 1, 5, 1, 1, 2, 1, 4]
def baseStart_3777895 : Nat := 118140960795 + 3777895 * 2 ^ 59
def prefixEnd_3777895 : Nat := 4983230072969 + 3 ^ 40 * 3777895 * 2
def baseEnd_3777895 : Nat := 1293250664811734468092189

theorem tailTrace_3777895 : CollatzResearch.WordTrace tailWord_3777895 prefixEnd_3777895 1293250664811734468092189 := by
  unfold tailWord_3777895
  simp only [CollatzResearch.WordTrace]
  refine ⟨137791150648339102943071139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91860767098892735295380759 137791150648339102943071139)
  ·
    refine ⟨206686725972508654414606709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137791150648339102943071139 206686725972508654414606709)
    ·
      refine ⟨19376880559922686351369379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 206686725972508654414606709 19376880559922686351369379)
      ·
        refine ⟨29065320839884029527054069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19376880559922686351369379 29065320839884029527054069)
        ·
          refine ⟨2724873828739127768161319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 29065320839884029527054069 2724873828739127768161319)
          ·
            refine ⟨4087310743108691652241979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2724873828739127768161319 4087310743108691652241979)
            ·
              refine ⟨6130966114663037478362969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4087310743108691652241979 6130966114663037478362969)
              ·
                refine ⟨4598224585997278108772227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6130966114663037478362969 4598224585997278108772227)
                ·
                  refine ⟨6897336878995917163158341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4598224585997278108772227 6897336878995917163158341)
                  ·
                    refine ⟨1293250664811734468092189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6897336878995917163158341 1293250664811734468092189)
                    ·
                      rfl

theorem cell22_3777895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 5, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 5, 1, 1, 2, 1, 4].length) (baseStart_3777895 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3777895 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3777895 prefixEnd_3777895 := by exact prefixLift 3777895
  have htrace : WordTrace (prefixWord ++ tailWord_3777895) baseStart_3777895 baseEnd_3777895 := by
    simpa [prefixWord, tailWord_3777895, baseEnd_3777895] using wordTrace_append hprefix tailTrace_3777895
  have hstable : (prefixWord ++ tailWord_3777895).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3777895).length < 2 ^ (prefixWord ++ tailWord_3777895).sum := by decide
  have hdescent : baseEnd_3777895 < baseStart_3777895 := by decide
  rcases family_descends (prefixWord ++ tailWord_3777895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3777906 : List Nat := [3, 2, 1, 2, 1, 2, 4, 1, 2, 4]
def baseStart_3777906 : Nat := 118140960795 + 3777906 * 2 ^ 59
def prefixEnd_3777906 : Nat := 4983230072969 + 3 ^ 40 * 3777906 * 2
def baseEnd_3777906 : Nat := 1293254430336534106067155

theorem tailTrace_3777906 : CollatzResearch.WordTrace tailWord_3777906 prefixEnd_3777906 1293254430336534106067155 := by
  unfold tailWord_3777906
  simp only [CollatzResearch.WordTrace]
  refine ⟨34447887962824812955430393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91861034567532834547814381 34447887962824812955430393)
  ·
    refine ⟨25835915972118609716572795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34447887962824812955430393 25835915972118609716572795)
    ·
      refine ⟨38753873958177914574859193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25835915972118609716572795 38753873958177914574859193)
      ·
        refine ⟨29065405468633435931144395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38753873958177914574859193 29065405468633435931144395)
        ·
          refine ⟨43598108202950153896716593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29065405468633435931144395 43598108202950153896716593)
          ·
            refine ⟨32698581152212615422537445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43598108202950153896716593 32698581152212615422537445)
            ·
              refine ⟨6130983966039865391725771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32698581152212615422537445 6130983966039865391725771)
              ·
                refine ⟨9196475949059798087588657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6130983966039865391725771 9196475949059798087588657)
                ·
                  refine ⟨6897356961794848565691493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9196475949059798087588657 6897356961794848565691493)
                  ·
                    refine ⟨1293254430336534106067155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6897356961794848565691493 1293254430336534106067155)
                    ·
                      rfl

theorem cell22_3777906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 4, 1, 2, 4].length) (baseStart_3777906 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3777906 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3777906 prefixEnd_3777906 := by exact prefixLift 3777906
  have htrace : WordTrace (prefixWord ++ tailWord_3777906) baseStart_3777906 baseEnd_3777906 := by
    simpa [prefixWord, tailWord_3777906, baseEnd_3777906] using wordTrace_append hprefix tailTrace_3777906
  have hstable : (prefixWord ++ tailWord_3777906).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3777906).length < 2 ^ (prefixWord ++ tailWord_3777906).sum := by decide
  have hdescent : baseEnd_3777906 < baseStart_3777906 := by decide
  rcases family_descends (prefixWord ++ tailWord_3777906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3777921 : List Nat := [1, 2, 4, 3, 3, 9]
def baseStart_3777921 : Nat := 118140960795 + 3777921 * 2 ^ 59
def prefixEnd_3777921 : Nat := 4983230072969 + 3 ^ 40 * 3777921 * 2
def baseEnd_3777921 : Nat := 15966167470902210702989

theorem tailTrace_3777921 : CollatzResearch.WordTrace tailWord_3777921 prefixEnd_3777921 15966167470902210702989 := by
  unfold tailWord_3777921
  simp only [CollatzResearch.WordTrace]
  refine ⟨137792098946244909383517617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91861399297496606255678411 137792098946244909383517617)
  ·
    refine ⟨103344074209683682037638213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137792098946244909383517617 103344074209683682037638213)
    ·
      refine ⟨19377013914315690382057165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 103344074209683682037638213 19377013914315690382057165)
      ·
        refine ⟨7266380217868383893271437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19377013914315690382057165 7266380217868383893271437)
        ·
          refine ⟨2724892581700643959976789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7266380217868383893271437 2724892581700643959976789)
          ·
            refine ⟨15966167470902210702989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2724892581700643959976789 15966167470902210702989)
            ·
              rfl

theorem cell22_3777921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 3, 9].length) (baseStart_3777921 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3777921 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3777921 prefixEnd_3777921 := by exact prefixLift 3777921
  have htrace : WordTrace (prefixWord ++ tailWord_3777921) baseStart_3777921 baseEnd_3777921 := by
    simpa [prefixWord, tailWord_3777921, baseEnd_3777921] using wordTrace_append hprefix tailTrace_3777921
  have hstable : (prefixWord ++ tailWord_3777921).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3777921).length < 2 ^ (prefixWord ++ tailWord_3777921).sum := by decide
  have hdescent : baseEnd_3777921 < baseStart_3777921 := by decide
  rcases family_descends (prefixWord ++ tailWord_3777921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3778013 : List Nat := [1, 4, 3, 1, 1, 2, 1, 4, 1, 4]
def baseStart_3778013 : Nat := 118140960795 + 3778013 * 2 ^ 59
def prefixEnd_3778013 : Nat := 4983230072969 + 3 ^ 40 * 3778013 * 2
def baseEnd_3778013 : Nat := 1293291058623221493641827

theorem tailTrace_3778013 : CollatzResearch.WordTrace tailWord_3778013 prefixEnd_3778013 1293291058623221493641827 := by
  unfold tailWord_3778013
  simp only [CollatzResearch.WordTrace]
  refine ⟨137795454461911609095866693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91863636307941072730577795 137795454461911609095866693)
  ·
    refine ⟨25836647711608426705475005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 137795454461911609095866693 25836647711608426705475005)
    ·
      refine ⟨9688742891853160014553127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25836647711608426705475005 9688742891853160014553127)
      ·
        refine ⟨14533114337779740021829691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9688742891853160014553127 14533114337779740021829691)
        ·
          refine ⟨21799671506669610032744537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14533114337779740021829691 21799671506669610032744537)
          ·
            refine ⟨16349753630002207524558403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21799671506669610032744537 16349753630002207524558403)
            ·
              refine ⟨24524630445003311286837605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16349753630002207524558403 24524630445003311286837605)
              ·
                refine ⟨4598368208438120866282051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24524630445003311286837605 4598368208438120866282051)
                ·
                  refine ⟨6897552312657181299423077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4598368208438120866282051 6897552312657181299423077)
                  ·
                    refine ⟨1293291058623221493641827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6897552312657181299423077 1293291058623221493641827)
                    ·
                      rfl

theorem cell22_3778013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 1, 4, 1, 4].length) (baseStart_3778013 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3778013 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3778013 prefixEnd_3778013 := by exact prefixLift 3778013
  have htrace : WordTrace (prefixWord ++ tailWord_3778013) baseStart_3778013 baseEnd_3778013 := by
    simpa [prefixWord, tailWord_3778013, baseEnd_3778013] using wordTrace_append hprefix tailTrace_3778013
  have hstable : (prefixWord ++ tailWord_3778013).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3778013).length < 2 ^ (prefixWord ++ tailWord_3778013).sum := by decide
  have hdescent : baseEnd_3778013 < baseStart_3778013 := by decide
  rcases family_descends (prefixWord ++ tailWord_3778013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3778045 : List Nat := [1, 4, 1, 1, 1, 5, 3, 2, 4]
def baseStart_3778045 : Nat := 118140960795 + 3778045 * 2 ^ 59
def prefixEnd_3778045 : Nat := 4983230072969 + 3 ^ 40 * 3778045 * 2
def baseEnd_3778045 : Nat := 431100670959061358947243

theorem tailTrace_3778045 : CollatzResearch.WordTrace tailWord_3778045 prefixEnd_3778045 431100670959061358947243 := by
  unfold tailWord_3778045
  simp only [CollatzResearch.WordTrace]
  refine ⟨137796621597795678561031589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91864414398530452374021059 137796621597795678561031589)
  ·
    refine ⟨25836866549586689730193423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 137796621597795678561031589 25836866549586689730193423)
    ·
      refine ⟨38755299824380034595290135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25836866549586689730193423 38755299824380034595290135)
      ·
        refine ⟨58132949736570051892935203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38755299824380034595290135 58132949736570051892935203)
        ·
          refine ⟨87199424604855077839402805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58132949736570051892935203 87199424604855077839402805)
          ·
            refine ⟨8174946056705163547444013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 87199424604855077839402805 8174946056705163547444013)
            ·
              refine ⟨3065604771264436330291505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8174946056705163547444013 3065604771264436330291505)
              ·
                refine ⟨2299203578448327247718629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3065604771264436330291505 2299203578448327247718629)
                ·
                  refine ⟨431100670959061358947243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2299203578448327247718629 431100670959061358947243)
                  ·
                    rfl

theorem cell22_3778045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 3, 2, 4].length) (baseStart_3778045 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3778045 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3778045 prefixEnd_3778045 := by exact prefixLift 3778045
  have htrace : WordTrace (prefixWord ++ tailWord_3778045) baseStart_3778045 baseEnd_3778045 := by
    simpa [prefixWord, tailWord_3778045, baseEnd_3778045] using wordTrace_append hprefix tailTrace_3778045
  have hstable : (prefixWord ++ tailWord_3778045).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3778045).length < 2 ^ (prefixWord ++ tailWord_3778045).sum := by decide
  have hdescent : baseEnd_3778045 < baseStart_3778045 := by decide
  rcases family_descends (prefixWord ++ tailWord_3778045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3778060 : List Nat := [2, 2, 1, 2, 5, 1, 1, 3, 2, 3]
def baseStart_3778060 : Nat := 118140960795 + 3778060 * 2 ^ 59
def prefixEnd_3778060 : Nat := 4983230072969 + 3 ^ 40 * 3778060 * 2
def baseEnd_3778060 : Nat := 1293307147683729037716683

theorem tailTrace_3778060 : CollatzResearch.WordTrace tailWord_3778060 prefixEnd_3778060 1293307147683729037716683 := by
  unfold tailWord_3778060
  simp only [CollatzResearch.WordTrace]
  refine ⟨68898584346370668061413817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91864779128494224081885089 68898584346370668061413817)
  ·
    refine ⟨51673938259778001046060363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68898584346370668061413817 51673938259778001046060363)
    ·
      refine ⟨77510907389667001569090545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51673938259778001046060363 77510907389667001569090545)
      ·
        refine ⟨58133180542250251176817909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77510907389667001569090545 58133180542250251176817909)
        ·
          refine ⟨5449985675835961047826679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 58133180542250251176817909 5449985675835961047826679)
          ·
            refine ⟨8174978513753941571740019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5449985675835961047826679 8174978513753941571740019)
            ·
              refine ⟨12262467770630912357610029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8174978513753941571740019 12262467770630912357610029)
              ·
                refine ⟨4598425413986592134103761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12262467770630912357610029 4598425413986592134103761)
                ·
                  refine ⟨3448819060489944100577821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4598425413986592134103761 3448819060489944100577821)
                  ·
                    refine ⟨1293307147683729037716683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3448819060489944100577821 1293307147683729037716683)
                    ·
                      rfl

theorem cell22_3778060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 1, 3, 2, 3].length) (baseStart_3778060 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3778060 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3778060 prefixEnd_3778060 := by exact prefixLift 3778060
  have htrace : WordTrace (prefixWord ++ tailWord_3778060) baseStart_3778060 baseEnd_3778060 := by
    simpa [prefixWord, tailWord_3778060, baseEnd_3778060] using wordTrace_append hprefix tailTrace_3778060
  have hstable : (prefixWord ++ tailWord_3778060).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3778060).length < 2 ^ (prefixWord ++ tailWord_3778060).sum := by decide
  have hdescent : baseEnd_3778060 < baseStart_3778060 := by decide
  rcases family_descends (prefixWord ++ tailWord_3778060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3778161 : List Nat := [1, 2, 2, 2, 1, 1, 1, 4, 3, 5]
def baseStart_3778161 : Nat := 118140960795 + 3778161 * 2 ^ 59
def prefixEnd_3778161 : Nat := 4983230072969 + 3 ^ 40 * 3778161 * 2
def baseEnd_3778161 : Nat := 1293341722047798440941373

theorem tailTrace_3778161 : CollatzResearch.WordTrace tailWord_3778161 prefixEnd_3778161 1293341722047798440941373 := by
  unfold tailWord_3778161
  simp only [CollatzResearch.WordTrace]
  refine ⟨137800852465375430372254337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91867234976916953581502891 137800852465375430372254337)
  ·
    refine ⟨103350639349031572779190753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137800852465375430372254337 103350639349031572779190753)
    ·
      refine ⟨77512979511773679584393065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103350639349031572779190753 77512979511773679584393065)
      ·
        refine ⟨58134734633830259688294799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77512979511773679584393065 58134734633830259688294799)
        ·
          refine ⟨87202101950745389532442199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58134734633830259688294799 87202101950745389532442199)
          ·
            refine ⟨130803152926118084298663299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87202101950745389532442199 130803152926118084298663299)
            ·
              refine ⟨196204729389177126447994949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 130803152926118084298663299 196204729389177126447994949)
              ·
                refine ⟨36788386760470711208999053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 196204729389177126447994949 36788386760470711208999053)
                ·
                  refine ⟨13795645035176516703374645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36788386760470711208999053 13795645035176516703374645)
                  ·
                    refine ⟨1293341722047798440941373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13795645035176516703374645 1293341722047798440941373)
                    ·
                      rfl

theorem cell22_3778161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 4, 3, 5].length) (baseStart_3778161 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3778161 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3778161 prefixEnd_3778161 := by exact prefixLift 3778161
  have htrace : WordTrace (prefixWord ++ tailWord_3778161) baseStart_3778161 baseEnd_3778161 := by
    simpa [prefixWord, tailWord_3778161, baseEnd_3778161] using wordTrace_append hprefix tailTrace_3778161
  have hstable : (prefixWord ++ tailWord_3778161).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3778161).length < 2 ^ (prefixWord ++ tailWord_3778161).sum := by decide
  have hdescent : baseEnd_3778161 < baseStart_3778161 := by decide
  rcases family_descends (prefixWord ++ tailWord_3778161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3778176 : List Nat := [2, 1, 1, 2, 1, 4, 1, 1, 3, 6]
def baseStart_3778176 : Nat := 118140960795 + 3778176 * 2 ^ 59
def prefixEnd_3778176 : Nat := 4983230072969 + 3 ^ 40 * 3778176 * 2
def baseEnd_3778176 : Nat := 1293346856854343401816327

theorem tailTrace_3778176 : CollatzResearch.WordTrace tailWord_3778176 prefixEnd_3778176 1293346856854343401816327 := by
  unfold tailWord_3778176
  simp only [CollatzResearch.WordTrace]
  refine ⟨68900699780160543967025191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91867599706880725289366921 68900699780160543967025191)
  ·
    refine ⟨103351049670240815950537787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68900699780160543967025191 103351049670240815950537787)
    ·
      refine ⟨155026574505361223925806681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103351049670240815950537787 155026574505361223925806681)
      ·
        refine ⟨116269930879020917944355011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155026574505361223925806681 116269930879020917944355011)
        ·
          refine ⟨174404896318531376916532517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116269930879020917944355011 174404896318531376916532517)
          ·
            refine ⟨32700918059724633171849847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 174404896318531376916532517 32700918059724633171849847)
            ·
              refine ⟨49051377089586949757774771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32700918059724633171849847 49051377089586949757774771)
              ·
                refine ⟨73577065634380424636662157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49051377089586949757774771 73577065634380424636662157)
                ·
                  refine ⟨27591399612892659238748309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 73577065634380424636662157 27591399612892659238748309)
                  ·
                    refine ⟨1293346856854343401816327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27591399612892659238748309 1293346856854343401816327)
                    ·
                      rfl

theorem cell22_3778176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 1, 3, 6].length) (baseStart_3778176 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3778176 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3778176 prefixEnd_3778176 := by exact prefixLift 3778176
  have htrace : WordTrace (prefixWord ++ tailWord_3778176) baseStart_3778176 baseEnd_3778176 := by
    simpa [prefixWord, tailWord_3778176, baseEnd_3778176] using wordTrace_append hprefix tailTrace_3778176
  have hstable : (prefixWord ++ tailWord_3778176).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3778176).length < 2 ^ (prefixWord ++ tailWord_3778176).sum := by decide
  have hdescent : baseEnd_3778176 < baseStart_3778176 := by decide
  rcases family_descends (prefixWord ++ tailWord_3778176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3778208 : List Nat := [2, 1, 1, 4, 3, 3, 8]
def baseStart_3778208 : Nat := 118140960795 + 3778208 * 2 ^ 59
def prefixEnd_3778208 : Nat := 4983230072969 + 3 ^ 40 * 3778208 * 2
def baseEnd_3778208 : Nat := 47902141152159480926527

theorem tailTrace_3778208 : CollatzResearch.WordTrace tailWord_3778208 prefixEnd_3778208 47902141152159480926527 := by
  unfold tailWord_3778208
  simp only [CollatzResearch.WordTrace]
  refine ⟨68901283348102578699607639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91868377797470104932810185 68901283348102578699607639)
  ·
    refine ⟨103351925022153868049411459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68901283348102578699607639 103351925022153868049411459)
    ·
      refine ⟨155027887533230802074117189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103351925022153868049411459 155027887533230802074117189)
      ·
        refine ⟨29067728912480775388896973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 155027887533230802074117189 29067728912480775388896973)
        ·
          refine ⟨10900398342180290770836365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29067728912480775388896973 10900398342180290770836365)
          ·
            refine ⟨4087649378317609039063637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10900398342180290770836365 4087649378317609039063637)
            ·
              refine ⟨47902141152159480926527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4087649378317609039063637 47902141152159480926527)
              ·
                rfl

theorem cell22_3778208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 3, 8].length) (baseStart_3778208 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3778208 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3778208 prefixEnd_3778208 := by exact prefixLift 3778208
  have htrace : WordTrace (prefixWord ++ tailWord_3778208) baseStart_3778208 baseEnd_3778208 := by
    simpa [prefixWord, tailWord_3778208, baseEnd_3778208] using wordTrace_append hprefix tailTrace_3778208
  have hstable : (prefixWord ++ tailWord_3778208).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3778208).length < 2 ^ (prefixWord ++ tailWord_3778208).sum := by decide
  have hdescent : baseEnd_3778208 < baseStart_3778208 := by decide
  rcases family_descends (prefixWord ++ tailWord_3778208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3778283 : List Nat := [1, 1, 1, 1, 2, 4, 3, 2, 3, 4]
def baseStart_3778283 : Nat := 118140960795 + 3778283 * 2 ^ 59
def prefixEnd_3778283 : Nat := 4983230072969 + 3 ^ 40 * 3778283 * 2
def baseEnd_3778283 : Nat := 1293383485141030789390999

theorem tailTrace_3778283 : CollatzResearch.WordTrace tailWord_3778283 prefixEnd_3778283 1293383485141030789390999 := by
  unfold tailWord_3778283
  simp only [CollatzResearch.WordTrace]
  refine ⟨137805302170933445208195503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91870201447288963472130335 137805302170933445208195503)
  ·
    refine ⟨206707953256400167812293255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137805302170933445208195503 206707953256400167812293255)
    ·
      refine ⟨310061929884600251718439883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206707953256400167812293255 310061929884600251718439883)
      ·
        refine ⟨465092894826900377577659825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 310061929884600251718439883 465092894826900377577659825)
        ·
          refine ⟨348819671120175283183244869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 465092894826900377577659825 348819671120175283183244869)
          ·
            refine ⟨65403688335032865596858413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 348819671120175283183244869 65403688335032865596858413)
            ·
              refine ⟨24526383125637324598821905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65403688335032865596858413 24526383125637324598821905)
              ·
                refine ⟨18394787344227993449116429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24526383125637324598821905 18394787344227993449116429)
                ·
                  refine ⟨6898045254085497543418661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18394787344227993449116429 6898045254085497543418661)
                  ·
                    refine ⟨1293383485141030789390999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6898045254085497543418661 1293383485141030789390999)
                    ·
                      rfl

theorem cell22_3778283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 3, 2, 3, 4].length) (baseStart_3778283 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3778283 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3778283 prefixEnd_3778283 := by exact prefixLift 3778283
  have htrace : WordTrace (prefixWord ++ tailWord_3778283) baseStart_3778283 baseEnd_3778283 := by
    simpa [prefixWord, tailWord_3778283, baseEnd_3778283] using wordTrace_append hprefix tailTrace_3778283
  have hstable : (prefixWord ++ tailWord_3778283).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3778283).length < 2 ^ (prefixWord ++ tailWord_3778283).sum := by decide
  have hdescent : baseEnd_3778283 < baseStart_3778283 := by decide
  rcases family_descends (prefixWord ++ tailWord_3778283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3778285 : List Nat := [1, 5, 1, 2, 1, 3, 1, 1, 2, 5]
def baseStart_3778285 : Nat := 118140960795 + 3778285 * 2 ^ 59
def prefixEnd_3778285 : Nat := 4983230072969 + 3 ^ 40 * 3778285 * 2
def baseEnd_3778285 : Nat := 1293384169781903450840993

theorem tailTrace_3778285 : CollatzResearch.WordTrace tailWord_3778285 prefixEnd_3778285 1293384169781903450840993 := by
  unfold tailWord_3778285
  simp only [CollatzResearch.WordTrace]
  refine ⟨137805375116926199549768309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91870250077950799699845539 137805375116926199549768309)
  ·
    refine ⟨12919253917211831207790779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 137805375116926199549768309 12919253917211831207790779)
    ·
      refine ⟨19378880875817746811686169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12919253917211831207790779 19378880875817746811686169)
      ·
        refine ⟨14534160656863310108764627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19378880875817746811686169 14534160656863310108764627)
        ·
          refine ⟨21801240985294965163146941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14534160656863310108764627 21801240985294965163146941)
          ·
            refine ⟨8175465369485611936180103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21801240985294965163146941 8175465369485611936180103)
            ·
              refine ⟨12263198054228417904270155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8175465369485611936180103 12263198054228417904270155)
              ·
                refine ⟨18394797081342626856405233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12263198054228417904270155 18394797081342626856405233)
                ·
                  refine ⟨13796097811006970142303925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18394797081342626856405233 13796097811006970142303925)
                  ·
                    refine ⟨1293384169781903450840993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13796097811006970142303925 1293384169781903450840993)
                    ·
                      rfl

theorem cell22_3778285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 1, 1, 2, 5].length) (baseStart_3778285 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3778285 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3778285 prefixEnd_3778285 := by exact prefixLift 3778285
  have htrace : WordTrace (prefixWord ++ tailWord_3778285) baseStart_3778285 baseEnd_3778285 := by
    simpa [prefixWord, tailWord_3778285, baseEnd_3778285] using wordTrace_append hprefix tailTrace_3778285
  have hstable : (prefixWord ++ tailWord_3778285).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3778285).length < 2 ^ (prefixWord ++ tailWord_3778285).sum := by decide
  have hdescent : baseEnd_3778285 < baseStart_3778285 := by decide
  rcases family_descends (prefixWord ++ tailWord_3778285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3778300 : List Nat := [2, 2, 2, 1, 3, 1, 2, 4, 1, 4]
def baseStart_3778300 : Nat := 118140960795 + 3778300 * 2 ^ 59
def prefixEnd_3778300 : Nat := 4983230072969 + 3 ^ 40 * 3778300 * 2
def baseEnd_3778300 : Nat := 1293389304588448411715947

theorem tailTrace_3778300 : CollatzResearch.WordTrace tailWord_3778300 prefixEnd_3778300 1293389304588448411715947 := by
  unfold tailWord_3778300
  simp only [CollatzResearch.WordTrace]
  refine ⟨68902961105935928555782177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91870614807914571407709569 68902961105935928555782177)
  ·
    refine ⟨51677220829451946416836633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68902961105935928555782177 51677220829451946416836633)
    ·
      refine ⟨38757915622088959812627475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51677220829451946416836633 38757915622088959812627475)
      ·
        refine ⟨58136873433133439718941213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38757915622088959812627475 58136873433133439718941213)
        ·
          refine ⟨21801327537425039894602955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58136873433133439718941213 21801327537425039894602955)
          ·
            refine ⟨32701991306137559841904433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21801327537425039894602955 32701991306137559841904433)
            ·
              refine ⟨24526493479603169881428325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32701991306137559841904433 24526493479603169881428325)
              ·
                refine ⟨4598717527425594352767811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24526493479603169881428325 4598717527425594352767811)
                ·
                  refine ⟨6898076291138391529151717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4598717527425594352767811 6898076291138391529151717)
                  ·
                    refine ⟨1293389304588448411715947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6898076291138391529151717 1293389304588448411715947)
                    ·
                      rfl

theorem cell22_3778300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 2, 4, 1, 4].length) (baseStart_3778300 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3778300 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3778300 prefixEnd_3778300 := by exact prefixLift 3778300
  have htrace : WordTrace (prefixWord ++ tailWord_3778300) baseStart_3778300 baseEnd_3778300 := by
    simpa [prefixWord, tailWord_3778300, baseEnd_3778300] using wordTrace_append hprefix tailTrace_3778300
  have hstable : (prefixWord ++ tailWord_3778300).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3778300).length < 2 ^ (prefixWord ++ tailWord_3778300).sum := by decide
  have hdescent : baseEnd_3778300 < baseStart_3778300 := by decide
  rcases family_descends (prefixWord ++ tailWord_3778300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3778315 : List Nat := [1, 1, 1, 1, 5, 1, 3, 5, 4]
def baseStart_3778315 : Nat := 118140960795 + 3778315 * 2 ^ 59
def prefixEnd_3778315 : Nat := 4983230072969 + 3 ^ 40 * 3778315 * 2
def baseEnd_3778315 : Nat := 431131479798331124196967

theorem tailTrace_3778315 : CollatzResearch.WordTrace tailWord_3778315 prefixEnd_3778315 431131479798331124196967 := by
  unfold tailWord_3778315
  simp only [CollatzResearch.WordTrace]
  refine ⟨137806469306817514673360399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91870979537878343115573599 137806469306817514673360399)
  ·
    refine ⟨206709703960226272010040599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137806469306817514673360399 206709703960226272010040599)
    ·
      refine ⟨310064555940339408015060899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206709703960226272010040599 310064555940339408015060899)
      ·
        refine ⟨465096833910509112022591349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 310064555940339408015060899 465096833910509112022591349)
        ·
          refine ⟨43602828179110229252117939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 465096833910509112022591349 43602828179110229252117939)
          ·
            refine ⟨65404242268665343878176909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43602828179110229252117939 65404242268665343878176909)
            ·
              refine ⟨24526590850749503954316341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65404242268665343878176909 24526590850749503954316341)
              ·
                refine ⟨2299367892257765995717157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24526590850749503954316341 2299367892257765995717157)
                ·
                  refine ⟨431131479798331124196967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2299367892257765995717157 431131479798331124196967)
                  ·
                    rfl

theorem cell22_3778315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 3, 5, 4].length) (baseStart_3778315 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3778315 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3778315 prefixEnd_3778315 := by exact prefixLift 3778315
  have htrace : WordTrace (prefixWord ++ tailWord_3778315) baseStart_3778315 baseEnd_3778315 := by
    simpa [prefixWord, tailWord_3778315, baseEnd_3778315] using wordTrace_append hprefix tailTrace_3778315
  have hstable : (prefixWord ++ tailWord_3778315).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3778315).length < 2 ^ (prefixWord ++ tailWord_3778315).sum := by decide
  have hdescent : baseEnd_3778315 < baseStart_3778315 := by decide
  rcases family_descends (prefixWord ++ tailWord_3778315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3778360 : List Nat := [2, 1, 2, 1, 3, 3, 4, 6]
def baseStart_3778360 : Nat := 118140960795 + 3778360 * 2 ^ 59
def prefixEnd_3778360 : Nat := 4983230072969 + 3 ^ 40 * 3778360 * 2
def baseEnd_3778360 : Nat := 143712204868292028357307

theorem tailTrace_3778360 : CollatzResearch.WordTrace tailWord_3778360 prefixEnd_3778360 143712204868292028357307 := by
  unfold tailWord_3778360
  simp only [CollatzResearch.WordTrace]
  refine ⟨68904055295827243679374267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91872073727769658239165689 68904055295827243679374267)
  ·
    refine ⟨103356082943740865519061401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68904055295827243679374267 103356082943740865519061401)
    ·
      refine ⟨77517062207805649139296051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103356082943740865519061401 77517062207805649139296051)
      ·
        refine ⟨116275593311708473708944077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77517062207805649139296051 116275593311708473708944077)
        ·
          refine ⟨43603347491890677640854029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 116275593311708473708944077 43603347491890677640854029)
          ·
            refine ⟨16351255309459004115320261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43603347491890677640854029 16351255309459004115320261)
            ·
              refine ⟨3065860370523563271622549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16351255309459004115320261 3065860370523563271622549)
              ·
                refine ⟨143712204868292028357307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3065860370523563271622549 143712204868292028357307)
                ·
                  rfl

theorem cell22_3778360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 4, 6].length) (baseStart_3778360 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3778360 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3778360 prefixEnd_3778360 := by exact prefixLift 3778360
  have htrace : WordTrace (prefixWord ++ tailWord_3778360) baseStart_3778360 baseEnd_3778360 := by
    simpa [prefixWord, tailWord_3778360, baseEnd_3778360] using wordTrace_append hprefix tailTrace_3778360
  have hstable : (prefixWord ++ tailWord_3778360).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3778360).length < 2 ^ (prefixWord ++ tailWord_3778360).sum := by decide
  have hdescent : baseEnd_3778360 < baseStart_3778360 := by decide
  rcases family_descends (prefixWord ++ tailWord_3778360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3778375 : List Nat := [1, 1, 4, 1, 2, 1, 2, 2, 5, 3]
def baseStart_3778375 : Nat := 118140960795 + 3778375 * 2 ^ 59
def prefixEnd_3778375 : Nat := 4983230072969 + 3 ^ 40 * 3778375 * 2
def baseEnd_3778375 : Nat := 1293414978621173216090717

theorem tailTrace_3778375 : CollatzResearch.WordTrace tailWord_3778375 prefixEnd_3778375 1293414978621173216090717 := by
  unfold tailWord_3778375
  simp only [CollatzResearch.WordTrace]
  refine ⟨137808657686600144920544579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91872438457733429947029719 137808657686600144920544579)
  ·
    refine ⟨206712986529900217380816869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137808657686600144920544579 206712986529900217380816869)
    ·
      refine ⟨38758684974356290758903163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 206712986529900217380816869 38758684974356290758903163)
      ·
        refine ⟨58138027461534436138354745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38758684974356290758903163 58138027461534436138354745)
        ·
          refine ⟨43603520596150827103766059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58138027461534436138354745 43603520596150827103766059)
          ·
            refine ⟨65405280894226240655649089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43603520596150827103766059 65405280894226240655649089)
            ·
              refine ⟨49053960670669680491736817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65405280894226240655649089 49053960670669680491736817)
              ·
                refine ⟨36790470503002260368802613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49053960670669680491736817 36790470503002260368802613)
                ·
                  refine ⟨3449106609656461909575245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 36790470503002260368802613 3449106609656461909575245)
                  ·
                    refine ⟨1293414978621173216090717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3449106609656461909575245 1293414978621173216090717)
                    ·
                      rfl

theorem cell22_3778375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 2, 5, 3].length) (baseStart_3778375 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3778375 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3778375 prefixEnd_3778375 := by exact prefixLift 3778375
  have htrace : WordTrace (prefixWord ++ tailWord_3778375) baseStart_3778375 baseEnd_3778375 := by
    simpa [prefixWord, tailWord_3778375, baseEnd_3778375] using wordTrace_append hprefix tailTrace_3778375
  have hstable : (prefixWord ++ tailWord_3778375).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3778375).length < 2 ^ (prefixWord ++ tailWord_3778375).sum := by decide
  have hdescent : baseEnd_3778375 < baseStart_3778375 := by decide
  rcases family_descends (prefixWord ++ tailWord_3778375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3778452 : List Nat := [2, 4, 2, 1, 1, 2, 1, 2, 3, 4]
def baseStart_3778452 : Nat := 118140960795 + 3778452 * 2 ^ 59
def prefixEnd_3778452 : Nat := 4983230072969 + 3 ^ 40 * 3778452 * 2
def baseEnd_3778452 : Nat := 1293441337294770681915481

theorem tailTrace_3778452 : CollatzResearch.WordTrace tailWord_3778452 prefixEnd_3778452 1293441337294770681915481 := by
  unfold tailWord_3778452
  simp only [CollatzResearch.WordTrace]
  refine ⟨68905733053660593535548805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91874310738214124714065073 68905733053660593535548805)
  ·
    refine ⟨12919824947561361287915401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 68905733053660593535548805 12919824947561361287915401)
    ·
      refine ⟨9689868710671020965936551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12919824947561361287915401 9689868710671020965936551)
      ·
        refine ⟨14534803066006531448904827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9689868710671020965936551 14534803066006531448904827)
        ·
          refine ⟨21802204599009797173357241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14534803066006531448904827 21802204599009797173357241)
          ·
            refine ⟨16351653449257347880017931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21802204599009797173357241 16351653449257347880017931)
            ·
              refine ⟨24527480173886021820026897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16351653449257347880017931 24527480173886021820026897)
              ·
                refine ⟨18395610130414516365020173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24527480173886021820026897 18395610130414516365020173)
                ·
                  refine ⟨6898353798905443636882565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18395610130414516365020173 6898353798905443636882565)
                  ·
                    refine ⟨1293441337294770681915481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6898353798905443636882565 1293441337294770681915481)
                    ·
                      rfl

theorem cell22_3778452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 1, 2, 3, 4].length) (baseStart_3778452 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3778452 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3778452 prefixEnd_3778452 := by exact prefixLift 3778452
  have htrace : WordTrace (prefixWord ++ tailWord_3778452) baseStart_3778452 baseEnd_3778452 := by
    simpa [prefixWord, tailWord_3778452, baseEnd_3778452] using wordTrace_append hprefix tailTrace_3778452
  have hstable : (prefixWord ++ tailWord_3778452).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3778452).length < 2 ^ (prefixWord ++ tailWord_3778452).sum := by decide
  have hdescent : baseEnd_3778452 < baseStart_3778452 := by decide
  rcases family_descends (prefixWord ++ tailWord_3778452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3778516 : List Nat := [2, 4, 1, 2, 1, 1, 5, 1, 2, 3]
def baseStart_3778516 : Nat := 118140960795 + 3778516 * 2 ^ 59
def prefixEnd_3778516 : Nat := 4983230072969 + 3 ^ 40 * 3778516 * 2
def baseEnd_3778516 : Nat := 1293463245802695848315285

theorem tailTrace_3778516 : CollatzResearch.WordTrace tailWord_3778516 prefixEnd_3778516 1293463245802695848315285 := by
  unfold tailWord_3778516
  simp only [CollatzResearch.WordTrace]
  refine ⟨68906900189544663000713701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91875866919392884000951601 68906900189544663000713701)
  ·
    refine ⟨12920043785539624312633819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 68906900189544663000713701 12920043785539624312633819)
    ·
      refine ⟨19380065678309436468950729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12920043785539624312633819 19380065678309436468950729)
      ·
        refine ⟨14535049258732077351713047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19380065678309436468950729 14535049258732077351713047)
        ·
          refine ⟨21802573888098116027569571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14535049258732077351713047 21802573888098116027569571)
          ·
            refine ⟨32703860832147174041354357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21802573888098116027569571 32703860832147174041354357)
            ·
              refine ⟨3065986953013797566376971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 32703860832147174041354357 3065986953013797566376971)
              ·
                refine ⟨4598980429520696349565457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3065986953013797566376971 4598980429520696349565457)
                ·
                  refine ⟨3449235322140522262174093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4598980429520696349565457 3449235322140522262174093)
                  ·
                    refine ⟨1293463245802695848315285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3449235322140522262174093 1293463245802695848315285)
                    ·
                      rfl

theorem cell22_3778516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 5, 1, 2, 3].length) (baseStart_3778516 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3778516 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3778516 prefixEnd_3778516 := by exact prefixLift 3778516
  have htrace : WordTrace (prefixWord ++ tailWord_3778516) baseStart_3778516 baseEnd_3778516 := by
    simpa [prefixWord, tailWord_3778516, baseEnd_3778516] using wordTrace_append hprefix tailTrace_3778516
  have hstable : (prefixWord ++ tailWord_3778516).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3778516).length < 2 ^ (prefixWord ++ tailWord_3778516).sum := by decide
  have hdescent : baseEnd_3778516 < baseStart_3778516 := by decide
  rcases family_descends (prefixWord ++ tailWord_3778516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3778555 : List Nat := [1, 1, 1, 1, 1, 3, 4, 1, 4, 5]
def baseStart_3778555 : Nat := 118140960795 + 3778555 * 2 ^ 59
def prefixEnd_3778555 : Nat := 4983230072969 + 3 ^ 40 * 3778555 * 2
def baseEnd_3778555 : Nat := 1293476596299712746590165

theorem tailTrace_3778555 : CollatzResearch.WordTrace tailWord_3778555 prefixEnd_3778555 1293476596299712746590165 := by
  unfold tailWord_3778555
  simp only [CollatzResearch.WordTrace]
  refine ⟨137815222825948035662097119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91876815217298690441398079 137815222825948035662097119)
  ·
    refine ⟨206722834238922053493145679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137815222825948035662097119 206722834238922053493145679)
    ·
      refine ⟨310084251358383080239718519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206722834238922053493145679 310084251358383080239718519)
      ·
        refine ⟨465126377037574620359577779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 310084251358383080239718519 465126377037574620359577779)
        ·
          refine ⟨697689565556361930539366669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 465126377037574620359577779 697689565556361930539366669)
          ·
            refine ⟨261633587083635723952262501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 697689565556361930539366669 261633587083635723952262501)
            ·
              refine ⟨49056297578181698241049219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 261633587083635723952262501 49056297578181698241049219)
              ·
                refine ⟨73584446367272547361573829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49056297578181698241049219 73584446367272547361573829)
                ·
                  refine ⟨13797083693863602630295093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 73584446367272547361573829 13797083693863602630295093)
                  ·
                    refine ⟨1293476596299712746590165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13797083693863602630295093 1293476596299712746590165)
                    ·
                      rfl

theorem cell22_3778555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 1, 4, 5].length) (baseStart_3778555 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3778555 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3778555 prefixEnd_3778555 := by exact prefixLift 3778555
  have htrace : WordTrace (prefixWord ++ tailWord_3778555) baseStart_3778555 baseEnd_3778555 := by
    simpa [prefixWord, tailWord_3778555, baseEnd_3778555] using wordTrace_append hprefix tailTrace_3778555
  have hstable : (prefixWord ++ tailWord_3778555).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3778555).length < 2 ^ (prefixWord ++ tailWord_3778555).sum := by decide
  have hdescent : baseEnd_3778555 < baseStart_3778555 := by decide
  rcases family_descends (prefixWord ++ tailWord_3778555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3778585 : List Nat := [1, 2, 1, 2, 1, 1, 3, 3, 8]
def baseStart_3778585 : Nat := 118140960795 + 3778585 * 2 ^ 59
def prefixEnd_3778585 : Nat := 4983230072969 + 3 ^ 40 * 3778585 * 2
def baseEnd_3778585 : Nat := 431162288637600889446691

theorem tailTrace_3778585 : CollatzResearch.WordTrace tailWord_3778585 prefixEnd_3778585 431162288637600889446691 := by
  unfold tailWord_3778585
  simp only [CollatzResearch.WordTrace]
  refine ⟨137816317015839350785689209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91877544677226233857126139 137816317015839350785689209)
  ·
    refine ⟨103362237761879513089266907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137816317015839350785689209 103362237761879513089266907)
    ·
      refine ⟨155043356642819269633900361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103362237761879513089266907 155043356642819269633900361)
      ·
        refine ⟨116282517482114452225425271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155043356642819269633900361 116282517482114452225425271)
        ·
          refine ⟨174423776223171678338137907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116282517482114452225425271 174423776223171678338137907)
          ·
            refine ⟨261635664334757517507206861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 174423776223171678338137907 261635664334757517507206861)
            ·
              refine ⟨98113374125534069065202573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 261635664334757517507206861 98113374125534069065202573)
              ·
                refine ⟨36792515297075275899450965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 98113374125534069065202573 36792515297075275899450965)
                ·
                  refine ⟨431162288637600889446691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 36792515297075275899450965 431162288637600889446691)
                  ·
                    rfl

theorem cell22_3778585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 3, 8].length) (baseStart_3778585 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3778585 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3778585 prefixEnd_3778585 := by exact prefixLift 3778585
  have htrace : WordTrace (prefixWord ++ tailWord_3778585) baseStart_3778585 baseEnd_3778585 := by
    simpa [prefixWord, tailWord_3778585, baseEnd_3778585] using wordTrace_append hprefix tailTrace_3778585
  have hstable : (prefixWord ++ tailWord_3778585).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3778585).length < 2 ^ (prefixWord ++ tailWord_3778585).sum := by decide
  have hdescent : baseEnd_3778585 < baseStart_3778585 := by decide
  rcases family_descends (prefixWord ++ tailWord_3778585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3778587 : List Nat := [1, 1, 1, 1, 1, 1, 3, 8, 1, 4]
def baseStart_3778587 : Nat := 118140960795 + 3778587 * 2 ^ 59
def prefixEnd_3778587 : Nat := 4983230072969 + 3 ^ 40 * 3778587 * 2
def baseEnd_3778587 : Nat := 1293487550553675329790067

theorem tailTrace_3778587 : CollatzResearch.WordTrace tailWord_3778587 prefixEnd_3778587 1293487550553675329790067 := by
  unfold tailWord_3778587
  simp only [CollatzResearch.WordTrace]
  refine ⟨137816389961832105127262015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91877593307888070084841343 137816389961832105127262015)
  ·
    refine ⟨206724584942748157690893023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137816389961832105127262015 206724584942748157690893023)
    ·
      refine ⟨310086877414122236536339535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206724584942748157690893023 310086877414122236536339535)
      ·
        refine ⟨465130316121183354804509303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 310086877414122236536339535 465130316121183354804509303)
        ·
          refine ⟨697695474181775032206763955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 465130316121183354804509303 697695474181775032206763955)
          ·
            refine ⟨1046543211272662548310145933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 697695474181775032206763955 1046543211272662548310145933)
            ·
              refine ⟨392453704227248455616304725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1046543211272662548310145933 392453704227248455616304725)
              ·
                refine ⟨4599066846413067839253571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 392453704227248455616304725 4599066846413067839253571)
                ·
                  refine ⟨6898600269619601758880357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4599066846413067839253571 6898600269619601758880357)
                  ·
                    refine ⟨1293487550553675329790067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6898600269619601758880357 1293487550553675329790067)
                    ·
                      rfl

theorem cell22_3778587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 8, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 8, 1, 4].length) (baseStart_3778587 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3778587 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3778587 prefixEnd_3778587 := by exact prefixLift 3778587
  have htrace : WordTrace (prefixWord ++ tailWord_3778587) baseStart_3778587 baseEnd_3778587 := by
    simpa [prefixWord, tailWord_3778587, baseEnd_3778587] using wordTrace_append hprefix tailTrace_3778587
  have hstable : (prefixWord ++ tailWord_3778587).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3778587).length < 2 ^ (prefixWord ++ tailWord_3778587).sum := by decide
  have hdescent : baseEnd_3778587 < baseStart_3778587 := by decide
  rcases family_descends (prefixWord ++ tailWord_3778587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3778612 : List Nat := [2, 5, 1, 2, 2, 2, 2, 2, 1, 3]
def baseStart_3778612 : Nat := 118140960795 + 3778612 * 2 ^ 59
def prefixEnd_3778612 : Nat := 4983230072969 + 3 ^ 40 * 3778612 * 2
def baseEnd_3778612 : Nat := 1293496108564583597914991

theorem tailTrace_3778612 : CollatzResearch.WordTrace tailWord_3778612 prefixEnd_3778612 1293496108564583597914991 := by
  unfold tailWord_3778612
  simp only [CollatzResearch.WordTrace]
  refine ⟨68908650893370767198461045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91878201191161022931281393 68908650893370767198461045)
  ·
    refine ⟨6460186021253509424855723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 68908650893370767198461045 6460186021253509424855723)
    ·
      refine ⟨9690279031880264137283585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6460186021253509424855723 9690279031880264137283585)
      ·
        refine ⟨7267709273910198102962689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9690279031880264137283585 7267709273910198102962689)
        ·
          refine ⟨5450781955432648577222017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7267709273910198102962689 5450781955432648577222017)
          ·
            refine ⟨4088086466574486432916513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5450781955432648577222017 4088086466574486432916513)
            ·
              refine ⟨3066064849930864824687385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4088086466574486432916513 3066064849930864824687385)
              ·
                refine ⟨2299548637448148618515539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3066064849930864824687385 2299548637448148618515539)
                ·
                  refine ⟨3449322956172222927773309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2299548637448148618515539 3449322956172222927773309)
                  ·
                    refine ⟨1293496108564583597914991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3449322956172222927773309 1293496108564583597914991)
                    ·
                      rfl

theorem cell22_3778612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 2, 2, 2, 1, 3].length) (baseStart_3778612 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3778612 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3778612 prefixEnd_3778612 := by exact prefixLift 3778612
  have htrace : WordTrace (prefixWord ++ tailWord_3778612) baseStart_3778612 baseEnd_3778612 := by
    simpa [prefixWord, tailWord_3778612, baseEnd_3778612] using wordTrace_append hprefix tailTrace_3778612
  have hstable : (prefixWord ++ tailWord_3778612).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3778612).length < 2 ^ (prefixWord ++ tailWord_3778612).sum := by decide
  have hdescent : baseEnd_3778612 < baseStart_3778612 := by decide
  rcases family_descends (prefixWord ++ tailWord_3778612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3778653 : List Nat := [1, 4, 4, 1, 1, 2, 2, 3, 4]
def baseStart_3778653 : Nat := 118140960795 + 3778653 * 2 ^ 59
def prefixEnd_3778653 : Nat := 4983230072969 + 3 ^ 40 * 3778653 * 2
def baseEnd_3778653 : Nat := 431170047900824385879955

theorem tailTrace_3778653 : CollatzResearch.WordTrace tailWord_3778653 prefixEnd_3778653 431170047900824385879955 := by
  unfold tailWord_3778653
  simp only [CollatzResearch.WordTrace]
  refine ⟨137818797179592998399164613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91879198119728665599443075 137818797179592998399164613)
  ·
    refine ⟨25841024471173687199843365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 137818797179592998399164613 25841024471173687199843365)
    ·
      refine ⟨4845192088345066349970631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25841024471173687199843365 4845192088345066349970631)
      ·
        refine ⟨7267788132517599524955947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4845192088345066349970631 7267788132517599524955947)
        ·
          refine ⟨10901682198776399287433921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7267788132517599524955947 10901682198776399287433921)
          ·
            refine ⟨8176261649082299465575441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10901682198776399287433921 8176261649082299465575441)
            ·
              refine ⟨6132196236811724599181581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8176261649082299465575441 6132196236811724599181581)
              ·
                refine ⟨2299573588804396724693093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6132196236811724599181581 2299573588804396724693093)
                ·
                  refine ⟨431170047900824385879955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2299573588804396724693093 431170047900824385879955)
                  ·
                    rfl

theorem cell22_3778653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 2, 3, 4].length) (baseStart_3778653 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3778653 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3778653 prefixEnd_3778653 := by exact prefixLift 3778653
  have htrace : WordTrace (prefixWord ++ tailWord_3778653) baseStart_3778653 baseEnd_3778653 := by
    simpa [prefixWord, tailWord_3778653, baseEnd_3778653] using wordTrace_append hprefix tailTrace_3778653
  have hstable : (prefixWord ++ tailWord_3778653).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3778653).length < 2 ^ (prefixWord ++ tailWord_3778653).sum := by decide
  have hdescent : baseEnd_3778653 < baseStart_3778653 := by decide
  rcases family_descends (prefixWord ++ tailWord_3778653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3778679 : List Nat := [1, 1, 3, 1, 1, 5, 1, 3, 3, 3]
def baseStart_3778679 : Nat := 118140960795 + 3778679 * 2 ^ 59
def prefixEnd_3778679 : Nat := 4983230072969 + 3 ^ 40 * 3778679 * 2
def baseEnd_3778679 : Nat := 1293519044033817756489785

theorem tailTrace_3778679 : CollatzResearch.WordTrace tailWord_3778679 prefixEnd_3778679 1293519044033817756489785 := by
  unfold tailWord_3778679
  simp only [CollatzResearch.WordTrace]
  refine ⟨137819745477498804839611091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91879830318332536559740727 137819745477498804839611091)
  ·
    refine ⟨206729618216248207259416637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137819745477498804839611091 206729618216248207259416637)
    ·
      refine ⟨77523606831093077722281239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 206729618216248207259416637 77523606831093077722281239)
      ·
        refine ⟨116285410246639616583421859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77523606831093077722281239 116285410246639616583421859)
        ·
          refine ⟨174428115369959424875132789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116285410246639616583421859 174428115369959424875132789)
          ·
            refine ⟨16352635815933696082043699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 174428115369959424875132789 16352635815933696082043699)
            ·
              refine ⟨24528953723900544123065549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16352635815933696082043699 24528953723900544123065549)
              ·
                refine ⟨9198357646462704046149581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24528953723900544123065549 9198357646462704046149581)
                ·
                  refine ⟨3449384117423514017306093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9198357646462704046149581 3449384117423514017306093)
                  ·
                    refine ⟨1293519044033817756489785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3449384117423514017306093 1293519044033817756489785)
                    ·
                      rfl

theorem cell22_3778679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 1, 3, 3, 3].length) (baseStart_3778679 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3778679 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3778679 prefixEnd_3778679 := by exact prefixLift 3778679
  have htrace : WordTrace (prefixWord ++ tailWord_3778679) baseStart_3778679 baseEnd_3778679 := by
    simpa [prefixWord, tailWord_3778679, baseEnd_3778679] using wordTrace_append hprefix tailTrace_3778679
  have hstable : (prefixWord ++ tailWord_3778679).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3778679).length < 2 ^ (prefixWord ++ tailWord_3778679).sum := by decide
  have hdescent : baseEnd_3778679 < baseStart_3778679 := by decide
  rcases family_descends (prefixWord ++ tailWord_3778679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3778696 : List Nat := [2, 1, 3, 4, 1, 1, 2, 2, 3, 3]
def baseStart_3778696 : Nat := 118140960795 + 3778696 * 2 ^ 59
def prefixEnd_3778696 : Nat := 4983230072969 + 3 ^ 40 * 3778696 * 2
def baseEnd_3778696 : Nat := 1293524863481235378814733

theorem tailTrace_3778696 : CollatzResearch.WordTrace tailWord_3778696 prefixEnd_3778696 1293524863481235378814733 := by
  unfold tailWord_3778696
  simp only [CollatzResearch.WordTrace]
  refine ⟨68910182759218608371489971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91880243678958144495319961 68910182759218608371489971)
  ·
    refine ⟨103365274138827912557234957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68910182759218608371489971 103365274138827912557234957)
    ·
      refine ⟨38761977802060467208963109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103365274138827912557234957 38761977802060467208963109)
      ·
        refine ⟨7267870837886337601680583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38761977802060467208963109 7267870837886337601680583)
        ·
          refine ⟨10901806256829506402520875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7267870837886337601680583 10901806256829506402520875)
          ·
            refine ⟨16352709385244259603781313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10901806256829506402520875 16352709385244259603781313)
            ·
              refine ⟨12264532038933194702835985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16352709385244259603781313 12264532038933194702835985)
              ·
                refine ⟨9198399029199896027126989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12264532038933194702835985 9198399029199896027126989)
                ·
                  refine ⟨3449399635949961010172621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9198399029199896027126989 3449399635949961010172621)
                  ·
                    refine ⟨1293524863481235378814733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3449399635949961010172621 1293524863481235378814733)
                    ·
                      rfl

theorem cell22_3778696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 2, 2, 3, 3].length) (baseStart_3778696 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3778696 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3778696 prefixEnd_3778696 := by exact prefixLift 3778696
  have htrace : WordTrace (prefixWord ++ tailWord_3778696) baseStart_3778696 baseEnd_3778696 := by
    simpa [prefixWord, tailWord_3778696, baseEnd_3778696] using wordTrace_append hprefix tailTrace_3778696
  have hstable : (prefixWord ++ tailWord_3778696).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3778696).length < 2 ^ (prefixWord ++ tailWord_3778696).sum := by decide
  have hdescent : baseEnd_3778696 < baseStart_3778696 := by decide
  rcases family_descends (prefixWord ++ tailWord_3778696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3778730 : List Nat := [3, 1, 5, 1, 2, 2, 1, 1, 3, 3]
def baseStart_3778730 : Nat := 118140960795 + 3778730 * 2 ^ 59
def prefixEnd_3778730 : Nat := 4983230072969 + 3 ^ 40 * 3778730 * 2
def baseEnd_3778730 : Nat := 1293536502376070623464629

theorem tailTrace_3778730 : CollatzResearch.WordTrace tailWord_3778730 prefixEnd_3778730 1293536502376070623464629 := by
  unfold tailWord_3778730
  simp only [CollatzResearch.WordTrace]
  refine ⟨34455401400078510137429411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91881070400209360366478429 34455401400078510137429411)
  ·
    refine ⟨51683102100117765206144117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34455401400078510137429411 51683102100117765206144117)
    ·
      refine ⟨4845290821886040488076011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 51683102100117765206144117 4845290821886040488076011)
      ·
        refine ⟨7267936232829060732114017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4845290821886040488076011 7267936232829060732114017)
        ·
          refine ⟨5450952174621795549085513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7267936232829060732114017 5450952174621795549085513)
          ·
            refine ⟨4088214130966346661814135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5450952174621795549085513 4088214130966346661814135)
            ·
              refine ⟨6132321196449519992721203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4088214130966346661814135 6132321196449519992721203)
              ·
                refine ⟨9198481794674279989081805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6132321196449519992721203 9198481794674279989081805)
                ·
                  refine ⟨3449430673002854995905677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9198481794674279989081805 3449430673002854995905677)
                  ·
                    refine ⟨1293536502376070623464629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3449430673002854995905677 1293536502376070623464629)
                    ·
                      rfl

theorem cell22_3778730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 2, 1, 1, 3, 3].length) (baseStart_3778730 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3778730 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3778730 prefixEnd_3778730 := by exact prefixLift 3778730
  have htrace : WordTrace (prefixWord ++ tailWord_3778730) baseStart_3778730 baseEnd_3778730 := by
    simpa [prefixWord, tailWord_3778730, baseEnd_3778730] using wordTrace_append hprefix tailTrace_3778730
  have hstable : (prefixWord ++ tailWord_3778730).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3778730).length < 2 ^ (prefixWord ++ tailWord_3778730).sum := by decide
  have hdescent : baseEnd_3778730 < baseStart_3778730 := by decide
  rcases family_descends (prefixWord ++ tailWord_3778730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3778756 : List Nat := [2, 3, 3, 1, 2, 2, 1, 1, 3, 4]
def baseStart_3778756 : Nat := 118140960795 + 3778756 * 2 ^ 59
def prefixEnd_3778756 : Nat := 4983230072969 + 3 ^ 40 * 3778756 * 2
def baseEnd_3778756 : Nat := 1293545402707415222314549

theorem tailTrace_3778756 : CollatzResearch.WordTrace tailWord_3778756 prefixEnd_3778756 1293545402707415222314549 := by
  unfold tailWord_3778756
  simp only [CollatzResearch.WordTrace]
  refine ⟨68911276949109923495082061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91881702598813231326776081 68911276949109923495082061)
  ·
    refine ⟨25841728855916221310655773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68911276949109923495082061 25841728855916221310655773)
    ·
      refine ⟨9690648320968582991495915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25841728855916221310655773 9690648320968582991495915)
      ·
        refine ⟨14535972481452874487243873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9690648320968582991495915 14535972481452874487243873)
        ·
          refine ⟨10901979361089655865432905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14535972481452874487243873 10901979361089655865432905)
          ·
            refine ⟨8176484520817241899074679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10901979361089655865432905 8176484520817241899074679)
            ·
              refine ⟨12264726781225862848612019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8176484520817241899074679 12264726781225862848612019)
              ·
                refine ⟨18397090171838794272918029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12264726781225862848612019 18397090171838794272918029)
                ·
                  refine ⟨6898908814439547852344261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18397090171838794272918029 6898908814439547852344261)
                  ·
                    refine ⟨1293545402707415222314549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6898908814439547852344261 1293545402707415222314549)
                    ·
                      rfl

theorem cell22_3778756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 1, 1, 3, 4].length) (baseStart_3778756 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3778756 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3778756 prefixEnd_3778756 := by exact prefixLift 3778756
  have htrace : WordTrace (prefixWord ++ tailWord_3778756) baseStart_3778756 baseEnd_3778756 := by
    simpa [prefixWord, tailWord_3778756, baseEnd_3778756] using wordTrace_append hprefix tailTrace_3778756
  have hstable : (prefixWord ++ tailWord_3778756).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3778756).length < 2 ^ (prefixWord ++ tailWord_3778756).sum := by decide
  have hdescent : baseEnd_3778756 < baseStart_3778756 := by decide
  rcases family_descends (prefixWord ++ tailWord_3778756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3778769 : List Nat := [1, 2, 2, 1, 2, 2, 2, 1, 6, 3]
def baseStart_3778769 : Nat := 118140960795 + 3778769 * 2 ^ 59
def prefixEnd_3778769 : Nat := 4983230072969 + 3 ^ 40 * 3778769 * 2
def baseEnd_3778769 : Nat := 1293549852873087521739509

theorem tailTrace_3778769 : CollatzResearch.WordTrace tailWord_3778769 prefixEnd_3778769 1293549852873087521739509 := by
  unfold tailWord_3778769
  simp only [CollatzResearch.WordTrace]
  refine ⟨137823028047172750210387361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91882018698115166806924907 137823028047172750210387361)
  ·
    refine ⟨103367271035379562657790521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137823028047172750210387361 103367271035379562657790521)
    ·
      refine ⟨77525453276534671993342891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103367271035379562657790521 77525453276534671993342891)
      ·
        refine ⟨116288179914802007990014337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77525453276534671993342891 116288179914802007990014337)
        ·
          refine ⟨87216134936101505992510753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116288179914802007990014337 87216134936101505992510753)
          ·
            refine ⟨65412101202076129494383065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87216134936101505992510753 65412101202076129494383065)
            ·
              refine ⟨49059075901557097120787299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65412101202076129494383065 49059075901557097120787299)
              ·
                refine ⟨73588613852335645681180949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49059075901557097120787299 73588613852335645681180949)
                ·
                  refine ⟨3449466274328233391305357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 73588613852335645681180949 3449466274328233391305357)
                  ·
                    refine ⟨1293549852873087521739509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3449466274328233391305357 1293549852873087521739509)
                    ·
                      rfl

theorem cell22_3778769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 1, 6, 3].length) (baseStart_3778769 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3778769 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3778769 prefixEnd_3778769 := by exact prefixLift 3778769
  have htrace : WordTrace (prefixWord ++ tailWord_3778769) baseStart_3778769 baseEnd_3778769 := by
    simpa [prefixWord, tailWord_3778769, baseEnd_3778769] using wordTrace_append hprefix tailTrace_3778769
  have hstable : (prefixWord ++ tailWord_3778769).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3778769).length < 2 ^ (prefixWord ++ tailWord_3778769).sum := by decide
  have hdescent : baseEnd_3778769 < baseStart_3778769 := by decide
  rcases family_descends (prefixWord ++ tailWord_3778769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3778782 : List Nat := [4, 18]
def baseStart_3778782 : Nat := 118140960795 + 3778782 * 2 ^ 59
def prefixEnd_3778782 : Nat := 4983230072969 + 3 ^ 40 * 3778782 * 2
def baseEnd_3778782 : Nat := 197158101362408142229

theorem tailTrace_3778782 : CollatzResearch.WordTrace tailWord_3778782 prefixEnd_3778782 197158101362408142229 := by
  unfold tailWord_3778782
  simp only [CollatzResearch.WordTrace]
  refine ⟨17227937774515706678826325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 91882334797417102287073733 17227937774515706678826325)
  ·
    refine ⟨197158101362408142229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 18 17227937774515706678826325 197158101362408142229)
    ·
      rfl

theorem cell22_3778782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 18].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 18].length) (baseStart_3778782 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3778782 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3778782 prefixEnd_3778782 := by exact prefixLift 3778782
  have htrace : WordTrace (prefixWord ++ tailWord_3778782) baseStart_3778782 baseEnd_3778782 := by
    simpa [prefixWord, tailWord_3778782, baseEnd_3778782] using wordTrace_append hprefix tailTrace_3778782
  have hstable : (prefixWord ++ tailWord_3778782).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3778782).length < 2 ^ (prefixWord ++ tailWord_3778782).sum := by decide
  have hdescent : baseEnd_3778782 < baseStart_3778782 := by decide
  rcases family_descends (prefixWord ++ tailWord_3778782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3778784 : List Nat := [2, 1, 1, 3, 1, 3, 1, 4, 2, 4]
def baseStart_3778784 : Nat := 118140960795 + 3778784 * 2 ^ 59
def prefixEnd_3778784 : Nat := 4983230072969 + 3 ^ 40 * 3778784 * 2
def baseEnd_3778784 : Nat := 1293554987679632482614463

theorem tailTrace_3778784 : CollatzResearch.WordTrace tailWord_3778784 prefixEnd_3778784 1293554987679632482614463 := by
  unfold tailWord_3778784
  simp only [CollatzResearch.WordTrace]
  refine ⟨68911787571059203886091703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91882383428078938514788937 68911787571059203886091703)
  ·
    refine ⟨103367681356588805829137555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68911787571059203886091703 103367681356588805829137555)
    ·
      refine ⟨155051522034883208743706333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103367681356588805829137555 155051522034883208743706333)
      ·
        refine ⟨58144320763081203278889875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 155051522034883208743706333 58144320763081203278889875)
        ·
          refine ⟨87216481144621804918334813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58144320763081203278889875 87216481144621804918334813)
          ·
            refine ⟨32706180429233176844375555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87216481144621804918334813 32706180429233176844375555)
            ·
              refine ⟨49059270643849765266563333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32706180429233176844375555 49059270643849765266563333)
              ·
                refine ⟨9198613245721830987480625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49059270643849765266563333 9198613245721830987480625)
                ·
                  refine ⟨6898959934291373240610469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9198613245721830987480625 6898959934291373240610469)
                  ·
                    refine ⟨1293554987679632482614463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6898959934291373240610469 1293554987679632482614463)
                    ·
                      rfl

theorem cell22_3778784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 4, 2, 4].length) (baseStart_3778784 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3778784 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3778784 prefixEnd_3778784 := by exact prefixLift 3778784
  have htrace : WordTrace (prefixWord ++ tailWord_3778784) baseStart_3778784 baseEnd_3778784 := by
    simpa [prefixWord, tailWord_3778784, baseEnd_3778784] using wordTrace_append hprefix tailTrace_3778784
  have hstable : (prefixWord ++ tailWord_3778784).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3778784).length < 2 ^ (prefixWord ++ tailWord_3778784).sum := by decide
  have hdescent : baseEnd_3778784 < baseStart_3778784 := by decide
  rcases family_descends (prefixWord ++ tailWord_3778784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3778799 : List Nat := [1, 1, 2, 1, 6, 1, 3, 7]
def baseStart_3778799 : Nat := 118140960795 + 3778799 * 2 ^ 59
def prefixEnd_3778799 : Nat := 4983230072969 + 3 ^ 40 * 3778799 * 2
def baseEnd_3778799 : Nat := 143728902498464160387713

theorem tailTrace_3778799 : CollatzResearch.WordTrace tailWord_3778799 prefixEnd_3778799 143728902498464160387713 := by
  unfold tailWord_3778799
  simp only [CollatzResearch.WordTrace]
  refine ⟨137824122237064065333979451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91882748158042710222652967 137824122237064065333979451)
  ·
    refine ⟨206736183355596098000969177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137824122237064065333979451 206736183355596098000969177)
    ·
      refine ⟨155052137516697073500726883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 206736183355596098000969177 155052137516697073500726883)
      ·
        refine ⟨232578206275045610251090325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155052137516697073500726883 232578206275045610251090325)
        ·
          refine ⟨10902103419142762980519859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 232578206275045610251090325 10902103419142762980519859)
          ·
            refine ⟨16353155128714144470779789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10902103419142762980519859 16353155128714144470779789)
            ·
              refine ⟨6132433173267804176542421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16353155128714144470779789 6132433173267804176542421)
              ·
                refine ⟨143728902498464160387713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6132433173267804176542421 143728902498464160387713)
                ·
                  rfl

theorem cell22_3778799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 3, 7].length) (baseStart_3778799 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3778799 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3778799 prefixEnd_3778799 := by exact prefixLift 3778799
  have htrace : WordTrace (prefixWord ++ tailWord_3778799) baseStart_3778799 baseEnd_3778799 := by
    simpa [prefixWord, tailWord_3778799, baseEnd_3778799] using wordTrace_append hprefix tailTrace_3778799
  have hstable : (prefixWord ++ tailWord_3778799).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3778799).length < 2 ^ (prefixWord ++ tailWord_3778799).sum := by decide
  have hdescent : baseEnd_3778799 < baseStart_3778799 := by decide
  rcases family_descends (prefixWord ++ tailWord_3778799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3778818 : List Nat := [3, 4, 1, 1, 2, 1, 3, 1, 2, 4]
def baseStart_3778818 : Nat := 118140960795 + 3778818 * 2 ^ 59
def prefixEnd_3778818 : Nat := 4983230072969 + 3 ^ 40 * 3778818 * 2
def baseEnd_3778818 : Nat := 1293566626574467727264359

theorem tailTrace_3778818 : CollatzResearch.WordTrace tailWord_3778818 prefixEnd_3778818 1293566626574467727264359 := by
  unfold tailWord_3778818
  simp only [CollatzResearch.WordTrace]
  refine ⟨34456203805998807894730277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91883210149330154385947405 34456203805998807894730277)
  ·
    refine ⟨6460538213624776480261927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34456203805998807894730277 6460538213624776480261927)
    ·
      refine ⟨9690807320437164720392891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6460538213624776480261927 9690807320437164720392891)
      ·
        refine ⟨14536210980655747080589337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9690807320437164720392891 14536210980655747080589337)
        ·
          refine ⟨10902158235491810310442003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14536210980655747080589337 10902158235491810310442003)
          ·
            refine ⟨16353237353237715465663005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10902158235491810310442003 16353237353237715465663005)
            ·
              refine ⟨6132464007464143299623627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16353237353237715465663005 6132464007464143299623627)
              ·
                refine ⟨9198696011196214949435441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6132464007464143299623627 9198696011196214949435441)
                ·
                  refine ⟨6899022008397161212076581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9198696011196214949435441 6899022008397161212076581)
                  ·
                    refine ⟨1293566626574467727264359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6899022008397161212076581 1293566626574467727264359)
                    ·
                      rfl

theorem cell22_3778818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 3, 1, 2, 4].length) (baseStart_3778818 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3778818 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3778818 prefixEnd_3778818 := by exact prefixLift 3778818
  have htrace : WordTrace (prefixWord ++ tailWord_3778818) baseStart_3778818 baseEnd_3778818 := by
    simpa [prefixWord, tailWord_3778818, baseEnd_3778818] using wordTrace_append hprefix tailTrace_3778818
  have hstable : (prefixWord ++ tailWord_3778818).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3778818).length < 2 ^ (prefixWord ++ tailWord_3778818).sum := by decide
  have hdescent : baseEnd_3778818 < baseStart_3778818 := by decide
  rcases family_descends (prefixWord ++ tailWord_3778818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3778848 : List Nat := [2, 1, 1, 5, 2, 2, 2, 1, 3, 3]
def baseStart_3778848 : Nat := 118140960795 + 3778848 * 2 ^ 59
def prefixEnd_3778848 : Nat := 4983230072969 + 3 ^ 40 * 3778848 * 2
def baseEnd_3778848 : Nat := 1293576896187557649014267

theorem tailTrace_3778848 : CollatzResearch.WordTrace tailWord_3778848 prefixEnd_3778848 1293576896187557649014267 := by
  unfold tailWord_3778848
  simp only [CollatzResearch.WordTrace]
  refine ⟨68912954706943273351256599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91883939609257697801675465 68912954706943273351256599)
  ·
    refine ⟨103369432060414910026884899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68912954706943273351256599 103369432060414910026884899)
    ·
      refine ⟨155054148090622365040327349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103369432060414910026884899 155054148090622365040327349)
      ·
        refine ⟨14536326383495846722530689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 155054148090622365040327349 14536326383495846722530689)
        ·
          refine ⟨10902244787621885041898017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14536326383495846722530689 10902244787621885041898017)
          ·
            refine ⟨8176683590716413781423513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10902244787621885041898017 8176683590716413781423513)
            ·
              refine ⟨6132512693037310336067635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8176683590716413781423513 6132512693037310336067635)
              ·
                refine ⟨9198769039555965504101453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6132512693037310336067635 9198769039555965504101453)
                ·
                  refine ⟨3449538389833487064038045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9198769039555965504101453 3449538389833487064038045)
                  ·
                    refine ⟨1293576896187557649014267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3449538389833487064038045 1293576896187557649014267)
                    ·
                      rfl

theorem cell22_3778848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 2, 1, 3, 3].length) (baseStart_3778848 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3778848 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3778848 prefixEnd_3778848 := by exact prefixLift 3778848
  have htrace : WordTrace (prefixWord ++ tailWord_3778848) baseStart_3778848 baseEnd_3778848 := by
    simpa [prefixWord, tailWord_3778848, baseEnd_3778848] using wordTrace_append hprefix tailTrace_3778848
  have hstable : (prefixWord ++ tailWord_3778848).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3778848).length < 2 ^ (prefixWord ++ tailWord_3778848).sum := by decide
  have hdescent : baseEnd_3778848 < baseStart_3778848 := by decide
  rcases family_descends (prefixWord ++ tailWord_3778848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
