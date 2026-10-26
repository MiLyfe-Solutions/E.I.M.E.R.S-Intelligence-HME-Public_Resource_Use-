import V185TrunkScan20Chunk055

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental

namespace V185TrunkScan20Incremental

def tailWord_339843 : List Nat := [1, 1, 1, 3, 4, 3, 1, 3, 3]
def baseStart_339843 : Nat := 118140960795 + 339843 * 2 ^ 59
def prefixEnd_339843 : Nat := 4983230072969 + 3 ^ 40 * 339843 * 2
def baseEnd_339843 : Nat := 155113605392016974577419

theorem tailTrace_339843 : CollatzResearch.WordTrace tailWord_339843 prefixEnd_339843 155113605392016974577419 := by
  unfold tailWord_339843
  simp only [CollatzResearch.WordTrace]
  refine ⟨12395092507814326408664183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8263395005209550939109455 12395092507814326408664183)
  ·
    refine ⟨18592638761721489612996275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12395092507814326408664183 18592638761721489612996275)
    ·
      refine ⟨27888958142582234419494413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18592638761721489612996275 27888958142582234419494413)
      ·
        refine ⟨10458359303468337907310405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27888958142582234419494413 10458359303468337907310405)
        ·
          refine ⟨1960942369400313357620701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10458359303468337907310405 1960942369400313357620701)
          ·
            refine ⟨735353388525117509107763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1960942369400313357620701 735353388525117509107763)
            ·
              refine ⟨1103030082787676263661645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 735353388525117509107763 1103030082787676263661645)
              ·
                refine ⟨413636281045378598873117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1103030082787676263661645 413636281045378598873117)
                ·
                  refine ⟨155113605392016974577419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 413636281045378598873117 155113605392016974577419)
                  ·
                    rfl

theorem cell20_339843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 1, 3, 3].length) (baseStart_339843 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_339843 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_339843 prefixEnd_339843 := by exact prefixLift 339843
  have htrace : WordTrace (prefixWord ++ tailWord_339843) baseStart_339843 baseEnd_339843 := by
    simpa [prefixWord, tailWord_339843, baseEnd_339843] using wordTrace_append hprefix tailTrace_339843
  have hstable : (prefixWord ++ tailWord_339843).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_339843).length < 2 ^ (prefixWord ++ tailWord_339843).sum := by decide
  have hdescent : baseEnd_339843 < baseStart_339843 := by decide
  rcases family_descends (prefixWord ++ tailWord_339843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_339874 : List Nat := [3, 3, 1, 2, 4, 7]
def baseStart_339874 : Nat := 118140960795 + 339874 * 2 ^ 59
def prefixEnd_339874 : Nat := 4983230072969 + 3 ^ 40 * 339874 * 2
def baseEnd_339874 : Nat := 5745472393952542390517

theorem tailTrace_339874 : CollatzResearch.WordTrace tailWord_339874 prefixEnd_339874 5745472393952542390517 := by
  unfold tailWord_339874
  simp only [CollatzResearch.WordTrace]
  refine ⟨3099055792675504675760669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8264148780468012468695117 3099055792675504675760669)
  ·
    refine ⟨1162145922253314253410251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3099055792675504675760669 1162145922253314253410251)
    ·
      refine ⟨1743218883379971380115377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1162145922253314253410251 1743218883379971380115377)
      ·
        refine ⟨1307414162534978535086533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1743218883379971380115377 1307414162534978535086533)
        ·
          refine ⟨245140155475308475328725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1307414162534978535086533 245140155475308475328725)
          ·
            refine ⟨5745472393952542390517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 245140155475308475328725 5745472393952542390517)
            ·
              rfl

theorem cell20_339874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 4, 7].length) (baseStart_339874 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_339874 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_339874 prefixEnd_339874 := by exact prefixLift 339874
  have htrace : WordTrace (prefixWord ++ tailWord_339874) baseStart_339874 baseEnd_339874 := by
    simpa [prefixWord, tailWord_339874, baseEnd_339874] using wordTrace_append hprefix tailTrace_339874
  have hstable : (prefixWord ++ tailWord_339874).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_339874).length < 2 ^ (prefixWord ++ tailWord_339874).sum := by decide
  have hdescent : baseEnd_339874 < baseStart_339874 := by decide
  rcases family_descends (prefixWord ++ tailWord_339874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_339912 : List Nat := [2, 1, 3, 1, 4, 2, 3, 4]
def baseStart_339912 : Nat := 118140960795 + 339912 * 2 ^ 59
def prefixEnd_339912 : Nat := 4983230072969 + 3 ^ 40 * 339912 * 2
def baseEnd_339912 : Nat := 51715032957386467092379

theorem tailTrace_339912 : CollatzResearch.WordTrace tailWord_339912 prefixEnd_339912 51715032957386467092379 := by
  unfold tailWord_339912
  simp only [CollatzResearch.WordTrace]
  refine ⟨6198804572282175596462995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8265072763042900795283993 6198804572282175596462995)
  ·
    refine ⟨9298206858423263394694493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6198804572282175596462995 9298206858423263394694493)
    ·
      refine ⟨3486827571908723773010435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9298206858423263394694493 3486827571908723773010435)
      ·
        refine ⟨5230241357863085659515653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3486827571908723773010435 5230241357863085659515653)
        ·
          refine ⟨980670254599328561159185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5230241357863085659515653 980670254599328561159185)
          ·
            refine ⟨735502690949496420869389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 980670254599328561159185 735502690949496420869389)
            ·
              refine ⟨275813509106061157826021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 735502690949496420869389 275813509106061157826021)
              ·
                refine ⟨51715032957386467092379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 275813509106061157826021 51715032957386467092379)
                ·
                  rfl

theorem cell20_339912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 3, 4].length) (baseStart_339912 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_339912 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_339912 prefixEnd_339912 := by exact prefixLift 339912
  have htrace : WordTrace (prefixWord ++ tailWord_339912) baseStart_339912 baseEnd_339912 := by
    simpa [prefixWord, tailWord_339912, baseEnd_339912] using wordTrace_append hprefix tailTrace_339912
  have hstable : (prefixWord ++ tailWord_339912).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_339912).length < 2 ^ (prefixWord ++ tailWord_339912).sum := by decide
  have hdescent : baseEnd_339912 < baseStart_339912 := by decide
  rcases family_descends (prefixWord ++ tailWord_339912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_339940 : List Nat := [2, 3, 1, 1, 1, 1, 5, 1, 5]
def baseStart_339940 : Nat := 118140960795 + 339940 * 2 ^ 59
def prefixEnd_339940 : Nat := 4983230072969 + 3 ^ 40 * 339940 * 2
def baseEnd_339940 : Nat := 155157878835115748343689

theorem tailTrace_339940 : CollatzResearch.WordTrace tailWord_339940 prefixEnd_339940 155157878835115748343689 := by
  unfold tailWord_339940
  simp only [CollatzResearch.WordTrace]
  refine ⟨6199315194231455987472637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8265753592308607983296849 6199315194231455987472637)
  ·
    refine ⟨2324743197836795995302239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6199315194231455987472637 2324743197836795995302239)
    ·
      refine ⟨3487114796755193992953359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2324743197836795995302239 3487114796755193992953359)
      ·
        refine ⟨5230672195132790989430039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3487114796755193992953359 5230672195132790989430039)
        ·
          refine ⟨7846008292699186484145059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5230672195132790989430039 7846008292699186484145059)
          ·
            refine ⟨11769012439048779726217589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7846008292699186484145059 11769012439048779726217589)
            ·
              refine ⟨1103344916160823099332899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11769012439048779726217589 1103344916160823099332899)
              ·
                refine ⟨1655017374241234648999349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1103344916160823099332899 1655017374241234648999349)
                ·
                  refine ⟨155157878835115748343689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1655017374241234648999349 155157878835115748343689)
                  ·
                    rfl

theorem cell20_339940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 5, 1, 5].length) (baseStart_339940 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_339940 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_339940 prefixEnd_339940 := by exact prefixLift 339940
  have htrace : WordTrace (prefixWord ++ tailWord_339940) baseStart_339940 baseEnd_339940 := by
    simpa [prefixWord, tailWord_339940, baseEnd_339940] using wordTrace_append hprefix tailTrace_339940
  have hstable : (prefixWord ++ tailWord_339940).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_339940).length < 2 ^ (prefixWord ++ tailWord_339940).sum := by decide
  have hdescent : baseEnd_339940 < baseStart_339940 := by decide
  rcases family_descends (prefixWord ++ tailWord_339940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_339943 : List Nat := [1, 1, 5, 2, 3, 1, 2, 1, 4]
def baseStart_339943 : Nat := 118140960795 + 339943 * 2 ^ 59
def prefixEnd_339943 : Nat := 4983230072969 + 3 ^ 40 * 339943 * 2
def baseEnd_339943 : Nat := 155159248116861071243677

theorem tailTrace_339943 : CollatzResearch.WordTrace tailWord_339943 prefixEnd_339943 155159248116861071243677 := by
  unfold tailWord_339943
  simp only [CollatzResearch.WordTrace]
  refine ⟨12398739807452043487304483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8265826538301362324869655 12398739807452043487304483)
  ·
    refine ⟨18598109711178065230956725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12398739807452043487304483 18598109711178065230956725)
    ·
      refine ⟨1743572785422943615402193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 18598109711178065230956725 1743572785422943615402193)
      ·
        refine ⟨1307679589067207711551645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1743572785422943615402193 1307679589067207711551645)
        ·
          refine ⟨490379845900202891831867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1307679589067207711551645 490379845900202891831867)
          ·
            refine ⟨735569768850304337747801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 490379845900202891831867 735569768850304337747801)
            ·
              refine ⟨551677326637728253310851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 735569768850304337747801 551677326637728253310851)
              ·
                refine ⟨827515989956592379966277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 551677326637728253310851 827515989956592379966277)
                ·
                  refine ⟨155159248116861071243677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 827515989956592379966277 155159248116861071243677)
                  ·
                    rfl

theorem cell20_339943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 2, 1, 4].length) (baseStart_339943 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_339943 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_339943 prefixEnd_339943 := by exact prefixLift 339943
  have htrace : WordTrace (prefixWord ++ tailWord_339943) baseStart_339943 baseEnd_339943 := by
    simpa [prefixWord, tailWord_339943, baseEnd_339943] using wordTrace_append hprefix tailTrace_339943
  have hstable : (prefixWord ++ tailWord_339943).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_339943).length < 2 ^ (prefixWord ++ tailWord_339943).sum := by decide
  have hdescent : baseEnd_339943 < baseStart_339943 := by decide
  rcases family_descends (prefixWord ++ tailWord_339943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_340008 : List Nat := [2, 1, 5, 3, 1, 2, 2, 1, 3]
def baseStart_340008 : Nat := 118140960795 + 340008 * 2 ^ 59
def prefixEnd_340008 : Nat := 4983230072969 + 3 ^ 40 * 340008 * 2
def baseEnd_340008 : Nat := 155188915888009734076745

theorem tailTrace_340008 : CollatzResearch.WordTrace tailWord_340008 prefixEnd_340008 155188915888009734076745 := by
  unfold tailWord_340008
  simp only [CollatzResearch.WordTrace]
  refine ⟨6200555276108279794210339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8267407034811039725613785 6200555276108279794210339)
  ·
    refine ⟨9300832914162419691315509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6200555276108279794210339 9300832914162419691315509)
    ·
      refine ⟨871953085702726846060829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 9300832914162419691315509 871953085702726846060829)
      ·
        refine ⟨326982407138522567272811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 871953085702726846060829 326982407138522567272811)
        ·
          refine ⟨490473610707783850909217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 326982407138522567272811 490473610707783850909217)
          ·
            refine ⟨367855208030837888181913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 490473610707783850909217 367855208030837888181913)
            ·
              refine ⟨275891406023128416136435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 367855208030837888181913 275891406023128416136435)
              ·
                refine ⟨413837109034692624204653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 275891406023128416136435 413837109034692624204653)
                ·
                  refine ⟨155188915888009734076745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 413837109034692624204653 155188915888009734076745)
                  ·
                    rfl

theorem cell20_340008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 2, 2, 1, 3].length) (baseStart_340008 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_340008 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_340008 prefixEnd_340008 := by exact prefixLift 340008
  have htrace : WordTrace (prefixWord ++ tailWord_340008) baseStart_340008 baseEnd_340008 := by
    simpa [prefixWord, tailWord_340008, baseEnd_340008] using wordTrace_append hprefix tailTrace_340008
  have hstable : (prefixWord ++ tailWord_340008).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_340008).length < 2 ^ (prefixWord ++ tailWord_340008).sum := by decide
  have hdescent : baseEnd_340008 < baseStart_340008 := by decide
  rcases family_descends (prefixWord ++ tailWord_340008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_340023 : List Nat := [1, 1, 3, 1, 2, 2, 2, 4, 4]
def baseStart_340023 : Nat := 118140960795 + 340023 * 2 ^ 59
def prefixEnd_340023 : Nat := 4983230072969 + 3 ^ 40 * 340023 * 2
def baseEnd_340023 : Nat := 155195762296736348576683

theorem tailTrace_340023 : CollatzResearch.WordTrace tailWord_340023 prefixEnd_340023 155195762296736348576683 := by
  unfold tailWord_340023
  simp only [CollatzResearch.WordTrace]
  refine ⟨12401657647162217150216723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8267771764774811433477815 12401657647162217150216723)
  ·
    refine ⟨18602486470743325725325085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12401657647162217150216723 18602486470743325725325085)
    ·
      refine ⟨6975932426528747146996907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18602486470743325725325085 6975932426528747146996907)
      ·
        refine ⟨10463898639793120720495361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6975932426528747146996907 10463898639793120720495361)
        ·
          refine ⟨7847923979844840540371521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10463898639793120720495361 7847923979844840540371521)
          ·
            refine ⟨5885942984883630405278641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7847923979844840540371521 5885942984883630405278641)
            ·
              refine ⟨4414457238662722803958981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5885942984883630405278641 4414457238662722803958981)
              ·
                refine ⟨827710732249260525742309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4414457238662722803958981 827710732249260525742309)
                ·
                  refine ⟨155195762296736348576683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 827710732249260525742309 155195762296736348576683)
                  ·
                    rfl

theorem cell20_340023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 4, 4].length) (baseStart_340023 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_340023 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_340023 prefixEnd_340023 := by exact prefixLift 340023
  have htrace : WordTrace (prefixWord ++ tailWord_340023) baseStart_340023 baseEnd_340023 := by
    simpa [prefixWord, tailWord_340023, baseEnd_340023] using wordTrace_append hprefix tailTrace_340023
  have hstable : (prefixWord ++ tailWord_340023).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_340023).length < 2 ^ (prefixWord ++ tailWord_340023).sum := by decide
  have hdescent : baseEnd_340023 < baseStart_340023 := by decide
  rcases family_descends (prefixWord ++ tailWord_340023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_340050 : List Nat := [3, 2, 2, 1, 4, 1, 2, 2, 3]
def baseStart_340050 : Nat := 118140960795 + 340050 * 2 ^ 59
def prefixEnd_340050 : Nat := 4983230072969 + 3 ^ 40 * 340050 * 2
def baseEnd_340050 : Nat := 155208085832444254676573

theorem tailTrace_340050 : CollatzResearch.WordTrace tailWord_340050 prefixEnd_340050 155208085832444254676573 := by
  unfold tailWord_340050
  simp only [CollatzResearch.WordTrace]
  refine ⟨3100660604516100190362401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8268428278709600507633069 3100660604516100190362401)
  ·
    refine ⟨2325495453387075142771801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3100660604516100190362401 2325495453387075142771801)
    ·
      refine ⟨1744121590040306357078851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2325495453387075142771801 1744121590040306357078851)
      ·
        refine ⟨2616182385060459535618277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1744121590040306357078851 2616182385060459535618277)
        ·
          refine ⟨490534197198836162928427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2616182385060459535618277 490534197198836162928427)
          ·
            refine ⟨735801295798254244392641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 490534197198836162928427 735801295798254244392641)
            ·
              refine ⟨551850971848690683294481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 735801295798254244392641 551850971848690683294481)
              ·
                refine ⟨413888228886518012470861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 551850971848690683294481 413888228886518012470861)
                ·
                  refine ⟨155208085832444254676573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 413888228886518012470861 155208085832444254676573)
                  ·
                    rfl

theorem cell20_340050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 2, 2, 3].length) (baseStart_340050 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_340050 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_340050 prefixEnd_340050 := by exact prefixLift 340050
  have htrace : WordTrace (prefixWord ++ tailWord_340050) baseStart_340050 baseEnd_340050 := by
    simpa [prefixWord, tailWord_340050, baseEnd_340050] using wordTrace_append hprefix tailTrace_340050
  have hstable : (prefixWord ++ tailWord_340050).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_340050).length < 2 ^ (prefixWord ++ tailWord_340050).sum := by decide
  have hdescent : baseEnd_340050 < baseStart_340050 := by decide
  rcases family_descends (prefixWord ++ tailWord_340050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_340078 : List Nat := [4, 1, 2, 2, 1, 1, 3, 2, 4]
def baseStart_340078 : Nat := 118140960795 + 340078 * 2 ^ 59
def prefixEnd_340078 : Nat := 4983230072969 + 3 ^ 40 * 340078 * 2
def baseEnd_340078 : Nat := 155220865795400601743125

theorem tailTrace_340078 : CollatzResearch.WordTrace tailWord_340078 prefixEnd_340078 155220865795400601743125 := by
  unfold tailWord_340078
  simp only [CollatzResearch.WordTrace]
  refine ⟨1550457957745370192933611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8269109107975307695645925 1550457957745370192933611)
  ·
    refine ⟨2325686936618055289400417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1550457957745370192933611 2325686936618055289400417)
    ·
      refine ⟨1744265202463541467050313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2325686936618055289400417 1744265202463541467050313)
      ·
        refine ⟨1308198901847656100287735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1744265202463541467050313 1308198901847656100287735)
        ·
          refine ⟨1962298352771484150431603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1308198901847656100287735 1962298352771484150431603)
          ·
            refine ⟨2943447529157226225647405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1962298352771484150431603 2943447529157226225647405)
            ·
              refine ⟨1103792823433959834617777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2943447529157226225647405 1103792823433959834617777)
              ·
                refine ⟨827844617575469875963333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1103792823433959834617777 827844617575469875963333)
                ·
                  refine ⟨155220865795400601743125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 827844617575469875963333 155220865795400601743125)
                  ·
                    rfl

theorem cell20_340078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 3, 2, 4].length) (baseStart_340078 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_340078 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_340078 prefixEnd_340078 := by exact prefixLift 340078
  have htrace : WordTrace (prefixWord ++ tailWord_340078) baseStart_340078 baseEnd_340078 := by
    simpa [prefixWord, tailWord_340078, baseEnd_340078] using wordTrace_append hprefix tailTrace_340078
  have hstable : (prefixWord ++ tailWord_340078).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_340078).length < 2 ^ (prefixWord ++ tailWord_340078).sum := by decide
  have hdescent : baseEnd_340078 < baseStart_340078 := by decide
  rcases family_descends (prefixWord ++ tailWord_340078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_340118 : List Nat := [5, 3, 2, 1, 1, 1, 3, 1, 3]
def baseStart_340118 : Nat := 118140960795 + 340118 * 2 ^ 59
def prefixEnd_340118 : Nat := 4983230072969 + 3 ^ 40 * 340118 * 2
def baseEnd_340118 : Nat := 155239122885338240409629

theorem tailTrace_340118 : CollatzResearch.WordTrace tailWord_340118 prefixEnd_340118 155239122885338240409629 := by
  unfold tailWord_340118
  simp only [CollatzResearch.WordTrace]
  refine ⟨775320161363628023432813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 8270081721212032249950005 775320161363628023432813)
  ·
    refine ⟨290745060511360508787305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 775320161363628023432813 290745060511360508787305)
    ·
      refine ⟨218058795383520381590479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 290745060511360508787305 218058795383520381590479)
      ·
        refine ⟨327088193075280572385719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 218058795383520381590479 327088193075280572385719)
        ·
          refine ⟨490632289612920858578579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 327088193075280572385719 490632289612920858578579)
          ·
            refine ⟨735948434419381287867869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 490632289612920858578579 735948434419381287867869)
            ·
              refine ⟨275980662907267982950451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 735948434419381287867869 275980662907267982950451)
              ·
                refine ⟨413970994360901974425677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 275980662907267982950451 413970994360901974425677)
                ·
                  refine ⟨155239122885338240409629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 413970994360901974425677 155239122885338240409629)
                  ·
                    rfl

theorem cell20_340118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 3, 1, 3].length) (baseStart_340118 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_340118 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_340118 prefixEnd_340118 := by exact prefixLift 340118
  have htrace : WordTrace (prefixWord ++ tailWord_340118) baseStart_340118 baseEnd_340118 := by
    simpa [prefixWord, tailWord_340118, baseEnd_340118] using wordTrace_append hprefix tailTrace_340118
  have hstable : (prefixWord ++ tailWord_340118).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_340118).length < 2 ^ (prefixWord ++ tailWord_340118).sum := by decide
  have hdescent : baseEnd_340118 < baseStart_340118 := by decide
  rcases family_descends (prefixWord ++ tailWord_340118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_340168 : List Nat := [2, 1, 3, 1, 2, 1, 1, 6, 3]
def baseStart_340168 : Nat := 118140960795 + 340168 * 2 ^ 59
def prefixEnd_340168 : Nat := 4983230072969 + 3 ^ 40 * 340168 * 2
def baseEnd_340168 : Nat := 155261944247760288742757

theorem tailTrace_340168 : CollatzResearch.WordTrace tailWord_340168 prefixEnd_340168 155261944247760288742757 := by
  unfold tailWord_340168
  simp only [CollatzResearch.WordTrace]
  refine ⟨6203473115818453457122579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8271297487757937942830105 6203473115818453457122579)
  ·
    refine ⟨9305209673727680185683869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6203473115818453457122579 9305209673727680185683869)
    ·
      refine ⟨3489453627647880069631451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9305209673727680185683869 3489453627647880069631451)
      ·
        refine ⟨5234180441471820104447177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3489453627647880069631451 5234180441471820104447177)
        ·
          refine ⟨3925635331103865078335383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5234180441471820104447177 3925635331103865078335383)
          ·
            refine ⟨5888452996655797617503075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3925635331103865078335383 5888452996655797617503075)
            ·
              refine ⟨8832679494983696426254613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5888452996655797617503075 8832679494983696426254613)
              ·
                refine ⟨414031851327360769980685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 8832679494983696426254613 414031851327360769980685)
                ·
                  refine ⟨155261944247760288742757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 414031851327360769980685 155261944247760288742757)
                  ·
                    rfl

theorem cell20_340168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 6, 3].length) (baseStart_340168 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_340168 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_340168 prefixEnd_340168 := by exact prefixLift 340168
  have htrace : WordTrace (prefixWord ++ tailWord_340168) baseStart_340168 baseEnd_340168 := by
    simpa [prefixWord, tailWord_340168, baseEnd_340168] using wordTrace_append hprefix tailTrace_340168
  have hstable : (prefixWord ++ tailWord_340168).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_340168).length < 2 ^ (prefixWord ++ tailWord_340168).sum := by decide
  have hdescent : baseEnd_340168 < baseStart_340168 := by decide
  rcases family_descends (prefixWord ++ tailWord_340168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_340171 : List Nat := [1, 1, 1, 1, 3, 2, 7, 2, 2]
def baseStart_340171 : Nat := 118140960795 + 340171 * 2 ^ 59
def prefixEnd_340171 : Nat := 4983230072969 + 3 ^ 40 * 340171 * 2
def baseEnd_340171 : Nat := 155263313529505611642745

theorem tailTrace_340171 : CollatzResearch.WordTrace tailWord_340171 prefixEnd_340171 155263313529505611642745 := by
  unfold tailWord_340171
  simp only [CollatzResearch.WordTrace]
  refine ⟨12407055650626038426604367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8271370433750692284402911 12407055650626038426604367)
  ·
    refine ⟨18610583475939057639906551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12407055650626038426604367 18610583475939057639906551)
    ·
      refine ⟨27915875213908586459859827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18610583475939057639906551 27915875213908586459859827)
      ·
        refine ⟨41873812820862879689789741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27915875213908586459859827 41873812820862879689789741)
        ·
          refine ⟨15702679807823579883671153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41873812820862879689789741 15702679807823579883671153)
          ·
            refine ⟨11777009855867684912753365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15702679807823579883671153 11777009855867684912753365)
            ·
              refine ⟨276023668496898865142657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 11777009855867684912753365 276023668496898865142657)
              ·
                refine ⟨207017751372674148856993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 276023668496898865142657 207017751372674148856993)
                ·
                  refine ⟨155263313529505611642745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 207017751372674148856993 155263313529505611642745)
                  ·
                    rfl

theorem cell20_340171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 7, 2, 2].length) (baseStart_340171 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_340171 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_340171 prefixEnd_340171 := by exact prefixLift 340171
  have htrace : WordTrace (prefixWord ++ tailWord_340171) baseStart_340171 baseEnd_340171 := by
    simpa [prefixWord, tailWord_340171, baseEnd_340171] using wordTrace_append hprefix tailTrace_340171
  have hstable : (prefixWord ++ tailWord_340171).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_340171).length < 2 ^ (prefixWord ++ tailWord_340171).sum := by decide
  have hdescent : baseEnd_340171 < baseStart_340171 := by decide
  rcases family_descends (prefixWord ++ tailWord_340171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_340181 : List Nat := [1, 3, 2, 4, 2, 2, 2, 1, 3]
def baseStart_340181 : Nat := 118140960795 + 340181 * 2 ^ 59
def prefixEnd_340181 : Nat := 4983230072969 + 3 ^ 40 * 340181 * 2
def baseEnd_340181 : Nat := 155267877801990021309371

theorem tailTrace_340181 : CollatzResearch.WordTrace tailWord_340181 prefixEnd_340181 155267877801990021309371 := by
  unfold tailWord_340181
  simp only [CollatzResearch.WordTrace]
  refine ⟨12407420380589810134468397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8271613587059873422978931 12407420380589810134468397)
  ·
    refine ⟨4652782642721178800425649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12407420380589810134468397 4652782642721178800425649)
    ·
      refine ⟨3489586982040884100319237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4652782642721178800425649 3489586982040884100319237)
      ·
        refine ⟨654297559132665768809857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3489586982040884100319237 654297559132665768809857)
        ·
          refine ⟨490723169349499326607393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 654297559132665768809857 490723169349499326607393)
          ·
            refine ⟨368042377012124494955545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 490723169349499326607393 368042377012124494955545)
            ·
              refine ⟨276031782759093371216659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 368042377012124494955545 276031782759093371216659)
              ·
                refine ⟨414047674138640056824989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 276031782759093371216659 414047674138640056824989)
                ·
                  refine ⟨155267877801990021309371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 414047674138640056824989 155267877801990021309371)
                  ·
                    rfl

theorem cell20_340181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 2, 2, 1, 3].length) (baseStart_340181 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_340181 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_340181 prefixEnd_340181 := by exact prefixLift 340181
  have htrace : WordTrace (prefixWord ++ tailWord_340181) baseStart_340181 baseEnd_340181 := by
    simpa [prefixWord, tailWord_340181, baseEnd_340181] using wordTrace_append hprefix tailTrace_340181
  have hstable : (prefixWord ++ tailWord_340181).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_340181).length < 2 ^ (prefixWord ++ tailWord_340181).sum := by decide
  have hdescent : baseEnd_340181 < baseStart_340181 := by decide
  rcases family_descends (prefixWord ++ tailWord_340181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_340185 : List Nat := [1, 2, 1, 2, 3, 1, 6, 1, 3]
def baseStart_340185 : Nat := 118140960795 + 340185 * 2 ^ 59
def prefixEnd_340185 : Nat := 4983230072969 + 3 ^ 40 * 340185 * 2
def baseEnd_340185 : Nat := 155269703510983785176021

theorem tailTrace_340185 : CollatzResearch.WordTrace tailWord_340185 prefixEnd_340185 155269703510983785176021 := by
  unfold tailWord_340185
  simp only [CollatzResearch.WordTrace]
  refine ⟨12407566272575318817614009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8271710848383545878409339 12407566272575318817614009)
  ·
    refine ⟨9305674704431489113210507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12407566272575318817614009 9305674704431489113210507)
    ·
      refine ⟨13958512056647233669815761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9305674704431489113210507 13958512056647233669815761)
      ·
        refine ⟨10468884042485425252361821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13958512056647233669815761 10468884042485425252361821)
        ·
          refine ⟨3925831515932034469635683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10468884042485425252361821 3925831515932034469635683)
          ·
            refine ⟨5888747273898051704453525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3925831515932034469635683 5888747273898051704453525)
            ·
              refine ⟨276035028463971173646259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 5888747273898051704453525 276035028463971173646259)
              ·
                refine ⟨414052542695956760469389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 276035028463971173646259 414052542695956760469389)
                ·
                  refine ⟨155269703510983785176021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 414052542695956760469389 155269703510983785176021)
                  ·
                    rfl

theorem cell20_340185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 6, 1, 3].length) (baseStart_340185 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_340185 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_340185 prefixEnd_340185 := by exact prefixLift 340185
  have htrace : WordTrace (prefixWord ++ tailWord_340185) baseStart_340185 baseEnd_340185 := by
    simpa [prefixWord, tailWord_340185, baseEnd_340185] using wordTrace_append hprefix tailTrace_340185
  have hstable : (prefixWord ++ tailWord_340185).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_340185).length < 2 ^ (prefixWord ++ tailWord_340185).sum := by decide
  have hdescent : baseEnd_340185 < baseStart_340185 := by decide
  rcases family_descends (prefixWord ++ tailWord_340185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_340199 : List Nat := [1, 1, 5, 3, 1, 1, 2, 6]
def baseStart_340199 : Nat := 118140960795 + 340199 * 2 ^ 59
def prefixEnd_340199 : Nat := 4983230072969 + 3 ^ 40 * 340199 * 2
def baseEnd_340199 : Nat := 51758697830820652903099

theorem tailTrace_340199 : CollatzResearch.WordTrace tailWord_340199 prefixEnd_340199 51758697830820652903099 := by
  unfold tailWord_340199
  simp only [CollatzResearch.WordTrace]
  refine ⟨12408076894524599208623651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8272051263016399472415767 12408076894524599208623651)
  ·
    refine ⟨18612115341786898812935477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12408076894524599208623651 18612115341786898812935477)
    ·
      refine ⟨1744885813292521763712701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 18612115341786898812935477 1744885813292521763712701)
      ·
        refine ⟨654332179984695661392263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1744885813292521763712701 654332179984695661392263)
        ·
          refine ⟨981498269977043492088395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 654332179984695661392263 981498269977043492088395)
          ·
            refine ⟨1472247404965565238132593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 981498269977043492088395 1472247404965565238132593)
            ·
              refine ⟨1104185553724173928599445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1472247404965565238132593 1104185553724173928599445)
              ·
                refine ⟨51758697830820652903099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1104185553724173928599445 51758697830820652903099)
                ·
                  rfl

theorem cell20_340199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 2, 6].length) (baseStart_340199 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_340199 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_340199 prefixEnd_340199 := by exact prefixLift 340199
  have htrace : WordTrace (prefixWord ++ tailWord_340199) baseStart_340199 baseEnd_340199 := by
    simpa [prefixWord, tailWord_340199, baseEnd_340199] using wordTrace_append hprefix tailTrace_340199
  have hstable : (prefixWord ++ tailWord_340199).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_340199).length < 2 ^ (prefixWord ++ tailWord_340199).sum := by decide
  have hdescent : baseEnd_340199 < baseStart_340199 := by decide
  rcases family_descends (prefixWord ++ tailWord_340199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_340220 : List Nat := [2, 2, 2, 1, 4, 9]
def baseStart_340220 : Nat := 118140960795 + 340220 * 2 ^ 59
def prefixEnd_340220 : Nat := 4983230072969 + 3 ^ 40 * 340220 * 2
def baseEnd_340220 : Nat := 5751321424617748852193

theorem tailTrace_340220 : CollatzResearch.WordTrace tailWord_340220 prefixEnd_340220 5751321424617748852193 := by
  unfold tailWord_340220
  simp only [CollatzResearch.WordTrace]
  refine ⟨6204421413724259897569057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8272561884965679863425409 6204421413724259897569057)
  ·
    refine ⟨4653316060293194923176793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6204421413724259897569057 4653316060293194923176793)
    ·
      refine ⟨3489987045219896192382595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4653316060293194923176793 3489987045219896192382595)
      ·
        refine ⟨5234980567829844288573893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3489987045219896192382595 5234980567829844288573893)
        ·
          refine ⟨981558856468095804107605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5234980567829844288573893 981558856468095804107605)
          ·
            refine ⟨5751321424617748852193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 981558856468095804107605 5751321424617748852193)
            ·
              rfl

theorem cell20_340220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 9].length) (baseStart_340220 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_340220 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_340220 prefixEnd_340220 := by exact prefixLift 340220
  have htrace : WordTrace (prefixWord ++ tailWord_340220) baseStart_340220 baseEnd_340220 := by
    simpa [prefixWord, tailWord_340220, baseEnd_340220] using wordTrace_append hprefix tailTrace_340220
  have hstable : (prefixWord ++ tailWord_340220).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_340220).length < 2 ^ (prefixWord ++ tailWord_340220).sum := by decide
  have hdescent : baseEnd_340220 < baseStart_340220 := by decide
  rcases family_descends (prefixWord ++ tailWord_340220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_340226 : List Nat := [3, 4, 1, 1, 2, 2, 1, 4, 2]
def baseStart_340226 : Nat := 118140960795 + 340226 * 2 ^ 59
def prefixEnd_340226 : Nat := 4983230072969 + 3 ^ 40 * 340226 * 2
def baseEnd_340226 : Nat := 155288417028169864809187

theorem tailTrace_340226 : CollatzResearch.WordTrace tailWord_340226 prefixEnd_340226 155288417028169864809187 := by
  unfold tailWord_340226
  simp only [CollatzResearch.WordTrace]
  refine ⟨3102265416356695704964133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8272707776951188546571021 3102265416356695704964133)
  ·
    refine ⟨581674765566880444680775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3102265416356695704964133 581674765566880444680775)
    ·
      refine ⟨872512148350320667021163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 581674765566880444680775 872512148350320667021163)
      ·
        refine ⟨1308768222525481000531745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 872512148350320667021163 1308768222525481000531745)
        ·
          refine ⟨981576166894110750398809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1308768222525481000531745 981576166894110750398809)
          ·
            refine ⟨736182125170583062799107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 981576166894110750398809 736182125170583062799107)
            ·
              refine ⟨1104273187755874594198661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 736182125170583062799107 1104273187755874594198661)
              ·
                refine ⟨207051222704226486412249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1104273187755874594198661 207051222704226486412249)
                ·
                  refine ⟨155288417028169864809187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 207051222704226486412249 155288417028169864809187)
                  ·
                    rfl

theorem cell20_340226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 1, 4, 2].length) (baseStart_340226 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_340226 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_340226 prefixEnd_340226 := by exact prefixLift 340226
  have htrace : WordTrace (prefixWord ++ tailWord_340226) baseStart_340226 baseEnd_340226 := by
    simpa [prefixWord, tailWord_340226, baseEnd_340226] using wordTrace_append hprefix tailTrace_340226
  have hstable : (prefixWord ++ tailWord_340226).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_340226).length < 2 ^ (prefixWord ++ tailWord_340226).sum := by decide
  have hdescent : baseEnd_340226 < baseStart_340226 := by decide
  rcases family_descends (prefixWord ++ tailWord_340226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_340264 : List Nat := [2, 1, 5, 1, 3, 1, 2, 3, 2]
def baseStart_340264 : Nat := 118140960795 + 340264 * 2 ^ 59
def prefixEnd_340264 : Nat := 4983230072969 + 3 ^ 40 * 340264 * 2
def baseEnd_340264 : Nat := 155305761263610621542365

theorem tailTrace_340264 : CollatzResearch.WordTrace tailWord_340264 prefixEnd_340264 155305761263610621542365 := by
  unfold tailWord_340264
  simp only [CollatzResearch.WordTrace]
  refine ⟨6205223819644557654869923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8273631759526076873159897 6205223819644557654869923)
  ·
    refine ⟨9307835729466836482304885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6205223819644557654869923 9307835729466836482304885)
    ·
      refine ⟨872609599637515920216083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 9307835729466836482304885 872609599637515920216083)
      ·
        refine ⟨1308914399456273880324125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 872609599637515920216083 1308914399456273880324125)
        ·
          refine ⟨490842899796102705121547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1308914399456273880324125 490842899796102705121547)
          ·
            refine ⟨736264349694154057682321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 490842899796102705121547 736264349694154057682321)
            ·
              refine ⟨552198262270615543261741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 736264349694154057682321 552198262270615543261741)
              ·
                refine ⟨207074348351480828723153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 552198262270615543261741 207074348351480828723153)
                ·
                  refine ⟨155305761263610621542365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 207074348351480828723153 155305761263610621542365)
                  ·
                    rfl

theorem cell20_340264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 2, 3, 2].length) (baseStart_340264 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_340264 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_340264 prefixEnd_340264 := by exact prefixLift 340264
  have htrace : WordTrace (prefixWord ++ tailWord_340264) baseStart_340264 baseEnd_340264 := by
    simpa [prefixWord, tailWord_340264, baseEnd_340264] using wordTrace_append hprefix tailTrace_340264
  have hstable : (prefixWord ++ tailWord_340264).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_340264).length < 2 ^ (prefixWord ++ tailWord_340264).sum := by decide
  have hdescent : baseEnd_340264 < baseStart_340264 := by decide
  rcases family_descends (prefixWord ++ tailWord_340264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_340268 : List Nat := [2, 2, 1, 1, 1, 3, 3, 5, 2]
def baseStart_340268 : Nat := 118140960795 + 340268 * 2 ^ 59
def prefixEnd_340268 : Nat := 4983230072969 + 3 ^ 40 * 340268 * 2
def baseEnd_340268 : Nat := 155307586972604385409015

theorem tailTrace_340268 : CollatzResearch.WordTrace tailWord_340268 prefixEnd_340268 155307586972604385409015 := by
  unfold tailWord_340268
  simp only [CollatzResearch.WordTrace]
  refine ⟨6205296765637311996442729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8273729020849749328590305 6205296765637311996442729)
  ·
    refine ⟨4653972574227983997332047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6205296765637311996442729 4653972574227983997332047)
    ·
      refine ⟨6980958861341975995998071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4653972574227983997332047 6980958861341975995998071)
      ·
        refine ⟨10471438292012963993997107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6980958861341975995998071 10471438292012963993997107)
        ·
          refine ⟨15707157438019445990995661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10471438292012963993997107 15707157438019445990995661)
          ·
            refine ⟨5890184039257292246623373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15707157438019445990995661 5890184039257292246623373)
            ·
              refine ⟨2208819014721484592483765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5890184039257292246623373 2208819014721484592483765)
              ·
                refine ⟨207076782630139180545353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2208819014721484592483765 207076782630139180545353)
                ·
                  refine ⟨155307586972604385409015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 207076782630139180545353 155307586972604385409015)
                  ·
                    rfl

theorem cell20_340268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 3, 5, 2].length) (baseStart_340268 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_340268 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_340268 prefixEnd_340268 := by exact prefixLift 340268
  have htrace : WordTrace (prefixWord ++ tailWord_340268) baseStart_340268 baseEnd_340268 := by
    simpa [prefixWord, tailWord_340268, baseEnd_340268] using wordTrace_append hprefix tailTrace_340268
  have hstable : (prefixWord ++ tailWord_340268).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_340268).length < 2 ^ (prefixWord ++ tailWord_340268).sum := by decide
  have hdescent : baseEnd_340268 < baseStart_340268 := by decide
  rcases family_descends (prefixWord ++ tailWord_340268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_340282 : List Nat := [3, 1, 1, 1, 4, 3, 1, 1, 5]
def baseStart_340282 : Nat := 118140960795 + 340282 * 2 ^ 59
def prefixEnd_340282 : Nat := 4983230072969 + 3 ^ 40 * 340282 * 2
def baseEnd_340282 : Nat := 155313976954082558942291

theorem tailTrace_340282 : CollatzResearch.WordTrace tailWord_340282 prefixEnd_340282 155313976954082558942291 := by
  unfold tailWord_340282
  simp only [CollatzResearch.WordTrace]
  refine ⟨3102776038305976095973775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8274069435482602922596733 3102776038305976095973775)
  ·
    refine ⟨4654164057458964143960663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3102776038305976095973775 4654164057458964143960663)
    ·
      refine ⟨6981246086188446215940995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4654164057458964143960663 6981246086188446215940995)
      ·
        refine ⟨10471869129282669323911493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6981246086188446215940995 10471869129282669323911493)
        ·
          refine ⟨1963475461740500498233405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10471869129282669323911493 1963475461740500498233405)
          ·
            refine ⟨736303298152687686837527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1963475461740500498233405 736303298152687686837527)
            ·
              refine ⟨1104454947229031530256291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 736303298152687686837527 1104454947229031530256291)
              ·
                refine ⟨1656682420843547295384437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1104454947229031530256291 1656682420843547295384437)
                ·
                  refine ⟨155313976954082558942291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1656682420843547295384437 155313976954082558942291)
                  ·
                    rfl

theorem cell20_340282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 1, 1, 5].length) (baseStart_340282 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_340282 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_340282 prefixEnd_340282 := by exact prefixLift 340282
  have htrace : WordTrace (prefixWord ++ tailWord_340282) baseStart_340282 baseEnd_340282 := by
    simpa [prefixWord, tailWord_340282, baseEnd_340282] using wordTrace_append hprefix tailTrace_340282
  have hstable : (prefixWord ++ tailWord_340282).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_340282).length < 2 ^ (prefixWord ++ tailWord_340282).sum := by decide
  have hdescent : baseEnd_340282 < baseStart_340282 := by decide
  rcases family_descends (prefixWord ++ tailWord_340282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_340309 : List Nat := [1, 3, 2, 2, 5, 1, 2, 4]
def baseStart_340309 : Nat := 118140960795 + 340309 * 2 ^ 59
def prefixEnd_340309 : Nat := 4983230072969 + 3 ^ 40 * 340309 * 2
def baseEnd_340309 : Nat := 51775433496596821680727

theorem tailTrace_340309 : CollatzResearch.WordTrace tailWord_340309 prefixEnd_340309 51775433496596821680727 := by
  unfold tailWord_340309
  simp only [CollatzResearch.WordTrace]
  refine ⟨12412088924126087995127981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8274725949417391996751987 12412088924126087995127981)
  ·
    refine ⟨4654533346547282998172993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12412088924126087995127981 4654533346547282998172993)
    ·
      refine ⟨3490900009910462248629745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4654533346547282998172993 3490900009910462248629745)
      ·
        refine ⟨2618175007432846686472309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3490900009910462248629745 2618175007432846686472309)
        ·
          refine ⟨245453906946829376856779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2618175007432846686472309 245453906946829376856779)
          ·
            refine ⟨368180860420244065285169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 245453906946829376856779 368180860420244065285169)
            ·
              refine ⟨276135645315183048963877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 368180860420244065285169 276135645315183048963877)
              ·
                refine ⟨51775433496596821680727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 276135645315183048963877 51775433496596821680727)
                ·
                  rfl

theorem cell20_340309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 5, 1, 2, 4].length) (baseStart_340309 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_340309 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_340309 prefixEnd_340309 := by exact prefixLift 340309
  have htrace : WordTrace (prefixWord ++ tailWord_340309) baseStart_340309 baseEnd_340309 := by
    simpa [prefixWord, tailWord_340309, baseEnd_340309] using wordTrace_append hprefix tailTrace_340309
  have hstable : (prefixWord ++ tailWord_340309).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_340309).length < 2 ^ (prefixWord ++ tailWord_340309).sum := by decide
  have hdescent : baseEnd_340309 < baseStart_340309 := by decide
  rcases family_descends (prefixWord ++ tailWord_340309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_340392 : List Nat := [2, 1, 6, 1, 1, 2, 2, 2, 3]
def baseStart_340392 : Nat := 118140960795 + 340392 * 2 ^ 59
def prefixEnd_340392 : Nat := 4983230072969 + 3 ^ 40 * 340392 * 2
def baseEnd_340392 : Nat := 155364183951411065275175

theorem tailTrace_340392 : CollatzResearch.WordTrace tailWord_340392 prefixEnd_340392 155364183951411065275175 := by
  unfold tailWord_340392
  simp only [CollatzResearch.WordTrace]
  refine ⟨6207558091412696585199715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8276744121883595446932953 6207558091412696585199715)
  ·
    refine ⟨9311337137119044877799573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6207558091412696585199715 9311337137119044877799573)
    ·
      refine ⟨436468928302455228646855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 9311337137119044877799573 436468928302455228646855)
      ·
        refine ⟨654703392453682842970283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 436468928302455228646855 654703392453682842970283)
        ·
          refine ⟨982055088680524264455425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 654703392453682842970283 982055088680524264455425)
          ·
            refine ⟨736541316510393198341569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 982055088680524264455425 736541316510393198341569)
            ·
              refine ⟨552405987382794898756177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 736541316510393198341569 552405987382794898756177)
              ·
                refine ⟨414304490537096174067133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 552405987382794898756177 414304490537096174067133)
                ·
                  refine ⟨155364183951411065275175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 414304490537096174067133 155364183951411065275175)
                  ·
                    rfl

theorem cell20_340392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 2, 2, 3].length) (baseStart_340392 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_340392 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_340392 prefixEnd_340392 := by exact prefixLift 340392
  have htrace : WordTrace (prefixWord ++ tailWord_340392) baseStart_340392 baseEnd_340392 := by
    simpa [prefixWord, tailWord_340392, baseEnd_340392] using wordTrace_append hprefix tailTrace_340392
  have hstable : (prefixWord ++ tailWord_340392).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_340392).length < 2 ^ (prefixWord ++ tailWord_340392).sum := by decide
  have hdescent : baseEnd_340392 < baseStart_340392 := by decide
  rcases family_descends (prefixWord ++ tailWord_340392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_340437 : List Nat := [1, 3, 2, 3, 1, 3, 2, 3, 2]
def baseStart_340437 : Nat := 118140960795 + 340437 * 2 ^ 59
def prefixEnd_340437 : Nat := 4983230072969 + 3 ^ 40 * 340437 * 2
def baseEnd_340437 : Nat := 155384723177590908774991

theorem tailTrace_340437 : CollatzResearch.WordTrace tailWord_340437 prefixEnd_340437 155384723177590908774991 := by
  unfold tailWord_340437
  simp only [CollatzResearch.WordTrace]
  refine ⟨12416757467662365855787565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8277838311774910570525043 12416757467662365855787565)
  ·
    refine ⟨4656284050373387195920337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12416757467662365855787565 4656284050373387195920337)
    ·
      refine ⟨3492213037780040396940253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4656284050373387195920337 3492213037780040396940253)
      ·
        refine ⟨1309579889167515148852595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3492213037780040396940253 1309579889167515148852595)
        ·
          refine ⟨1964369833751272723278893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1309579889167515148852595 1964369833751272723278893)
          ·
            refine ⟨736638687656727271229585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1964369833751272723278893 736638687656727271229585)
            ·
              refine ⟨552479015742545453422189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 736638687656727271229585 552479015742545453422189)
              ·
                refine ⟨207179630903454545033321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 552479015742545453422189 207179630903454545033321)
                ·
                  refine ⟨155384723177590908774991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 207179630903454545033321 155384723177590908774991)
                  ·
                    rfl

theorem cell20_340437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 2, 3, 2].length) (baseStart_340437 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_340437 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_340437 prefixEnd_340437 := by exact prefixLift 340437
  have htrace : WordTrace (prefixWord ++ tailWord_340437) baseStart_340437 baseEnd_340437 := by
    simpa [prefixWord, tailWord_340437, baseEnd_340437] using wordTrace_append hprefix tailTrace_340437
  have hstable : (prefixWord ++ tailWord_340437).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_340437).length < 2 ^ (prefixWord ++ tailWord_340437).sum := by decide
  have hdescent : baseEnd_340437 < baseStart_340437 := by decide
  rcases family_descends (prefixWord ++ tailWord_340437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_340458 : List Nat := [3, 1, 3, 1, 3, 2, 2, 1, 4]
def baseStart_340458 : Nat := 118140960795 + 340458 * 2 ^ 59
def prefixEnd_340458 : Nat := 4983230072969 + 3 ^ 40 * 340458 * 2
def baseEnd_340458 : Nat := 155394308149808169074905

theorem tailTrace_340458 : CollatzResearch.WordTrace tailWord_340458 prefixEnd_340458 155394308149808169074905 := by
  unfold tailWord_340458
  simp only [CollatzResearch.WordTrace]
  refine ⟨3104380850146571610575507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8278348933724190961534685 3104380850146571610575507)
  ·
    refine ⟨4656571275219857415863261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3104380850146571610575507 4656571275219857415863261)
    ·
      refine ⟨1746214228207446530948723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4656571275219857415863261 1746214228207446530948723)
      ·
        refine ⟨2619321342311169796423085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1746214228207446530948723 2619321342311169796423085)
        ·
          refine ⟨982245503366688673658657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2619321342311169796423085 982245503366688673658657)
          ·
            refine ⟨736684127525016505243993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 982245503366688673658657 736684127525016505243993)
            ·
              refine ⟨552513095643762378932995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 736684127525016505243993 552513095643762378932995)
              ·
                refine ⟨828769643465643568399493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 552513095643762378932995 828769643465643568399493)
                ·
                  refine ⟨155394308149808169074905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 828769643465643568399493 155394308149808169074905)
                  ·
                    rfl

theorem cell20_340458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 2, 1, 4].length) (baseStart_340458 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_340458 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_340458 prefixEnd_340458 := by exact prefixLift 340458
  have htrace : WordTrace (prefixWord ++ tailWord_340458) baseStart_340458 baseEnd_340458 := by
    simpa [prefixWord, tailWord_340458, baseEnd_340458] using wordTrace_append hprefix tailTrace_340458
  have hstable : (prefixWord ++ tailWord_340458).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_340458).length < 2 ^ (prefixWord ++ tailWord_340458).sum := by decide
  have hdescent : baseEnd_340458 < baseStart_340458 := by decide
  rcases family_descends (prefixWord ++ tailWord_340458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_340482 : List Nat := [3, 4, 1, 2, 2, 1, 1, 6]
def baseStart_340482 : Nat := 118140960795 + 340482 * 2 ^ 59
def prefixEnd_340482 : Nat := 4983230072969 + 3 ^ 40 * 340482 * 2
def baseEnd_340482 : Nat := 51801754134590250758269

theorem tailTrace_340482 : CollatzResearch.WordTrace tailWord_340482 prefixEnd_340482 51801754134590250758269 := by
  unfold tailWord_340482
  simp only [CollatzResearch.WordTrace]
  refine ⟨3104599688124834635293925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8278932501666225694117133 3104599688124834635293925)
  ·
    refine ⟨582112441523406494117611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3104599688124834635293925 582112441523406494117611)
    ·
      refine ⟨873168662285109741176417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 582112441523406494117611 873168662285109741176417)
      ·
        refine ⟨654876496713832305882313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 873168662285109741176417 654876496713832305882313)
        ·
          refine ⟨491157372535374229411735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 654876496713832305882313 491157372535374229411735)
          ·
            refine ⟨736736058803061344117603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 491157372535374229411735 736736058803061344117603)
            ·
              refine ⟨1105104088204592016176405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 736736058803061344117603 1105104088204592016176405)
              ·
                refine ⟨51801754134590250758269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1105104088204592016176405 51801754134590250758269)
                ·
                  rfl

theorem cell20_340482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 1, 6].length) (baseStart_340482 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_340482 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_340482 prefixEnd_340482 := by exact prefixLift 340482
  have htrace : WordTrace (prefixWord ++ tailWord_340482) baseStart_340482 baseEnd_340482 := by
    simpa [prefixWord, tailWord_340482, baseEnd_340482] using wordTrace_append hprefix tailTrace_340482
  have hstable : (prefixWord ++ tailWord_340482).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_340482).length < 2 ^ (prefixWord ++ tailWord_340482).sum := by decide
  have hdescent : baseEnd_340482 < baseStart_340482 := by decide
  rcases family_descends (prefixWord ++ tailWord_340482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_340513 : List Nat := [1, 2, 3, 2, 2, 1, 5, 2, 2]
def baseStart_340513 : Nat := 118140960795 + 340513 * 2 ^ 59
def prefixEnd_340513 : Nat := 4983230072969 + 3 ^ 40 * 340513 * 2
def baseEnd_340513 : Nat := 155419411648472422241347

theorem tailTrace_340513 : CollatzResearch.WordTrace tailWord_340513 prefixEnd_340513 155419411648472422241347 := by
  unfold tailWord_340513
  simp only [CollatzResearch.WordTrace]
  refine ⟨12419529415387030835554193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8279686276924687223702795 12419529415387030835554193)
  ·
    refine ⟨9314647061540273126665645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12419529415387030835554193 9314647061540273126665645)
    ·
      refine ⟨3492992648077602422499617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9314647061540273126665645 3492992648077602422499617)
      ·
        refine ⟨2619744486058201816874713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3492992648077602422499617 2619744486058201816874713)
        ·
          refine ⟨1964808364543651362656035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2619744486058201816874713 1964808364543651362656035)
          ·
            refine ⟨2947212546815477043984053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1964808364543651362656035 2947212546815477043984053)
            ·
              refine ⟨276301176263950972873505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2947212546815477043984053 276301176263950972873505)
              ·
                refine ⟨207225882197963229655129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 276301176263950972873505 207225882197963229655129)
                ·
                  refine ⟨155419411648472422241347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 207225882197963229655129 155419411648472422241347)
                  ·
                    rfl

theorem cell20_340513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 5, 2, 2].length) (baseStart_340513 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_340513 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_340513 prefixEnd_340513 := by exact prefixLift 340513
  have htrace : WordTrace (prefixWord ++ tailWord_340513) baseStart_340513 baseEnd_340513 := by
    simpa [prefixWord, tailWord_340513, baseEnd_340513] using wordTrace_append hprefix tailTrace_340513
  have hstable : (prefixWord ++ tailWord_340513).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_340513).length < 2 ^ (prefixWord ++ tailWord_340513).sum := by decide
  have hdescent : baseEnd_340513 < baseStart_340513 := by decide
  rcases family_descends (prefixWord ++ tailWord_340513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_340517 : List Nat := [1, 3, 1, 2, 2, 1, 5, 1, 4]
def baseStart_340517 : Nat := 118140960795 + 340517 * 2 ^ 59
def prefixEnd_340517 : Nat := 4983230072969 + 3 ^ 40 * 340517 * 2
def baseEnd_340517 : Nat := 155421237357466186107997

theorem tailTrace_340517 : CollatzResearch.WordTrace tailWord_340517 prefixEnd_340517 155421237357466186107997 := by
  unfold tailWord_340517
  simp only [CollatzResearch.WordTrace]
  refine ⟨12419675307372539518699805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8279783538248359679133203 12419675307372539518699805)
  ·
    refine ⟨4657378240264702319512427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12419675307372539518699805 4657378240264702319512427)
    ·
      refine ⟨6986067360397053479268641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4657378240264702319512427 6986067360397053479268641)
      ·
        refine ⟨5239550520297790109451481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6986067360397053479268641 5239550520297790109451481)
        ·
          refine ⟨3929662890223342582088611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5239550520297790109451481 3929662890223342582088611)
          ·
            refine ⟨5894494335335013873132917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3929662890223342582088611 5894494335335013873132917)
            ·
              refine ⟨552608843937657550606211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5894494335335013873132917 552608843937657550606211)
              ·
                refine ⟨828913265906486325909317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 552608843937657550606211 828913265906486325909317)
                ·
                  refine ⟨155421237357466186107997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 828913265906486325909317 155421237357466186107997)
                  ·
                    rfl

theorem cell20_340517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 5, 1, 4].length) (baseStart_340517 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_340517 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_340517 prefixEnd_340517 := by exact prefixLift 340517
  have htrace : WordTrace (prefixWord ++ tailWord_340517) baseStart_340517 baseEnd_340517 := by
    simpa [prefixWord, tailWord_340517, baseEnd_340517] using wordTrace_append hprefix tailTrace_340517
  have hstable : (prefixWord ++ tailWord_340517).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_340517).length < 2 ^ (prefixWord ++ tailWord_340517).sum := by decide
  have hdescent : baseEnd_340517 < baseStart_340517 := by decide
  rcases family_descends (prefixWord ++ tailWord_340517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_340586 : List Nat := [3, 1, 3, 2, 1, 1, 1, 5, 3]
def baseStart_340586 : Nat := 118140960795 + 340586 * 2 ^ 59
def prefixEnd_340586 : Nat := 4983230072969 + 3 ^ 40 * 340586 * 2
def baseEnd_340586 : Nat := 155452730837608612807715

theorem tailTrace_340586 : CollatzResearch.WordTrace tailWord_340586 prefixEnd_340586 155452730837608612807715 := by
  unfold tailWord_340586
  simp only [CollatzResearch.WordTrace]
  refine ⟨3105547986030641075740403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8281461296081709535307741 3105547986030641075740403)
  ·
    refine ⟨4658321979045961613610605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3105547986030641075740403 4658321979045961613610605)
    ·
      refine ⟨1746870742142235605103977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4658321979045961613610605 1746870742142235605103977)
      ·
        refine ⟨1310153056606676703827983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1746870742142235605103977 1310153056606676703827983)
        ·
          refine ⟨1965229584910015055741975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1310153056606676703827983 1965229584910015055741975)
          ·
            refine ⟨2947844377365022583612963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1965229584910015055741975 2947844377365022583612963)
            ·
              refine ⟨4421766566047533875419445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2947844377365022583612963 4421766566047533875419445)
              ·
                refine ⟨414540615566956300820573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4421766566047533875419445 414540615566956300820573)
                ·
                  refine ⟨155452730837608612807715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 414540615566956300820573 155452730837608612807715)
                  ·
                    rfl

theorem cell20_340586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 5, 3].length) (baseStart_340586 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_340586 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_340586 prefixEnd_340586 := by exact prefixLift 340586
  have htrace : WordTrace (prefixWord ++ tailWord_340586) baseStart_340586 baseEnd_340586 := by
    simpa [prefixWord, tailWord_340586, baseEnd_340586] using wordTrace_append hprefix tailTrace_340586
  have hstable : (prefixWord ++ tailWord_340586).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_340586).length < 2 ^ (prefixWord ++ tailWord_340586).sum := by decide
  have hdescent : baseEnd_340586 < baseStart_340586 := by decide
  rcases family_descends (prefixWord ++ tailWord_340586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_340631 : List Nat := [1, 1, 3, 3, 2, 1, 4, 1, 4]
def baseStart_340631 : Nat := 118140960795 + 340631 * 2 ^ 59
def prefixEnd_340631 : Nat := 4983230072969 + 3 ^ 40 * 340631 * 2
def baseEnd_340631 : Nat := 155473270063788456307531

theorem tailTrace_340631 : CollatzResearch.WordTrace tailWord_340631 prefixEnd_340631 155473270063788456307531 := by
  unfold tailWord_340631
  simp only [CollatzResearch.WordTrace]
  refine ⟨12423833228959536988349747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8282555485973024658899831 12423833228959536988349747)
  ·
    refine ⟨18635749843439305482524621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12423833228959536988349747 18635749843439305482524621)
    ·
      refine ⟨6988406191289739555946733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18635749843439305482524621 6988406191289739555946733)
      ·
        refine ⟨2620652321733652333480025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6988406191289739555946733 2620652321733652333480025)
        ·
          refine ⟨1965489241300239250110019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2620652321733652333480025 1965489241300239250110019)
          ·
            refine ⟨2948233861950358875165029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1965489241300239250110019 2948233861950358875165029)
            ·
              refine ⟨552793849115692289093443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2948233861950358875165029 552793849115692289093443)
              ·
                refine ⟨829190773673538433640165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 552793849115692289093443 829190773673538433640165)
                ·
                  refine ⟨155473270063788456307531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 829190773673538433640165 155473270063788456307531)
                  ·
                    rfl

theorem cell20_340631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 4, 1, 4].length) (baseStart_340631 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_340631 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_340631 prefixEnd_340631 := by exact prefixLift 340631
  have htrace : WordTrace (prefixWord ++ tailWord_340631) baseStart_340631 baseEnd_340631 := by
    simpa [prefixWord, tailWord_340631, baseEnd_340631] using wordTrace_append hprefix tailTrace_340631
  have hstable : (prefixWord ++ tailWord_340631).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_340631).length < 2 ^ (prefixWord ++ tailWord_340631).sum := by decide
  have hdescent : baseEnd_340631 < baseStart_340631 := by decide
  rcases family_descends (prefixWord ++ tailWord_340631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_340655 : List Nat := [1, 1, 2, 1, 2, 7, 2, 4]
def baseStart_340655 : Nat := 118140960795 + 340655 * 2 ^ 59
def prefixEnd_340655 : Nat := 4983230072969 + 3 ^ 40 * 340655 * 2
def baseEnd_340655 : Nat := 51828074772583679835811

theorem tailTrace_340655 : CollatzResearch.WordTrace tailWord_340655 prefixEnd_340655 51828074772583679835811 := by
  unfold tailWord_340655
  simp only [CollatzResearch.WordTrace]
  refine ⟨12424708580872589087223419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8283139053915059391482279 12424708580872589087223419)
  ·
    refine ⟨18637062871308883630835129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12424708580872589087223419 18637062871308883630835129)
    ·
      refine ⟨13977797153481662723126347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18637062871308883630835129 13977797153481662723126347)
      ·
        refine ⟨20966695730222494084689521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13977797153481662723126347 20966695730222494084689521)
        ·
          refine ⟨15725021797666870563517141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20966695730222494084689521 15725021797666870563517141)
          ·
            refine ⟨368555198382817278832433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 15725021797666870563517141 368555198382817278832433)
            ·
              refine ⟨276416398787112959124325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 368555198382817278832433 276416398787112959124325)
              ·
                refine ⟨51828074772583679835811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 276416398787112959124325 51828074772583679835811)
                ·
                  rfl

theorem cell20_340655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 7, 2, 4].length) (baseStart_340655 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_340655 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_340655 prefixEnd_340655 := by exact prefixLift 340655
  have htrace : WordTrace (prefixWord ++ tailWord_340655) baseStart_340655 baseEnd_340655 := by
    simpa [prefixWord, tailWord_340655, baseEnd_340655] using wordTrace_append hprefix tailTrace_340655
  have hstable : (prefixWord ++ tailWord_340655).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_340655).length < 2 ^ (prefixWord ++ tailWord_340655).sum := by decide
  have hdescent : baseEnd_340655 < baseStart_340655 := by decide
  rcases family_descends (prefixWord ++ tailWord_340655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_340676 : List Nat := [2, 3, 3, 1, 1, 2, 8]
def baseStart_340676 : Nat := 118140960795 + 340676 * 2 ^ 59
def prefixEnd_340676 : Nat := 4983230072969 + 3 ^ 40 * 340676 * 2
def baseEnd_340676 : Nat := 17277089921107588867483

theorem tailTrace_340676 : CollatzResearch.WordTrace tailWord_340676 prefixEnd_340676 17277089921107588867483 := by
  unfold tailWord_340676
  simp only [CollatzResearch.WordTrace]
  refine ⟨6212737256898254836868941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8283649675864339782491921 6212737256898254836868941)
  ·
    refine ⟨2329776471336845563825853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6212737256898254836868941 2329776471336845563825853)
    ·
      refine ⟨873666176751317086434695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2329776471336845563825853 873666176751317086434695)
      ·
        refine ⟨1310499265126975629652043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 873666176751317086434695 1310499265126975629652043)
        ·
          refine ⟨1965748897690463444478065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1310499265126975629652043 1965748897690463444478065)
          ·
            refine ⟨1474311673267847583358549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1965748897690463444478065 1474311673267847583358549)
            ·
              refine ⟨17277089921107588867483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1474311673267847583358549 17277089921107588867483)
              ·
                rfl

theorem cell20_340676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 8].length) (baseStart_340676 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_340676 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_340676 prefixEnd_340676 := by exact prefixLift 340676
  have htrace : WordTrace (prefixWord ++ tailWord_340676) baseStart_340676 baseEnd_340676 := by
    simpa [prefixWord, tailWord_340676, baseEnd_340676] using wordTrace_append hprefix tailTrace_340676
  have hstable : (prefixWord ++ tailWord_340676).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_340676).length < 2 ^ (prefixWord ++ tailWord_340676).sum := by decide
  have hdescent : baseEnd_340676 < baseStart_340676 := by decide
  rcases family_descends (prefixWord ++ tailWord_340676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_340678 : List Nat := [6, 1, 2, 1, 2, 1, 3, 2, 2]
def baseStart_340678 : Nat := 118140960795 + 340678 * 2 ^ 59
def prefixEnd_340678 : Nat := 4983230072969 + 3 ^ 40 * 340678 * 2
def baseEnd_340678 : Nat := 155494722144465181740673

theorem tailTrace_340678 : CollatzResearch.WordTrace tailWord_340678 prefixEnd_340678 155494722144465181740673 := by
  unfold tailWord_340678
  simp only [CollatzResearch.WordTrace]
  refine ⟨388298358118414500478459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 8283698306526176010207125 388298358118414500478459)
  ·
    refine ⟨582447537177621750717689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 388298358118414500478459 582447537177621750717689)
    ·
      refine ⟨436835652883216313038267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 582447537177621750717689 436835652883216313038267)
      ·
        refine ⟨655253479324824469557401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 436835652883216313038267 655253479324824469557401)
        ·
          refine ⟨491440109493618352168051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 655253479324824469557401 491440109493618352168051)
          ·
            refine ⟨737160164240427528252077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 491440109493618352168051 737160164240427528252077)
            ·
              refine ⟨276435061590160323094529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 737160164240427528252077 276435061590160323094529)
              ·
                refine ⟨207326296192620242320897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 276435061590160323094529 207326296192620242320897)
                ·
                  refine ⟨155494722144465181740673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 207326296192620242320897 155494722144465181740673)
                  ·
                    rfl

theorem cell20_340678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 3, 2, 2].length) (baseStart_340678 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_340678 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_340678 prefixEnd_340678 := by exact prefixLift 340678
  have htrace : WordTrace (prefixWord ++ tailWord_340678) baseStart_340678 baseEnd_340678 := by
    simpa [prefixWord, tailWord_340678, baseEnd_340678] using wordTrace_append hprefix tailTrace_340678
  have hstable : (prefixWord ++ tailWord_340678).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_340678).length < 2 ^ (prefixWord ++ tailWord_340678).sum := by decide
  have hdescent : baseEnd_340678 < baseStart_340678 := by decide
  rcases family_descends (prefixWord ++ tailWord_340678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_340686 : List Nat := [4, 1, 1, 1, 3, 4, 1, 1, 4]
def baseStart_340686 : Nat := 118140960795 + 340686 * 2 ^ 59
def prefixEnd_340686 : Nat := 4983230072969 + 3 ^ 40 * 340686 * 2
def baseEnd_340686 : Nat := 155498373562452709473973

theorem tailTrace_340686 : CollatzResearch.WordTrace tailWord_340686 prefixEnd_340686 155498373562452709473973 := by
  unfold tailWord_340686
  simp only [CollatzResearch.WordTrace]
  refine ⟨1553229905470035172700239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8283892829173520921067941 1553229905470035172700239)
  ·
    refine ⟨2329844858205052759050359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1553229905470035172700239 2329844858205052759050359)
    ·
      refine ⟨3494767287307579138575539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2329844858205052759050359 3494767287307579138575539)
      ·
        refine ⟨5242150930961368707863309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3494767287307579138575539 5242150930961368707863309)
        ·
          refine ⟨1965806599110513265448741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5242150930961368707863309 1965806599110513265448741)
          ·
            refine ⟨368588737333221237271639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1965806599110513265448741 368588737333221237271639)
            ·
              refine ⟨552883105999831855907459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 368588737333221237271639 552883105999831855907459)
              ·
                refine ⟨829324658999747783861189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 552883105999831855907459 829324658999747783861189)
                ·
                  refine ⟨155498373562452709473973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 829324658999747783861189 155498373562452709473973)
                  ·
                    rfl

theorem cell20_340686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 4, 1, 1, 4].length) (baseStart_340686 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_340686 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_340686 prefixEnd_340686 := by exact prefixLift 340686
  have htrace : WordTrace (prefixWord ++ tailWord_340686) baseStart_340686 baseEnd_340686 := by
    simpa [prefixWord, tailWord_340686, baseEnd_340686] using wordTrace_append hprefix tailTrace_340686
  have hstable : (prefixWord ++ tailWord_340686).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_340686).length < 2 ^ (prefixWord ++ tailWord_340686).sum := by decide
  have hdescent : baseEnd_340686 < baseStart_340686 := by decide
  rcases family_descends (prefixWord ++ tailWord_340686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_340834 : List Nat := [3, 3, 2, 1, 3, 2, 1, 3, 2]
def baseStart_340834 : Nat := 118140960795 + 340834 * 2 ^ 59
def prefixEnd_340834 : Nat := 4983230072969 + 3 ^ 40 * 340834 * 2
def baseEnd_340834 : Nat := 155565924795221972540035

theorem tailTrace_340834 : CollatzResearch.WordTrace tailWord_340834 prefixEnd_340834 155565924795221972540035 := by
  unfold tailWord_340834
  simp only [CollatzResearch.WordTrace]
  refine ⟨3107809311806025664497389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8287491498149401771993037 3107809311806025664497389)
  ·
    refine ⟨1165428491927259624186521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3107809311806025664497389 1165428491927259624186521)
    ·
      refine ⟨874071368945444718139891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1165428491927259624186521 874071368945444718139891)
      ·
        refine ⟨1311107053418167077209837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 874071368945444718139891 1311107053418167077209837)
        ·
          refine ⟨491665145031812653953689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1311107053418167077209837 491665145031812653953689)
          ·
            refine ⟨368748858773859490465267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 491665145031812653953689 368748858773859490465267)
            ·
              refine ⟨553123288160789235697901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 368748858773859490465267 553123288160789235697901)
              ·
                refine ⟨207421233060295963386713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 553123288160789235697901 207421233060295963386713)
                ·
                  refine ⟨155565924795221972540035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 207421233060295963386713 155565924795221972540035)
                  ·
                    rfl

theorem cell20_340834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 2, 1, 3, 2].length) (baseStart_340834 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_340834 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_340834 prefixEnd_340834 := by exact prefixLift 340834
  have htrace : WordTrace (prefixWord ++ tailWord_340834) baseStart_340834 baseEnd_340834 := by
    simpa [prefixWord, tailWord_340834, baseEnd_340834] using wordTrace_append hprefix tailTrace_340834
  have hstable : (prefixWord ++ tailWord_340834).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_340834).length < 2 ^ (prefixWord ++ tailWord_340834).sum := by decide
  have hdescent : baseEnd_340834 < baseStart_340834 := by decide
  rcases family_descends (prefixWord ++ tailWord_340834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_340835 : List Nat := [1, 1, 1, 5, 3, 1, 1, 2, 5]
def baseStart_340835 : Nat := 118140960795 + 340835 * 2 ^ 59
def prefixEnd_340835 : Nat := 4983230072969 + 3 ^ 40 * 340835 * 2
def baseEnd_340835 : Nat := 155566381222470413506697

theorem tailTrace_340835 : CollatzResearch.WordTrace tailWord_340835 prefixEnd_340835 155566381222470413506697 := by
  unfold tailWord_340835
  simp only [CollatzResearch.WordTrace]
  refine ⟨12431273720220479828775959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8287515813480319885850639 12431273720220479828775959)
  ·
    refine ⟨18646910580330719743163939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12431273720220479828775959 18646910580330719743163939)
    ·
      refine ⟨27970365870496079614745909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18646910580330719743163939 27970365870496079614745909)
      ·
        refine ⟨2622221800359007463882429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 27970365870496079614745909 2622221800359007463882429)
        ·
          refine ⟨983333175134627798955911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2622221800359007463882429 983333175134627798955911)
          ·
            refine ⟨1474999762701941698433867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 983333175134627798955911 1474999762701941698433867)
            ·
              refine ⟨2212499644052912547650801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1474999762701941698433867 2212499644052912547650801)
              ·
                refine ⟨1659374733039684410738101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2212499644052912547650801 1659374733039684410738101)
                ·
                  refine ⟨155566381222470413506697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1659374733039684410738101 155566381222470413506697)
                  ·
                    rfl

theorem cell20_340835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 1, 2, 5].length) (baseStart_340835 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_340835 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_340835 prefixEnd_340835 := by exact prefixLift 340835
  have htrace : WordTrace (prefixWord ++ tailWord_340835) baseStart_340835 baseEnd_340835 := by
    simpa [prefixWord, tailWord_340835, baseEnd_340835] using wordTrace_append hprefix tailTrace_340835
  have hstable : (prefixWord ++ tailWord_340835).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_340835).length < 2 ^ (prefixWord ++ tailWord_340835).sum := by decide
  have hdescent : baseEnd_340835 < baseStart_340835 := by decide
  rcases family_descends (prefixWord ++ tailWord_340835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_340849 : List Nat := [1, 2, 2, 2, 1, 4, 8]
def baseStart_340849 : Nat := 118140960795 + 340849 * 2 ^ 59
def prefixEnd_340849 : Nat := 4983230072969 + 3 ^ 40 * 340849 * 2
def baseEnd_340849 : Nat := 17285863467105398559997

theorem tailTrace_340849 : CollatzResearch.WordTrace tailWord_340849 prefixEnd_340849 17285863467105398559997 := by
  unfold tailWord_340849
  simp only [CollatzResearch.WordTrace]
  refine ⟨12431784342169760219785601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8287856228113173479857067 12431784342169760219785601)
  ·
    refine ⟨9323838256627320164839201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12431784342169760219785601 9323838256627320164839201)
    ·
      refine ⟨6992878692470490123629401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9323838256627320164839201 6992878692470490123629401)
      ·
        refine ⟨5244659019352867592722051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6992878692470490123629401 5244659019352867592722051)
        ·
          refine ⟨7866988529029301389083077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5244659019352867592722051 7866988529029301389083077)
          ·
            refine ⟨1475060349192994010453077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7866988529029301389083077 1475060349192994010453077)
            ·
              refine ⟨17285863467105398559997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1475060349192994010453077 17285863467105398559997)
              ·
                rfl

theorem cell20_340849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 8].length) (baseStart_340849 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_340849 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_340849 prefixEnd_340849 := by exact prefixLift 340849
  have htrace : WordTrace (prefixWord ++ tailWord_340849) baseStart_340849 baseEnd_340849 := by
    simpa [prefixWord, tailWord_340849, baseEnd_340849] using wordTrace_append hprefix tailTrace_340849
  have hstable : (prefixWord ++ tailWord_340849).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_340849).length < 2 ^ (prefixWord ++ tailWord_340849).sum := by decide
  have hdescent : baseEnd_340849 < baseStart_340849 := by decide
  rcases family_descends (prefixWord ++ tailWord_340849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_340859 : List Nat := [1, 1, 1, 1, 1, 5, 2, 6, 2]
def baseStart_340859 : Nat := 118140960795 + 340859 * 2 ^ 59
def prefixEnd_340859 : Nat := 4983230072969 + 3 ^ 40 * 340859 * 2
def baseEnd_340859 : Nat := 155577335476432996706599

theorem tailTrace_340859 : CollatzResearch.WordTrace tailWord_340859 prefixEnd_340859 155577335476432996706599 := by
  unfold tailWord_340859
  simp only [CollatzResearch.WordTrace]
  refine ⟨12432149072133531927649631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8288099381422354618433087 12432149072133531927649631)
  ·
    refine ⟨18648223608200297891474447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12432149072133531927649631 18648223608200297891474447)
    ·
      refine ⟨27972335412300446837211671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18648223608200297891474447 27972335412300446837211671)
      ·
        refine ⟨41958503118450670255817507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27972335412300446837211671 41958503118450670255817507)
        ·
          refine ⟨62937754677676005383726261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41958503118450670255817507 62937754677676005383726261)
          ·
            refine ⟨5900414501032125504724337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 62937754677676005383726261 5900414501032125504724337)
            ·
              refine ⟨4425310875774094128543253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5900414501032125504724337 4425310875774094128543253)
              ·
                refine ⟨207436447301910662275465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 4425310875774094128543253 207436447301910662275465)
                ·
                  refine ⟨155577335476432996706599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 207436447301910662275465 155577335476432996706599)
                  ·
                    rfl

theorem cell20_340859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 6, 2].length) (baseStart_340859 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_340859 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_340859 prefixEnd_340859 := by exact prefixLift 340859
  have htrace : WordTrace (prefixWord ++ tailWord_340859) baseStart_340859 baseEnd_340859 := by
    simpa [prefixWord, tailWord_340859, baseEnd_340859] using wordTrace_append hprefix tailTrace_340859
  have hstable : (prefixWord ++ tailWord_340859).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_340859).length < 2 ^ (prefixWord ++ tailWord_340859).sum := by decide
  have hdescent : baseEnd_340859 < baseStart_340859 := by decide
  rcases family_descends (prefixWord ++ tailWord_340859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_340862 : List Nat := [4, 2, 3, 1, 2, 1, 2, 5]
def baseStart_340862 : Nat := 118140960795 + 340862 * 2 ^ 59
def prefixEnd_340862 : Nat := 4983230072969 + 3 ^ 40 * 340862 * 2
def baseEnd_340862 : Nat := 51859568252726106535529

theorem tailTrace_340862 : CollatzResearch.WordTrace tailWord_340862 prefixEnd_340862 51859568252726106535529 := by
  unfold tailWord_340862
  simp only [CollatzResearch.WordTrace]
  refine ⟨1554032311390332930001105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8288172327415108960005893 1554032311390332930001105)
  ·
    refine ⟨1165524233542749697500829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1554032311390332930001105 1165524233542749697500829)
    ·
      refine ⟨437071587578531136562811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1165524233542749697500829 437071587578531136562811)
      ·
        refine ⟨655607381367796704844217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 437071587578531136562811 655607381367796704844217)
        ·
          refine ⟨491705536025847528633163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 655607381367796704844217 491705536025847528633163)
          ·
            refine ⟨737558304038771292949745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 491705536025847528633163 737558304038771292949745)
            ·
              refine ⟨553168728029078469712309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 737558304038771292949745 553168728029078469712309)
              ·
                refine ⟨51859568252726106535529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 553168728029078469712309 51859568252726106535529)
                ·
                  rfl

theorem cell20_340862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 2, 5].length) (baseStart_340862 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_340862 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_340862 prefixEnd_340862 := by exact prefixLift 340862
  have htrace : WordTrace (prefixWord ++ tailWord_340862) baseStart_340862 baseEnd_340862 := by
    simpa [prefixWord, tailWord_340862, baseEnd_340862] using wordTrace_append hprefix tailTrace_340862
  have hstable : (prefixWord ++ tailWord_340862).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_340862).length < 2 ^ (prefixWord ++ tailWord_340862).sum := by decide
  have hdescent : baseEnd_340862 < baseStart_340862 := by decide
  rcases family_descends (prefixWord ++ tailWord_340862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_340869 : List Nat := [1, 3, 1, 1, 3, 5, 2, 1, 3]
def baseStart_340869 : Nat := 118140960795 + 340869 * 2 ^ 59
def prefixEnd_340869 : Nat := 4983230072969 + 3 ^ 40 * 340869 * 2
def baseEnd_340869 : Nat := 155581899748917406373225

theorem tailTrace_340869 : CollatzResearch.WordTrace tailWord_340869 prefixEnd_340869 155581899748917406373225 := by
  unfold tailWord_340869
  simp only [CollatzResearch.WordTrace]
  refine ⟨12432513802097303635513661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8288342534731535757009107 12432513802097303635513661)
  ·
    refine ⟨4662192675786488863317623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12432513802097303635513661 4662192675786488863317623)
    ·
      refine ⟨6993289013679733294976435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4662192675786488863317623 6993289013679733294976435)
      ·
        refine ⟨10489933520519599942464653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6993289013679733294976435 10489933520519599942464653)
        ·
          refine ⟨3933725070194849978424245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10489933520519599942464653 3933725070194849978424245)
          ·
            refine ⟨368786725330767185477273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3933725070194849978424245 368786725330767185477273)
            ·
              refine ⟨276590043998075389107955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 368786725330767185477273 276590043998075389107955)
              ·
                refine ⟨414885065997113083661933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 276590043998075389107955 414885065997113083661933)
                ·
                  refine ⟨155581899748917406373225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 414885065997113083661933 155581899748917406373225)
                  ·
                    rfl

theorem cell20_340869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 5, 2, 1, 3].length) (baseStart_340869 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_340869 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_340869 prefixEnd_340869 := by exact prefixLift 340869
  have htrace : WordTrace (prefixWord ++ tailWord_340869) baseStart_340869 baseEnd_340869 := by
    simpa [prefixWord, tailWord_340869, baseEnd_340869] using wordTrace_append hprefix tailTrace_340869
  have hstable : (prefixWord ++ tailWord_340869).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_340869).length < 2 ^ (prefixWord ++ tailWord_340869).sum := by decide
  have hdescent : baseEnd_340869 < baseStart_340869 := by decide
  rcases family_descends (prefixWord ++ tailWord_340869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_340887 : List Nat := [1, 1, 3, 3, 1, 2, 1, 8]
def baseStart_340887 : Nat := 118140960795 + 340887 * 2 ^ 59
def prefixEnd_340887 : Nat := 4983230072969 + 3 ^ 40 * 340887 * 2
def baseEnd_340887 : Nat := 51863371813129781257717

theorem tailTrace_340887 : CollatzResearch.WordTrace tailWord_340887 prefixEnd_340887 51863371813129781257717 := by
  unfold tailWord_340887
  simp only [CollatzResearch.WordTrace]
  refine ⟨12433170316032092709668915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8288780210688061806445943 12433170316032092709668915)
  ·
    refine ⟨18649755474048139064503373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12433170316032092709668915 18649755474048139064503373)
    ·
      refine ⟨6993658302768052149188765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18649755474048139064503373 6993658302768052149188765)
      ·
        refine ⟨2622621863538019555945787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6993658302768052149188765 2622621863538019555945787)
        ·
          refine ⟨3933932795307029333918681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2622621863538019555945787 3933932795307029333918681)
          ·
            refine ⟨2950449596480272000439011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3933932795307029333918681 2950449596480272000439011)
            ·
              refine ⟨4425674394720408000658517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2950449596480272000439011 4425674394720408000658517)
              ·
                refine ⟨51863371813129781257717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4425674394720408000658517 51863371813129781257717)
                ·
                  rfl

theorem cell20_340887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 8].length) (baseStart_340887 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_340887 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_340887 prefixEnd_340887 := by exact prefixLift 340887
  have htrace : WordTrace (prefixWord ++ tailWord_340887) baseStart_340887 baseEnd_340887 := by
    simpa [prefixWord, tailWord_340887, baseEnd_340887] using wordTrace_append hprefix tailTrace_340887
  have hstable : (prefixWord ++ tailWord_340887).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_340887).length < 2 ^ (prefixWord ++ tailWord_340887).sum := by decide
  have hdescent : baseEnd_340887 < baseStart_340887 := by decide
  rcases family_descends (prefixWord ++ tailWord_340887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_340952 : List Nat := [2, 1, 2, 2, 2, 4, 2, 3, 2]
def baseStart_340952 : Nat := 118140960795 + 340952 * 2 ^ 59
def prefixEnd_340952 : Nat := 4983230072969 + 3 ^ 40 * 340952 * 2
def baseEnd_340952 : Nat := 155619783210538006606219

theorem tailTrace_340952 : CollatzResearch.WordTrace tailWord_340952 prefixEnd_340952 155619783210538006606219 := by
  unfold tailWord_340952
  simp only [CollatzResearch.WordTrace]
  refine ⟨6217770530398304405392555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8290360707197739207190073 6217770530398304405392555)
  ·
    refine ⟨9326655795597456608088833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6217770530398304405392555 9326655795597456608088833)
    ·
      refine ⟨6994991846698092456066625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9326655795597456608088833 6994991846698092456066625)
      ·
        refine ⟨5246243885023569342049969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6994991846698092456066625 5246243885023569342049969)
        ·
          refine ⟨3934682913767677006537477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5246243885023569342049969 3934682913767677006537477)
          ·
            refine ⟨737753046331439438725777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3934682913767677006537477 737753046331439438725777)
            ·
              refine ⟨553314784748579579044333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 737753046331439438725777 553314784748579579044333)
              ·
                refine ⟨207493044280717342141625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 553314784748579579044333 207493044280717342141625)
                ·
                  refine ⟨155619783210538006606219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 207493044280717342141625 155619783210538006606219)
                  ·
                    rfl

theorem cell20_340952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 2, 3, 2].length) (baseStart_340952 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_340952 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_340952 prefixEnd_340952 := by exact prefixLift 340952
  have htrace : WordTrace (prefixWord ++ tailWord_340952) baseStart_340952 baseEnd_340952 := by
    simpa [prefixWord, tailWord_340952, baseEnd_340952] using wordTrace_append hprefix tailTrace_340952
  have hstable : (prefixWord ++ tailWord_340952).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_340952).length < 2 ^ (prefixWord ++ tailWord_340952).sum := by decide
  have hdescent : baseEnd_340952 < baseStart_340952 := by decide
  rcases family_descends (prefixWord ++ tailWord_340952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_340962 : List Nat := [3, 3, 3, 1, 1, 3, 1, 2, 3]
def baseStart_340962 : Nat := 118140960795 + 340962 * 2 ^ 59
def prefixEnd_340962 : Nat := 4983230072969 + 3 ^ 40 * 340962 * 2
def baseEnd_340962 : Nat := 155624347483022416272845

theorem tailTrace_340962 : CollatzResearch.WordTrace tailWord_340962 prefixEnd_340962 155624347483022416272845 := by
  unfold tailWord_340962
  simp only [CollatzResearch.WordTrace]
  refine ⟨3108976447690095129662285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8290603860506920345766093 3108976447690095129662285)
  ·
    refine ⟨1165866167883785673623357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3108976447690095129662285 1165866167883785673623357)
    ·
      refine ⟨437199812956419627608759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1165866167883785673623357 437199812956419627608759)
      ·
        refine ⟨655799719434629441413139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 437199812956419627608759 655799719434629441413139)
        ·
          refine ⟨983699579151944162119709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 655799719434629441413139 983699579151944162119709)
          ·
            refine ⟨368887342181979060794891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 983699579151944162119709 368887342181979060794891)
            ·
              refine ⟨553331013272968591192337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 368887342181979060794891 553331013272968591192337)
              ·
                refine ⟨414998259954726443394253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 553331013272968591192337 414998259954726443394253)
                ·
                  refine ⟨155624347483022416272845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 414998259954726443394253 155624347483022416272845)
                  ·
                    rfl

theorem cell20_340962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 3, 1, 2, 3].length) (baseStart_340962 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_340962 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_340962 prefixEnd_340962 := by exact prefixLift 340962
  have htrace : WordTrace (prefixWord ++ tailWord_340962) baseStart_340962 baseEnd_340962 := by
    simpa [prefixWord, tailWord_340962, baseEnd_340962] using wordTrace_append hprefix tailTrace_340962
  have hstable : (prefixWord ++ tailWord_340962).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_340962).length < 2 ^ (prefixWord ++ tailWord_340962).sum := by decide
  have hdescent : baseEnd_340962 < baseStart_340962 := by decide
  rcases family_descends (prefixWord ++ tailWord_340962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_340963 : List Nat := [1, 1, 1, 6, 1, 1, 9]
def baseStart_340963 : Nat := 118140960795 + 340963 * 2 ^ 59
def prefixEnd_340963 : Nat := 4983230072969 + 3 ^ 40 * 340963 * 2
def baseEnd_340963 : Nat := 17291644878918984137723

theorem tailTrace_340963 : CollatzResearch.WordTrace tailWord_340963 prefixEnd_340963 17291644878918984137723 := by
  unfold tailWord_340963
  simp only [CollatzResearch.WordTrace]
  refine ⟨12435942263756757689435543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8290628175837838459623695 12435942263756757689435543)
  ·
    refine ⟨18653913395635136534153315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12435942263756757689435543 18653913395635136534153315)
    ·
      refine ⟨27980870093452704801229973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18653913395635136534153315 27980870093452704801229973)
      ·
        refine ⟨1311603285630595537557655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 27980870093452704801229973 1311603285630595537557655)
        ·
          refine ⟨1967404928445893306336483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1311603285630595537557655 1967404928445893306336483)
          ·
            refine ⟨2951107392668839959504725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1967404928445893306336483 2951107392668839959504725)
            ·
              refine ⟨17291644878918984137723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2951107392668839959504725 17291644878918984137723)
              ·
                rfl

theorem cell20_340963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 9].length) (baseStart_340963 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_340963 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_340963 prefixEnd_340963 := by exact prefixLift 340963
  have htrace : WordTrace (prefixWord ++ tailWord_340963) baseStart_340963 baseEnd_340963 := by
    simpa [prefixWord, tailWord_340963, baseEnd_340963] using wordTrace_append hprefix tailTrace_340963
  have hstable : (prefixWord ++ tailWord_340963).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_340963).length < 2 ^ (prefixWord ++ tailWord_340963).sum := by decide
  have hdescent : baseEnd_340963 < baseStart_340963 := by decide
  rcases family_descends (prefixWord ++ tailWord_340963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_341024 : List Nat := [2, 1, 1, 7, 1, 1, 3, 2, 2]
def baseStart_341024 : Nat := 118140960795 + 341024 * 2 ^ 59
def prefixEnd_341024 : Nat := 4983230072969 + 3 ^ 40 * 341024 * 2
def baseEnd_341024 : Nat := 155652645972425756205925

theorem tailTrace_341024 : CollatzResearch.WordTrace tailWord_341024 prefixEnd_341024 155652645972425756205925 := by
  unfold tailWord_341024
  simp only [CollatzResearch.WordTrace]
  refine ⟨6219083558267882553703063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8292111411023843404937417 6219083558267882553703063)
  ·
    refine ⟨9328625337401823830554595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6219083558267882553703063 9328625337401823830554595)
    ·
      refine ⟨13992938006102735745831893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9328625337401823830554595 13992938006102735745831893)
      ·
        refine ⟨327959484518032869042935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 13992938006102735745831893 327959484518032869042935)
        ·
          refine ⟨491939226777049303564403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 327959484518032869042935 491939226777049303564403)
          ·
            refine ⟨737908840165573955346605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 491939226777049303564403 737908840165573955346605)
            ·
              refine ⟨276715815062090233254977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 737908840165573955346605 276715815062090233254977)
              ·
                refine ⟨207536861296567674941233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 276715815062090233254977 207536861296567674941233)
                ·
                  refine ⟨155652645972425756205925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 207536861296567674941233 155652645972425756205925)
                  ·
                    rfl

theorem cell20_341024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 3, 2, 2].length) (baseStart_341024 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_341024 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_341024 prefixEnd_341024 := by exact prefixLift 341024
  have htrace : WordTrace (prefixWord ++ tailWord_341024) baseStart_341024 baseEnd_341024 := by
    simpa [prefixWord, tailWord_341024, baseEnd_341024] using wordTrace_append hprefix tailTrace_341024
  have hstable : (prefixWord ++ tailWord_341024).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_341024).length < 2 ^ (prefixWord ++ tailWord_341024).sum := by decide
  have hdescent : baseEnd_341024 < baseStart_341024 := by decide
  rcases family_descends (prefixWord ++ tailWord_341024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_341025 : List Nat := [1, 2, 3, 2, 3, 1, 2, 1, 5]
def baseStart_341025 : Nat := 118140960795 + 341025 * 2 ^ 59
def prefixEnd_341025 : Nat := 4983230072969 + 3 ^ 40 * 341025 * 2
def baseEnd_341025 : Nat := 155653102399674197172587

theorem tailTrace_341025 : CollatzResearch.WordTrace tailWord_341025 prefixEnd_341025 155653102399674197172587 := by
  unfold tailWord_341025
  simp only [CollatzResearch.WordTrace]
  refine ⟨12438203589532142278192529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8292135726354761518795019 12438203589532142278192529)
  ·
    refine ⟨9328652692149106708644397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12438203589532142278192529 9328652692149106708644397)
    ·
      refine ⟨3498244759555915015741649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9328652692149106708644397 3498244759555915015741649)
      ·
        refine ⟨2623683569666936261806237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3498244759555915015741649 2623683569666936261806237)
        ·
          refine ⟨983881338625101098177339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2623683569666936261806237 983881338625101098177339)
          ·
            refine ⟨1475822007937651647266009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 983881338625101098177339 1475822007937651647266009)
            ·
              refine ⟨1106866505953238735449507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1475822007937651647266009 1106866505953238735449507)
              ·
                refine ⟨1660299758929858103174261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1106866505953238735449507 1660299758929858103174261)
                ·
                  refine ⟨155653102399674197172587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1660299758929858103174261 155653102399674197172587)
                  ·
                    rfl

theorem cell20_341025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 2, 1, 5].length) (baseStart_341025 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_341025 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_341025 prefixEnd_341025 := by exact prefixLift 341025
  have htrace : WordTrace (prefixWord ++ tailWord_341025) baseStart_341025 baseEnd_341025 := by
    simpa [prefixWord, tailWord_341025, baseEnd_341025] using wordTrace_append hprefix tailTrace_341025
  have hstable : (prefixWord ++ tailWord_341025).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_341025).length < 2 ^ (prefixWord ++ tailWord_341025).sum := by decide
  have hdescent : baseEnd_341025 < baseStart_341025 := by decide
  rcases family_descends (prefixWord ++ tailWord_341025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_341028 : List Nat := [2, 3, 1, 4, 1, 3, 1, 1, 4]
def baseStart_341028 : Nat := 118140960795 + 341028 * 2 ^ 59
def prefixEnd_341028 : Nat := 4983230072969 + 3 ^ 40 * 341028 * 2
def baseEnd_341028 : Nat := 155654471681419520072575

theorem tailTrace_341028 : CollatzResearch.WordTrace tailWord_341028 prefixEnd_341028 155654471681419520072575 := by
  unfold tailWord_341028
  simp only [CollatzResearch.WordTrace]
  refine ⟨6219156504260636895275869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8292208672347515860367825 6219156504260636895275869)
  ·
    refine ⟨2332183689097738835728451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6219156504260636895275869 2332183689097738835728451)
    ·
      refine ⟨3498275533646608253592677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2332183689097738835728451 3498275533646608253592677)
      ·
        refine ⟨655926662558739047548627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3498275533646608253592677 655926662558739047548627)
        ·
          refine ⟨983889993838108571322941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 655926662558739047548627 983889993838108571322941)
          ·
            refine ⟨368958747689290714246103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 983889993838108571322941 368958747689290714246103)
            ·
              refine ⟨553438121533936071369155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 368958747689290714246103 553438121533936071369155)
              ·
                refine ⟨830157182300904107053733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 553438121533936071369155 830157182300904107053733)
                ·
                  refine ⟨155654471681419520072575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 830157182300904107053733 155654471681419520072575)
                  ·
                    rfl

theorem cell20_341028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 3, 1, 1, 4].length) (baseStart_341028 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_341028 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_341028 prefixEnd_341028 := by exact prefixLift 341028
  have htrace : WordTrace (prefixWord ++ tailWord_341028) baseStart_341028 baseEnd_341028 := by
    simpa [prefixWord, tailWord_341028, baseEnd_341028] using wordTrace_append hprefix tailTrace_341028
  have hstable : (prefixWord ++ tailWord_341028).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_341028).length < 2 ^ (prefixWord ++ tailWord_341028).sum := by decide
  have hdescent : baseEnd_341028 < baseStart_341028 := by decide
  rcases family_descends (prefixWord ++ tailWord_341028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_341087 : List Nat := [1, 1, 2, 3, 1, 1, 5, 4, 2]
def baseStart_341087 : Nat := 118140960795 + 341087 * 2 ^ 59
def prefixEnd_341087 : Nat := 4983230072969 + 3 ^ 40 * 341087 * 2
def baseEnd_341087 : Nat := 155681400889077537105667

theorem tailTrace_341087 : CollatzResearch.WordTrace tailWord_341087 prefixEnd_341087 155681400889077537105667 := by
  unfold tailWord_341087
  simp only [CollatzResearch.WordTrace]
  refine ⟨12440464915307526866949515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8293643276871684577966343 12440464915307526866949515)
  ·
    refine ⟨18660697372961290300424273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12440464915307526866949515 18660697372961290300424273)
    ·
      refine ⟨13995523029720967725318205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18660697372961290300424273 13995523029720967725318205)
      ·
        refine ⟨5248321136145362896994327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13995523029720967725318205 5248321136145362896994327)
        ·
          refine ⟨7872481704218044345491491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5248321136145362896994327 7872481704218044345491491)
          ·
            refine ⟨11808722556327066518237237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7872481704218044345491491 11808722556327066518237237)
            ·
              refine ⟨1107067739655662486084741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11808722556327066518237237 1107067739655662486084741)
              ·
                refine ⟨207575201185436716140889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1107067739655662486084741 207575201185436716140889)
                ·
                  refine ⟨155681400889077537105667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 207575201185436716140889 155681400889077537105667)
                  ·
                    rfl

theorem cell20_341087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 5, 4, 2].length) (baseStart_341087 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_341087 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_341087 prefixEnd_341087 := by exact prefixLift 341087
  have htrace : WordTrace (prefixWord ++ tailWord_341087) baseStart_341087 baseEnd_341087 := by
    simpa [prefixWord, tailWord_341087, baseEnd_341087] using wordTrace_append hprefix tailTrace_341087
  have hstable : (prefixWord ++ tailWord_341087).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_341087).length < 2 ^ (prefixWord ++ tailWord_341087).sum := by decide
  have hdescent : baseEnd_341087 < baseStart_341087 := by decide
  rcases family_descends (prefixWord ++ tailWord_341087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_341139 : List Nat := [1, 1, 1, 2, 1, 2, 7, 2, 3]
def baseStart_341139 : Nat := 118140960795 + 341139 * 2 ^ 59
def prefixEnd_341139 : Nat := 4983230072969 + 3 ^ 40 * 341139 * 2
def baseEnd_341139 : Nat := 155705135105996467372121

theorem tailTrace_341139 : CollatzResearch.WordTrace tailWord_341139 prefixEnd_341139 155705135105996467372121 := by
  unfold tailWord_341139
  simp only [CollatzResearch.WordTrace]
  refine ⟨12442361511119139747842471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8294907674079426498561647 12442361511119139747842471)
  ·
    refine ⟨18663542266678709621763707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12442361511119139747842471 18663542266678709621763707)
    ·
      refine ⟨27995313400018064432645561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18663542266678709621763707 27995313400018064432645561)
      ·
        refine ⟨20996485050013548324484171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27995313400018064432645561 20996485050013548324484171)
        ·
          refine ⟨31494727575020322486726257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20996485050013548324484171 31494727575020322486726257)
          ·
            refine ⟨23621045681265241865044693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31494727575020322486726257 23621045681265241865044693)
            ·
              refine ⟨553618258154654106211985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 23621045681265241865044693 553618258154654106211985)
              ·
                refine ⟨415213693615990579658989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 553618258154654106211985 415213693615990579658989)
                ·
                  refine ⟨155705135105996467372121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 415213693615990579658989 155705135105996467372121)
                  ·
                    rfl

theorem cell20_341139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 7, 2, 3].length) (baseStart_341139 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_341139 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_341139 prefixEnd_341139 := by exact prefixLift 341139
  have htrace : WordTrace (prefixWord ++ tailWord_341139) baseStart_341139 baseEnd_341139 := by
    simpa [prefixWord, tailWord_341139, baseEnd_341139] using wordTrace_append hprefix tailTrace_341139
  have hstable : (prefixWord ++ tailWord_341139).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_341139).length < 2 ^ (prefixWord ++ tailWord_341139).sum := by decide
  have hdescent : baseEnd_341139 < baseStart_341139 := by decide
  rcases family_descends (prefixWord ++ tailWord_341139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_341153 : List Nat := [1, 2, 3, 3, 1, 1, 2, 7]
def baseStart_341153 : Nat := 118140960795 + 341153 * 2 ^ 59
def prefixEnd_341153 : Nat := 4983230072969 + 3 ^ 40 * 341153 * 2
def baseEnd_341153 : Nat := 51903841695824880301799

theorem tailTrace_341153 : CollatzResearch.WordTrace tailWord_341153 prefixEnd_341153 51903841695824880301799 := by
  unfold tailWord_341153
  simp only [CollatzResearch.WordTrace]
  refine ⟨12442872133068420138852113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8295248088712280092568075 12442872133068420138852113)
  ·
    refine ⟨9332154099801315104139085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12442872133068420138852113 9332154099801315104139085)
    ·
      refine ⟨3499557787425493164052157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9332154099801315104139085 3499557787425493164052157)
      ·
        refine ⟨1312334170284559936519559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3499557787425493164052157 1312334170284559936519559)
        ·
          refine ⟨1968501255426839904779339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1312334170284559936519559 1968501255426839904779339)
          ·
            refine ⟨2952751883140259857169009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1968501255426839904779339 2952751883140259857169009)
            ·
              refine ⟨2214563912355194892876757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2952751883140259857169009 2214563912355194892876757)
              ·
                refine ⟨51903841695824880301799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2214563912355194892876757 51903841695824880301799)
                ·
                  rfl

theorem cell20_341153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 2, 7].length) (baseStart_341153 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_341153 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_341153 prefixEnd_341153 := by exact prefixLift 341153
  have htrace : WordTrace (prefixWord ++ tailWord_341153) baseStart_341153 baseEnd_341153 := by
    simpa [prefixWord, tailWord_341153, baseEnd_341153] using wordTrace_append hprefix tailTrace_341153
  have hstable : (prefixWord ++ tailWord_341153).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_341153).length < 2 ^ (prefixWord ++ tailWord_341153).sum := by decide
  have hdescent : baseEnd_341153 < baseStart_341153 := by decide
  rcases family_descends (prefixWord ++ tailWord_341153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_341170 : List Nat := [3, 2, 1, 1, 1, 4, 4, 4]
def baseStart_341170 : Nat := 118140960795 + 341170 * 2 ^ 59
def prefixEnd_341170 : Nat := 4983230072969 + 3 ^ 40 * 341170 * 2
def baseEnd_341170 : Nat := 51906428116899379112887

theorem tailTrace_341170 : CollatzResearch.WordTrace tailWord_341170 prefixEnd_341170 51906428116899379112887 := by
  unfold tailWord_341170
  simp only [CollatzResearch.WordTrace]
  refine ⟨3110873043501708010555241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8295661449337888028147309 3110873043501708010555241)
  ·
    refine ⟨2333154782626281007916431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3110873043501708010555241 2333154782626281007916431)
    ·
      refine ⟨3499732173939421511874647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2333154782626281007916431 3499732173939421511874647)
      ·
        refine ⟨5249598260909132267811971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3499732173939421511874647 5249598260909132267811971)
        ·
          refine ⟨7874397391363698401717957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5249598260909132267811971 7874397391363698401717957)
          ·
            refine ⟨1476449510880693450322117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7874397391363698401717957 1476449510880693450322117)
            ·
              refine ⟨276834283290130021935397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1476449510880693450322117 276834283290130021935397)
              ·
                refine ⟨51906428116899379112887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 276834283290130021935397 51906428116899379112887)
                ·
                  rfl

theorem cell20_341170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 4, 4].length) (baseStart_341170 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_341170 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_341170 prefixEnd_341170 := by exact prefixLift 341170
  have htrace : WordTrace (prefixWord ++ tailWord_341170) baseStart_341170 baseEnd_341170 := by
    simpa [prefixWord, tailWord_341170, baseEnd_341170] using wordTrace_append hprefix tailTrace_341170
  have hstable : (prefixWord ++ tailWord_341170).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_341170).length < 2 ^ (prefixWord ++ tailWord_341170).sum := by decide
  have hdescent : baseEnd_341170 < baseStart_341170 := by decide
  rcases family_descends (prefixWord ++ tailWord_341170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_341180 : List Nat := [2, 2, 2, 3, 2, 1, 3, 3, 2]
def baseStart_341180 : Nat := 118140960795 + 341180 * 2 ^ 59
def prefixEnd_341180 : Nat := 4983230072969 + 3 ^ 40 * 341180 * 2
def baseEnd_341180 : Nat := 155723848623182547005287

theorem tailTrace_341180 : CollatzResearch.WordTrace tailWord_341180 prefixEnd_341180 155723848623182547005287 := by
  unfold tailWord_341180
  simp only [CollatzResearch.WordTrace]
  refine ⟨6221928451985301875042497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8295904602647069166723329 6221928451985301875042497)
  ·
    refine ⟨4666446338988976406281873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6221928451985301875042497 4666446338988976406281873)
    ·
      refine ⟨3499834754241732304711405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4666446338988976406281873 3499834754241732304711405)
      ·
        refine ⟨1312438032840649614266777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3499834754241732304711405 1312438032840649614266777)
        ·
          refine ⟨984328524630487210700083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1312438032840649614266777 984328524630487210700083)
          ·
            refine ⟨1476492786945730816050125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 984328524630487210700083 1476492786945730816050125)
            ·
              refine ⟨553684795104649056018797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1476492786945730816050125 553684795104649056018797)
              ·
                refine ⟨207631798164243396007049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 553684795104649056018797 207631798164243396007049)
                ·
                  refine ⟨155723848623182547005287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 207631798164243396007049 155723848623182547005287)
                  ·
                    rfl

theorem cell20_341180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 3, 3, 2].length) (baseStart_341180 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_341180 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_341180 prefixEnd_341180 := by exact prefixLift 341180
  have htrace : WordTrace (prefixWord ++ tailWord_341180) baseStart_341180 baseEnd_341180 := by
    simpa [prefixWord, tailWord_341180, baseEnd_341180] using wordTrace_append hprefix tailTrace_341180
  have hstable : (prefixWord ++ tailWord_341180).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_341180).length < 2 ^ (prefixWord ++ tailWord_341180).sum := by decide
  have hdescent : baseEnd_341180 < baseStart_341180 := by decide
  rcases family_descends (prefixWord ++ tailWord_341180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_341208 : List Nat := [2, 1, 2, 2, 5, 1, 2, 5]
def baseStart_341208 : Nat := 118140960795 + 341208 * 2 ^ 59
def prefixEnd_341208 : Nat := 4983230072969 + 3 ^ 40 * 341208 * 2
def baseEnd_341208 : Nat := 51912209528712964690613

theorem tailTrace_341208 : CollatzResearch.WordTrace tailWord_341208 prefixEnd_341208 51912209528712964690613 := by
  unfold tailWord_341208
  simp only [CollatzResearch.WordTrace]
  refine ⟨6222439073934582266052139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8296585431912776354736185 6222439073934582266052139)
  ·
    refine ⟨9333658610901873399078209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6222439073934582266052139 9333658610901873399078209)
    ·
      refine ⟨7000243958176405049308657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9333658610901873399078209 7000243958176405049308657)
      ·
        refine ⟨5250182968632303786981493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7000243958176405049308657 5250182968632303786981493)
        ·
          refine ⟨492204653309278480029515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5250182968632303786981493 492204653309278480029515)
          ·
            refine ⟨738306979963917720044273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 492204653309278480029515 738306979963917720044273)
            ·
              refine ⟨553730234972938290033205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 738306979963917720044273 553730234972938290033205)
              ·
                refine ⟨51912209528712964690613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 553730234972938290033205 51912209528712964690613)
                ·
                  rfl

theorem cell20_341208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 2, 5].length) (baseStart_341208 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_341208 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_341208 prefixEnd_341208 := by exact prefixLift 341208
  have htrace : WordTrace (prefixWord ++ tailWord_341208) baseStart_341208 baseEnd_341208 := by
    simpa [prefixWord, tailWord_341208, baseEnd_341208] using wordTrace_append hprefix tailTrace_341208
  have hstable : (prefixWord ++ tailWord_341208).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_341208).length < 2 ^ (prefixWord ++ tailWord_341208).sum := by decide
  have hdescent : baseEnd_341208 < baseStart_341208 := by decide
  rcases family_descends (prefixWord ++ tailWord_341208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_341253 : List Nat := [1, 3, 1, 1, 2, 1, 6, 2, 3]
def baseStart_341253 : Nat := 118140960795 + 341253 * 2 ^ 59
def prefixEnd_341253 : Nat := 4983230072969 + 3 ^ 40 * 341253 * 2
def baseEnd_341253 : Nat := 155757167812318737571655

theorem tailTrace_341253 : CollatzResearch.WordTrace tailWord_341253 prefixEnd_341253 155757167812318737571655 := by
  unfold tailWord_341253
  simp only [CollatzResearch.WordTrace]
  refine ⟨12446519432706137217492413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8297679621804091478328275 12446519432706137217492413)
  ·
    refine ⟨4667444787264801456559655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12446519432706137217492413 4667444787264801456559655)
    ·
      refine ⟨7001167180897202184839483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4667444787264801456559655 7001167180897202184839483)
      ·
        refine ⟨10501750771345803277259225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7001167180897202184839483 10501750771345803277259225)
        ·
          refine ⟨7876313078509352457944419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10501750771345803277259225 7876313078509352457944419)
          ·
            refine ⟨11814469617764028686916629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7876313078509352457944419 11814469617764028686916629)
            ·
              refine ⟨553803263332688844699217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 11814469617764028686916629 553803263332688844699217)
              ·
                refine ⟨415352447499516633524413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 553803263332688844699217 415352447499516633524413)
                ·
                  refine ⟨155757167812318737571655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 415352447499516633524413 155757167812318737571655)
                  ·
                    rfl

theorem cell20_341253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 6, 2, 3].length) (baseStart_341253 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_341253 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_341253 prefixEnd_341253 := by exact prefixLift 341253
  have htrace : WordTrace (prefixWord ++ tailWord_341253) baseStart_341253 baseEnd_341253 := by
    simpa [prefixWord, tailWord_341253, baseEnd_341253] using wordTrace_append hprefix tailTrace_341253
  have hstable : (prefixWord ++ tailWord_341253).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_341253).length < 2 ^ (prefixWord ++ tailWord_341253).sum := by decide
  have hdescent : baseEnd_341253 < baseStart_341253 := by decide
  rcases family_descends (prefixWord ++ tailWord_341253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_341256 : List Nat := [2, 1, 3, 2, 4, 1, 1, 4, 2]
def baseStart_341256 : Nat := 118140960795 + 341256 * 2 ^ 59
def prefixEnd_341256 : Nat := 4983230072969 + 3 ^ 40 * 341256 * 2
def baseEnd_341256 : Nat := 155758537094064060471643

theorem tailTrace_341256 : CollatzResearch.WordTrace tailWord_341256 prefixEnd_341256 155758537094064060471643 := by
  unfold tailWord_341256
  simp only [CollatzResearch.WordTrace]
  refine ⟨6223314425847634364925811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8297752567796845819901081 6223314425847634364925811)
  ·
    refine ⟨9334971638771451547388717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6223314425847634364925811 9334971638771451547388717)
    ·
      refine ⟨3500614364539294330270769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9334971638771451547388717 3500614364539294330270769)
      ·
        refine ⟨2625460773404470747703077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3500614364539294330270769 2625460773404470747703077)
        ·
          refine ⟨492273895013338265194327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2625460773404470747703077 492273895013338265194327)
          ·
            refine ⟨738410842520007397791491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 492273895013338265194327 738410842520007397791491)
            ·
              refine ⟨1107616263780011096687237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 738410842520007397791491 1107616263780011096687237)
              ·
                refine ⟨207678049458752080628857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1107616263780011096687237 207678049458752080628857)
                ·
                  refine ⟨155758537094064060471643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 207678049458752080628857 155758537094064060471643)
                  ·
                    rfl

theorem cell20_341256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 1, 4, 2].length) (baseStart_341256 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_341256 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_341256 prefixEnd_341256 := by exact prefixLift 341256
  have htrace : WordTrace (prefixWord ++ tailWord_341256) baseStart_341256 baseEnd_341256 := by
    simpa [prefixWord, tailWord_341256, baseEnd_341256] using wordTrace_append hprefix tailTrace_341256
  have hstable : (prefixWord ++ tailWord_341256).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_341256).length < 2 ^ (prefixWord ++ tailWord_341256).sum := by decide
  have hdescent : baseEnd_341256 < baseStart_341256 := by decide
  rcases family_descends (prefixWord ++ tailWord_341256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_341277 : List Nat := [1, 4, 2, 3, 1, 2, 1, 2, 4]
def baseStart_341277 : Nat := 118140960795 + 341277 * 2 ^ 59
def prefixEnd_341277 : Nat := 4983230072969 + 3 ^ 40 * 341277 * 2
def baseEnd_341277 : Nat := 155768122066281320771557

theorem tailTrace_341277 : CollatzResearch.WordTrace tailWord_341277 prefixEnd_341277 155768122066281320771557 := by
  unfold tailWord_341277
  simp only [CollatzResearch.WordTrace]
  refine ⟨12447394784619189316366085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8298263189746126210910723 12447394784619189316366085)
  ·
    refine ⟨2333886522116097996818641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12447394784619189316366085 2333886522116097996818641)
    ·
      refine ⟨1750414891587073497613981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2333886522116097996818641 1750414891587073497613981)
      ·
        refine ⟨656405584345152561605243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1750414891587073497613981 656405584345152561605243)
        ·
          refine ⟨984608376517728842407865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 656405584345152561605243 984608376517728842407865)
          ·
            refine ⟨738456282388296631805899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 984608376517728842407865 738456282388296631805899)
            ·
              refine ⟨1107684423582444947708849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 738456282388296631805899 1107684423582444947708849)
              ·
                refine ⟨830763317686833710781637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1107684423582444947708849 830763317686833710781637)
                ·
                  refine ⟨155768122066281320771557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 830763317686833710781637 155768122066281320771557)
                  ·
                    rfl

theorem cell20_341277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 1, 2, 4].length) (baseStart_341277 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_341277 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_341277 prefixEnd_341277 := by exact prefixLift 341277
  have htrace : WordTrace (prefixWord ++ tailWord_341277) baseStart_341277 baseEnd_341277 := by
    simpa [prefixWord, tailWord_341277, baseEnd_341277] using wordTrace_append hprefix tailTrace_341277
  have hstable : (prefixWord ++ tailWord_341277).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_341277).length < 2 ^ (prefixWord ++ tailWord_341277).sum := by decide
  have hdescent : baseEnd_341277 < baseStart_341277 := by decide
  rcases family_descends (prefixWord ++ tailWord_341277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_341284 : List Nat := [2, 3, 1, 3, 1, 1, 5, 4]
def baseStart_341284 : Nat := 118140960795 + 341284 * 2 ^ 59
def prefixEnd_341284 : Nat := 4983230072969 + 3 ^ 40 * 341284 * 2
def baseEnd_341284 : Nat := 51923772352340135846065

theorem tailTrace_341284 : CollatzResearch.WordTrace tailWord_341284 prefixEnd_341284 51923772352340135846065 := by
  unfold tailWord_341284
  simp only [CollatzResearch.WordTrace]
  refine ⟨6223825047796914755935453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8298433397062553007913937 6223825047796914755935453)
  ·
    refine ⟨2333934392923843033475795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6223825047796914755935453 2333934392923843033475795)
    ·
      refine ⟨3500901589385764550213693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2333934392923843033475795 3500901589385764550213693)
      ·
        refine ⟨1312838096019661706330135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3500901589385764550213693 1312838096019661706330135)
        ·
          refine ⟨1969257144029492559495203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1312838096019661706330135 1969257144029492559495203)
          ·
            refine ⟨2953885716044238839242805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1969257144029492559495203 2953885716044238839242805)
            ·
              refine ⟨276926785879147391179013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2953885716044238839242805 276926785879147391179013)
              ·
                refine ⟨51923772352340135846065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 276926785879147391179013 51923772352340135846065)
                ·
                  rfl

theorem cell20_341284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 5, 4].length) (baseStart_341284 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_341284 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_341284 prefixEnd_341284 := by exact prefixLift 341284
  have htrace : WordTrace (prefixWord ++ tailWord_341284) baseStart_341284 baseEnd_341284 := by
    simpa [prefixWord, tailWord_341284, baseEnd_341284] using wordTrace_append hprefix tailTrace_341284
  have hstable : (prefixWord ++ tailWord_341284).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_341284).length < 2 ^ (prefixWord ++ tailWord_341284).sum := by decide
  have hdescent : baseEnd_341284 < baseStart_341284 := by decide
  rcases family_descends (prefixWord ++ tailWord_341284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_341308 : List Nat := [2, 2, 2, 2, 1, 5, 1, 2, 3]
def baseStart_341308 : Nat := 118140960795 + 341308 * 2 ^ 59
def prefixEnd_341308 : Nat := 4983230072969 + 3 ^ 40 * 341308 * 2
def baseEnd_341308 : Nat := 155782271310982990738097

theorem tailTrace_341308 : CollatzResearch.WordTrace tailWord_341308 prefixEnd_341308 155782271310982990738097 := by
  unfold tailWord_341308
  simp only [CollatzResearch.WordTrace]
  refine ⟨6224262723753440805372289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8299016965004587740496385 6224262723753440805372289)
  ·
    refine ⟨4668197042815080604029217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6224262723753440805372289 4668197042815080604029217)
    ·
      refine ⟨3501147782111310453021913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4668197042815080604029217 3501147782111310453021913)
      ·
        refine ⟨2625860836583482839766435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3501147782111310453021913 2625860836583482839766435)
        ·
          refine ⟨3938791254875224259649653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2625860836583482839766435 3938791254875224259649653)
          ·
            refine ⟨369261680144552274342155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3938791254875224259649653 369261680144552274342155)
            ·
              refine ⟨553892520216828411513233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 369261680144552274342155 553892520216828411513233)
              ·
                refine ⟨415419390162621308634925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 553892520216828411513233 415419390162621308634925)
                ·
                  refine ⟨155782271310982990738097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 415419390162621308634925 155782271310982990738097)
                  ·
                    rfl

theorem cell20_341308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 5, 1, 2, 3].length) (baseStart_341308 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_341308 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_341308 prefixEnd_341308 := by exact prefixLift 341308
  have htrace : WordTrace (prefixWord ++ tailWord_341308) baseStart_341308 baseEnd_341308 := by
    simpa [prefixWord, tailWord_341308, baseEnd_341308] using wordTrace_append hprefix tailTrace_341308
  have hstable : (prefixWord ++ tailWord_341308).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_341308).length < 2 ^ (prefixWord ++ tailWord_341308).sum := by decide
  have hdescent : baseEnd_341308 < baseStart_341308 := by decide
  rcases family_descends (prefixWord ++ tailWord_341308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_341312 : List Nat := [2, 1, 1, 2, 2, 1, 5, 1, 5]
def baseStart_341312 : Nat := 118140960795 + 341312 * 2 ^ 59
def prefixEnd_341312 : Nat := 4983230072969 + 3 ^ 40 * 341312 * 2
def baseEnd_341312 : Nat := 155784097019976754604747

theorem tailTrace_341312 : CollatzResearch.WordTrace tailWord_341312 prefixEnd_341312 155784097019976754604747 := by
  unfold tailWord_341312
  simp only [CollatzResearch.WordTrace]
  refine ⟨6224335669746195146945095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8299114226328260195926793 6224335669746195146945095)
  ·
    refine ⟨9336503504619292720417643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6224335669746195146945095 9336503504619292720417643)
    ·
      refine ⟨14004755256928939080626465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9336503504619292720417643 14004755256928939080626465)
      ·
        refine ⟨10503566442696704310469849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14004755256928939080626465 10503566442696704310469849)
        ·
          refine ⟨7877674832022528232852387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10503566442696704310469849 7877674832022528232852387)
          ·
            refine ⟨11816512248033792349278581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7877674832022528232852387 11816512248033792349278581)
            ·
              refine ⟨1107798023253168032744867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11816512248033792349278581 1107798023253168032744867)
              ·
                refine ⟨1661697034879752049117301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1107798023253168032744867 1661697034879752049117301)
                ·
                  refine ⟨155784097019976754604747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1661697034879752049117301 155784097019976754604747)
                  ·
                    rfl

theorem cell20_341312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 5, 1, 5].length) (baseStart_341312 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_341312 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_341312 prefixEnd_341312 := by exact prefixLift 341312
  have htrace : WordTrace (prefixWord ++ tailWord_341312) baseStart_341312 baseEnd_341312 := by
    simpa [prefixWord, tailWord_341312, baseEnd_341312] using wordTrace_append hprefix tailTrace_341312
  have hstable : (prefixWord ++ tailWord_341312).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_341312).length < 2 ^ (prefixWord ++ tailWord_341312).sum := by decide
  have hdescent : baseEnd_341312 < baseStart_341312 := by decide
  rcases family_descends (prefixWord ++ tailWord_341312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_341384 : List Nat := [2, 1, 3, 3, 1, 2, 4, 1, 3]
def baseStart_341384 : Nat := 118140960795 + 341384 * 2 ^ 59
def prefixEnd_341384 : Nat := 4983230072969 + 3 ^ 40 * 341384 * 2
def baseEnd_341384 : Nat := 155816959781864504204453

theorem tailTrace_341384 : CollatzResearch.WordTrace tailWord_341384 prefixEnd_341384 155816959781864504204453 := by
  unfold tailWord_341384
  simp only [CollatzResearch.WordTrace]
  refine ⟨6225648697615773295255603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8300864930154364393674137 6225648697615773295255603)
  ·
    refine ⟨9338473046423659942883405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6225648697615773295255603 9338473046423659942883405)
    ·
      refine ⟨3501927392408872478581277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9338473046423659942883405 3501927392408872478581277)
      ·
        refine ⟨1313222772153327179467979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3501927392408872478581277 1313222772153327179467979)
        ·
          refine ⟨1969834158229990769201969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1313222772153327179467979 1969834158229990769201969)
          ·
            refine ⟨1477375618672493076901477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1969834158229990769201969 1477375618672493076901477)
            ·
              refine ⟨277007928501092451919027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1477375618672493076901477 277007928501092451919027)
              ·
                refine ⟨415511892751638677878541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 277007928501092451919027 415511892751638677878541)
                ·
                  refine ⟨155816959781864504204453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 415511892751638677878541 155816959781864504204453)
                  ·
                    rfl

theorem cell20_341384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 4, 1, 3].length) (baseStart_341384 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_341384 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_341384 prefixEnd_341384 := by exact prefixLift 341384
  have htrace : WordTrace (prefixWord ++ tailWord_341384) baseStart_341384 baseEnd_341384 := by
    simpa [prefixWord, tailWord_341384, baseEnd_341384] using wordTrace_append hprefix tailTrace_341384
  have hstable : (prefixWord ++ tailWord_341384).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_341384).length < 2 ^ (prefixWord ++ tailWord_341384).sum := by decide
  have hdescent : baseEnd_341384 < baseStart_341384 := by decide
  rcases family_descends (prefixWord ++ tailWord_341384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_341442 : List Nat := [3, 5, 2, 1, 1, 1, 1, 2, 4]
def baseStart_341442 : Nat := 118140960795 + 341442 * 2 ^ 59
def prefixEnd_341442 : Nat := 4983230072969 + 3 ^ 40 * 341442 * 2
def baseEnd_341442 : Nat := 155843432562274080270883

theorem tailTrace_341442 : CollatzResearch.WordTrace tailWord_341442 prefixEnd_341442 155843432562274080270883 := by
  unfold tailWord_341442
  simp only [CollatzResearch.WordTrace]
  refine ⟨3113353207255355624030645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8302275219347614997415053 3113353207255355624030645)
  ·
    refine ⟨291876863180189589752873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 3113353207255355624030645 291876863180189589752873)
    ·
      refine ⟨218907647385142192314655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 291876863180189589752873 218907647385142192314655)
      ·
        refine ⟨328361471077713288471983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 218907647385142192314655 328361471077713288471983)
        ·
          refine ⟨492542206616569932707975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 328361471077713288471983 492542206616569932707975)
          ·
            refine ⟨738813309924854899061963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 492542206616569932707975 738813309924854899061963)
            ·
              refine ⟨1108219964887282348592945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 738813309924854899061963 1108219964887282348592945)
              ·
                refine ⟨831164973665461761444709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1108219964887282348592945 831164973665461761444709)
                ·
                  refine ⟨155843432562274080270883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 831164973665461761444709 155843432562274080270883)
                  ·
                    rfl

theorem cell20_341442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 1, 2, 4].length) (baseStart_341442 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_341442 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_341442 prefixEnd_341442 := by exact prefixLift 341442
  have htrace : WordTrace (prefixWord ++ tailWord_341442) baseStart_341442 baseEnd_341442 := by
    simpa [prefixWord, tailWord_341442, baseEnd_341442] using wordTrace_append hprefix tailTrace_341442
  have hstable : (prefixWord ++ tailWord_341442).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_341442).length < 2 ^ (prefixWord ++ tailWord_341442).sum := by decide
  have hdescent : baseEnd_341442 < baseStart_341442 := by decide
  rcases family_descends (prefixWord ++ tailWord_341442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_341450 : List Nat := [3, 1, 2, 1, 2, 4, 1, 2, 4]
def baseStart_341450 : Nat := 118140960795 + 341450 * 2 ^ 59
def prefixEnd_341450 : Nat := 4983230072969 + 3 ^ 40 * 341450 * 2
def baseEnd_341450 : Nat := 155847083980261608004183

theorem tailTrace_341450 : CollatzResearch.WordTrace tailWord_341450 prefixEnd_341450 155847083980261608004183 := by
  unfold tailWord_341450
  simp only [CollatzResearch.WordTrace]
  refine ⟨3113426153248109965603451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8302469741994959908275869 3113426153248109965603451)
  ·
    refine ⟨4670139229872164948405177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3113426153248109965603451 4670139229872164948405177)
    ·
      refine ⟨3502604422404123711303883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4670139229872164948405177 3502604422404123711303883)
      ·
        refine ⟨5253906633606185566955825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3502604422404123711303883 5253906633606185566955825)
        ·
          refine ⟨3940429975204639175216869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5253906633606185566955825 3940429975204639175216869)
          ·
            refine ⟨738830620350869845353163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3940429975204639175216869 738830620350869845353163)
            ·
              refine ⟨1108245930526304768029745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 738830620350869845353163 1108245930526304768029745)
              ·
                refine ⟨831184447894728576022309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1108245930526304768029745 831184447894728576022309)
                ·
                  refine ⟨155847083980261608004183, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 831184447894728576022309 155847083980261608004183)
                  ·
                    rfl

theorem cell20_341450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 1, 2, 4].length) (baseStart_341450 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_341450 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_341450 prefixEnd_341450 := by exact prefixLift 341450
  have htrace : WordTrace (prefixWord ++ tailWord_341450) baseStart_341450 baseEnd_341450 := by
    simpa [prefixWord, tailWord_341450, baseEnd_341450] using wordTrace_append hprefix tailTrace_341450
  have hstable : (prefixWord ++ tailWord_341450).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_341450).length < 2 ^ (prefixWord ++ tailWord_341450).sum := by decide
  have hdescent : baseEnd_341450 < baseStart_341450 := by decide
  rcases family_descends (prefixWord ++ tailWord_341450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_341471 : List Nat := [1, 1, 2, 3, 3, 1, 1, 2, 6]
def baseStart_341471 : Nat := 118140960795 + 341471 * 2 ^ 59
def prefixEnd_341471 : Nat := 4983230072969 + 3 ^ 40 * 341471 * 2
def baseEnd_341471 : Nat := 155856668952478868304097

theorem tailTrace_341471 : CollatzResearch.WordTrace tailWord_341471 prefixEnd_341471 155856668952478868304097 := by
  unfold tailWord_341471
  simp only [CollatzResearch.WordTrace]
  refine ⟨12454470545916360448928267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8302980363944240299285511 12454470545916360448928267)
  ·
    refine ⟨18681705818874540673392401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12454470545916360448928267 18681705818874540673392401)
    ·
      refine ⟨14011279364155905505044301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18681705818874540673392401 14011279364155905505044301)
      ·
        refine ⟨5254229761558464564391613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14011279364155905505044301 5254229761558464564391613)
        ·
          refine ⟨1970336160584424211646855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5254229761558464564391613 1970336160584424211646855)
          ·
            refine ⟨2955504240876636317470283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1970336160584424211646855 2955504240876636317470283)
            ·
              refine ⟨4433256361314954476205425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2955504240876636317470283 4433256361314954476205425)
              ·
                refine ⟨3324942270986215857154069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4433256361314954476205425 3324942270986215857154069)
                ·
                  refine ⟨155856668952478868304097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3324942270986215857154069 155856668952478868304097)
                  ·
                    rfl

theorem cell20_341471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 2, 6].length) (baseStart_341471 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_341471 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_341471 prefixEnd_341471 := by exact prefixLift 341471
  have htrace : WordTrace (prefixWord ++ tailWord_341471) baseStart_341471 baseEnd_341471 := by
    simpa [prefixWord, tailWord_341471, baseEnd_341471] using wordTrace_append hprefix tailTrace_341471
  have hstable : (prefixWord ++ tailWord_341471).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_341471).length < 2 ^ (prefixWord ++ tailWord_341471).sum := by decide
  have hdescent : baseEnd_341471 < baseStart_341471 := by decide
  rcases family_descends (prefixWord ++ tailWord_341471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_341488 : List Nat := [2, 1, 1, 1, 3, 5, 2, 1, 4]
def baseStart_341488 : Nat := 118140960795 + 341488 * 2 ^ 59
def prefixEnd_341488 : Nat := 4983230072969 + 3 ^ 40 * 341488 * 2
def baseEnd_341488 : Nat := 155864428215702364737361

theorem tailTrace_341488 : CollatzResearch.WordTrace tailWord_341488 prefixEnd_341488 155864428215702364737361 := by
  unfold tailWord_341488
  simp only [CollatzResearch.WordTrace]
  refine ⟨6227545293427386176148559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8303393724569848234864745 6227545293427386176148559)
  ·
    refine ⟨9341317940141079264222839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6227545293427386176148559 9341317940141079264222839)
    ·
      refine ⟨14011976910211618896334259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9341317940141079264222839 14011976910211618896334259)
      ·
        refine ⟨21017965365317428344501389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14011976910211618896334259 21017965365317428344501389)
        ·
          refine ⟨7881737011994035629188021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21017965365317428344501389 7881737011994035629188021)
          ·
            refine ⟨738912844874440840236377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 7881737011994035629188021 738912844874440840236377)
            ·
              refine ⟨554184633655830630177283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 738912844874440840236377 554184633655830630177283)
              ·
                refine ⟨831276950483745945265925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 554184633655830630177283 831276950483745945265925)
                ·
                  refine ⟨155864428215702364737361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 831276950483745945265925 155864428215702364737361)
                  ·
                    rfl

theorem cell20_341488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 2, 1, 4].length) (baseStart_341488 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_341488 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_341488 prefixEnd_341488 := by exact prefixLift 341488
  have htrace : WordTrace (prefixWord ++ tailWord_341488) baseStart_341488 baseEnd_341488 := by
    simpa [prefixWord, tailWord_341488, baseEnd_341488] using wordTrace_append hprefix tailTrace_341488
  have hstable : (prefixWord ++ tailWord_341488).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_341488).length < 2 ^ (prefixWord ++ tailWord_341488).sum := by decide
  have hdescent : baseEnd_341488 < baseStart_341488 := by decide
  rcases family_descends (prefixWord ++ tailWord_341488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_341508 : List Nat := [2, 3, 2, 3, 3, 1, 2, 4]
def baseStart_341508 : Nat := 118140960795 + 341508 * 2 ^ 59
def prefixEnd_341508 : Nat := 4983230072969 + 3 ^ 40 * 341508 * 2
def baseEnd_341508 : Nat := 51957852253557061356871

theorem tailTrace_341508 : CollatzResearch.WordTrace tailWord_341508 prefixEnd_341508 51957852253557061356871 := by
  unfold tailWord_341508
  simp only [CollatzResearch.WordTrace]
  refine ⟨6227910023391157884012589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8303880031188210512016785 6227910023391157884012589)
  ·
    refine ⟨2335466258771684206504721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6227910023391157884012589 2335466258771684206504721)
    ·
      refine ⟨1751599694078763154878541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2335466258771684206504721 1751599694078763154878541)
      ·
        refine ⟨656849885279536183079453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1751599694078763154878541 656849885279536183079453)
        ·
          refine ⟨246318706979826068654795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 656849885279536183079453 246318706979826068654795)
          ·
            refine ⟨369478060469739102982193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 246318706979826068654795 369478060469739102982193)
            ·
              refine ⟨277108545352304327236645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 369478060469739102982193 277108545352304327236645)
              ·
                refine ⟨51957852253557061356871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 277108545352304327236645 51957852253557061356871)
                ·
                  rfl

theorem cell20_341508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 3, 1, 2, 4].length) (baseStart_341508 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_341508 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_341508 prefixEnd_341508 := by exact prefixLift 341508
  have htrace : WordTrace (prefixWord ++ tailWord_341508) baseStart_341508 baseEnd_341508 := by
    simpa [prefixWord, tailWord_341508, baseEnd_341508] using wordTrace_append hprefix tailTrace_341508
  have hstable : (prefixWord ++ tailWord_341508).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_341508).length < 2 ^ (prefixWord ++ tailWord_341508).sum := by decide
  have hdescent : baseEnd_341508 < baseStart_341508 := by decide
  rcases family_descends (prefixWord ++ tailWord_341508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_341550 : List Nat := [4, 1, 3, 1, 2, 2, 2, 5]
def baseStart_341550 : Nat := 118140960795 + 341550 * 2 ^ 59
def prefixEnd_341550 : Nat := 4983230072969 + 3 ^ 40 * 341550 * 2
def baseEnd_341550 : Nat := 51964242235035234890147

theorem tailTrace_341550 : CollatzResearch.WordTrace tailWord_341550 prefixEnd_341550 51964242235035234890147 := by
  unfold tailWord_341550
  simp only [CollatzResearch.WordTrace]
  refine ⟨1557168989078769617631763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8304901275086771294036069 1557168989078769617631763)
  ·
    refine ⟨2335753483618154426447645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1557168989078769617631763 2335753483618154426447645)
    ·
      refine ⟨875907556356807909917867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2335753483618154426447645 875907556356807909917867)
      ·
        refine ⟨1313861334535211864876801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 875907556356807909917867 1313861334535211864876801)
        ·
          refine ⟨985396000901408898657601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1313861334535211864876801 985396000901408898657601)
          ·
            refine ⟨739047000676056673993201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 985396000901408898657601 739047000676056673993201)
            ·
              refine ⟨554285250507042505494901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 739047000676056673993201 554285250507042505494901)
              ·
                refine ⟨51964242235035234890147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 554285250507042505494901 51964242235035234890147)
                ·
                  rfl

theorem cell20_341550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 2, 5].length) (baseStart_341550 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_341550 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_341550 prefixEnd_341550 := by exact prefixLift 341550
  have htrace : WordTrace (prefixWord ++ tailWord_341550) baseStart_341550 baseEnd_341550 := by
    simpa [prefixWord, tailWord_341550, baseEnd_341550] using wordTrace_append hprefix tailTrace_341550
  have hstable : (prefixWord ++ tailWord_341550).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_341550).length < 2 ^ (prefixWord ++ tailWord_341550).sum := by decide
  have hdescent : baseEnd_341550 < baseStart_341550 := by decide
  rcases family_descends (prefixWord ++ tailWord_341550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_341557 : List Nat := [1, 3, 3, 1, 1, 4, 1, 3, 3]
def baseStart_341557 : Nat := 118140960795 + 341557 * 2 ^ 59
def prefixEnd_341557 : Nat := 4983230072969 + 3 ^ 40 * 341557 * 2
def baseEnd_341557 : Nat := 155895921695844791437079

theorem tailTrace_341557 : CollatzResearch.WordTrace tailWord_341557 prefixEnd_341557 155895921695844791437079 := by
  unfold tailWord_341557
  simp only [CollatzResearch.WordTrace]
  refine ⟨12457607223604797136558925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8305071482403198091039283 12457607223604797136558925)
  ·
    refine ⟨4671602708851798926209597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12457607223604797136558925 4671602708851798926209597)
    ·
      refine ⟨1751851015819424597328599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4671602708851798926209597 1751851015819424597328599)
      ·
        refine ⟨2627776523729136895992899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1751851015819424597328599 2627776523729136895992899)
        ·
          refine ⟨3941664785593705343989349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2627776523729136895992899 3941664785593705343989349)
          ·
            refine ⟨739062147298819751998003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3941664785593705343989349 739062147298819751998003)
            ·
              refine ⟨1108593220948229627997005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 739062147298819751998003 1108593220948229627997005)
              ·
                refine ⟨415722457855586110498877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1108593220948229627997005 415722457855586110498877)
                ·
                  refine ⟨155895921695844791437079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 415722457855586110498877 155895921695844791437079)
                  ·
                    rfl

theorem cell20_341557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 1, 3, 3].length) (baseStart_341557 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_341557 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_341557 prefixEnd_341557 := by exact prefixLift 341557
  have htrace : WordTrace (prefixWord ++ tailWord_341557) baseStart_341557 baseEnd_341557 := by
    simpa [prefixWord, tailWord_341557, baseEnd_341557] using wordTrace_append hprefix tailTrace_341557
  have hstable : (prefixWord ++ tailWord_341557).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_341557).length < 2 ^ (prefixWord ++ tailWord_341557).sum := by decide
  have hdescent : baseEnd_341557 < baseStart_341557 := by decide
  rcases family_descends (prefixWord ++ tailWord_341557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_341590 : List Nat := [5, 2, 2, 2, 2, 1, 2, 2, 2]
def baseStart_341590 : Nat := 118140960795 + 341590 * 2 ^ 59
def prefixEnd_341590 : Nat := 4983230072969 + 3 ^ 40 * 341590 * 2
def baseEnd_341590 : Nat := 155910983795043343336945

theorem tailTrace_341590 : CollatzResearch.WordTrace tailWord_341590 prefixEnd_341590 155910983795043343336945 := by
  unfold tailWord_341590
  simp only [CollatzResearch.WordTrace]
  refine ⟨778675677030327735781889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 8305873888323495848340149 778675677030327735781889)
  ·
    refine ⟨584006757772745801836417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 778675677030327735781889 584006757772745801836417)
    ·
      refine ⟨438005068329559351377313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 584006757772745801836417 438005068329559351377313)
      ·
        refine ⟨328503801247169513532985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 438005068329559351377313 328503801247169513532985)
        ·
          refine ⟨246377850935377135149739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 328503801247169513532985 246377850935377135149739)
          ·
            refine ⟨369566776403065702724609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 246377850935377135149739 369566776403065702724609)
            ·
              refine ⟨277175082302299277043457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 369566776403065702724609 277175082302299277043457)
              ·
                refine ⟨207881311726724457782593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 277175082302299277043457 207881311726724457782593)
                ·
                  refine ⟨155910983795043343336945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 207881311726724457782593 155910983795043343336945)
                  ·
                    rfl

theorem cell20_341590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 2, 1, 2, 2, 2].length) (baseStart_341590 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_341590 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_341590 prefixEnd_341590 := by exact prefixLift 341590
  have htrace : WordTrace (prefixWord ++ tailWord_341590) baseStart_341590 baseEnd_341590 := by
    simpa [prefixWord, tailWord_341590, baseEnd_341590] using wordTrace_append hprefix tailTrace_341590
  have hstable : (prefixWord ++ tailWord_341590).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_341590).length < 2 ^ (prefixWord ++ tailWord_341590).sum := by decide
  have hdescent : baseEnd_341590 < baseStart_341590 := by decide
  rcases family_descends (prefixWord ++ tailWord_341590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_341636 : List Nat := [2, 3, 2, 1, 4, 1, 2, 3, 2]
def baseStart_341636 : Nat := 118140960795 + 341636 * 2 ^ 59
def prefixEnd_341636 : Nat := 4983230072969 + 3 ^ 40 * 341636 * 2
def baseEnd_341636 : Nat := 155931979448471627803423

theorem tailTrace_341636 : CollatzResearch.WordTrace tailWord_341636 prefixEnd_341636 155931979448471627803423 := by
  unfold tailWord_341636
  simp only [CollatzResearch.WordTrace]
  refine ⟨6230244295159296814342381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8306992393545729085789841 6230244295159296814342381)
  ·
    refine ⟨2336341610684736305378393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6230244295159296814342381 2336341610684736305378393)
    ·
      refine ⟨1752256208013552229033795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2336341610684736305378393 1752256208013552229033795)
      ·
        refine ⟨2628384312020328343550693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1752256208013552229033795 2628384312020328343550693)
        ·
          refine ⟨492822058503811564415755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2628384312020328343550693 492822058503811564415755)
          ·
            refine ⟨739233087755717346623633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 492822058503811564415755 739233087755717346623633)
            ·
              refine ⟨554424815816788009967725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 739233087755717346623633 554424815816788009967725)
              ·
                refine ⟨207909305931295503737897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 554424815816788009967725 207909305931295503737897)
                ·
                  refine ⟨155931979448471627803423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 207909305931295503737897 155931979448471627803423)
                  ·
                    rfl

theorem cell20_341636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 2, 3, 2].length) (baseStart_341636 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_341636 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_341636 prefixEnd_341636 := by exact prefixLift 341636
  have htrace : WordTrace (prefixWord ++ tailWord_341636) baseStart_341636 baseEnd_341636 := by
    simpa [prefixWord, tailWord_341636, baseEnd_341636] using wordTrace_append hprefix tailTrace_341636
  have hstable : (prefixWord ++ tailWord_341636).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_341636).length < 2 ^ (prefixWord ++ tailWord_341636).sum := by decide
  have hdescent : baseEnd_341636 < baseStart_341636 := by decide
  rcases family_descends (prefixWord ++ tailWord_341636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_341692 : List Nat := [2, 2, 2, 3, 1, 2, 1, 2, 5]
def baseStart_341692 : Nat := 118140960795 + 341692 * 2 ^ 59
def prefixEnd_341692 : Nat := 4983230072969 + 3 ^ 40 * 341692 * 2
def baseEnd_341692 : Nat := 155957539374384321936527

theorem tailTrace_341692 : CollatzResearch.WordTrace tailWord_341692 prefixEnd_341692 155957539374384321936527 := by
  unfold tailWord_341692
  simp only [CollatzResearch.WordTrace]
  refine ⟨6231265539057857596361665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8308354052077143461815553 6231265539057857596361665)
  ·
    refine ⟨4673449154293393197271249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6231265539057857596361665 4673449154293393197271249)
    ·
      refine ⟨3505086865720044897953437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4673449154293393197271249 3505086865720044897953437)
      ·
        refine ⟨1314407574645016836732539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3505086865720044897953437 1314407574645016836732539)
        ·
          refine ⟨1971611361967525255098809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1314407574645016836732539 1971611361967525255098809)
          ·
            refine ⟨1478708521475643941324107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1971611361967525255098809 1478708521475643941324107)
            ·
              refine ⟨2218062782213465911986161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1478708521475643941324107 2218062782213465911986161)
              ·
                refine ⟨1663547086660099433989621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2218062782213465911986161 1663547086660099433989621)
                ·
                  refine ⟨155957539374384321936527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1663547086660099433989621 155957539374384321936527)
                  ·
                    rfl

theorem cell20_341692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 1, 2, 5].length) (baseStart_341692 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_341692 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_341692 prefixEnd_341692 := by exact prefixLift 341692
  have htrace : WordTrace (prefixWord ++ tailWord_341692) baseStart_341692 baseEnd_341692 := by
    simpa [prefixWord, tailWord_341692, baseEnd_341692] using wordTrace_append hprefix tailTrace_341692
  have hstable : (prefixWord ++ tailWord_341692).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_341692).length < 2 ^ (prefixWord ++ tailWord_341692).sum := by decide
  have hdescent : baseEnd_341692 < baseStart_341692 := by decide
  rcases family_descends (prefixWord ++ tailWord_341692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_341698 : List Nat := [3, 5, 1, 2, 1, 2, 6]
def baseStart_341698 : Nat := 118140960795 + 341698 * 2 ^ 59
def prefixEnd_341698 : Nat := 4983230072969 + 3 ^ 40 * 341698 * 2
def baseEnd_341698 : Nat := 17328919770874996415167

theorem tailTrace_341698 : CollatzResearch.WordTrace tailWord_341698 prefixEnd_341698 17328919770874996415167 := by
  unfold tailWord_341698
  simp only [CollatzResearch.WordTrace]
  refine ⟨3115687479023494554360437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8308499944062652144961165 3115687479023494554360437)
  ·
    refine ⟨292095701158452614471291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 3115687479023494554360437 292095701158452614471291)
    ·
      refine ⟨438143551737678921706937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 292095701158452614471291 438143551737678921706937)
      ·
        refine ⟨328607663803259191280203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 438143551737678921706937 328607663803259191280203)
        ·
          refine ⟨492911495704888786920305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 328607663803259191280203 492911495704888786920305)
          ·
            refine ⟨369683621778666590190229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 492911495704888786920305 369683621778666590190229)
            ·
              refine ⟨17328919770874996415167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 369683621778666590190229 17328919770874996415167)
              ·
                rfl

theorem cell20_341698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 2, 6].length) (baseStart_341698 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_341698 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_341698 prefixEnd_341698 := by exact prefixLift 341698
  have htrace : WordTrace (prefixWord ++ tailWord_341698) baseStart_341698 baseEnd_341698 := by
    simpa [prefixWord, tailWord_341698, baseEnd_341698] using wordTrace_append hprefix tailTrace_341698
  have hstable : (prefixWord ++ tailWord_341698).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_341698).length < 2 ^ (prefixWord ++ tailWord_341698).sum := by decide
  have hdescent : baseEnd_341698 < baseStart_341698 := by decide
  rcases family_descends (prefixWord ++ tailWord_341698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_341751 : List Nat := [1, 1, 3, 1, 1, 1, 4, 1, 7]
def baseStart_341751 : Nat := 118140960795 + 341751 * 2 ^ 59
def prefixEnd_341751 : Nat := 4983230072969 + 3 ^ 40 * 341751 * 2
def baseEnd_341751 : Nat := 155984468582042338969619

theorem tailTrace_341751 : CollatzResearch.WordTrace tailWord_341751 prefixEnd_341751 155984468582042338969619 := by
  unfold tailWord_341751
  simp only [CollatzResearch.WordTrace]
  refine ⟨12464682984901968269121107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8309788656601312179414071 12464682984901968269121107)
  ·
    refine ⟨18697024477352952403681661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12464682984901968269121107 18697024477352952403681661)
    ·
      refine ⟨7011384179007357151380623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18697024477352952403681661 7011384179007357151380623)
      ·
        refine ⟨10517076268511035727070935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7011384179007357151380623 10517076268511035727070935)
        ·
          refine ⟨15775614402766553590606403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10517076268511035727070935 15775614402766553590606403)
          ·
            refine ⟨23663421604149830385909605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15775614402766553590606403 23663421604149830385909605)
            ·
              refine ⟨4436891550778093197358051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23663421604149830385909605 4436891550778093197358051)
              ·
                refine ⟨6655337326167139796037077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4436891550778093197358051 6655337326167139796037077)
                ·
                  refine ⟨155984468582042338969619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6655337326167139796037077 155984468582042338969619)
                  ·
                    rfl

theorem cell20_341751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 1, 7].length) (baseStart_341751 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_341751 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_341751 prefixEnd_341751 := by exact prefixLift 341751
  have htrace : WordTrace (prefixWord ++ tailWord_341751) baseStart_341751 baseEnd_341751 := by
    simpa [prefixWord, tailWord_341751, baseEnd_341751] using wordTrace_append hprefix tailTrace_341751
  have hstable : (prefixWord ++ tailWord_341751).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_341751).length < 2 ^ (prefixWord ++ tailWord_341751).sum := by decide
  have hdescent : baseEnd_341751 < baseStart_341751 := by decide
  rcases family_descends (prefixWord ++ tailWord_341751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_341754 : List Nat := [3, 1, 1, 1, 1, 3, 1, 7, 2]
def baseStart_341754 : Nat := 118140960795 + 341754 * 2 ^ 59
def prefixEnd_341754 : Nat := 4983230072969 + 3 ^ 40 * 341754 * 2
def baseEnd_341754 : Nat := 155985837863787661869607

theorem tailTrace_341754 : CollatzResearch.WordTrace tailWord_341754 prefixEnd_341754 155985837863787661869607 := by
  unfold tailWord_341754
  simp only [CollatzResearch.WordTrace]
  refine ⟨3116198100972774945370079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8309861602594066520986877 3116198100972774945370079)
  ·
    refine ⟨4674297151459162418055119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3116198100972774945370079 4674297151459162418055119)
    ·
      refine ⟨7011445727188743627082679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4674297151459162418055119 7011445727188743627082679)
      ·
        refine ⟨10517168590783115440624019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7011445727188743627082679 10517168590783115440624019)
        ·
          refine ⟨15775752886174673160936029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10517168590783115440624019 15775752886174673160936029)
          ·
            refine ⟨5915907332315502435351011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15775752886174673160936029 5915907332315502435351011)
            ·
              refine ⟨8873860998473253653026517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5915907332315502435351011 8873860998473253653026517)
              ·
                refine ⟨207981117151716882492809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 8873860998473253653026517 207981117151716882492809)
                ·
                  refine ⟨155985837863787661869607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 207981117151716882492809 155985837863787661869607)
                  ·
                    rfl

theorem cell20_341754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 7, 2].length) (baseStart_341754 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_341754 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_341754 prefixEnd_341754 := by exact prefixLift 341754
  have htrace : WordTrace (prefixWord ++ tailWord_341754) baseStart_341754 baseEnd_341754 := by
    simpa [prefixWord, tailWord_341754, baseEnd_341754] using wordTrace_append hprefix tailTrace_341754
  have hstable : (prefixWord ++ tailWord_341754).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_341754).length < 2 ^ (prefixWord ++ tailWord_341754).sum := by decide
  have hdescent : baseEnd_341754 < baseStart_341754 := by decide
  rcases family_descends (prefixWord ++ tailWord_341754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_341767 : List Nat := [1, 1, 4, 4, 2, 2, 2, 2, 2]
def baseStart_341767 : Nat := 118140960795 + 341767 * 2 ^ 59
def prefixEnd_341767 : Nat := 4983230072969 + 3 ^ 40 * 341767 * 2
def baseEnd_341767 : Nat := 155991771418017394436221

theorem tailTrace_341767 : CollatzResearch.WordTrace tailWord_341767 prefixEnd_341767 155991771418017394436221 := by
  unfold tailWord_341767
  simp only [CollatzResearch.WordTrace]
  refine ⟨12465266552844003001703555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8310177701896002001135703 12465266552844003001703555)
  ·
    refine ⟨18697899829266004502555333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12465266552844003001703555 18697899829266004502555333)
    ·
      refine ⟨3505856217987375844229125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18697899829266004502555333 3505856217987375844229125)
      ·
        refine ⟨657348040872632970792961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3505856217987375844229125 657348040872632970792961)
        ·
          refine ⟨493011030654474728094721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 657348040872632970792961 493011030654474728094721)
          ·
            refine ⟨369758272990856046071041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 493011030654474728094721 369758272990856046071041)
            ·
              refine ⟨277318704743142034553281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 369758272990856046071041 277318704743142034553281)
              ·
                refine ⟨207989028557356525914961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 277318704743142034553281 207989028557356525914961)
                ·
                  refine ⟨155991771418017394436221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 207989028557356525914961 155991771418017394436221)
                  ·
                    rfl

theorem cell20_341767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 2, 2, 2, 2].length) (baseStart_341767 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_341767 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_341767 prefixEnd_341767 := by exact prefixLift 341767
  have htrace : WordTrace (prefixWord ++ tailWord_341767) baseStart_341767 baseEnd_341767 := by
    simpa [prefixWord, tailWord_341767, baseEnd_341767] using wordTrace_append hprefix tailTrace_341767
  have hstable : (prefixWord ++ tailWord_341767).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_341767).length < 2 ^ (prefixWord ++ tailWord_341767).sum := by decide
  have hdescent : baseEnd_341767 < baseStart_341767 := by decide
  rcases family_descends (prefixWord ++ tailWord_341767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_341771 : List Nat := [1, 1, 1, 1, 5, 1, 6, 2, 2]
def baseStart_341771 : Nat := 118140960795 + 341771 * 2 ^ 59
def prefixEnd_341771 : Nat := 4983230072969 + 3 ^ 40 * 341771 * 2
def baseEnd_341771 : Nat := 155993597127011158302871

theorem tailTrace_341771 : CollatzResearch.WordTrace tailWord_341771 prefixEnd_341771 155993597127011158302871 := by
  unfold tailWord_341771
  simp only [CollatzResearch.WordTrace]
  refine ⟨12465412444829511684849167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8310274963219674456566111 12465412444829511684849167)
  ·
    refine ⟨18698118667244267527273751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12465412444829511684849167 18698118667244267527273751)
    ·
      refine ⟨28047178000866401290910627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18698118667244267527273751 28047178000866401290910627)
      ·
        refine ⟨42070767001299601936365941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28047178000866401290910627 42070767001299601936365941)
        ·
          refine ⟨3944134406371837681534307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 42070767001299601936365941 3944134406371837681534307)
          ·
            refine ⟨5916201609557756522301461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3944134406371837681534307 5916201609557756522301461)
            ·
              refine ⟨277321950448019836982881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 5916201609557756522301461 277321950448019836982881)
              ·
                refine ⟨207991462836014877737161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 277321950448019836982881 207991462836014877737161)
                ·
                  refine ⟨155993597127011158302871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 207991462836014877737161 155993597127011158302871)
                  ·
                    rfl

theorem cell20_341771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 6, 2, 2].length) (baseStart_341771 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_341771 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_341771 prefixEnd_341771 := by exact prefixLift 341771
  have htrace : WordTrace (prefixWord ++ tailWord_341771) baseStart_341771 baseEnd_341771 := by
    simpa [prefixWord, tailWord_341771, baseEnd_341771] using wordTrace_append hprefix tailTrace_341771
  have hstable : (prefixWord ++ tailWord_341771).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_341771).length < 2 ^ (prefixWord ++ tailWord_341771).sum := by decide
  have hdescent : baseEnd_341771 < baseStart_341771 := by decide
  rcases family_descends (prefixWord ++ tailWord_341771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_341778 : List Nat := [3, 2, 4, 1, 1, 1, 3, 5]
def baseStart_341778 : Nat := 118140960795 + 341778 * 2 ^ 59
def prefixEnd_341778 : Nat := 4983230072969 + 3 ^ 40 * 341778 * 2
def baseEnd_341778 : Nat := 51998930705916748356503

theorem tailTrace_341778 : CollatzResearch.WordTrace tailWord_341778 prefixEnd_341778 51998930705916748356503 := by
  unfold tailWord_341778
  simp only [CollatzResearch.WordTrace]
  refine ⟨3116416938951037970088497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8310445170536101253569325 3116416938951037970088497)
  ·
    refine ⟨2337312704213278477566373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3116416938951037970088497 2337312704213278477566373)
    ·
      refine ⟨438246132039989714543695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2337312704213278477566373 438246132039989714543695)
      ·
        refine ⟨657369198059984571815543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 438246132039989714543695 657369198059984571815543)
        ·
          refine ⟨986053797089976857723315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 657369198059984571815543 986053797089976857723315)
          ·
            refine ⟨1479080695634965286584973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 986053797089976857723315 1479080695634965286584973)
            ·
              refine ⟨554655260863111982469365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1479080695634965286584973 554655260863111982469365)
              ·
                refine ⟨51998930705916748356503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 554655260863111982469365 51998930705916748356503)
                ·
                  rfl

theorem cell20_341778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 3, 5].length) (baseStart_341778 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_341778 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_341778 prefixEnd_341778 := by exact prefixLift 341778
  have htrace : WordTrace (prefixWord ++ tailWord_341778) baseStart_341778 baseEnd_341778 := by
    simpa [prefixWord, tailWord_341778, baseEnd_341778] using wordTrace_append hprefix tailTrace_341778
  have hstable : (prefixWord ++ tailWord_341778).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_341778).length < 2 ^ (prefixWord ++ tailWord_341778).sum := by decide
  have hdescent : baseEnd_341778 < baseStart_341778 := by decide
  rcases family_descends (prefixWord ++ tailWord_341778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_341809 : List Nat := [1, 2, 2, 3, 2, 3, 2, 3, 2]
def baseStart_341809 : Nat := 118140960795 + 341809 * 2 ^ 59
def prefixEnd_341809 : Nat := 4983230072969 + 3 ^ 40 * 341809 * 2
def baseEnd_341809 : Nat := 156010941362451915036049

theorem tailTrace_341809 : CollatzResearch.WordTrace tailWord_341809 prefixEnd_341809 156010941362451915036049 := by
  unfold tailWord_341809
  simp only [CollatzResearch.WordTrace]
  refine ⟨12466798418691844174732481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8311198945794562783154987 12466798418691844174732481)
  ·
    refine ⟨9350098814018883131049361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12466798418691844174732481 9350098814018883131049361)
    ·
      refine ⟨7012574110514162348287021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9350098814018883131049361 7012574110514162348287021)
      ·
        refine ⟨2629715291442810880607633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7012574110514162348287021 2629715291442810880607633)
        ·
          refine ⟨1972286468582108160455725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2629715291442810880607633 1972286468582108160455725)
          ·
            refine ⟨739607425718290560170897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1972286468582108160455725 739607425718290560170897)
            ·
              refine ⟨554705569288717920128173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 739607425718290560170897 554705569288717920128173)
              ·
                refine ⟨208014588483269220048065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 554705569288717920128173 208014588483269220048065)
                ·
                  refine ⟨156010941362451915036049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 208014588483269220048065 156010941362451915036049)
                  ·
                    rfl

theorem cell20_341809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 2, 3, 2].length) (baseStart_341809 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_341809 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_341809 prefixEnd_341809 := by exact prefixLift 341809
  have htrace : WordTrace (prefixWord ++ tailWord_341809) baseStart_341809 baseEnd_341809 := by
    simpa [prefixWord, tailWord_341809, baseEnd_341809] using wordTrace_append hprefix tailTrace_341809
  have hstable : (prefixWord ++ tailWord_341809).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_341809).length < 2 ^ (prefixWord ++ tailWord_341809).sum := by decide
  have hdescent : baseEnd_341809 < baseStart_341809 := by decide
  rcases family_descends (prefixWord ++ tailWord_341809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_341895 : List Nat := [1, 1, 4, 2, 5, 1, 2, 1, 3]
def baseStart_341895 : Nat := 118140960795 + 341895 * 2 ^ 59
def prefixEnd_341895 : Nat := 4983230072969 + 3 ^ 40 * 341895 * 2
def baseEnd_341895 : Nat := 156050194105817838169031

theorem tailTrace_341895 : CollatzResearch.WordTrace tailWord_341895 prefixEnd_341895 156050194105817838169031 := by
  unfold tailWord_341895
  simp only [CollatzResearch.WordTrace]
  refine ⟨12469935096380280862363139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8313290064253520574908759 12469935096380280862363139)
  ·
    refine ⟨18704902644570421293544709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12469935096380280862363139 18704902644570421293544709)
    ·
      refine ⟨3507169245856953992539633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18704902644570421293544709 3507169245856953992539633)
      ·
        refine ⟨2630376934392715494404725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3507169245856953992539633 2630376934392715494404725)
        ·
          refine ⟨246597837599317077600443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2630376934392715494404725 246597837599317077600443)
          ·
            refine ⟨369896756398975616400665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 246597837599317077600443 369896756398975616400665)
            ·
              refine ⟨277422567299231712300499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 369896756398975616400665 277422567299231712300499)
              ·
                refine ⟨416133850948847568450749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 277422567299231712300499 416133850948847568450749)
                ·
                  refine ⟨156050194105817838169031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 416133850948847568450749 156050194105817838169031)
                  ·
                    rfl

theorem cell20_341895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 5, 1, 2, 1, 3].length) (baseStart_341895 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_341895 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_341895 prefixEnd_341895 := by exact prefixLift 341895
  have htrace : WordTrace (prefixWord ++ tailWord_341895) baseStart_341895 baseEnd_341895 := by
    simpa [prefixWord, tailWord_341895, baseEnd_341895] using wordTrace_append hprefix tailTrace_341895
  have hstable : (prefixWord ++ tailWord_341895).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_341895).length < 2 ^ (prefixWord ++ tailWord_341895).sum := by decide
  have hdescent : baseEnd_341895 < baseStart_341895 := by decide
  rcases family_descends (prefixWord ++ tailWord_341895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_341937 : List Nat := [1, 2, 2, 4, 2, 2, 2, 2, 3]
def baseStart_341937 : Nat := 118140960795 + 341937 * 2 ^ 59
def prefixEnd_341937 : Nat := 4983230072969 + 3 ^ 40 * 341937 * 2
def baseEnd_341937 : Nat := 156069364050252358768859

theorem tailTrace_341937 : CollatzResearch.WordTrace tailWord_341937 prefixEnd_341937 156069364050252358768859 := by
  unfold tailWord_341937
  simp only [CollatzResearch.WordTrace]
  refine ⟨12471466962228122035392065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8314311308152081356928043 12471466962228122035392065)
  ·
    refine ⟨9353600221671091526544049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12471466962228122035392065 9353600221671091526544049)
    ·
      refine ⟨7015200166253318644908037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9353600221671091526544049 7015200166253318644908037)
      ·
        refine ⟨1315350031172497245920257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7015200166253318644908037 1315350031172497245920257)
        ·
          refine ⟨986512523379372934440193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1315350031172497245920257 986512523379372934440193)
          ·
            refine ⟨739884392534529700830145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 986512523379372934440193 739884392534529700830145)
            ·
              refine ⟨554913294400897275622609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 739884392534529700830145 554913294400897275622609)
              ·
                refine ⟨416184970800672956716957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 554913294400897275622609 416184970800672956716957)
                ·
                  refine ⟨156069364050252358768859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 416184970800672956716957 156069364050252358768859)
                  ·
                    rfl

theorem cell20_341937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 2, 2, 3].length) (baseStart_341937 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_341937 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_341937 prefixEnd_341937 := by exact prefixLift 341937
  have htrace : WordTrace (prefixWord ++ tailWord_341937) baseStart_341937 baseEnd_341937 := by
    simpa [prefixWord, tailWord_341937, baseEnd_341937] using wordTrace_append hprefix tailTrace_341937
  have hstable : (prefixWord ++ tailWord_341937).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_341937).length < 2 ^ (prefixWord ++ tailWord_341937).sum := by decide
  have hdescent : baseEnd_341937 < baseStart_341937 := by decide
  rcases family_descends (prefixWord ++ tailWord_341937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_341944 : List Nat := [2, 1, 2, 1, 2, 3, 3, 4, 2]
def baseStart_341944 : Nat := 118140960795 + 341944 * 2 ^ 59
def prefixEnd_341944 : Nat := 4983230072969 + 3 ^ 40 * 341944 * 2
def baseEnd_341944 : Nat := 156072559040991445535497

theorem tailTrace_341944 : CollatzResearch.WordTrace tailWord_341944 prefixEnd_341944 156072559040991445535497 := by
  unfold tailWord_341944
  simp only [CollatzResearch.WordTrace]
  refine ⟨6235861136601381115448443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8314481515468508153931257 6235861136601381115448443)
  ·
    refine ⟨9353791704902071673172665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6235861136601381115448443 9353791704902071673172665)
    ·
      refine ⟨7015343778676553754879499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9353791704902071673172665 7015343778676553754879499)
      ·
        refine ⟨10523015668014830632319249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7015343778676553754879499 10523015668014830632319249)
        ·
          refine ⟨7892261751011122974239437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10523015668014830632319249 7892261751011122974239437)
          ·
            refine ⟨2959598156629171115339789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7892261751011122974239437 2959598156629171115339789)
            ·
              refine ⟨1109849308735939168252421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2959598156629171115339789 1109849308735939168252421)
              ·
                refine ⟨208096745387988594047329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1109849308735939168252421 208096745387988594047329)
                ·
                  refine ⟨156072559040991445535497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 208096745387988594047329 156072559040991445535497)
                  ·
                    rfl

theorem cell20_341944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 3, 4, 2].length) (baseStart_341944 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_341944 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_341944 prefixEnd_341944 := by exact prefixLift 341944
  have htrace : WordTrace (prefixWord ++ tailWord_341944) baseStart_341944 baseEnd_341944 := by
    simpa [prefixWord, tailWord_341944, baseEnd_341944] using wordTrace_append hprefix tailTrace_341944
  have hstable : (prefixWord ++ tailWord_341944).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_341944).length < 2 ^ (prefixWord ++ tailWord_341944).sum := by decide
  have hdescent : baseEnd_341944 < baseStart_341944 := by decide
  rcases family_descends (prefixWord ++ tailWord_341944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_342029 : List Nat := [1, 7, 1, 2, 2, 1, 1, 3, 2]
def baseStart_342029 : Nat := 118140960795 + 342029 * 2 ^ 59
def prefixEnd_342029 : Nat := 4983230072969 + 3 ^ 40 * 342029 * 2
def baseEnd_342029 : Nat := 156111355357108927701817

theorem tailTrace_342029 : CollatzResearch.WordTrace tailWord_342029 prefixEnd_342029 156111355357108927701817 := by
  unfold tailWord_342029
  simp only [CollatzResearch.WordTrace]
  refine ⟨12474822477894821747741141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8316548318596547831827427 12474822477894821747741141)
  ·
    refine ⟨292378651825659884712683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 12474822477894821747741141 292378651825659884712683)
    ·
      refine ⟨438567977738489827069025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 292378651825659884712683 438567977738489827069025)
      ·
        refine ⟨328925983303867370301769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 438567977738489827069025 328925983303867370301769)
        ·
          refine ⟨246694487477900527726327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 328925983303867370301769 246694487477900527726327)
          ·
            refine ⟨370041731216850791589491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 246694487477900527726327 370041731216850791589491)
            ·
              refine ⟨555062596825276187384237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 370041731216850791589491 555062596825276187384237)
              ·
                refine ⟨208148473809478570269089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 555062596825276187384237 208148473809478570269089)
                ·
                  refine ⟨156111355357108927701817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 208148473809478570269089 156111355357108927701817)
                  ·
                    rfl

theorem cell20_342029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 2, 1, 1, 3, 2].length) (baseStart_342029 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_342029 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_342029 prefixEnd_342029 := by exact prefixLift 342029
  have htrace : WordTrace (prefixWord ++ tailWord_342029) baseStart_342029 baseEnd_342029 := by
    simpa [prefixWord, tailWord_342029, baseEnd_342029] using wordTrace_append hprefix tailTrace_342029
  have hstable : (prefixWord ++ tailWord_342029).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_342029).length < 2 ^ (prefixWord ++ tailWord_342029).sum := by decide
  have hdescent : baseEnd_342029 < baseStart_342029 := by decide
  rcases family_descends (prefixWord ++ tailWord_342029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_342058 : List Nat := [3, 1, 4, 1, 2, 1, 3, 1, 4]
def baseStart_342058 : Nat := 118140960795 + 342058 * 2 ^ 59
def prefixEnd_342058 : Nat := 4983230072969 + 3 ^ 40 * 342058 * 2
def baseEnd_342058 : Nat := 156124591747313715735031

theorem tailTrace_342058 : CollatzResearch.WordTrace tailWord_342058 prefixEnd_342058 156124591747313715735031 := by
  unfold tailWord_342058
  simp only [CollatzResearch.WordTrace]
  refine ⟨3118970048697439925136707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8317253463193173133697885 3118970048697439925136707)
  ·
    refine ⟨4678455073046159887705061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3118970048697439925136707 4678455073046159887705061)
    ·
      refine ⟨877210326196154978944699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4678455073046159887705061 877210326196154978944699)
      ·
        refine ⟨1315815489294232468417049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 877210326196154978944699 1315815489294232468417049)
        ·
          refine ⟨986861616970674351312787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1315815489294232468417049 986861616970674351312787)
          ·
            refine ⟨1480292425456011526969181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 986861616970674351312787 1480292425456011526969181)
            ·
              refine ⟨555109659546004322613443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1480292425456011526969181 555109659546004322613443)
              ·
                refine ⟨832664489319006483920165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 555109659546004322613443 832664489319006483920165)
                ·
                  refine ⟨156124591747313715735031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 832664489319006483920165 156124591747313715735031)
                  ·
                    rfl

theorem cell20_342058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 3, 1, 4].length) (baseStart_342058 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_342058 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_342058 prefixEnd_342058 := by exact prefixLift 342058
  have htrace : WordTrace (prefixWord ++ tailWord_342058) baseStart_342058 baseEnd_342058 := by
    simpa [prefixWord, tailWord_342058, baseEnd_342058] using wordTrace_append hprefix tailTrace_342058
  have hstable : (prefixWord ++ tailWord_342058).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_342058).length < 2 ^ (prefixWord ++ tailWord_342058).sum := by decide
  have hdescent : baseEnd_342058 < baseStart_342058 := by decide
  rcases family_descends (prefixWord ++ tailWord_342058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_342068 : List Nat := [2, 5, 1, 2, 2, 1, 1, 3, 3]
def baseStart_342068 : Nat := 118140960795 + 342068 * 2 ^ 59
def prefixEnd_342068 : Nat := 4983230072969 + 3 ^ 40 * 342068 * 2
def baseEnd_342068 : Nat := 156129156019798125401657

theorem tailTrace_342068 : CollatzResearch.WordTrace tailWord_342068 prefixEnd_342068 156129156019798125401657 := by
  unfold tailWord_342068
  simp only [CollatzResearch.WordTrace]
  refine ⟨6238122462376765704205429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8317496616502354272273905 6238122462376765704205429)
  ·
    refine ⟨584823980847821784769259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 6238122462376765704205429 584823980847821784769259)
    ·
      refine ⟨877235971271732677153889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 584823980847821784769259 877235971271732677153889)
      ·
        refine ⟨657926978453799507865417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 877235971271732677153889 657926978453799507865417)
        ·
          refine ⟨493445233840349630899063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 657926978453799507865417 493445233840349630899063)
          ·
            refine ⟨740167850760524446348595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 493445233840349630899063 740167850760524446348595)
            ·
              refine ⟨1110251776140786669522893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 740167850760524446348595 1110251776140786669522893)
              ·
                refine ⟨416344416052795001071085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1110251776140786669522893 416344416052795001071085)
                ·
                  refine ⟨156129156019798125401657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 416344416052795001071085 156129156019798125401657)
                  ·
                    rfl

theorem cell20_342068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 1, 3, 3].length) (baseStart_342068 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_342068 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_342068 prefixEnd_342068 := by exact prefixLift 342068
  have htrace : WordTrace (prefixWord ++ tailWord_342068) baseStart_342068 baseEnd_342068 := by
    simpa [prefixWord, tailWord_342068, baseEnd_342068] using wordTrace_append hprefix tailTrace_342068
  have hstable : (prefixWord ++ tailWord_342068).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_342068).length < 2 ^ (prefixWord ++ tailWord_342068).sum := by decide
  have hdescent : baseEnd_342068 < baseStart_342068 := by decide
  rcases family_descends (prefixWord ++ tailWord_342068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_342109 : List Nat := [1, 4, 4, 1, 1, 3, 2, 2, 2]
def baseStart_342109 : Nat := 118140960795 + 342109 * 2 ^ 59
def prefixEnd_342109 : Nat := 4983230072969 + 3 ^ 40 * 342109 * 2
def baseEnd_342109 : Nat := 156147869536984205034823

theorem tailTrace_342109 : CollatzResearch.WordTrace tailWord_342109 prefixEnd_342109 156147869536984205034823 := by
  unfold tailWord_342109
  simp only [CollatzResearch.WordTrace]
  refine ⟨12477740317604995410653381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8318493545069996940435587 12477740317604995410653381)
  ·
    refine ⟨2339576309550936639497509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12477740317604995410653381 2339576309550936639497509)
    ·
      refine ⟨438670558040800619905783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2339576309550936639497509 438670558040800619905783)
      ·
        refine ⟨658005837061200929858675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 438670558040800619905783 658005837061200929858675)
        ·
          refine ⟨987008755591801394788013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 658005837061200929858675 987008755591801394788013)
          ·
            refine ⟨370128283346925523045505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 987008755591801394788013 370128283346925523045505)
            ·
              refine ⟨277596212510194142284129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 370128283346925523045505 277596212510194142284129)
              ·
                refine ⟨208197159382645606713097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 277596212510194142284129 208197159382645606713097)
                ·
                  refine ⟨156147869536984205034823, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 208197159382645606713097 156147869536984205034823)
                  ·
                    rfl

theorem cell20_342109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 3, 2, 2, 2].length) (baseStart_342109 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_342109 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_342109 prefixEnd_342109 := by exact prefixLift 342109
  have htrace : WordTrace (prefixWord ++ tailWord_342109) baseStart_342109 baseEnd_342109 := by
    simpa [prefixWord, tailWord_342109, baseEnd_342109] using wordTrace_append hprefix tailTrace_342109
  have hstable : (prefixWord ++ tailWord_342109).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_342109).length < 2 ^ (prefixWord ++ tailWord_342109).sum := by decide
  have hdescent : baseEnd_342109 < baseStart_342109 := by decide
  rcases family_descends (prefixWord ++ tailWord_342109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_342124 : List Nat := [2, 2, 1, 1, 3, 3, 3, 5]
def baseStart_342124 : Nat := 118140960795 + 342124 * 2 ^ 59
def prefixEnd_342124 : Nat := 4983230072969 + 3 ^ 40 * 342124 * 2
def baseEnd_342124 : Nat := 52051571981903606511587

theorem tailTrace_342124 : CollatzResearch.WordTrace tailWord_342124 prefixEnd_342124 52051571981903606511587 := by
  unfold tailWord_342124
  simp only [CollatzResearch.WordTrace]
  refine ⟨6239143706275326486224713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8318858275033768648299617 6239143706275326486224713)
  ·
    refine ⟨4679357779706494864668535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6239143706275326486224713 4679357779706494864668535)
    ·
      refine ⟨7019036669559742297002803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4679357779706494864668535 7019036669559742297002803)
      ·
        refine ⟨10528555004339613445504205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7019036669559742297002803 10528555004339613445504205)
        ·
          refine ⟨3948208126627355042064077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10528555004339613445504205 3948208126627355042064077)
          ·
            refine ⟨1480578047485258140774029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3948208126627355042064077 1480578047485258140774029)
            ·
              refine ⟨555216767806971802790261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1480578047485258140774029 555216767806971802790261)
              ·
                refine ⟨52051571981903606511587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 555216767806971802790261 52051571981903606511587)
                ·
                  rfl

theorem cell20_342124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 3, 5].length) (baseStart_342124 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_342124 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_342124 prefixEnd_342124 := by exact prefixLift 342124
  have htrace : WordTrace (prefixWord ++ tailWord_342124) baseStart_342124 baseEnd_342124 := by
    simpa [prefixWord, tailWord_342124, baseEnd_342124] using wordTrace_append hprefix tailTrace_342124
  have hstable : (prefixWord ++ tailWord_342124).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_342124).length < 2 ^ (prefixWord ++ tailWord_342124).sum := by decide
  have hdescent : baseEnd_342124 < baseStart_342124 := by decide
  rcases family_descends (prefixWord ++ tailWord_342124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_342134 : List Nat := [5, 1, 1, 2, 1, 3, 1, 2, 4]
def baseStart_342134 : Nat := 118140960795 + 342134 * 2 ^ 59
def prefixEnd_342134 : Nat := 4983230072969 + 3 ^ 40 * 342134 * 2
def baseEnd_342134 : Nat := 156159280218195229201387

theorem tailTrace_342134 : CollatzResearch.WordTrace tailWord_342134 prefixEnd_342134 156159280218195229201387 := by
  unfold tailWord_342134
  simp only [CollatzResearch.WordTrace]
  refine ⟨779915758907151542519591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 8319101428342949786875637 779915758907151542519591)
  ·
    refine ⟨1169873638360727313779387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 779915758907151542519591 1169873638360727313779387)
    ·
      refine ⟨1754810457541090970669081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1169873638360727313779387 1754810457541090970669081)
      ·
        refine ⟨1316107843155818228001811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1754810457541090970669081 1316107843155818228001811)
        ·
          refine ⟨1974161764733727342002717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1316107843155818228001811 1974161764733727342002717)
          ·
            refine ⟨740310661775147753251019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1974161764733727342002717 740310661775147753251019)
            ·
              refine ⟨1110465992662721629876529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 740310661775147753251019 1110465992662721629876529)
              ·
                refine ⟨832849494497041222407397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1110465992662721629876529 832849494497041222407397)
                ·
                  refine ⟨156159280218195229201387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 832849494497041222407397 156159280218195229201387)
                  ·
                    rfl

theorem cell20_342134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 1, 2, 4].length) (baseStart_342134 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_342134 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_342134 prefixEnd_342134 := by exact prefixLift 342134
  have htrace : WordTrace (prefixWord ++ tailWord_342134) baseStart_342134 baseEnd_342134 := by
    simpa [prefixWord, tailWord_342134, baseEnd_342134] using wordTrace_append hprefix tailTrace_342134
  have hstable : (prefixWord ++ tailWord_342134).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_342134).length < 2 ^ (prefixWord ++ tailWord_342134).sum := by decide
  have hdescent : baseEnd_342134 < baseStart_342134 := by decide
  rcases family_descends (prefixWord ++ tailWord_342134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_342141 : List Nat := [1, 4, 1, 1, 3, 3, 3, 4]
def baseStart_342141 : Nat := 118140960795 + 342141 * 2 ^ 59
def prefixEnd_342141 : Nat := 4983230072969 + 3 ^ 40 * 342141 * 2
def baseEnd_342141 : Nat := 52054158402978105322675

theorem tailTrace_342141 : CollatzResearch.WordTrace tailWord_342141 prefixEnd_342141 52054158402978105322675 := by
  unfold tailWord_342141
  simp only [CollatzResearch.WordTrace]
  refine ⟨12478907453489064875818277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8319271635659376583878851 12478907453489064875818277)
  ·
    refine ⟨2339795147529199664215927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12478907453489064875818277 2339795147529199664215927)
    ·
      refine ⟨3509692721293799496323891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2339795147529199664215927 3509692721293799496323891)
      ·
        refine ⟨5264539081940699244485837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3509692721293799496323891 5264539081940699244485837)
        ·
          refine ⟨1974202155727762216682189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5264539081940699244485837 1974202155727762216682189)
          ·
            refine ⟨740325808397910831255821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1974202155727762216682189 740325808397910831255821)
            ·
              refine ⟨277622178149216561720933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 740325808397910831255821 277622178149216561720933)
              ·
                refine ⟨52054158402978105322675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 277622178149216561720933 52054158402978105322675)
                ·
                  rfl

theorem cell20_342141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 3, 4].length) (baseStart_342141 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_342141 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_342141 prefixEnd_342141 := by exact prefixLift 342141
  have htrace : WordTrace (prefixWord ++ tailWord_342141) baseStart_342141 baseEnd_342141 := by
    simpa [prefixWord, tailWord_342141, baseEnd_342141] using wordTrace_append hprefix tailTrace_342141
  have hstable : (prefixWord ++ tailWord_342141).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_342141).length < 2 ^ (prefixWord ++ tailWord_342141).sum := by decide
  have hdescent : baseEnd_342141 < baseStart_342141 := by decide
  rcases family_descends (prefixWord ++ tailWord_342141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_342162 : List Nat := [3, 2, 3, 1, 1, 1, 9]
def baseStart_342162 : Nat := 118140960795 + 342162 * 2 ^ 59
def prefixEnd_342162 : Nat := 4983230072969 + 3 ^ 40 * 342162 * 2
def baseEnd_342162 : Nat := 17352451131239064029771

theorem tailTrace_342162 : CollatzResearch.WordTrace tailWord_342162 prefixEnd_342162 17352451131239064029771 := by
  unfold tailWord_342162
  simp only [CollatzResearch.WordTrace]
  refine ⟨3119918346603246365583185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8319782257608656974888493 3119918346603246365583185)
  ·
    refine ⟨2339938759952434774187389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3119918346603246365583185 2339938759952434774187389)
    ·
      refine ⟨877477034982163040320271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2339938759952434774187389 877477034982163040320271)
      ·
        refine ⟨1316215552473244560480407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 877477034982163040320271 1316215552473244560480407)
        ·
          refine ⟨1974323328709866840720611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1316215552473244560480407 1974323328709866840720611)
          ·
            refine ⟨2961484993064800261080917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1974323328709866840720611 2961484993064800261080917)
            ·
              refine ⟨17352451131239064029771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2961484993064800261080917 17352451131239064029771)
              ·
                rfl

theorem cell20_342162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 9].length) (baseStart_342162 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_342162 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_342162 prefixEnd_342162 := by exact prefixLift 342162
  have htrace : WordTrace (prefixWord ++ tailWord_342162) baseStart_342162 baseEnd_342162 := by
    simpa [prefixWord, tailWord_342162, baseEnd_342162] using wordTrace_append hprefix tailTrace_342162
  have hstable : (prefixWord ++ tailWord_342162).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_342162).length < 2 ^ (prefixWord ++ tailWord_342162).sum := by decide
  have hdescent : baseEnd_342162 < baseStart_342162 := by decide
  rcases family_descends (prefixWord ++ tailWord_342162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_342172 : List Nat := [2, 2, 3, 2, 1, 1, 1, 6, 2]
def baseStart_342172 : Nat := 118140960795 + 342172 * 2 ^ 59
def prefixEnd_342172 : Nat := 4983230072969 + 3 ^ 40 * 342172 * 2
def baseEnd_342172 : Nat := 156176624453635985934565

theorem tailTrace_342172 : CollatzResearch.WordTrace tailWord_342172 prefixEnd_342172 156176624453635985934565 := by
  unfold tailWord_342172
  simp only [CollatzResearch.WordTrace]
  refine ⟨6240019058188378585098385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8320025410917838113464513 6240019058188378585098385)
  ·
    refine ⟨4680014293641283938823789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6240019058188378585098385 4680014293641283938823789)
    ·
      refine ⟨1755005360115481477058921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4680014293641283938823789 1755005360115481477058921)
      ·
        refine ⟨1316254020086611107794191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1755005360115481477058921 1316254020086611107794191)
        ·
          refine ⟨1974381030129916661691287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1316254020086611107794191 1974381030129916661691287)
          ·
            refine ⟨2961571545194874992536931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1974381030129916661691287 2961571545194874992536931)
            ·
              refine ⟨4442357317792312488805397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2961571545194874992536931 4442357317792312488805397)
              ·
                refine ⟨208235499271514647912753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 4442357317792312488805397 208235499271514647912753)
                ·
                  refine ⟨156176624453635985934565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 208235499271514647912753 156176624453635985934565)
                  ·
                    rfl

theorem cell20_342172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 6, 2].length) (baseStart_342172 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_342172 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_342172 prefixEnd_342172 := by exact prefixLift 342172
  have htrace : WordTrace (prefixWord ++ tailWord_342172) baseStart_342172 baseEnd_342172 := by
    simpa [prefixWord, tailWord_342172, baseEnd_342172] using wordTrace_append hprefix tailTrace_342172
  have hstable : (prefixWord ++ tailWord_342172).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_342172).length < 2 ^ (prefixWord ++ tailWord_342172).sum := by decide
  have hdescent : baseEnd_342172 < baseStart_342172 := by decide
  rcases family_descends (prefixWord ++ tailWord_342172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_342206 : List Nat := [4, 2, 1, 1, 4, 2, 1, 3, 2]
def baseStart_342206 : Nat := 118140960795 + 342206 * 2 ^ 59
def prefixEnd_342206 : Nat := 4983230072969 + 3 ^ 40 * 342206 * 2
def baseEnd_342206 : Nat := 156192142980082978801093

theorem tailTrace_342206 : CollatzResearch.WordTrace tailWord_342206 prefixEnd_342206 156192142980082978801093 := by
  unfold tailWord_342206
  simp only [CollatzResearch.WordTrace]
  refine ⟨1560159774781697622116809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8320852132169053984622981 1560159774781697622116809)
  ·
    refine ⟨1170119831086273216587607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1560159774781697622116809 1170119831086273216587607)
    ·
      refine ⟨1755179746629409824881411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1170119831086273216587607 1755179746629409824881411)
      ·
        refine ⟨2632769619944114737322117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1755179746629409824881411 2632769619944114737322117)
        ·
          refine ⟨493644303739521513247897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2632769619944114737322117 493644303739521513247897)
          ·
            refine ⟨370233227804641134935923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 493644303739521513247897 370233227804641134935923)
            ·
              refine ⟨555349841706961702403885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 370233227804641134935923 555349841706961702403885)
              ·
                refine ⟨208256190640110638401457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 555349841706961702403885 208256190640110638401457)
                ·
                  refine ⟨156192142980082978801093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 208256190640110638401457 156192142980082978801093)
                  ·
                    rfl

theorem cell20_342206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 2, 1, 3, 2].length) (baseStart_342206 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_342206 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_342206 prefixEnd_342206 := by exact prefixLift 342206
  have htrace : WordTrace (prefixWord ++ tailWord_342206) baseStart_342206 baseEnd_342206 := by
    simpa [prefixWord, tailWord_342206, baseEnd_342206] using wordTrace_append hprefix tailTrace_342206
  have hstable : (prefixWord ++ tailWord_342206).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_342206).length < 2 ^ (prefixWord ++ tailWord_342206).sum := by decide
  have hdescent : baseEnd_342206 < baseStart_342206 := by decide
  rcases family_descends (prefixWord ++ tailWord_342206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_342252 : List Nat := [2, 2, 1, 1, 2, 3, 2, 1, 6]
def baseStart_342252 : Nat := 118140960795 + 342252 * 2 ^ 59
def prefixEnd_342252 : Nat := 4983230072969 + 3 ^ 40 * 342252 * 2
def baseEnd_342252 : Nat := 156213138633511263267571

theorem tailTrace_342252 : CollatzResearch.WordTrace tailWord_342252 prefixEnd_342252 156213138633511263267571 := by
  unfold tailWord_342252
  simp only [CollatzResearch.WordTrace]
  refine ⟨6241477978043465416554505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8321970637391287222072673 6241477978043465416554505)
  ·
    refine ⟨4681108483532599062415879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6241477978043465416554505 4681108483532599062415879)
    ·
      refine ⟨7021662725298898593623819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4681108483532599062415879 7021662725298898593623819)
      ·
        refine ⟨10532494087948347890435729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7021662725298898593623819 10532494087948347890435729)
        ·
          refine ⟨7899370565961260917826797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10532494087948347890435729 7899370565961260917826797)
          ·
            refine ⟨2962263962235472844185049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7899370565961260917826797 2962263962235472844185049)
            ·
              refine ⟨2221697971676604633138787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2962263962235472844185049 2221697971676604633138787)
              ·
                refine ⟨3332546957514906949708181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2221697971676604633138787 3332546957514906949708181)
                ·
                  refine ⟨156213138633511263267571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3332546957514906949708181 156213138633511263267571)
                  ·
                    rfl

theorem cell20_342252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 6].length) (baseStart_342252 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_342252 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_342252 prefixEnd_342252 := by exact prefixLift 342252
  have htrace : WordTrace (prefixWord ++ tailWord_342252) baseStart_342252 baseEnd_342252 := by
    simpa [prefixWord, tailWord_342252, baseEnd_342252] using wordTrace_append hprefix tailTrace_342252
  have hstable : (prefixWord ++ tailWord_342252).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_342252).length < 2 ^ (prefixWord ++ tailWord_342252).sum := by decide
  have hdescent : baseEnd_342252 < baseStart_342252 := by decide
  rcases family_descends (prefixWord ++ tailWord_342252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_342259 : List Nat := [1, 1, 1, 2, 2, 4, 1, 8]
def baseStart_342259 : Nat := 118140960795 + 342259 * 2 ^ 59
def prefixEnd_342259 : Nat := 4983230072969 + 3 ^ 40 * 342259 * 2
def baseEnd_342259 : Nat := 52072111208083450011403

theorem tailTrace_342259 : CollatzResearch.WordTrace tailWord_342259 prefixEnd_342259 52072111208083450011403 := by
  unfold tailWord_342259
  simp only [CollatzResearch.WordTrace]
  refine ⟨12483211267061571028613831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8322140844707714019075887 12483211267061571028613831)
  ·
    refine ⟨18724816900592356542920747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12483211267061571028613831 18724816900592356542920747)
    ·
      refine ⟨28087225350888534814381121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18724816900592356542920747 28087225350888534814381121)
      ·
        refine ⟨21065419013166401110785841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28087225350888534814381121 21065419013166401110785841)
        ·
          refine ⟨15799064259874800833089381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21065419013166401110785841 15799064259874800833089381)
          ·
            refine ⟨2962324548726525156204259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15799064259874800833089381 2962324548726525156204259)
            ·
              refine ⟨4443486823089787734306389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2962324548726525156204259 4443486823089787734306389)
              ·
                refine ⟨52072111208083450011403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4443486823089787734306389 52072111208083450011403)
                ·
                  rfl

theorem cell20_342259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 8].length) (baseStart_342259 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_342259 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_342259 prefixEnd_342259 := by exact prefixLift 342259
  have htrace : WordTrace (prefixWord ++ tailWord_342259) baseStart_342259 baseEnd_342259 := by
    simpa [prefixWord, tailWord_342259, baseEnd_342259] using wordTrace_append hprefix tailTrace_342259
  have hstable : (prefixWord ++ tailWord_342259).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_342259).length < 2 ^ (prefixWord ++ tailWord_342259).sum := by decide
  have hdescent : baseEnd_342259 < baseStart_342259 := by decide
  rcases family_descends (prefixWord ++ tailWord_342259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_342276 : List Nat := [2, 3, 2, 2, 3, 8]
def baseStart_342276 : Nat := 118140960795 + 342276 * 2 ^ 59
def prefixEnd_342276 : Nat := 4983230072969 + 3 ^ 40 * 342276 * 2
def baseEnd_342276 : Nat := 5786077514350883202499

theorem tailTrace_342276 : CollatzResearch.WordTrace tailWord_342276 prefixEnd_342276 5786077514350883202499 := by
  unfold tailWord_342276
  simp only [CollatzResearch.WordTrace]
  refine ⟨6241915653999991465991341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8322554205333321954655121 6241915653999991465991341)
  ·
    refine ⟨2340718370249996799746753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6241915653999991465991341 2340718370249996799746753)
    ·
      refine ⟨1755538777687497599810065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2340718370249996799746753 1755538777687497599810065)
      ·
        refine ⟨1316654083265623199857549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1755538777687497599810065 1316654083265623199857549)
        ·
          refine ⟨493745281224608699946581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1316654083265623199857549 493745281224608699946581)
          ·
            refine ⟨5786077514350883202499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 493745281224608699946581 5786077514350883202499)
            ·
              rfl

theorem cell20_342276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 8].length) (baseStart_342276 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_342276 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_342276 prefixEnd_342276 := by exact prefixLift 342276
  have htrace : WordTrace (prefixWord ++ tailWord_342276) baseStart_342276 baseEnd_342276 := by
    simpa [prefixWord, tailWord_342276, baseEnd_342276] using wordTrace_append hprefix tailTrace_342276
  have hstable : (prefixWord ++ tailWord_342276).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_342276).length < 2 ^ (prefixWord ++ tailWord_342276).sum := by decide
  have hdescent : baseEnd_342276 < baseStart_342276 := by decide
  rcases family_descends (prefixWord ++ tailWord_342276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_342286 : List Nat := [4, 1, 1, 2, 1, 2, 3, 4, 2]
def baseStart_342286 : Nat := 118140960795 + 342286 * 2 ^ 59
def prefixEnd_342286 : Nat := 4983230072969 + 3 ^ 40 * 342286 * 2
def baseEnd_342286 : Nat := 156228657159958256134099

theorem tailTrace_342286 : CollatzResearch.WordTrace tailWord_342286 prefixEnd_342286 156228657159958256134099 := by
  unfold tailWord_342286
  simp only [CollatzResearch.WordTrace]
  refine ⟨1560524504745469329980839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8322797358642503093231141 1560524504745469329980839)
  ·
    refine ⟨2340786757118203994971259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1560524504745469329980839 2340786757118203994971259)
    ·
      refine ⟨3511180135677305992456889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2340786757118203994971259 3511180135677305992456889)
      ·
        refine ⟨2633385101757979494342667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3511180135677305992456889 2633385101757979494342667)
        ·
          refine ⟨3950077652636969241514001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2633385101757979494342667 3950077652636969241514001)
          ·
            refine ⟨2962558239477726931135501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3950077652636969241514001 2962558239477726931135501)
            ·
              refine ⟨1110959339804147599175813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2962558239477726931135501 1110959339804147599175813)
              ·
                refine ⟨208304876213277674845465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1110959339804147599175813 208304876213277674845465)
                ·
                  refine ⟨156228657159958256134099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 208304876213277674845465 156228657159958256134099)
                  ·
                    rfl

theorem cell20_342286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 3, 4, 2].length) (baseStart_342286 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_342286 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_342286 prefixEnd_342286 := by exact prefixLift 342286
  have htrace : WordTrace (prefixWord ++ tailWord_342286) baseStart_342286 baseEnd_342286 := by
    simpa [prefixWord, tailWord_342286, baseEnd_342286] using wordTrace_append hprefix tailTrace_342286
  have hstable : (prefixWord ++ tailWord_342286).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_342286).length < 2 ^ (prefixWord ++ tailWord_342286).sum := by decide
  have hdescent : baseEnd_342286 < baseStart_342286 := by decide
  rcases family_descends (prefixWord ++ tailWord_342286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_342335 : List Nat := [1, 1, 2, 2, 4, 1, 9]
def baseStart_342335 : Nat := 118140960795 + 342335 * 2 ^ 59
def prefixEnd_342335 : Nat := 4983230072969 + 3 ^ 40 * 342335 * 2
def baseEnd_342335 : Nat := 17361224677236873722285

theorem tailTrace_342335 : CollatzResearch.WordTrace tailWord_342335 prefixEnd_342335 17361224677236873722285 := by
  unfold tailWord_342335
  simp only [CollatzResearch.WordTrace]
  refine ⟨12485983214786236008380459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8323988809857490672253639 12485983214786236008380459)
  ·
    refine ⟨18728974822179354012570689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12485983214786236008380459 18728974822179354012570689)
    ·
      refine ⟨14046731116634515509428017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18728974822179354012570689 14046731116634515509428017)
      ·
        refine ⟨10535048337475886632071013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14046731116634515509428017 10535048337475886632071013)
        ·
          refine ⟨1975321563276728743513315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10535048337475886632071013 1975321563276728743513315)
          ·
            refine ⟨2962982344915093115269973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1975321563276728743513315 2962982344915093115269973)
            ·
              refine ⟨17361224677236873722285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2962982344915093115269973 17361224677236873722285)
              ·
                rfl

theorem cell20_342335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 9].length) (baseStart_342335 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_342335 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_342335 prefixEnd_342335 := by exact prefixLift 342335
  have htrace : WordTrace (prefixWord ++ tailWord_342335) baseStart_342335 baseEnd_342335 := by
    simpa [prefixWord, tailWord_342335, baseEnd_342335] using wordTrace_append hprefix tailTrace_342335
  have hstable : (prefixWord ++ tailWord_342335).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_342335).length < 2 ^ (prefixWord ++ tailWord_342335).sum := by decide
  have hdescent : baseEnd_342335 < baseStart_342335 := by decide
  rcases family_descends (prefixWord ++ tailWord_342335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_342383 : List Nat := [1, 1, 2, 1, 3, 1, 2, 7, 2]
def baseStart_342383 : Nat := 118140960795 + 342383 * 2 ^ 59
def prefixEnd_342383 : Nat := 4983230072969 + 3 ^ 40 * 342383 * 2
def baseEnd_342383 : Nat := 156272930603057029900369

theorem tailTrace_342383 : CollatzResearch.WordTrace tailWord_342383 prefixEnd_342383 156272930603057029900369 := by
  unfold tailWord_342383
  simp only [CollatzResearch.WordTrace]
  refine ⟨12487733918612340206127803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8325155945741560137418535 12487733918612340206127803)
  ·
    refine ⟨18731600877918510309191705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12487733918612340206127803 18731600877918510309191705)
    ·
      refine ⟨14048700658438882731893779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18731600877918510309191705 14048700658438882731893779)
      ·
        refine ⟨21073050987658324097840669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14048700658438882731893779 21073050987658324097840669)
        ·
          refine ⟨7902394120371871536690251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21073050987658324097840669 7902394120371871536690251)
          ·
            refine ⟨11853591180557807305035377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7902394120371871536690251 11853591180557807305035377)
            ·
              refine ⟨8890193385418355478776533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11853591180557807305035377 8890193385418355478776533)
              ·
                refine ⟨208363907470742706533825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 8890193385418355478776533 208363907470742706533825)
                ·
                  refine ⟨156272930603057029900369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 208363907470742706533825 156272930603057029900369)
                  ·
                    rfl

theorem cell20_342383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 7, 2].length) (baseStart_342383 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_342383 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_342383 prefixEnd_342383 := by exact prefixLift 342383
  have htrace : WordTrace (prefixWord ++ tailWord_342383) baseStart_342383 baseEnd_342383 := by
    simpa [prefixWord, tailWord_342383, baseEnd_342383] using wordTrace_append hprefix tailTrace_342383
  have hstable : (prefixWord ++ tailWord_342383).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_342383).length < 2 ^ (prefixWord ++ tailWord_342383).sum := by decide
  have hdescent : baseEnd_342383 < baseStart_342383 := by decide
  rcases family_descends (prefixWord ++ tailWord_342383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_342397 : List Nat := [1, 4, 1, 1, 2, 3, 2, 1, 5]
def baseStart_342397 : Nat := 118140960795 + 342397 * 2 ^ 59
def prefixEnd_342397 : Nat := 4983230072969 + 3 ^ 40 * 342397 * 2
def baseEnd_342397 : Nat := 156279320584535203433645

theorem tailTrace_342397 : CollatzResearch.WordTrace tailWord_342397 prefixEnd_342397 156279320584535203433645 := by
  unfold tailWord_342397
  simp only [CollatzResearch.WordTrace]
  refine ⟨12488244540561620597137445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8325496360374413731424963 12488244540561620597137445)
  ·
    refine ⟨2341545851355303861963271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12488244540561620597137445 2341545851355303861963271)
    ·
      refine ⟨3512318777032955792944907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2341545851355303861963271 3512318777032955792944907)
      ·
        refine ⟨5268478165549433689417361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3512318777032955792944907 5268478165549433689417361)
        ·
          refine ⟨3951358624162075267063021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5268478165549433689417361 3951358624162075267063021)
          ·
            refine ⟨1481759484060778225148633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3951358624162075267063021 1481759484060778225148633)
            ·
              refine ⟨1111319613045583668861475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1481759484060778225148633 1111319613045583668861475)
              ·
                refine ⟨1666979419568375503292213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1111319613045583668861475 1666979419568375503292213)
                ·
                  refine ⟨156279320584535203433645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1666979419568375503292213 156279320584535203433645)
                  ·
                    rfl

theorem cell20_342397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 2, 1, 5].length) (baseStart_342397 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_342397 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_342397 prefixEnd_342397 := by exact prefixLift 342397
  have htrace : WordTrace (prefixWord ++ tailWord_342397) baseStart_342397 baseEnd_342397 := by
    simpa [prefixWord, tailWord_342397, baseEnd_342397] using wordTrace_append hprefix tailTrace_342397
  have hstable : (prefixWord ++ tailWord_342397).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_342397).length < 2 ^ (prefixWord ++ tailWord_342397).sum := by decide
  have hdescent : baseEnd_342397 < baseStart_342397 := by decide
  rcases family_descends (prefixWord ++ tailWord_342397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_342411 : List Nat := [1, 1, 1, 1, 4, 4, 1, 7]
def baseStart_342411 : Nat := 118140960795 + 342411 * 2 ^ 59
def prefixEnd_342411 : Nat := 4983230072969 + 3 ^ 40 * 342411 * 2
def baseEnd_342411 : Nat := 52095236855337792322307

theorem tailTrace_342411 : CollatzResearch.WordTrace tailWord_342411 prefixEnd_342411 52095236855337792322307 := by
  unfold tailWord_342411
  simp only [CollatzResearch.WordTrace]
  refine ⟨12488755162510900988147087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8325836775007267325431391 12488755162510900988147087)
  ·
    refine ⟨18733132743766351482220631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12488755162510900988147087 18733132743766351482220631)
    ·
      refine ⟨28099699115649527223330947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18733132743766351482220631 28099699115649527223330947)
      ·
        refine ⟨42149548673474290834996421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28099699115649527223330947 42149548673474290834996421)
        ·
          refine ⟨7903040376276429531561829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 42149548673474290834996421 7903040376276429531561829)
          ·
            refine ⟨1481820070551830537167843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7903040376276429531561829 1481820070551830537167843)
            ·
              refine ⟨2222730105827745805751765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1481820070551830537167843 2222730105827745805751765)
              ·
                refine ⟨52095236855337792322307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2222730105827745805751765 52095236855337792322307)
                ·
                  rfl

theorem cell20_342411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 1, 7].length) (baseStart_342411 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_342411 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_342411 prefixEnd_342411 := by exact prefixLift 342411
  have htrace : WordTrace (prefixWord ++ tailWord_342411) baseStart_342411 baseEnd_342411 := by
    simpa [prefixWord, tailWord_342411, baseEnd_342411] using wordTrace_append hprefix tailTrace_342411
  have hstable : (prefixWord ++ tailWord_342411).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_342411).length < 2 ^ (prefixWord ++ tailWord_342411).sum := by decide
  have hdescent : baseEnd_342411 < baseStart_342411 := by decide
  rcases family_descends (prefixWord ++ tailWord_342411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_342445 : List Nat := [1, 5, 2, 2, 3, 7]
def baseStart_342445 : Nat := 118140960795 + 342445 * 2 ^ 59
def prefixEnd_342445 : Nat := 4983230072969 + 3 ^ 40 * 342445 * 2
def baseEnd_342445 : Nat := 5788934410831865549387

theorem tailTrace_342445 : CollatzResearch.WordTrace tailWord_342445 prefixEnd_342445 5788934410831865549387 := by
  unfold tailWord_342445
  simp only [CollatzResearch.WordTrace]
  refine ⟨12489995244387724794884789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8326663496258483196589859 12489995244387724794884789)
  ·
    refine ⟨1170937054161349199520449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 12489995244387724794884789 1170937054161349199520449)
    ·
      refine ⟨878202790621011899640337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1170937054161349199520449 878202790621011899640337)
      ·
        refine ⟨658652092965758924730253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 878202790621011899640337 658652092965758924730253)
        ·
          refine ⟨246994534862159596773845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 658652092965758924730253 246994534862159596773845)
          ·
            refine ⟨5788934410831865549387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 246994534862159596773845 5788934410831865549387)
            ·
              rfl

theorem cell20_342445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 3, 7].length) (baseStart_342445 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_342445 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_342445 prefixEnd_342445 := by exact prefixLift 342445
  have htrace : WordTrace (prefixWord ++ tailWord_342445) baseStart_342445 baseEnd_342445 := by
    simpa [prefixWord, tailWord_342445, baseEnd_342445] using wordTrace_append hprefix tailTrace_342445
  have hstable : (prefixWord ++ tailWord_342445).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_342445).length < 2 ^ (prefixWord ++ tailWord_342445).sum := by decide
  have hdescent : baseEnd_342445 < baseStart_342445 := by decide
  rcases family_descends (prefixWord ++ tailWord_342445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_342449 : List Nat := [1, 2, 2, 4, 1, 10]
def baseStart_342449 : Nat := 118140960795 + 342449 * 2 ^ 59
def prefixEnd_342449 : Nat := 4983230072969 + 3 ^ 40 * 342449 * 2
def baseEnd_342449 : Nat := 5789002029683486433337

theorem tailTrace_342449 : CollatzResearch.WordTrace tailWord_342449 prefixEnd_342449 5789002029683486433337 := by
  unfold tailWord_342449
  simp only [CollatzResearch.WordTrace]
  refine ⟨12490141136373233478030401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8326760757582155652020267 12490141136373233478030401)
  ·
    refine ⟨9367605852279925108522801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12490141136373233478030401 9367605852279925108522801)
    ·
      refine ⟨7025704389209943831392101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9367605852279925108522801 7025704389209943831392101)
      ·
        refine ⟨1317319572976864468386019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7025704389209943831392101 1317319572976864468386019)
        ·
          refine ⟨1975979359465296702579029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1317319572976864468386019 1975979359465296702579029)
          ·
            refine ⟨5789002029683486433337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 1975979359465296702579029 5789002029683486433337)
            ·
              rfl

theorem cell20_342449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 10].length) (baseStart_342449 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_342449 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_342449 prefixEnd_342449 := by exact prefixLift 342449
  have htrace : WordTrace (prefixWord ++ tailWord_342449) baseStart_342449 baseEnd_342449 := by
    simpa [prefixWord, tailWord_342449, baseEnd_342449] using wordTrace_append hprefix tailTrace_342449
  have hstable : (prefixWord ++ tailWord_342449).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_342449).length < 2 ^ (prefixWord ++ tailWord_342449).sum := by decide
  have hdescent : baseEnd_342449 < baseStart_342449 := by decide
  rcases family_descends (prefixWord ++ tailWord_342449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_342455 : List Nat := [1, 1, 3, 1, 3, 5, 2, 2, 2]
def baseStart_342455 : Nat := 118140960795 + 342455 * 2 ^ 59
def prefixEnd_342455 : Nat := 4983230072969 + 3 ^ 40 * 342455 * 2
def baseEnd_342455 : Nat := 156305793364944779500075

theorem tailTrace_342455 : CollatzResearch.WordTrace tailWord_342455 prefixEnd_342455 156305793364944779500075 := by
  unfold tailWord_342455
  simp only [CollatzResearch.WordTrace]
  refine ⟨12490359974351496502748819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8326906649567664335165879 12490359974351496502748819)
  ·
    refine ⟨18735539961527244754123229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12490359974351496502748819 18735539961527244754123229)
    ·
      refine ⟨7025827485572716782796211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18735539961527244754123229 7025827485572716782796211)
      ·
        refine ⟨10538741228359075174194317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7025827485572716782796211 10538741228359075174194317)
        ·
          refine ⟨3952027960634653190322869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10538741228359075174194317 3952027960634653190322869)
          ·
            refine ⟨370502621309498736592769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3952027960634653190322869 370502621309498736592769)
            ·
              refine ⟨277876965982124052444577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 370502621309498736592769 277876965982124052444577)
              ·
                refine ⟨208407724486593039333433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 277876965982124052444577 208407724486593039333433)
                ·
                  refine ⟨156305793364944779500075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 208407724486593039333433 156305793364944779500075)
                  ·
                    rfl

theorem cell20_342455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 5, 2, 2, 2].length) (baseStart_342455 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_342455 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_342455 prefixEnd_342455 := by exact prefixLift 342455
  have htrace : WordTrace (prefixWord ++ tailWord_342455) baseStart_342455 baseEnd_342455 := by
    simpa [prefixWord, tailWord_342455, baseEnd_342455] using wordTrace_append hprefix tailTrace_342455
  have hstable : (prefixWord ++ tailWord_342455).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_342455).length < 2 ^ (prefixWord ++ tailWord_342455).sum := by decide
  have hdescent : baseEnd_342455 < baseStart_342455 := by decide
  rcases family_descends (prefixWord ++ tailWord_342455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_342473 : List Nat := [1, 2, 1, 1, 2, 1, 6, 3, 3]
def baseStart_342473 : Nat := 118140960795 + 342473 * 2 ^ 59
def prefixEnd_342473 : Nat := 4983230072969 + 3 ^ 40 * 342473 * 2
def baseEnd_342473 : Nat := 156314009055416716900001

theorem tailTrace_342473 : CollatzResearch.WordTrace tailWord_342473 prefixEnd_342473 156314009055416716900001 := by
  unfold tailWord_342473
  simp only [CollatzResearch.WordTrace]
  refine ⟨12491016488286285576904073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8327344325524190384602715 12491016488286285576904073)
  ·
    refine ⟨9368262366214714182678055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12491016488286285576904073 9368262366214714182678055)
    ·
      refine ⟨14052393549322071274017083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9368262366214714182678055 14052393549322071274017083)
      ·
        refine ⟨21078590323983106911025625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14052393549322071274017083 21078590323983106911025625)
        ·
          refine ⟨15808942742987330183269219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21078590323983106911025625 15808942742987330183269219)
          ·
            refine ⟨23713414114480995274903829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15808942742987330183269219 23713414114480995274903829)
            ·
              refine ⟨1111566286616296653511117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 23713414114480995274903829 1111566286616296653511117)
              ·
                refine ⟨416837357481111245066669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1111566286616296653511117 416837357481111245066669)
                ·
                  refine ⟨156314009055416716900001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 416837357481111245066669 156314009055416716900001)
                  ·
                    rfl

theorem cell20_342473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 6, 3, 3].length) (baseStart_342473 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_342473 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_342473 prefixEnd_342473 := by exact prefixLift 342473
  have htrace : WordTrace (prefixWord ++ tailWord_342473) baseStart_342473 baseEnd_342473 := by
    simpa [prefixWord, tailWord_342473, baseEnd_342473] using wordTrace_append hprefix tailTrace_342473
  have hstable : (prefixWord ++ tailWord_342473).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_342473).length < 2 ^ (prefixWord ++ tailWord_342473).sum := by decide
  have hdescent : baseEnd_342473 < baseStart_342473 := by decide
  rcases family_descends (prefixWord ++ tailWord_342473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_342514 : List Nat := [3, 2, 1, 4, 2, 1, 2, 1, 4]
def baseStart_342514 : Nat := 118140960795 + 342514 * 2 ^ 59
def prefixEnd_342514 : Nat := 4983230072969 + 3 ^ 40 * 342514 * 2
def baseEnd_342514 : Nat := 156332722572602796533167

theorem tailTrace_342514 : CollatzResearch.WordTrace tailWord_342514 prefixEnd_342514 156332722572602796533167 := by
  unfold tailWord_342514
  simp only [CollatzResearch.WordTrace]
  refine ⟨3123127970284437394786649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8328341254091833052764397 3123127970284437394786649)
  ·
    refine ⟨2342345977713328046089987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3123127970284437394786649 2342345977713328046089987)
    ·
      refine ⟨3513518966569992069134981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2342345977713328046089987 3513518966569992069134981)
      ·
        refine ⟨658784806231873512962809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3513518966569992069134981 658784806231873512962809)
        ·
          refine ⟨494088604673905134722107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 658784806231873512962809 494088604673905134722107)
          ·
            refine ⟨741132907010857702083161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 494088604673905134722107 741132907010857702083161)
            ·
              refine ⟨555849680258143276562371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 741132907010857702083161 555849680258143276562371)
              ·
                refine ⟨833774520387214914843557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 555849680258143276562371 833774520387214914843557)
                ·
                  refine ⟨156332722572602796533167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 833774520387214914843557 156332722572602796533167)
                  ·
                    rfl

theorem cell20_342514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 2, 1, 4].length) (baseStart_342514 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_342514 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_342514 prefixEnd_342514 := by exact prefixLift 342514
  have htrace : WordTrace (prefixWord ++ tailWord_342514) baseStart_342514 baseEnd_342514 := by
    simpa [prefixWord, tailWord_342514, baseEnd_342514] using wordTrace_append hprefix tailTrace_342514
  have hstable : (prefixWord ++ tailWord_342514).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_342514).length < 2 ^ (prefixWord ++ tailWord_342514).sum := by decide
  have hdescent : baseEnd_342514 < baseStart_342514 := by decide
  rcases family_descends (prefixWord ++ tailWord_342514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_342525 : List Nat := [1, 4, 1, 1, 1, 3, 2, 7]
def baseStart_342525 : Nat := 118140960795 + 342525 * 2 ^ 59
def prefixEnd_342525 : Nat := 4983230072969 + 3 ^ 40 * 342525 * 2
def baseEnd_342525 : Nat := 52112581090778549055485

theorem tailTrace_342525 : CollatzResearch.WordTrace tailWord_342525 prefixEnd_342525 52112581090778549055485 := by
  unfold tailWord_342525
  simp only [CollatzResearch.WordTrace]
  refine ⟨12492913084097898457797029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8328608722731932305198019 12492913084097898457797029)
  ·
    refine ⟨2342421203268355960836943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12492913084097898457797029 2342421203268355960836943)
    ·
      refine ⟨3513631804902533941255415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2342421203268355960836943 3513631804902533941255415)
      ·
        refine ⟨5270447707353800911883123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3513631804902533941255415 5270447707353800911883123)
        ·
          refine ⟨7905671561030701367824685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5270447707353800911883123 7905671561030701367824685)
          ·
            refine ⟨2964626835386513012934257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7905671561030701367824685 2964626835386513012934257)
            ·
              refine ⟨2223470126539884759700693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2964626835386513012934257 2223470126539884759700693)
              ·
                refine ⟨52112581090778549055485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2223470126539884759700693 52112581090778549055485)
                ·
                  rfl

theorem cell20_342525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 2, 7].length) (baseStart_342525 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_342525 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_342525 prefixEnd_342525 := by exact prefixLift 342525
  have htrace : WordTrace (prefixWord ++ tailWord_342525) baseStart_342525 baseEnd_342525 := by
    simpa [prefixWord, tailWord_342525, baseEnd_342525] using wordTrace_append hprefix tailTrace_342525
  have hstable : (prefixWord ++ tailWord_342525).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_342525).length < 2 ^ (prefixWord ++ tailWord_342525).sum := by decide
  have hdescent : baseEnd_342525 < baseStart_342525 := by decide
  rcases family_descends (prefixWord ++ tailWord_342525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_342534 : List Nat := [6, 2, 1, 1, 1, 3, 2, 4]
def baseStart_342534 : Nat := 118140960795 + 342534 * 2 ^ 59
def prefixEnd_342534 : Nat := 4983230072969 + 3 ^ 40 * 342534 * 2
def baseEnd_342534 : Nat := 52113950372523871955473

theorem tailTrace_342534 : CollatzResearch.WordTrace tailWord_342534 prefixEnd_342534 52113950372523871955473 := by
  unfold tailWord_342534
  simp only [CollatzResearch.WordTrace]
  refine ⟨390413791908290406089833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 8328827560710195329916437 390413791908290406089833)
  ·
    refine ⟨292810343931217804567375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 390413791908290406089833 292810343931217804567375)
    ·
      refine ⟨439215515896826706851063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 292810343931217804567375 439215515896826706851063)
      ·
        refine ⟨658823273845240060276595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 439215515896826706851063 658823273845240060276595)
        ·
          refine ⟨988234910767860090414893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 658823273845240060276595 988234910767860090414893)
          ·
            refine ⟨370588091537947533905585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 988234910767860090414893 370588091537947533905585)
            ·
              refine ⟨277941068653460650429189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 370588091537947533905585 277941068653460650429189)
              ·
                refine ⟨52113950372523871955473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 277941068653460650429189 52113950372523871955473)
                ·
                  rfl

theorem cell20_342534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 3, 2, 4].length) (baseStart_342534 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_342534 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_342534 prefixEnd_342534 := by exact prefixLift 342534
  have htrace : WordTrace (prefixWord ++ tailWord_342534) baseStart_342534 baseEnd_342534 := by
    simpa [prefixWord, tailWord_342534, baseEnd_342534] using wordTrace_append hprefix tailTrace_342534
  have hstable : (prefixWord ++ tailWord_342534).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_342534).length < 2 ^ (prefixWord ++ tailWord_342534).sum := by decide
  have hdescent : baseEnd_342534 < baseStart_342534 := by decide
  rcases family_descends (prefixWord ++ tailWord_342534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_342542 : List Nat := [4, 1, 1, 2, 3, 2, 1, 6]
def baseStart_342542 : Nat := 118140960795 + 342542 * 2 ^ 59
def prefixEnd_342542 : Nat := 4983230072969 + 3 ^ 40 * 342542 * 2
def baseEnd_342542 : Nat := 52115167511853047866573

theorem tailTrace_342542 : CollatzResearch.WordTrace tailWord_342542 prefixEnd_342542 52115167511853047866573 := by
  unfold tailWord_342542
  simp only [CollatzResearch.WordTrace]
  refine ⟨1561691640629538795145735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8329022083357540240777253 1561691640629538795145735)
  ·
    refine ⟨2342537460944308192718603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1561691640629538795145735 2342537460944308192718603)
    ·
      refine ⟨3513806191416462289077905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2342537460944308192718603 3513806191416462289077905)
      ·
        refine ⟨2635354643562346716808429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3513806191416462289077905 2635354643562346716808429)
        ·
          refine ⟨988257991335880018803161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2635354643562346716808429 988257991335880018803161)
          ·
            refine ⟨741193493501910014102371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 988257991335880018803161 741193493501910014102371)
            ·
              refine ⟨1111790240252865021153557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 741193493501910014102371 1111790240252865021153557)
              ·
                refine ⟨52115167511853047866573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1111790240252865021153557 52115167511853047866573)
                ·
                  rfl

theorem cell20_342542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 1, 6].length) (baseStart_342542 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_342542 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_342542 prefixEnd_342542 := by exact prefixLift 342542
  have htrace : WordTrace (prefixWord ++ tailWord_342542) baseStart_342542 baseEnd_342542 := by
    simpa [prefixWord, tailWord_342542, baseEnd_342542] using wordTrace_append hprefix tailTrace_342542
  have hstable : (prefixWord ++ tailWord_342542).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_342542).length < 2 ^ (prefixWord ++ tailWord_342542).sum := by decide
  have hdescent : baseEnd_342542 < baseStart_342542 := by decide
  rcases family_descends (prefixWord ++ tailWord_342542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_342548 : List Nat := [2, 4, 3, 1, 1, 3, 1, 3, 2]
def baseStart_342548 : Nat := 118140960795 + 342548 * 2 ^ 59
def prefixEnd_342548 : Nat := 4983230072969 + 3 ^ 40 * 342548 * 2
def baseEnd_342548 : Nat := 156348241099049789399695

theorem tailTrace_342548 : CollatzResearch.WordTrace tailWord_342548 prefixEnd_342548 156348241099049789399695 := by
  unfold tailWord_342548
  simp only [CollatzResearch.WordTrace]
  refine ⟨6246875981507286692942149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8329167975343048923922865 6246875981507286692942149)
  ·
    refine ⟨1171289246532616254926653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6246875981507286692942149 1171289246532616254926653)
    ·
      refine ⟨439233467449731095597495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1171289246532616254926653 439233467449731095597495)
      ·
        refine ⟨658850201174596643396243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 439233467449731095597495 658850201174596643396243)
        ·
          refine ⟨988275301761894965094365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 658850201174596643396243 988275301761894965094365)
          ·
            refine ⟨370603238160710611910387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 988275301761894965094365 370603238160710611910387)
            ·
              refine ⟨555904857241065917865581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 370603238160710611910387 555904857241065917865581)
              ·
                refine ⟨208464321465399719199593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 555904857241065917865581 208464321465399719199593)
                ·
                  refine ⟨156348241099049789399695, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 208464321465399719199593 156348241099049789399695)
                  ·
                    rfl

theorem cell20_342548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 3, 1, 3, 2].length) (baseStart_342548 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_342548 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_342548 prefixEnd_342548 := by exact prefixLift 342548
  have htrace : WordTrace (prefixWord ++ tailWord_342548) baseStart_342548 baseEnd_342548 := by
    simpa [prefixWord, tailWord_342548, baseEnd_342548] using wordTrace_append hprefix tailTrace_342548
  have hstable : (prefixWord ++ tailWord_342548).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_342548).length < 2 ^ (prefixWord ++ tailWord_342548).sum := by decide
  have hdescent : baseEnd_342548 < baseStart_342548 := by decide
  rcases family_descends (prefixWord ++ tailWord_342548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_342552 : List Nat := [2, 1, 2, 3, 3, 1, 3, 3, 2]
def baseStart_342552 : Nat := 118140960795 + 342552 * 2 ^ 59
def prefixEnd_342552 : Nat := 4983230072969 + 3 ^ 40 * 342552 * 2
def baseEnd_342552 : Nat := 156350066808043553266345

theorem tailTrace_342552 : CollatzResearch.WordTrace tailWord_342552 prefixEnd_342552 156350066808043553266345 := by
  unfold tailWord_342552
  simp only [CollatzResearch.WordTrace]
  refine ⟨6246948927500041034514955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8329265236666721379353273 6246948927500041034514955)
  ·
    refine ⟨9370423391250061551772433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6246948927500041034514955 9370423391250061551772433)
    ·
      refine ⟨7027817543437546163829325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9370423391250061551772433 7027817543437546163829325)
      ·
        refine ⟨2635431578789079811435997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7027817543437546163829325 2635431578789079811435997)
        ·
          refine ⟨988286842045904929288499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2635431578789079811435997 988286842045904929288499)
          ·
            refine ⟨1482430263068857393932749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 988286842045904929288499 1482430263068857393932749)
            ·
              refine ⟨555911348650821522724781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1482430263068857393932749 555911348650821522724781)
              ·
                refine ⟨208466755744058071021793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 555911348650821522724781 208466755744058071021793)
                ·
                  refine ⟨156350066808043553266345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 208466755744058071021793 156350066808043553266345)
                  ·
                    rfl

theorem cell20_342552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 3, 3, 2].length) (baseStart_342552 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_342552 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_342552 prefixEnd_342552 := by exact prefixLift 342552
  have htrace : WordTrace (prefixWord ++ tailWord_342552) baseStart_342552 baseEnd_342552 := by
    simpa [prefixWord, tailWord_342552, baseEnd_342552] using wordTrace_append hprefix tailTrace_342552
  have hstable : (prefixWord ++ tailWord_342552).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_342552).length < 2 ^ (prefixWord ++ tailWord_342552).sum := by decide
  have hdescent : baseEnd_342552 < baseStart_342552 := by decide
  rcases family_descends (prefixWord ++ tailWord_342552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_342563 : List Nat := [1, 1, 1, 4, 4, 1, 8]
def baseStart_342563 : Nat := 118140960795 + 342563 * 2 ^ 59
def prefixEnd_342563 : Nat := 4983230072969 + 3 ^ 40 * 342563 * 2
def baseEnd_342563 : Nat := 17372787500864044877737

theorem tailTrace_342563 : CollatzResearch.WordTrace tailWord_342563 prefixEnd_342563 17372787500864044877737 := by
  unfold tailWord_342563
  simp only [CollatzResearch.WordTrace]
  refine ⟨12494299057960230947680343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8329532705306820631786895 12494299057960230947680343)
  ·
    refine ⟨18741448586940346421520515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12494299057960230947680343 18741448586940346421520515)
    ·
      refine ⟨28112172880410519632280773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18741448586940346421520515 28112172880410519632280773)
      ·
        refine ⟨5271032415076972431052645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28112172880410519632280773 5271032415076972431052645)
        ·
          refine ⟨988318577826932330822371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5271032415076972431052645 988318577826932330822371)
          ·
            refine ⟨1482477866740398496233557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 988318577826932330822371 1482477866740398496233557)
            ·
              refine ⟨17372787500864044877737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1482477866740398496233557 17372787500864044877737)
              ·
                rfl

theorem cell20_342563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 8].length) (baseStart_342563 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_342563 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_342563 prefixEnd_342563 := by exact prefixLift 342563
  have htrace : WordTrace (prefixWord ++ tailWord_342563) baseStart_342563 baseEnd_342563 := by
    simpa [prefixWord, tailWord_342563, baseEnd_342563] using wordTrace_append hprefix tailTrace_342563
  have hstable : (prefixWord ++ tailWord_342563).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_342563).length < 2 ^ (prefixWord ++ tailWord_342563).sum := by decide
  have hdescent : baseEnd_342563 < baseStart_342563 := by decide
  rcases family_descends (prefixWord ++ tailWord_342563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_342608 : List Nat := [2, 1, 1, 1, 1, 3, 2, 4, 5]
def baseStart_342608 : Nat := 118140960795 + 342608 * 2 ^ 59
def prefixEnd_342608 : Nat := 4983230072969 + 3 ^ 40 * 342608 * 2
def baseEnd_342608 : Nat := 156375626733956247399449

theorem tailTrace_342608 : CollatzResearch.WordTrace tailWord_342608 prefixEnd_342608 156375626733956247399449 := by
  unfold tailWord_342608
  simp only [CollatzResearch.WordTrace]
  refine ⟨6247970171398601816534239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8330626895198135755378985 6247970171398601816534239)
  ·
    refine ⟨9371955257097902724801359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6247970171398601816534239 9371955257097902724801359)
    ·
      refine ⟨14057932885646854087202039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9371955257097902724801359 14057932885646854087202039)
      ·
        refine ⟨21086899328470281130803059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14057932885646854087202039 21086899328470281130803059)
        ·
          refine ⟨31630348992705421696204589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21086899328470281130803059 31630348992705421696204589)
          ·
            refine ⟨11861380872264533136076721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31630348992705421696204589 11861380872264533136076721)
            ·
              refine ⟨8896035654198399852057541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11861380872264533136076721 8896035654198399852057541)
              ·
                refine ⟨1668006685162199972260789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8896035654198399852057541 1668006685162199972260789)
                ·
                  refine ⟨156375626733956247399449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1668006685162199972260789 156375626733956247399449)
                  ·
                    rfl

theorem cell20_342608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 4, 5].length) (baseStart_342608 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_342608 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_342608 prefixEnd_342608 := by exact prefixLift 342608
  have htrace : WordTrace (prefixWord ++ tailWord_342608) baseStart_342608 baseEnd_342608 := by
    simpa [prefixWord, tailWord_342608, baseEnd_342608] using wordTrace_append hprefix tailTrace_342608
  have hstable : (prefixWord ++ tailWord_342608).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_342608).length < 2 ^ (prefixWord ++ tailWord_342608).sum := by decide
  have hdescent : baseEnd_342608 < baseStart_342608 := by decide
  rcases family_descends (prefixWord ++ tailWord_342608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_342625 : List Nat := [1, 2, 3, 1, 1, 4, 1, 4, 3]
def baseStart_342625 : Nat := 118140960795 + 342625 * 2 ^ 59
def prefixEnd_342625 : Nat := 4983230072969 + 3 ^ 40 * 342625 * 2
def baseEnd_342625 : Nat := 156383385997179743832713

theorem tailTrace_342625 : CollatzResearch.WordTrace tailWord_342625 prefixEnd_342625 156383385997179743832713 := by
  unfold tailWord_342625
  simp only [CollatzResearch.WordTrace]
  refine ⟨12496560383735615536437329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8331040255823743690958219 12496560383735615536437329)
  ·
    refine ⟨9372420287801711652327997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12496560383735615536437329 9372420287801711652327997)
    ·
      refine ⟨3514657607925641869622999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9372420287801711652327997 3514657607925641869622999)
      ·
        refine ⟨5271986411888462804434499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3514657607925641869622999 5271986411888462804434499)
        ·
          refine ⟨7907979617832694206651749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5271986411888462804434499 7907979617832694206651749)
          ·
            refine ⟨1482746178343630163747203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7907979617832694206651749 1482746178343630163747203)
            ·
              refine ⟨2224119267515445245620805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1482746178343630163747203 2224119267515445245620805)
              ·
                refine ⟨417022362659145983553901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2224119267515445245620805 417022362659145983553901)
                ·
                  refine ⟨156383385997179743832713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 417022362659145983553901 156383385997179743832713)
                  ·
                    rfl

theorem cell20_342625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 1, 4, 3].length) (baseStart_342625 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_342625 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_342625 prefixEnd_342625 := by exact prefixLift 342625
  have htrace : WordTrace (prefixWord ++ tailWord_342625) baseStart_342625 baseEnd_342625 := by
    simpa [prefixWord, tailWord_342625, baseEnd_342625] using wordTrace_append hprefix tailTrace_342625
  have hstable : (prefixWord ++ tailWord_342625).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_342625).length < 2 ^ (prefixWord ++ tailWord_342625).sum := by decide
  have hdescent : baseEnd_342625 < baseStart_342625 := by decide
  rcases family_descends (prefixWord ++ tailWord_342625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_342639 : List Nat := [1, 1, 2, 1, 3, 2, 5, 5]
def baseStart_342639 : Nat := 118140960795 + 342639 * 2 ^ 59
def prefixEnd_342639 : Nat := 4983230072969 + 3 ^ 40 * 342639 * 2
def baseEnd_342639 : Nat := 52129925326219305788663

theorem tailTrace_342639 : CollatzResearch.WordTrace tailWord_342639 prefixEnd_342639 52129925326219305788663 := by
  unfold tailWord_342639
  simp only [CollatzResearch.WordTrace]
  refine ⟨12497071005684895927446971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8331380670456597284964647 12497071005684895927446971)
  ·
    refine ⟨18745606508527343891170457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12497071005684895927446971 18745606508527343891170457)
    ·
      refine ⟨14059204881395507918377843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18745606508527343891170457 14059204881395507918377843)
      ·
        refine ⟨21088807322093261877566765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14059204881395507918377843 21088807322093261877566765)
        ·
          refine ⟨7908302745784973204087537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21088807322093261877566765 7908302745784973204087537)
          ·
            refine ⟨5931227059338729903065653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7908302745784973204087537 5931227059338729903065653)
            ·
              refine ⟨556052536813005928412405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5931227059338729903065653 556052536813005928412405)
              ·
                refine ⟨52129925326219305788663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 556052536813005928412405 52129925326219305788663)
                ·
                  rfl

theorem cell20_342639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 5, 5].length) (baseStart_342639 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_342639 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_342639 prefixEnd_342639 := by exact prefixLift 342639
  have htrace : WordTrace (prefixWord ++ tailWord_342639) baseStart_342639 baseEnd_342639 := by
    simpa [prefixWord, tailWord_342639, baseEnd_342639] using wordTrace_append hprefix tailTrace_342639
  have hstable : (prefixWord ++ tailWord_342639).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_342639).length < 2 ^ (prefixWord ++ tailWord_342639).sum := by decide
  have hdescent : baseEnd_342639 < baseStart_342639 := by decide
  rcases family_descends (prefixWord ++ tailWord_342639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_342656 : List Nat := [2, 1, 1, 2, 1, 6, 3, 4]
def baseStart_342656 : Nat := 118140960795 + 342656 * 2 ^ 59
def prefixEnd_342656 : Nat := 4983230072969 + 3 ^ 40 * 342656 * 2
def baseEnd_342656 : Nat := 52132511747293804599751

theorem tailTrace_342656 : CollatzResearch.WordTrace tailWord_342656 prefixEnd_342656 52132511747293804599751 := by
  unfold tailWord_342656
  simp only [CollatzResearch.WordTrace]
  refine ⟨6248845523311653915407911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8331794031082205220543881 6248845523311653915407911)
  ·
    refine ⟨9373268284967480873111867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6248845523311653915407911 9373268284967480873111867)
    ·
      refine ⟨14059902427451221309667801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9373268284967480873111867 14059902427451221309667801)
      ·
        refine ⟨10544926820588415982250851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14059902427451221309667801 10544926820588415982250851)
        ·
          refine ⟨15817390230882623973376277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10544926820588415982250851 15817390230882623973376277)
          ·
            refine ⟨741440167072622998752013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 15817390230882623973376277 741440167072622998752013)
            ·
              refine ⟨278040062652233624532005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 741440167072622998752013 278040062652233624532005)
              ·
                refine ⟨52132511747293804599751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 278040062652233624532005 52132511747293804599751)
                ·
                  rfl

theorem cell20_342656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 3, 4].length) (baseStart_342656 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_342656 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_342656 prefixEnd_342656 := by exact prefixLift 342656
  have htrace : WordTrace (prefixWord ++ tailWord_342656) baseStart_342656 baseEnd_342656 := by
    simpa [prefixWord, tailWord_342656, baseEnd_342656] using wordTrace_append hprefix tailTrace_342656
  have hstable : (prefixWord ++ tailWord_342656).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_342656).length < 2 ^ (prefixWord ++ tailWord_342656).sum := by decide
  have hdescent : baseEnd_342656 < baseStart_342656 := by decide
  rcases family_descends (prefixWord ++ tailWord_342656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_342670 : List Nat := [4, 1, 1, 3, 1, 1, 1, 2, 6]
def baseStart_342670 : Nat := 118140960795 + 342670 * 2 ^ 59
def prefixEnd_342670 : Nat := 4983230072969 + 3 ^ 40 * 342670 * 2
def baseEnd_342670 : Nat := 156403925223359587332529

theorem tailTrace_342670 : CollatzResearch.WordTrace tailWord_342670 prefixEnd_342670 156403925223359587332529 := by
  unfold tailWord_342670
  simp only [CollatzResearch.WordTrace]
  refine ⟨1562275208571573527728183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8332134445715058814550309 1562275208571573527728183)
  ·
    refine ⟨2343412812857360291592275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1562275208571573527728183 2343412812857360291592275)
    ·
      refine ⟨3515119219286040437388413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2343412812857360291592275 3515119219286040437388413)
      ·
        refine ⟨1318169707232265164020655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3515119219286040437388413 1318169707232265164020655)
        ·
          refine ⟨1977254560848397746030983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1318169707232265164020655 1977254560848397746030983)
          ·
            refine ⟨2965881841272596619046475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1977254560848397746030983 2965881841272596619046475)
            ·
              refine ⟨4448822761908894928569713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2965881841272596619046475 4448822761908894928569713)
              ·
                refine ⟨3336617071431671196427285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4448822761908894928569713 3336617071431671196427285)
                ·
                  refine ⟨156403925223359587332529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3336617071431671196427285 156403925223359587332529)
                  ·
                    rfl

theorem cell20_342670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 2, 6].length) (baseStart_342670 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_342670 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_342670 prefixEnd_342670 := by exact prefixLift 342670
  have htrace : WordTrace (prefixWord ++ tailWord_342670) baseStart_342670 baseEnd_342670 := by
    simpa [prefixWord, tailWord_342670, baseEnd_342670] using wordTrace_append hprefix tailTrace_342670
  have hstable : (prefixWord ++ tailWord_342670).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_342670).length < 2 ^ (prefixWord ++ tailWord_342670).sum := by decide
  have hdescent : baseEnd_342670 < baseStart_342670 := by decide
  rcases family_descends (prefixWord ++ tailWord_342670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_342711 : List Nat := [1, 1, 3, 1, 6, 2, 2, 4]
def baseStart_342711 : Nat := 118140960795 + 342711 * 2 ^ 59
def prefixEnd_342711 : Nat := 4983230072969 + 3 ^ 40 * 342711 * 2
def baseEnd_342711 : Nat := 52140879580181888988565

theorem tailTrace_342711 : CollatzResearch.WordTrace tailWord_342711 prefixEnd_342711 52140879580181888988565 := by
  unfold tailWord_342711
  simp only [CollatzResearch.WordTrace]
  refine ⟨12499697061424052224067987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8333131374282701482711991 12499697061424052224067987)
  ·
    refine ⟨18749545592136078336101981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12499697061424052224067987 18749545592136078336101981)
    ·
      refine ⟨7031079597051029376038243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18749545592136078336101981 7031079597051029376038243)
      ·
        refine ⟨10546619395576544064057365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7031079597051029376038243 10546619395576544064057365)
        ·
          refine ⟨494372784167650503002689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 10546619395576544064057365 494372784167650503002689)
          ·
            refine ⟨370779588125737877252017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 494372784167650503002689 370779588125737877252017)
            ·
              refine ⟨278084691094303407939013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 370779588125737877252017 278084691094303407939013)
              ·
                refine ⟨52140879580181888988565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 278084691094303407939013 52140879580181888988565)
                ·
                  rfl

theorem cell20_342711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 2, 2, 4].length) (baseStart_342711 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_342711 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_342711 prefixEnd_342711 := by exact prefixLift 342711
  have htrace : WordTrace (prefixWord ++ tailWord_342711) baseStart_342711 baseEnd_342711 := by
    simpa [prefixWord, tailWord_342711, baseEnd_342711] using wordTrace_append hprefix tailTrace_342711
  have hstable : (prefixWord ++ tailWord_342711).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_342711).length < 2 ^ (prefixWord ++ tailWord_342711).sum := by decide
  have hdescent : baseEnd_342711 < baseStart_342711 := by decide
  rcases family_descends (prefixWord ++ tailWord_342711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_342732 : List Nat := [2, 2, 1, 5, 1, 3, 6]
def baseStart_342732 : Nat := 118140960795 + 342732 * 2 ^ 59
def prefixEnd_342732 : Nat := 4983230072969 + 3 ^ 40 * 342732 * 2
def baseEnd_342732 : Nat := 17381358190306991918401

theorem tailTrace_342732 : CollatzResearch.WordTrace tailWord_342732 prefixEnd_342732 17381358190306991918401 := by
  unfold tailWord_342732
  simp only [CollatzResearch.WordTrace]
  refine ⟨6250231497173986405291225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8333641996231981873721633 6250231497173986405291225)
  ·
    refine ⟨4687673622880489803968419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6250231497173986405291225 4687673622880489803968419)
    ·
      refine ⟨7031510434320734705952629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4687673622880489803968419 7031510434320734705952629)
      ·
        refine ⟨659204103217568878683059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 7031510434320734705952629 659204103217568878683059)
        ·
          refine ⟨988806154826353318024589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 659204103217568878683059 988806154826353318024589)
          ·
            refine ⟨370802308059882494259221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 988806154826353318024589 370802308059882494259221)
            ·
              refine ⟨17381358190306991918401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 370802308059882494259221 17381358190306991918401)
              ·
                rfl

theorem cell20_342732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 3, 6].length) (baseStart_342732 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_342732 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_342732 prefixEnd_342732 := by exact prefixLift 342732
  have htrace : WordTrace (prefixWord ++ tailWord_342732) baseStart_342732 baseEnd_342732 := by
    simpa [prefixWord, tailWord_342732, baseEnd_342732] using wordTrace_append hprefix tailTrace_342732
  have hstable : (prefixWord ++ tailWord_342732).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_342732).length < 2 ^ (prefixWord ++ tailWord_342732).sum := by decide
  have hdescent : baseEnd_342732 < baseStart_342732 := by decide
  rcases family_descends (prefixWord ++ tailWord_342732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_342753 : List Nat := [1, 2, 3, 1, 4, 1, 1, 7]
def baseStart_342753 : Nat := 118140960795 + 342753 * 2 ^ 59
def prefixEnd_342753 : Nat := 4983230072969 + 3 ^ 40 * 342753 * 2
def baseEnd_342753 : Nat := 52147269561660062521841

theorem tailTrace_342753 : CollatzResearch.WordTrace tailWord_342753 prefixEnd_342753 52147269561660062521841 := by
  unfold tailWord_342753
  simp only [CollatzResearch.WordTrace]
  refine ⟨12501228927271893397096913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8334152618181262264731275 12501228927271893397096913)
  ·
    refine ⟨9375921695453920047822685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12501228927271893397096913 9375921695453920047822685)
    ·
      refine ⟨3515970635795220017933507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9375921695453920047822685 3515970635795220017933507)
      ·
        refine ⟨5273955953692830026900261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3515970635795220017933507 5273955953692830026900261)
        ·
          refine ⟨988866741317405630043799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5273955953692830026900261 988866741317405630043799)
          ·
            refine ⟨1483300111976108445065699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 988866741317405630043799 1483300111976108445065699)
            ·
              refine ⟨2224950167964162667598549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1483300111976108445065699 2224950167964162667598549)
              ·
                refine ⟨52147269561660062521841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2224950167964162667598549 52147269561660062521841)
                ·
                  rfl

theorem cell20_342753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 1, 7].length) (baseStart_342753 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_342753 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_342753 prefixEnd_342753 := by exact prefixLift 342753
  have htrace : WordTrace (prefixWord ++ tailWord_342753) baseStart_342753 baseEnd_342753 := by
    simpa [prefixWord, tailWord_342753, baseEnd_342753] using wordTrace_append hprefix tailTrace_342753
  have hstable : (prefixWord ++ tailWord_342753).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_342753).length < 2 ^ (prefixWord ++ tailWord_342753).sum := by decide
  have hdescent : baseEnd_342753 < baseStart_342753 := by decide
  rcases family_descends (prefixWord ++ tailWord_342753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_342756 : List Nat := [2, 3, 1, 1, 1, 4, 4, 1, 3]
def baseStart_342756 : Nat := 118140960795 + 342756 * 2 ^ 59
def prefixEnd_342756 : Nat := 4983230072969 + 3 ^ 40 * 342756 * 2
def baseEnd_342756 : Nat := 156443177966725510465511

theorem tailTrace_342756 : CollatzResearch.WordTrace tailWord_342756 prefixEnd_342756 156443177966725510465511 := by
  unfold tailWord_342756
  simp only [CollatzResearch.WordTrace]
  refine ⟨6250669173130512454728061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8334225564174016606304081 6250669173130512454728061)
  ·
    refine ⟨2344000939923942170523023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6250669173130512454728061 2344000939923942170523023)
    ·
      refine ⟨3516001409885913255784535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2344000939923942170523023 3516001409885913255784535)
      ·
        refine ⟨5274002114828869883676803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3516001409885913255784535 5274002114828869883676803)
        ·
          refine ⟨7911003172243304825515205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5274002114828869883676803 7911003172243304825515205)
          ·
            refine ⟨1483313094795619654784101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7911003172243304825515205 1483313094795619654784101)
            ·
              refine ⟨278121205274178685272019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1483313094795619654784101 278121205274178685272019)
              ·
                refine ⟨417181807911268027908029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 278121205274178685272019 417181807911268027908029)
                ·
                  refine ⟨156443177966725510465511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 417181807911268027908029 156443177966725510465511)
                  ·
                    rfl

theorem cell20_342756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 4, 1, 3].length) (baseStart_342756 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_342756 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_342756 prefixEnd_342756 := by exact prefixLift 342756
  have htrace : WordTrace (prefixWord ++ tailWord_342756) baseStart_342756 baseEnd_342756 := by
    simpa [prefixWord, tailWord_342756, baseEnd_342756] using wordTrace_append hprefix tailTrace_342756
  have hstable : (prefixWord ++ tailWord_342756).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_342756).length < 2 ^ (prefixWord ++ tailWord_342756).sum := by decide
  have hdescent : baseEnd_342756 < baseStart_342756 := by decide
  rcases family_descends (prefixWord ++ tailWord_342756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_342791 : List Nat := [1, 1, 4, 4, 1, 9]
def baseStart_342791 : Nat := 118140960795 + 342791 * 2 ^ 59
def prefixEnd_342791 : Nat := 4983230072969 + 3 ^ 40 * 342791 * 2
def baseEnd_342791 : Nat := 5794783441497072011063

theorem tailTrace_342791 : CollatzResearch.WordTrace tailWord_342791 prefixEnd_342791 5794783441497072011063 := by
  unfold tailWord_342791
  simp only [CollatzResearch.WordTrace]
  refine ⟨12502614901134225886980227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8335076600756150591320151 12502614901134225886980227)
  ·
    refine ⟨18753922351701338830470341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12502614901134225886980227 18753922351701338830470341)
    ·
      refine ⟨3516360440944001030713189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18753922351701338830470341 3516360440944001030713189)
      ·
        refine ⟨659317582677000193258723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3516360440944001030713189 659317582677000193258723)
        ·
          refine ⟨988976374015500289888085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 659317582677000193258723 988976374015500289888085)
          ·
            refine ⟨5794783441497072011063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 988976374015500289888085 5794783441497072011063)
            ·
              rfl

theorem cell20_342791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 9].length) (baseStart_342791 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_342791 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_342791 prefixEnd_342791 := by exact prefixLift 342791
  have htrace : WordTrace (prefixWord ++ tailWord_342791) baseStart_342791 baseEnd_342791 := by
    simpa [prefixWord, tailWord_342791, baseEnd_342791] using wordTrace_append hprefix tailTrace_342791
  have hstable : (prefixWord ++ tailWord_342791).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_342791).length < 2 ^ (prefixWord ++ tailWord_342791).sum := by decide
  have hdescent : baseEnd_342791 < baseStart_342791 := by decide
  rcases family_descends (prefixWord ++ tailWord_342791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_342815 : List Nat := [1, 1, 2, 4, 2, 2, 2, 3, 3]
def baseStart_342815 : Nat := 118140960795 + 342815 * 2 ^ 59
def prefixEnd_342815 : Nat := 4983230072969 + 3 ^ 40 * 342815 * 2
def baseEnd_342815 : Nat := 156470107174383527498603

theorem tailTrace_342815 : CollatzResearch.WordTrace tailWord_342815 prefixEnd_342815 156470107174383527498603 := by
  unfold tailWord_342815
  simp only [CollatzResearch.WordTrace]
  refine ⟨12503490253047277985853899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8335660168698185323902599 12503490253047277985853899)
  ·
    refine ⟨18755235379570916978780849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12503490253047277985853899 18755235379570916978780849)
    ·
      refine ⟨14066426534678187734085637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18755235379570916978780849 14066426534678187734085637)
      ·
        refine ⟨2637454975252160200141057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14066426534678187734085637 2637454975252160200141057)
        ·
          refine ⟨1978091231439120150105793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2637454975252160200141057 1978091231439120150105793)
          ·
            refine ⟨1483568423579340112579345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1978091231439120150105793 1483568423579340112579345)
            ·
              refine ⟨1112676317684505084434509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1483568423579340112579345 1112676317684505084434509)
              ·
                refine ⟨417253619131689406662941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1112676317684505084434509 417253619131689406662941)
                ·
                  refine ⟨156470107174383527498603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 417253619131689406662941 156470107174383527498603)
                  ·
                    rfl

theorem cell20_342815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 2, 3, 3].length) (baseStart_342815 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_342815 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_342815 prefixEnd_342815 := by exact prefixLift 342815
  have htrace : WordTrace (prefixWord ++ tailWord_342815) baseStart_342815 baseEnd_342815 := by
    simpa [prefixWord, tailWord_342815, baseEnd_342815] using wordTrace_append hprefix tailTrace_342815
  have hstable : (prefixWord ++ tailWord_342815).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_342815).length < 2 ^ (prefixWord ++ tailWord_342815).sum := by decide
  have hdescent : baseEnd_342815 < baseStart_342815 := by decide
  rcases family_descends (prefixWord ++ tailWord_342815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_342839 : List Nat := [1, 1, 3, 1, 2, 1, 6, 3, 2]
def baseStart_342839 : Nat := 118140960795 + 342839 * 2 ^ 59
def prefixEnd_342839 : Nat := 4983230072969 + 3 ^ 40 * 342839 * 2
def baseEnd_342839 : Nat := 156481061428346110698505

theorem tailTrace_342839 : CollatzResearch.WordTrace tailWord_342839 prefixEnd_342839 156481061428346110698505 := by
  unfold tailWord_342839
  simp only [CollatzResearch.WordTrace]
  refine ⟨12504365604960330084727571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8336243736640220056485047 12504365604960330084727571)
  ·
    refine ⟨18756548407440495127091357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12504365604960330084727571 18756548407440495127091357)
    ·
      refine ⟨7033705652790185672659259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18756548407440495127091357 7033705652790185672659259)
      ·
        refine ⟨10550558479185278508988889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7033705652790185672659259 10550558479185278508988889)
        ·
          refine ⟨7912918859388958881741667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10550558479185278508988889 7912918859388958881741667)
          ·
            refine ⟨11869378289083438322612501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7912918859388958881741667 11869378289083438322612501)
            ·
              refine ⟨556377107300786171372461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 11869378289083438322612501 556377107300786171372461)
              ·
                refine ⟨208641415237794814264673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 556377107300786171372461 208641415237794814264673)
                ·
                  refine ⟨156481061428346110698505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 208641415237794814264673 156481061428346110698505)
                  ·
                    rfl

theorem cell20_342839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 6, 3, 2].length) (baseStart_342839 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_342839 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_342839 prefixEnd_342839 := by exact prefixLift 342839
  have htrace : WordTrace (prefixWord ++ tailWord_342839) baseStart_342839 baseEnd_342839 := by
    simpa [prefixWord, tailWord_342839, baseEnd_342839] using wordTrace_append hprefix tailTrace_342839
  have hstable : (prefixWord ++ tailWord_342839).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_342839).length < 2 ^ (prefixWord ++ tailWord_342839).sum := by decide
  have hdescent : baseEnd_342839 < baseStart_342839 := by decide
  rcases family_descends (prefixWord ++ tailWord_342839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_342846 : List Nat := [4, 2, 1, 2, 3, 1, 7]
def baseStart_342846 : Nat := 118140960795 + 342846 * 2 ^ 59
def prefixEnd_342846 : Nat := 4983230072969 + 3 ^ 40 * 342846 * 2
def baseEnd_342846 : Nat := 17387139602120577496127

theorem tailTrace_342846 : CollatzResearch.WordTrace tailWord_342846 prefixEnd_342846 17387139602120577496127 := by
  unfold tailWord_342846
  simp only [CollatzResearch.WordTrace]
  refine ⟨1563077614491871285029049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8336413943956646853488261 1563077614491871285029049)
  ·
    refine ⟨1172308210868903463771787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1563077614491871285029049 1172308210868903463771787)
    ·
      refine ⟨1758462316303355195657681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1172308210868903463771787 1758462316303355195657681)
      ·
        refine ⟨1318846737227516396743261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1758462316303355195657681 1318846737227516396743261)
        ·
          refine ⟨494567526460318648778723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1318846737227516396743261 494567526460318648778723)
          ·
            refine ⟨741851289690477973168085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 494567526460318648778723 741851289690477973168085)
            ·
              refine ⟨17387139602120577496127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 741851289690477973168085 17387139602120577496127)
              ·
                rfl

theorem cell20_342846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 7].length) (baseStart_342846 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_342846 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_342846 prefixEnd_342846 := by exact prefixLift 342846
  have htrace : WordTrace (prefixWord ++ tailWord_342846) baseStart_342846 baseEnd_342846 := by
    simpa [prefixWord, tailWord_342846, baseEnd_342846] using wordTrace_append hprefix tailTrace_342846
  have hstable : (prefixWord ++ tailWord_342846).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_342846).length < 2 ^ (prefixWord ++ tailWord_342846).sum := by decide
  have hdescent : baseEnd_342846 < baseStart_342846 := by decide
  rcases family_descends (prefixWord ++ tailWord_342846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_342860 : List Nat := [2, 2, 1, 3, 3, 1, 1, 3, 4]
def baseStart_342860 : Nat := 118140960795 + 342860 * 2 ^ 59
def prefixEnd_342860 : Nat := 4983230072969 + 3 ^ 40 * 342860 * 2
def baseEnd_342860 : Nat := 156490646400563370998419

theorem tailTrace_342860 : CollatzResearch.WordTrace tailWord_342860 prefixEnd_342860 156490646400563370998419 := by
  unfold tailWord_342860
  simp only [CollatzResearch.WordTrace]
  refine ⟨6252565768942125335621017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8336754358589500447494689 6252565768942125335621017)
  ·
    refine ⟨4689424326706594001715763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6252565768942125335621017 4689424326706594001715763)
    ·
      refine ⟨7034136490059891002573645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4689424326706594001715763 7034136490059891002573645)
      ·
        refine ⟨2637801183772459125965117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7034136490059891002573645 2637801183772459125965117)
        ·
          refine ⟨989175443914672172236919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2637801183772459125965117 989175443914672172236919)
          ·
            refine ⟨1483763165872008258355379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 989175443914672172236919 1483763165872008258355379)
            ·
              refine ⟨2225644748808012387533069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1483763165872008258355379 2225644748808012387533069)
              ·
                refine ⟨834616780803004645324901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2225644748808012387533069 834616780803004645324901)
                ·
                  refine ⟨156490646400563370998419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 834616780803004645324901 156490646400563370998419)
                  ·
                    rfl

theorem cell20_342860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 1, 3, 4].length) (baseStart_342860 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_342860 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_342860 prefixEnd_342860 := by exact prefixLift 342860
  have htrace : WordTrace (prefixWord ++ tailWord_342860) baseStart_342860 baseEnd_342860 := by
    simpa [prefixWord, tailWord_342860, baseEnd_342860] using wordTrace_append hprefix tailTrace_342860
  have hstable : (prefixWord ++ tailWord_342860).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_342860).length < 2 ^ (prefixWord ++ tailWord_342860).sum := by decide
  have hdescent : baseEnd_342860 < baseStart_342860 := by decide
  rcases family_descends (prefixWord ++ tailWord_342860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_342881 : List Nat := [1, 2, 3, 1, 1, 1, 2, 3, 6]
def baseStart_342881 : Nat := 118140960795 + 342881 * 2 ^ 59
def prefixEnd_342881 : Nat := 4983230072969 + 3 ^ 40 * 342881 * 2
def baseEnd_342881 : Nat := 156500231372780631298333

theorem tailTrace_342881 : CollatzResearch.WordTrace tailWord_342881 prefixEnd_342881 156500231372780631298333 := by
  unfold tailWord_342881
  simp only [CollatzResearch.WordTrace]
  refine ⟨12505897470808171257756497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8337264980538780838504331 12505897470808171257756497)
  ·
    refine ⟨9379423103106128443317373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12505897470808171257756497 9379423103106128443317373)
    ·
      refine ⟨3517283663664798166244015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9379423103106128443317373 3517283663664798166244015)
      ·
        refine ⟨5275925495497197249366023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3517283663664798166244015 5275925495497197249366023)
        ·
          refine ⟨7913888243245795874049035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5275925495497197249366023 7913888243245795874049035)
          ·
            refine ⟨11870832364868693811073553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7913888243245795874049035 11870832364868693811073553)
            ·
              refine ⟨8903124273651520358305165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11870832364868693811073553 8903124273651520358305165)
              ·
                refine ⟨3338671602619320134364437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8903124273651520358305165 3338671602619320134364437)
                ·
                  refine ⟨156500231372780631298333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3338671602619320134364437 156500231372780631298333)
                  ·
                    rfl

theorem cell20_342881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 3, 6].length) (baseStart_342881 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_342881 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_342881 prefixEnd_342881 := by exact prefixLift 342881
  have htrace : WordTrace (prefixWord ++ tailWord_342881) baseStart_342881 baseEnd_342881 := by
    simpa [prefixWord, tailWord_342881, baseEnd_342881] using wordTrace_append hprefix tailTrace_342881
  have hstable : (prefixWord ++ tailWord_342881).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_342881).length < 2 ^ (prefixWord ++ tailWord_342881).sum := by decide
  have hdescent : baseEnd_342881 < baseStart_342881 := by decide
  rcases family_descends (prefixWord ++ tailWord_342881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_342884 : List Nat := [2, 3, 1, 1, 4, 1, 4, 4]
def baseStart_342884 : Nat := 118140960795 + 342884 * 2 ^ 59
def prefixEnd_342884 : Nat := 4983230072969 + 3 ^ 40 * 342884 * 2
def baseEnd_342884 : Nat := 52167200218175318066107

theorem tailTrace_342884 : CollatzResearch.WordTrace tailWord_342884 prefixEnd_342884 52167200218175318066107 := by
  unfold tailWord_342884
  simp only [CollatzResearch.WordTrace]
  refine ⟨6253003444898651385057853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8337337926531535180077137 6253003444898651385057853)
  ·
    refine ⟨2344876291836994269396695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6253003444898651385057853 2344876291836994269396695)
    ·
      refine ⟨3517314437755491404095043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2344876291836994269396695 3517314437755491404095043)
      ·
        refine ⟨5275971656633237106142565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3517314437755491404095043 5275971656633237106142565)
        ·
          refine ⟨989244685618731957401731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5275971656633237106142565 989244685618731957401731)
          ·
            refine ⟨1483867028428097936102597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 989244685618731957401731 1483867028428097936102597)
            ·
              refine ⟨278225067830268363019237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1483867028428097936102597 278225067830268363019237)
              ·
                refine ⟨52167200218175318066107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 278225067830268363019237 52167200218175318066107)
                ·
                  rfl

theorem cell20_342884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 4, 4].length) (baseStart_342884 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_342884 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_342884 prefixEnd_342884 := by exact prefixLift 342884
  have htrace : WordTrace (prefixWord ++ tailWord_342884) baseStart_342884 baseEnd_342884 := by
    simpa [prefixWord, tailWord_342884, baseEnd_342884] using wordTrace_append hprefix tailTrace_342884
  have hstable : (prefixWord ++ tailWord_342884).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_342884).length < 2 ^ (prefixWord ++ tailWord_342884).sum := by decide
  have hdescent : baseEnd_342884 < baseStart_342884 := by decide
  rcases family_descends (prefixWord ++ tailWord_342884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_342905 : List Nat := [1, 2, 1, 3, 2, 5, 6]
def baseStart_342905 : Nat := 118140960795 + 342905 * 2 ^ 59
def prefixEnd_342905 : Nat := 4983230072969 + 3 ^ 40 * 342905 * 2
def baseEnd_342905 : Nat := 17390131736304801610915

theorem tailTrace_342905 : CollatzResearch.WordTrace tailWord_342905 prefixEnd_342905 17390131736304801610915 := by
  unfold tailWord_342905
  simp only [CollatzResearch.WordTrace]
  refine ⟨12506772822721223356630169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8337848548480815571086779 12506772822721223356630169)
  ·
    refine ⟨9380079617040917517472627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12506772822721223356630169 9380079617040917517472627)
    ·
      refine ⟨14070119425561376276208941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9380079617040917517472627 14070119425561376276208941)
      ·
        refine ⟨5276294784585516103578353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14070119425561376276208941 5276294784585516103578353)
        ·
          refine ⟨3957221088439137077683765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5276294784585516103578353 3957221088439137077683765)
          ·
            refine ⟨370989477041169101032853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3957221088439137077683765 370989477041169101032853)
            ·
              refine ⟨17390131736304801610915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 370989477041169101032853 17390131736304801610915)
              ·
                rfl

theorem cell20_342905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 5, 6].length) (baseStart_342905 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_342905 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_342905 prefixEnd_342905 := by exact prefixLift 342905
  have htrace : WordTrace (prefixWord ++ tailWord_342905) baseStart_342905 baseEnd_342905 := by
    simpa [prefixWord, tailWord_342905, baseEnd_342905] using wordTrace_append hprefix tailTrace_342905
  have hstable : (prefixWord ++ tailWord_342905).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_342905).length < 2 ^ (prefixWord ++ tailWord_342905).sum := by decide
  have hdescent : baseEnd_342905 < baseStart_342905 := by decide
  rcases family_descends (prefixWord ++ tailWord_342905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_342922 : List Nat := [3, 1, 2, 4, 1, 2, 2, 5]
def baseStart_342922 : Nat := 118140960795 + 342922 * 2 ^ 59
def prefixEnd_342922 : Nat := 4983230072969 + 3 ^ 40 * 342922 * 2
def baseEnd_342922 : Nat := 52172981629988903643833

theorem tailTrace_342922 : CollatzResearch.WordTrace tailWord_342922 prefixEnd_342922 52172981629988903643833 := by
  unfold tailWord_342922
  simp only [CollatzResearch.WordTrace]
  refine ⟨3126848215914908814999755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8338261909106423506666013 3126848215914908814999755)
  ·
    refine ⟨4690272323872363222499633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3126848215914908814999755 4690272323872363222499633)
    ·
      refine ⟨3517704242904272416874725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4690272323872363222499633 3517704242904272416874725)
      ·
        refine ⟨659569545544551078164011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3517704242904272416874725 659569545544551078164011)
        ·
          refine ⟨989354318316826617246017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 659569545544551078164011 989354318316826617246017)
          ·
            refine ⟨742015738737619962934513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 989354318316826617246017 742015738737619962934513)
            ·
              refine ⟨556511804053214972200885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 742015738737619962934513 556511804053214972200885)
              ·
                refine ⟨52172981629988903643833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 556511804053214972200885 52172981629988903643833)
                ·
                  rfl

theorem cell20_342922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 2, 5].length) (baseStart_342922 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_342922 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_342922 prefixEnd_342922 := by exact prefixLift 342922
  have htrace : WordTrace (prefixWord ++ tailWord_342922) baseStart_342922 baseEnd_342922 := by
    simpa [prefixWord, tailWord_342922, baseEnd_342922] using wordTrace_append hprefix tailTrace_342922
  have hstable : (prefixWord ++ tailWord_342922).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_342922).length < 2 ^ (prefixWord ++ tailWord_342922).sum := by decide
  have hdescent : baseEnd_342922 < baseStart_342922 := by decide
  rcases family_descends (prefixWord ++ tailWord_342922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_342943 : List Nat := [1, 1, 2, 5, 2, 1, 2, 6]
def baseStart_342943 : Nat := 118140960795 + 342943 * 2 ^ 59
def prefixEnd_342943 : Nat := 4983230072969 + 3 ^ 40 * 342943 * 2
def baseEnd_342943 : Nat := 52176176620727990410471

theorem tailTrace_342943 : CollatzResearch.WordTrace tailWord_342943 prefixEnd_342943 52176176620727990410471 := by
  unfold tailWord_342943
  simp only [CollatzResearch.WordTrace]
  refine ⟨12508158796583555846513483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8338772531055703897675655 12508158796583555846513483)
  ·
    refine ⟨18762238194875333769770225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12508158796583555846513483 18762238194875333769770225)
    ·
      refine ⟨14071678646156500327327669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18762238194875333769770225 14071678646156500327327669)
      ·
        refine ⟨1319219873077171905686969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 14071678646156500327327669 1319219873077171905686969)
        ·
          refine ⟨989414904807878929265227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1319219873077171905686969 989414904807878929265227)
          ·
            refine ⟨1484122357211818393897841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 989414904807878929265227 1484122357211818393897841)
            ·
              refine ⟨1113091767908863795423381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1484122357211818393897841 1113091767908863795423381)
              ·
                refine ⟨52176176620727990410471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1113091767908863795423381 52176176620727990410471)
                ·
                  rfl

theorem cell20_342943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 2, 6].length) (baseStart_342943 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_342943 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_342943 prefixEnd_342943 := by exact prefixLift 342943
  have htrace : WordTrace (prefixWord ++ tailWord_342943) baseStart_342943 baseEnd_342943 := by
    simpa [prefixWord, tailWord_342943, baseEnd_342943] using wordTrace_append hprefix tailTrace_342943
  have hstable : (prefixWord ++ tailWord_342943).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_342943).length < 2 ^ (prefixWord ++ tailWord_342943).sum := by decide
  have hdescent : baseEnd_342943 < baseStart_342943 := by decide
  rcases family_descends (prefixWord ++ tailWord_342943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_342974 : List Nat := [4, 2, 1, 1, 1, 2, 2, 3, 4]
def baseStart_342974 : Nat := 118140960795 + 342974 * 2 ^ 59
def prefixEnd_342974 : Nat := 4983230072969 + 3 ^ 40 * 342974 * 2
def baseEnd_342974 : Nat := 156542679106885641197953

theorem tailTrace_342974 : CollatzResearch.WordTrace tailWord_342974 prefixEnd_342974 156542679106885641197953 := by
  unfold tailWord_342974
  simp only [CollatzResearch.WordTrace]
  refine ⟨1563661182433906017611497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8339526306314165427261317 1563661182433906017611497)
  ·
    refine ⟨1172745886825429513208623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1563661182433906017611497 1172745886825429513208623)
    ·
      refine ⟨1759118830238144269812935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1172745886825429513208623 1759118830238144269812935)
      ·
        refine ⟨2638678245357216404719403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1759118830238144269812935 2638678245357216404719403)
        ·
          refine ⟨3958017368035824607079105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2638678245357216404719403 3958017368035824607079105)
          ·
            refine ⟨2968513026026868455309329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3958017368035824607079105 2968513026026868455309329)
            ·
              refine ⟨2226384769520151341481997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2968513026026868455309329 2226384769520151341481997)
              ·
                refine ⟨834894288570056753055749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2226384769520151341481997 834894288570056753055749)
                ·
                  refine ⟨156542679106885641197953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 834894288570056753055749 156542679106885641197953)
                  ·
                    rfl

theorem cell20_342974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 2, 3, 4].length) (baseStart_342974 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_342974 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_342974 prefixEnd_342974 := by exact prefixLift 342974
  have htrace : WordTrace (prefixWord ++ tailWord_342974) baseStart_342974 baseEnd_342974 := by
    simpa [prefixWord, tailWord_342974, baseEnd_342974] using wordTrace_append hprefix tailTrace_342974
  have hstable : (prefixWord ++ tailWord_342974).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_342974).length < 2 ^ (prefixWord ++ tailWord_342974).sum := by decide
  have hdescent : baseEnd_342974 < baseStart_342974 := by decide
  rcases family_descends (prefixWord ++ tailWord_342974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_343050 : List Nat := [3, 1, 2, 2, 3, 1, 2, 2, 4]
def baseStart_343050 : Nat := 118140960795 + 343050 * 2 ^ 59
def prefixEnd_343050 : Nat := 4983230072969 + 3 ^ 40 * 343050 * 2
def baseEnd_343050 : Nat := 156577367577767154664309

theorem tailTrace_343050 : CollatzResearch.WordTrace tailWord_343050 prefixEnd_343050 156577367577767154664309 := by
  unfold tailWord_343050
  simp only [CollatzResearch.WordTrace]
  refine ⟨3128015351798978280164651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8341374271463942080439069 3128015351798978280164651)
  ·
    refine ⟨4692023027698467420246977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3128015351798978280164651 4692023027698467420246977)
    ·
      refine ⟨3519017270773850565185233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4692023027698467420246977 3519017270773850565185233)
      ·
        refine ⟨2639262953080387923888925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3519017270773850565185233 2639262953080387923888925)
        ·
          refine ⟨989723607405145471458347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2639262953080387923888925 989723607405145471458347)
          ·
            refine ⟨1484585411107718207187521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 989723607405145471458347 1484585411107718207187521)
            ·
              refine ⟨1113439058330788655390641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1484585411107718207187521 1113439058330788655390641)
              ·
                refine ⟨835079293748091491542981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1113439058330788655390641 835079293748091491542981)
                ·
                  refine ⟨156577367577767154664309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 835079293748091491542981 156577367577767154664309)
                  ·
                    rfl

theorem cell20_343050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 2, 2, 4].length) (baseStart_343050 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_343050 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_343050 prefixEnd_343050 := by exact prefixLift 343050
  have htrace : WordTrace (prefixWord ++ tailWord_343050) baseStart_343050 baseEnd_343050 := by
    simpa [prefixWord, tailWord_343050, baseEnd_343050] using wordTrace_append hprefix tailTrace_343050
  have hstable : (prefixWord ++ tailWord_343050).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_343050).length < 2 ^ (prefixWord ++ tailWord_343050).sum := by decide
  have hdescent : baseEnd_343050 < baseStart_343050 := by decide
  rcases family_descends (prefixWord ++ tailWord_343050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_343064 : List Nat := [2, 1, 2, 3, 2, 2, 1, 2, 5]
def baseStart_343064 : Nat := 118140960795 + 343064 * 2 ^ 59
def prefixEnd_343064 : Nat := 4983230072969 + 3 ^ 40 * 343064 * 2
def baseEnd_343064 : Nat := 156583757559245328197585

theorem tailTrace_343064 : CollatzResearch.WordTrace tailWord_343064 prefixEnd_343064 156583757559245328197585 := by
  unfold tailWord_343064
  simp only [CollatzResearch.WordTrace]
  refine ⟨6256286014572596755834123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8341714686096795674445497 6256286014572596755834123)
  ·
    refine ⟨9384429021858895133751185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6256286014572596755834123 9384429021858895133751185)
    ·
      refine ⟨7038321766394171350313389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9384429021858895133751185 7038321766394171350313389)
      ·
        refine ⟨2639370662397814256367521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7038321766394171350313389 2639370662397814256367521)
        ·
          refine ⟨1979527996798360692275641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2639370662397814256367521 1979527996798360692275641)
          ·
            refine ⟨1484645997598770519206731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1979527996798360692275641 1484645997598770519206731)
            ·
              refine ⟨2226968996398155778810097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1484645997598770519206731 2226968996398155778810097)
              ·
                refine ⟨1670226747298616834107573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2226968996398155778810097 1670226747298616834107573)
                ·
                  refine ⟨156583757559245328197585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1670226747298616834107573 156583757559245328197585)
                  ·
                    rfl

theorem cell20_343064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 1, 2, 5].length) (baseStart_343064 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_343064 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_343064 prefixEnd_343064 := by exact prefixLift 343064
  have htrace : WordTrace (prefixWord ++ tailWord_343064) baseStart_343064 baseEnd_343064 := by
    simpa [prefixWord, tailWord_343064, baseEnd_343064] using wordTrace_append hprefix tailTrace_343064
  have hstable : (prefixWord ++ tailWord_343064).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_343064).length < 2 ^ (prefixWord ++ tailWord_343064).sum := by decide
  have hdescent : baseEnd_343064 < baseStart_343064 := by decide
  rcases family_descends (prefixWord ++ tailWord_343064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_343109 : List Nat := [1, 3, 1, 1, 1, 3, 2, 4, 4]
def baseStart_343109 : Nat := 118140960795 + 343109 * 2 ^ 59
def prefixEnd_343109 : Nat := 4983230072969 + 3 ^ 40 * 343109 * 2
def baseEnd_343109 : Nat := 156604296785425171697401

theorem tailTrace_343109 : CollatzResearch.WordTrace tailWord_343109 prefixEnd_343109 156604296785425171697401 := by
  unfold tailWord_343109
  simp only [CollatzResearch.WordTrace]
  refine ⟨12514213313982166197056381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8342808875988110798037587 12514213313982166197056381)
  ·
    refine ⟨4692829992743312323896143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12514213313982166197056381 4692829992743312323896143)
    ·
      refine ⟨7039244989114968485844215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4692829992743312323896143 7039244989114968485844215)
      ·
        refine ⟨10558867483672452728766323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7039244989114968485844215 10558867483672452728766323)
        ·
          refine ⟨15838301225508679093149485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10558867483672452728766323 15838301225508679093149485)
          ·
            refine ⟨5939362959565754659931057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15838301225508679093149485 5939362959565754659931057)
            ·
              refine ⟨4454522219674315994948293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5939362959565754659931057 4454522219674315994948293)
              ·
                refine ⟨835222916188934249052805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4454522219674315994948293 835222916188934249052805)
                ·
                  refine ⟨156604296785425171697401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 835222916188934249052805 156604296785425171697401)
                  ·
                    rfl

theorem cell20_343109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 4, 4].length) (baseStart_343109 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_343109 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_343109 prefixEnd_343109 := by exact prefixLift 343109
  have htrace : WordTrace (prefixWord ++ tailWord_343109) baseStart_343109 baseEnd_343109 := by
    simpa [prefixWord, tailWord_343109, baseEnd_343109] using wordTrace_append hprefix tailTrace_343109
  have hstable : (prefixWord ++ tailWord_343109).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_343109).length < 2 ^ (prefixWord ++ tailWord_343109).sum := by decide
  have hdescent : baseEnd_343109 < baseStart_343109 := by decide
  rcases family_descends (prefixWord ++ tailWord_343109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_343133 : List Nat := [1, 4, 4, 1, 10]
def baseStart_343133 : Nat := 118140960795 + 343133 * 2 ^ 59
def prefixEnd_343133 : Nat := 4983230072969 + 3 ^ 40 * 343133 * 2
def baseEnd_343133 : Nat := 1933521617770219196263

theorem tailTrace_343133 : CollatzResearch.WordTrace tailWord_343133 prefixEnd_343133 1933521617770219196263 := by
  unfold tailWord_343133
  simp only [CollatzResearch.WordTrace]
  refine ⟨12515088665895218295930053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8343392443930145530620035 12515088665895218295930053)
  ·
    refine ⟨2346579124855353430486885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12515088665895218295930053 2346579124855353430486885)
    ·
      refine ⟨439983585910378768216291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2346579124855353430486885 439983585910378768216291)
      ·
        refine ⟨659975378865568152324437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 439983585910378768216291 659975378865568152324437)
        ·
          refine ⟨1933521617770219196263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 659975378865568152324437 1933521617770219196263)
          ·
            rfl

theorem cell20_343133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 10].length) (baseStart_343133 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_343133 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_343133 prefixEnd_343133 := by exact prefixLift 343133
  have htrace : WordTrace (prefixWord ++ tailWord_343133) baseStart_343133 baseEnd_343133 := by
    simpa [prefixWord, tailWord_343133, baseEnd_343133] using wordTrace_append hprefix tailTrace_343133
  have hstable : (prefixWord ++ tailWord_343133).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_343133).length < 2 ^ (prefixWord ++ tailWord_343133).sum := by decide
  have hdescent : baseEnd_343133 < baseStart_343133 := by decide
  rcases family_descends (prefixWord ++ tailWord_343133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_343143 : List Nat := [1, 1, 5, 1, 1, 4, 1, 4, 2]
def baseStart_343143 : Nat := 118140960795 + 343143 * 2 ^ 59
def prefixEnd_343143 : Nat := 4983230072969 + 3 ^ 40 * 343143 * 2
def baseEnd_343143 : Nat := 156619815311872164563929

theorem tailTrace_343143 : CollatzResearch.WordTrace tailWord_343143 prefixEnd_343143 156619815311872164563929 := by
  unfold tailWord_343143
  simp only [CollatzResearch.WordTrace]
  refine ⟨12515453395858990003794083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8343635597239326669196055 12515453395858990003794083)
  ·
    refine ⟨18773180093788485005691125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12515453395858990003794083 18773180093788485005691125)
    ·
      refine ⟨1759985633792670469283543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 18773180093788485005691125 1759985633792670469283543)
      ·
        refine ⟨2639978450689005703925315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1759985633792670469283543 2639978450689005703925315)
        ·
          refine ⟨3959967676033508555887973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2639978450689005703925315 3959967676033508555887973)
          ·
            refine ⟨742493939256282854228995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3959967676033508555887973 742493939256282854228995)
            ·
              refine ⟨1113740908884424281343493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 742493939256282854228995 1113740908884424281343493)
              ·
                refine ⟨208826420415829552751905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1113740908884424281343493 208826420415829552751905)
                ·
                  refine ⟨156619815311872164563929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 208826420415829552751905 156619815311872164563929)
                  ·
                    rfl

theorem cell20_343143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 1, 4, 2].length) (baseStart_343143 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_343143 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_343143 prefixEnd_343143 := by exact prefixLift 343143
  have htrace : WordTrace (prefixWord ++ tailWord_343143) baseStart_343143 baseEnd_343143 := by
    simpa [prefixWord, tailWord_343143, baseEnd_343143] using wordTrace_append hprefix tailTrace_343143
  have hstable : (prefixWord ++ tailWord_343143).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_343143).length < 2 ^ (prefixWord ++ tailWord_343143).sum := by decide
  have hdescent : baseEnd_343143 < baseStart_343143 := by decide
  rcases family_descends (prefixWord ++ tailWord_343143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_343150 : List Nat := [4, 1, 2, 2, 1, 4, 1, 5]
def baseStart_343150 : Nat := 118140960795 + 343150 * 2 ^ 59
def prefixEnd_343150 : Nat := 4983230072969 + 3 ^ 40 * 343150 * 2
def baseEnd_343150 : Nat := 52207670100870417110189

theorem tailTrace_343150 : CollatzResearch.WordTrace tailWord_343150 prefixEnd_343150 52207670100870417110189 := by
  unfold tailWord_343150
  simp only [CollatzResearch.WordTrace]
  refine ⟨1564463588354203774912363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8343805804555753466199269 1564463588354203774912363)
  ·
    refine ⟨2346695382531305662368545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1564463588354203774912363 2346695382531305662368545)
    ·
      refine ⟨1760021536898479246776409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2346695382531305662368545 1760021536898479246776409)
      ·
        refine ⟨1320016152673859435082307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1760021536898479246776409 1320016152673859435082307)
        ·
          refine ⟨1980024229010789152623461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1320016152673859435082307 1980024229010789152623461)
          ·
            refine ⟨371254542939522966116899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1980024229010789152623461 371254542939522966116899)
            ·
              refine ⟨556881814409284449175349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 371254542939522966116899 556881814409284449175349)
              ·
                refine ⟨52207670100870417110189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 556881814409284449175349 52207670100870417110189)
                ·
                  rfl

theorem cell20_343150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 4, 1, 5].length) (baseStart_343150 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_343150 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_343150 prefixEnd_343150 := by exact prefixLift 343150
  have htrace : WordTrace (prefixWord ++ tailWord_343150) baseStart_343150 baseEnd_343150 := by
    simpa [prefixWord, tailWord_343150, baseEnd_343150] using wordTrace_append hprefix tailTrace_343150
  have hstable : (prefixWord ++ tailWord_343150).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_343150).length < 2 ^ (prefixWord ++ tailWord_343150).sum := by decide
  have hdescent : baseEnd_343150 < baseStart_343150 := by decide
  rcases family_descends (prefixWord ++ tailWord_343150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_343171 : List Nat := [1, 1, 1, 3, 3, 2, 5, 4]
def baseStart_343171 : Nat := 118140960795 + 343171 * 2 ^ 59
def prefixEnd_343171 : Nat := 4983230072969 + 3 ^ 40 * 343171 * 2
def baseEnd_343171 : Nat := 52210865091609503876827

theorem tailTrace_343171 : CollatzResearch.WordTrace tailWord_343171 prefixEnd_343171 52210865091609503876827 := by
  unfold tailWord_343171
  simp only [CollatzResearch.WordTrace]
  refine ⟨12516474639757550785813367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8344316426505033857208911 12516474639757550785813367)
  ·
    refine ⟨18774711959636326178720051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12516474639757550785813367 18774711959636326178720051)
    ·
      refine ⟨28162067939454489268080077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18774711959636326178720051 28162067939454489268080077)
      ·
        refine ⟨10560775477295433475530029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28162067939454489268080077 10560775477295433475530029)
        ·
          refine ⟨3960290803985787553323761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10560775477295433475530029 3960290803985787553323761)
          ·
            refine ⟨2970218102989340664992821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3960290803985787553323761 2970218102989340664992821)
            ·
              refine ⟨278457947155250687343077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2970218102989340664992821 278457947155250687343077)
              ·
                refine ⟨52210865091609503876827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 278457947155250687343077 52210865091609503876827)
                ·
                  rfl

theorem cell20_343171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 5, 4].length) (baseStart_343171 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_343171 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_343171 prefixEnd_343171 := by exact prefixLift 343171
  have htrace : WordTrace (prefixWord ++ tailWord_343171) baseStart_343171 baseEnd_343171 := by
    simpa [prefixWord, tailWord_343171, baseEnd_343171] using wordTrace_append hprefix tailTrace_343171
  have hstable : (prefixWord ++ tailWord_343171).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_343171).length < 2 ^ (prefixWord ++ tailWord_343171).sum := by decide
  have hdescent : baseEnd_343171 < baseStart_343171 := by decide
  rcases family_descends (prefixWord ++ tailWord_343171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_343178 : List Nat := [3, 1, 2, 3, 1, 1, 2, 2, 5]
def baseStart_343178 : Nat := 118140960795 + 343178 * 2 ^ 59
def prefixEnd_343178 : Nat := 4983230072969 + 3 ^ 40 * 343178 * 2
def baseEnd_343178 : Nat := 156635790265567598397119

theorem tailTrace_343178 : CollatzResearch.WordTrace tailWord_343178 prefixEnd_343178 156635790265567598397119 := by
  unfold tailWord_343178
  simp only [CollatzResearch.WordTrace]
  refine ⟨3129182487683047745329547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8344486633821460654212125 3129182487683047745329547)
  ·
    refine ⟨4693773731524571617994321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3129182487683047745329547 4693773731524571617994321)
    ·
      refine ⟨3520330298643428713495741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4693773731524571617994321 3520330298643428713495741)
      ·
        refine ⟨1320123861991285767560903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3520330298643428713495741 1320123861991285767560903)
        ·
          refine ⟨1980185792986928651341355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1320123861991285767560903 1980185792986928651341355)
          ·
            refine ⟨2970278689480392977012033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1980185792986928651341355 2970278689480392977012033)
            ·
              refine ⟨2227709017110294732759025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2970278689480392977012033 2227709017110294732759025)
              ·
                refine ⟨1670781762832721049569269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2227709017110294732759025 1670781762832721049569269)
                ·
                  refine ⟨156635790265567598397119, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1670781762832721049569269 156635790265567598397119)
                  ·
                    rfl

theorem cell20_343178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 2, 2, 5].length) (baseStart_343178 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_343178 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_343178 prefixEnd_343178 := by exact prefixLift 343178
  have htrace : WordTrace (prefixWord ++ tailWord_343178) baseStart_343178 baseEnd_343178 := by
    simpa [prefixWord, tailWord_343178, baseEnd_343178] using wordTrace_append hprefix tailTrace_343178
  have hstable : (prefixWord ++ tailWord_343178).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_343178).length < 2 ^ (prefixWord ++ tailWord_343178).sum := by decide
  have hdescent : baseEnd_343178 < baseStart_343178 := by decide
  rcases family_descends (prefixWord ++ tailWord_343178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_343198 : List Nat := [4, 3, 1, 1, 2, 1, 2, 4, 2]
def baseStart_343198 : Nat := 118140960795 + 343198 * 2 ^ 59
def prefixEnd_343198 : Nat := 4983230072969 + 3 ^ 40 * 343198 * 2
def baseEnd_343198 : Nat := 156644918810536417730371

theorem tailTrace_343198 : CollatzResearch.WordTrace tailWord_343198 prefixEnd_343198 156644918810536417730371 := by
  unfold tailWord_343198
  simp only [CollatzResearch.WordTrace]
  refine ⟨1564682426332466799630781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8344972940439822931364165 1564682426332466799630781)
  ·
    refine ⟨586755909874675049861543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1564682426332466799630781 586755909874675049861543)
    ·
      refine ⟨880133864812012574792315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 586755909874675049861543 880133864812012574792315)
      ·
        refine ⟨1320200797218018862188473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 880133864812012574792315 1320200797218018862188473)
        ·
          refine ⟨990150597913514146641355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1320200797218018862188473 990150597913514146641355)
          ·
            refine ⟨1485225896870271219962033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 990150597913514146641355 1485225896870271219962033)
            ·
              refine ⟨1113919422652703414971525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1485225896870271219962033 1113919422652703414971525)
              ·
                refine ⟨208859891747381890307161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1113919422652703414971525 208859891747381890307161)
                ·
                  refine ⟨156644918810536417730371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 208859891747381890307161 156644918810536417730371)
                  ·
                    rfl

theorem cell20_343198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 2, 4, 2].length) (baseStart_343198 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_343198 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_343198 prefixEnd_343198 := by exact prefixLift 343198
  have htrace : WordTrace (prefixWord ++ tailWord_343198) baseStart_343198 baseEnd_343198 := by
    simpa [prefixWord, tailWord_343198, baseEnd_343198] using wordTrace_append hprefix tailTrace_343198
  have hstable : (prefixWord ++ tailWord_343198).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_343198).length < 2 ^ (prefixWord ++ tailWord_343198).sum := by decide
  have hdescent : baseEnd_343198 < baseStart_343198 := by decide
  rcases family_descends (prefixWord ++ tailWord_343198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_343223 : List Nat := [1, 1, 3, 1, 4, 1, 1, 4, 4]
def baseStart_343223 : Nat := 118140960795 + 343223 * 2 ^ 59
def prefixEnd_343223 : Nat := 4983230072969 + 3 ^ 40 * 343223 * 2
def baseEnd_343223 : Nat := 156656329491747441896935

theorem tailTrace_343223 : CollatzResearch.WordTrace tailWord_343223 prefixEnd_343223 156656329491747441896935 := by
  unfold tailWord_343223
  simp only [CollatzResearch.WordTrace]
  refine ⟨12518371235569163666706323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8345580823712775777804215 12518371235569163666706323)
  ·
    refine ⟨18777556853353745500059485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12518371235569163666706323 18777556853353745500059485)
    ·
      refine ⟨7041583820007654562522307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18777556853353745500059485 7041583820007654562522307)
      ·
        refine ⟨10562375730011481843783461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7041583820007654562522307 10562375730011481843783461)
        ·
          refine ⟨1980445449377152845709399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10562375730011481843783461 1980445449377152845709399)
          ·
            refine ⟨2970668174065729268564099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1980445449377152845709399 2970668174065729268564099)
            ·
              refine ⟨4456002261098593902846149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2970668174065729268564099 4456002261098593902846149)
              ·
                refine ⟨835500423955986356783653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4456002261098593902846149 835500423955986356783653)
                ·
                  refine ⟨156656329491747441896935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 835500423955986356783653 156656329491747441896935)
                  ·
                    rfl

theorem cell20_343223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 4, 4].length) (baseStart_343223 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_343223 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_343223 prefixEnd_343223 := by exact prefixLift 343223
  have htrace : WordTrace (prefixWord ++ tailWord_343223) baseStart_343223 baseEnd_343223 := by
    simpa [prefixWord, tailWord_343223, baseEnd_343223] using wordTrace_append hprefix tailTrace_343223
  have hstable : (prefixWord ++ tailWord_343223).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_343223).length < 2 ^ (prefixWord ++ tailWord_343223).sum := by decide
  have hdescent : baseEnd_343223 < baseStart_343223 := by decide
  rcases family_descends (prefixWord ++ tailWord_343223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_343233 : List Nat := [1, 2, 6, 1, 1, 1, 1, 2, 5]
def baseStart_343233 : Nat := 118140960795 + 343233 * 2 ^ 59
def prefixEnd_343233 : Nat := 4983230072969 + 3 ^ 40 * 343233 * 2
def baseEnd_343233 : Nat := 156660893764231851563561

theorem tailTrace_343233 : CollatzResearch.WordTrace tailWord_343233 prefixEnd_343233 156660893764231851563561 := by
  unfold tailWord_343233
  simp only [CollatzResearch.WordTrace]
  refine ⟨12518735965532935374570353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8345823977021956916380235 12518735965532935374570353)
  ·
    refine ⟨9389051974149701530927765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12518735965532935374570353 9389051974149701530927765)
    ·
      refine ⟨440111811288267259262239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 9389051974149701530927765 440111811288267259262239)
      ·
        refine ⟨660167716932400888893359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 440111811288267259262239 660167716932400888893359)
        ·
          refine ⟨990251575398601333340039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 660167716932400888893359 990251575398601333340039)
          ·
            refine ⟨1485377363097902000010059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 990251575398601333340039 1485377363097902000010059)
            ·
              refine ⟨2228066044646853000015089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1485377363097902000010059 2228066044646853000015089)
              ·
                refine ⟨1671049533485139750011317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2228066044646853000015089 1671049533485139750011317)
                ·
                  refine ⟨156660893764231851563561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1671049533485139750011317 156660893764231851563561)
                  ·
                    rfl

theorem cell20_343233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 1, 2, 5].length) (baseStart_343233 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_343233 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_343233 prefixEnd_343233 := by exact prefixLift 343233
  have htrace : WordTrace (prefixWord ++ tailWord_343233) baseStart_343233 baseEnd_343233 := by
    simpa [prefixWord, tailWord_343233, baseEnd_343233] using wordTrace_append hprefix tailTrace_343233
  have hstable : (prefixWord ++ tailWord_343233).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_343233).length < 2 ^ (prefixWord ++ tailWord_343233).sum := by decide
  have hdescent : baseEnd_343233 < baseStart_343233 := by decide
  rcases family_descends (prefixWord ++ tailWord_343233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_343268 : List Nat := [2, 3, 1, 1, 1, 2, 3, 7]
def baseStart_343268 : Nat := 118140960795 + 343268 * 2 ^ 59
def prefixEnd_343268 : Nat := 4983230072969 + 3 ^ 40 * 343268 * 2
def baseEnd_343268 : Nat := 52225622905975761798917

theorem tailTrace_343268 : CollatzResearch.WordTrace tailWord_343268 prefixEnd_343268 52225622905975761798917 := by
  unfold tailWord_343268
  simp only [CollatzResearch.WordTrace]
  refine ⟨6260006260203068176047229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8346675013604090901396305 6260006260203068176047229)
  ·
    refine ⟨2347502347576150566017711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6260006260203068176047229 2347502347576150566017711)
    ·
      refine ⟨3521253521364225849026567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2347502347576150566017711 3521253521364225849026567)
      ·
        refine ⟨5281880282046338773539851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3521253521364225849026567 5281880282046338773539851)
        ·
          refine ⟨7922820423069508160309777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5281880282046338773539851 7922820423069508160309777)
          ·
            refine ⟨5942115317302131120232333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7922820423069508160309777 5942115317302131120232333)
            ·
              refine ⟨2228293243988299170087125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5942115317302131120232333 2228293243988299170087125)
              ·
                refine ⟨52225622905975761798917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2228293243988299170087125 52225622905975761798917)
                ·
                  rfl

theorem cell20_343268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 3, 7].length) (baseStart_343268 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_343268 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_343268 prefixEnd_343268 := by exact prefixLift 343268
  have htrace : WordTrace (prefixWord ++ tailWord_343268) baseStart_343268 baseEnd_343268 := by
    simpa [prefixWord, tailWord_343268, baseEnd_343268] using wordTrace_append hprefix tailTrace_343268
  have hstable : (prefixWord ++ tailWord_343268).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_343268).length < 2 ^ (prefixWord ++ tailWord_343268).sum := by decide
  have hdescent : baseEnd_343268 < baseStart_343268 := by decide
  rcases family_descends (prefixWord ++ tailWord_343268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_343361 : List Nat := [1, 2, 5, 2, 1, 2, 7]
def baseStart_343361 : Nat := 118140960795 + 343361 * 2 ^ 59
def prefixEnd_343361 : Nat := 4983230072969 + 3 ^ 40 * 343361 * 2
def baseEnd_343361 : Nat := 17413257383559143921819

theorem tailTrace_343361 : CollatzResearch.WordTrace tailWord_343361 prefixEnd_343361 17413257383559143921819 := by
  unfold tailWord_343361
  simp only [CollatzResearch.WordTrace]
  refine ⟨12523404509069213235229937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8348936339379475490153291 12523404509069213235229937)
  ·
    refine ⟨9392553381801909926422453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12523404509069213235229937 9392553381801909926422453)
    ·
      refine ⟨880551879543929055602105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 9392553381801909926422453 880551879543929055602105)
      ·
        refine ⟨660413909657946791701579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 880551879543929055602105 660413909657946791701579)
        ·
          refine ⟨990620864486920187552369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 660413909657946791701579 990620864486920187552369)
          ·
            refine ⟨742965648365190140664277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 990620864486920187552369 742965648365190140664277)
            ·
              refine ⟨17413257383559143921819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 742965648365190140664277 17413257383559143921819)
              ·
                rfl

theorem cell20_343361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 7].length) (baseStart_343361 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_343361 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_343361 prefixEnd_343361 := by exact prefixLift 343361
  have htrace : WordTrace (prefixWord ++ tailWord_343361) baseStart_343361 baseEnd_343361 := by
    simpa [prefixWord, tailWord_343361, baseEnd_343361] using wordTrace_append hprefix tailTrace_343361
  have hstable : (prefixWord ++ tailWord_343361).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_343361).length < 2 ^ (prefixWord ++ tailWord_343361).sum := by decide
  have hdescent : baseEnd_343361 < baseStart_343361 := by decide
  rcases family_descends (prefixWord ++ tailWord_343361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_343364 : List Nat := [2, 3, 4, 1, 1, 1, 3, 2, 3]
def baseStart_343364 : Nat := 118140960795 + 343364 * 2 ^ 59
def prefixEnd_343364 : Nat := 4983230072969 + 3 ^ 40 * 343364 * 2
def baseEnd_343364 : Nat := 156720685733777618196359

theorem tailTrace_343364 : CollatzResearch.WordTrace tailWord_343364 prefixEnd_343364 156720685733777618196359 := by
  unfold tailWord_343364
  simp only [CollatzResearch.WordTrace]
  refine ⟨6261756964029172373794573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8349009285372229831726097 6261756964029172373794573)
  ·
    refine ⟨2348158861510939640172965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6261756964029172373794573 2348158861510939640172965)
    ·
      refine ⟨440279786533301182532431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2348158861510939640172965 440279786533301182532431)
      ·
        refine ⟨660419679799951773798647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 440279786533301182532431 660419679799951773798647)
        ·
          refine ⟨990629519699927660697971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 660419679799951773798647 990629519699927660697971)
          ·
            refine ⟨1485944279549891491046957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 990629519699927660697971 1485944279549891491046957)
            ·
              refine ⟨557229104831209309142609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1485944279549891491046957 557229104831209309142609)
              ·
                refine ⟨417921828623406981856957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 557229104831209309142609 417921828623406981856957)
                ·
                  refine ⟨156720685733777618196359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 417921828623406981856957 156720685733777618196359)
                  ·
                    rfl

theorem cell20_343364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 3, 2, 3].length) (baseStart_343364 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_343364 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_343364 prefixEnd_343364 := by exact prefixLift 343364
  have htrace : WordTrace (prefixWord ++ tailWord_343364) baseStart_343364 baseEnd_343364 := by
    simpa [prefixWord, tailWord_343364, baseEnd_343364] using wordTrace_append hprefix tailTrace_343364
  have hstable : (prefixWord ++ tailWord_343364).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_343364).length < 2 ^ (prefixWord ++ tailWord_343364).sum := by decide
  have hdescent : baseEnd_343364 < baseStart_343364 := by decide
  rcases family_descends (prefixWord ++ tailWord_343364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_343399 : List Nat := [1, 1, 5, 1, 4, 1, 1, 6]
def baseStart_343399 : Nat := 118140960795 + 343399 * 2 ^ 59
def prefixEnd_343399 : Nat := 4983230072969 + 3 ^ 40 * 343399 * 2
def baseEnd_343399 : Nat := 52245553562491017343183

theorem tailTrace_343399 : CollatzResearch.WordTrace tailWord_343399 prefixEnd_343399 52245553562491017343183 := by
  unfold tailWord_343399
  simp only [CollatzResearch.WordTrace]
  refine ⟨12524790482931545725113251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8349860321954363816742167 12524790482931545725113251)
  ·
    refine ⟨18787185724397318587669877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12524790482931545725113251 18787185724397318587669877)
    ·
      refine ⟨1761298661662248617594051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 18787185724397318587669877 1761298661662248617594051)
      ·
        refine ⟨2641947992493372926391077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1761298661662248617594051 2641947992493372926391077)
        ·
          refine ⟨495365248592507423698327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2641947992493372926391077 495365248592507423698327)
          ·
            refine ⟨743047872888761135547491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 495365248592507423698327 743047872888761135547491)
            ·
              refine ⟨1114571809333141703321237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 743047872888761135547491 1114571809333141703321237)
              ·
                refine ⟨52245553562491017343183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1114571809333141703321237 52245553562491017343183)
                ·
                  rfl

theorem cell20_343399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 1, 6].length) (baseStart_343399 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_343399 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_343399 prefixEnd_343399 := by exact prefixLift 343399
  have htrace : WordTrace (prefixWord ++ tailWord_343399) baseStart_343399 baseEnd_343399 := by
    simpa [prefixWord, tailWord_343399, baseEnd_343399] using wordTrace_append hprefix tailTrace_343399
  have hstable : (prefixWord ++ tailWord_343399).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_343399).length < 2 ^ (prefixWord ++ tailWord_343399).sum := by decide
  have hdescent : baseEnd_343399 < baseStart_343399 := by decide
  rcases family_descends (prefixWord ++ tailWord_343399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_343422 : List Nat := [4, 2, 3, 2, 1, 1, 3, 2, 2]
def baseStart_343422 : Nat := 118140960795 + 343422 * 2 ^ 59
def prefixEnd_343422 : Nat := 4983230072969 + 3 ^ 40 * 343422 * 2
def baseEnd_343422 : Nat := 156747158514187194262789

theorem tailTrace_343422 : CollatzResearch.WordTrace tailWord_343422 prefixEnd_343422 156747158514187194262789 := by
  unfold tailWord_343422
  simp only [CollatzResearch.WordTrace]
  refine ⟨1565703670231027581650065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8350419574565480435467013 1565703670231027581650065)
  ·
    refine ⟨1174277752673270686237549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1565703670231027581650065 1174277752673270686237549)
    ·
      refine ⟨440354157252476507339081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1174277752673270686237549 440354157252476507339081)
      ·
        refine ⟨330265617939357380504311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 440354157252476507339081 330265617939357380504311)
        ·
          refine ⟨495398426909036070756467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 330265617939357380504311 495398426909036070756467)
          ·
            refine ⟨743097640363554106134701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 495398426909036070756467 743097640363554106134701)
            ·
              refine ⟨278661615136332789800513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 743097640363554106134701 278661615136332789800513)
              ·
                refine ⟨208996211352249592350385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 278661615136332789800513 208996211352249592350385)
                ·
                  refine ⟨156747158514187194262789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 208996211352249592350385 156747158514187194262789)
                  ·
                    rfl

theorem cell20_343422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 3, 2, 2].length) (baseStart_343422 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_343422 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_343422 prefixEnd_343422 := by exact prefixLift 343422
  have htrace : WordTrace (prefixWord ++ tailWord_343422) baseStart_343422 baseEnd_343422 := by
    simpa [prefixWord, tailWord_343422, baseEnd_343422] using wordTrace_append hprefix tailTrace_343422
  have hstable : (prefixWord ++ tailWord_343422).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_343422).length < 2 ^ (prefixWord ++ tailWord_343422).sum := by decide
  have hdescent : baseEnd_343422 < baseStart_343422 := by decide
  rcases family_descends (prefixWord ++ tailWord_343422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_343426 : List Nat := [3, 4, 2, 1, 1, 3, 1, 1, 4]
def baseStart_343426 : Nat := 118140960795 + 343426 * 2 ^ 59
def prefixEnd_343426 : Nat := 4983230072969 + 3 ^ 40 * 343426 * 2
def baseEnd_343426 : Nat := 156748984223180958129439

theorem tailTrace_343426 : CollatzResearch.WordTrace tailWord_343426 prefixEnd_343426 156748984223180958129439 := by
  unfold tailWord_343426
  simp only [CollatzResearch.WordTrace]
  refine ⟨3131443813458432334086533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8350516835889152890897421 3131443813458432334086533)
  ·
    refine ⟨587145715023456062641225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3131443813458432334086533 587145715023456062641225)
    ·
      refine ⟨440359286267592046980919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 587145715023456062641225 440359286267592046980919)
      ·
        refine ⟨660538929401388070471379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 440359286267592046980919 660538929401388070471379)
        ·
          refine ⟨990808394102082105707069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 660538929401388070471379 990808394102082105707069)
          ·
            refine ⟨371553147788280789640151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 990808394102082105707069 371553147788280789640151)
            ·
              refine ⟨557329721682421184460227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 371553147788280789640151 557329721682421184460227)
              ·
                refine ⟨835994582523631776690341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 557329721682421184460227 835994582523631776690341)
                ·
                  refine ⟨156748984223180958129439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 835994582523631776690341 156748984223180958129439)
                  ·
                    rfl

theorem cell20_343426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 3, 1, 1, 4].length) (baseStart_343426 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_343426 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_343426 prefixEnd_343426 := by exact prefixLift 343426
  have htrace : WordTrace (prefixWord ++ tailWord_343426) baseStart_343426 baseEnd_343426 := by
    simpa [prefixWord, tailWord_343426, baseEnd_343426] using wordTrace_append hprefix tailTrace_343426
  have hstable : (prefixWord ++ tailWord_343426).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_343426).length < 2 ^ (prefixWord ++ tailWord_343426).sum := by decide
  have hdescent : baseEnd_343426 < baseStart_343426 := by decide
  rcases family_descends (prefixWord ++ tailWord_343426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_343472 : List Nat := [2, 1, 1, 1, 2, 1, 1, 3, 8]
def baseStart_343472 : Nat := 118140960795 + 343472 * 2 ^ 59
def prefixEnd_343472 : Nat := 4983230072969 + 3 ^ 40 * 343472 * 2
def baseEnd_343472 : Nat := 156769979876609242595917

theorem tailTrace_343472 : CollatzResearch.WordTrace tailWord_343472 prefixEnd_343472 156769979876609242595917 := by
  unfold tailWord_343472
  simp only [CollatzResearch.WordTrace]
  refine ⟨6263726505833539596260335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8351635341111386128347113 6263726505833539596260335)
  ·
    refine ⟨9395589758750309394390503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6263726505833539596260335 9395589758750309394390503)
    ·
      refine ⟨14093384638125464091585755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9395589758750309394390503 14093384638125464091585755)
      ·
        refine ⟨21140076957188196137378633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14093384638125464091585755 21140076957188196137378633)
        ·
          refine ⟨15855057717891147103033975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21140076957188196137378633 15855057717891147103033975)
          ·
            refine ⟨23782586576836720654550963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15855057717891147103033975 23782586576836720654550963)
            ·
              refine ⟨35673879865255080981826445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23782586576836720654550963 35673879865255080981826445)
              ·
                refine ⟨13377704949470655368184917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35673879865255080981826445 13377704949470655368184917)
                ·
                  refine ⟨156769979876609242595917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 13377704949470655368184917 156769979876609242595917)
                  ·
                    rfl

theorem cell20_343472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 3, 8].length) (baseStart_343472 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_343472 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_343472 prefixEnd_343472 := by exact prefixLift 343472
  have htrace : WordTrace (prefixWord ++ tailWord_343472) baseStart_343472 baseEnd_343472 := by
    simpa [prefixWord, tailWord_343472, baseEnd_343472] using wordTrace_append hprefix tailTrace_343472
  have hstable : (prefixWord ++ tailWord_343472).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_343472).length < 2 ^ (prefixWord ++ tailWord_343472).sum := by decide
  have hdescent : baseEnd_343472 < baseStart_343472 := by decide
  rcases family_descends (prefixWord ++ tailWord_343472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_343481 : List Nat := [1, 2, 1, 4, 5, 1, 2, 2, 2]
def baseStart_343481 : Nat := 118140960795 + 343481 * 2 ^ 59
def prefixEnd_343481 : Nat := 4983230072969 + 3 ^ 40 * 343481 * 2
def baseEnd_343481 : Nat := 156774087721845211295881

theorem tailTrace_343481 : CollatzResearch.WordTrace tailWord_343481 prefixEnd_343481 156774087721845211295881 := by
  unfold tailWord_343481
  simp only [CollatzResearch.WordTrace]
  refine ⟨12527781268634473729598297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8351854179089649153065531 12527781268634473729598297)
  ·
    refine ⟨9395835951475855297198723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12527781268634473729598297 9395835951475855297198723)
    ·
      refine ⟨14093753927213782945798085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9395835951475855297198723 14093753927213782945798085)
      ·
        refine ⟨2642578861352584302337141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14093753927213782945798085 2642578861352584302337141)
        ·
          refine ⟨247741768251804778344107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2642578861352584302337141 247741768251804778344107)
          ·
            refine ⟨371612652377707167516161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 247741768251804778344107 371612652377707167516161)
            ·
              refine ⟨278709489283280375637121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 371612652377707167516161 278709489283280375637121)
              ·
                refine ⟨209032116962460281727841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 278709489283280375637121 209032116962460281727841)
                ·
                  refine ⟨156774087721845211295881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 209032116962460281727841 156774087721845211295881)
                  ·
                    rfl

theorem cell20_343481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 5, 1, 2, 2, 2].length) (baseStart_343481 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_343481 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_343481 prefixEnd_343481 := by exact prefixLift 343481
  have htrace : WordTrace (prefixWord ++ tailWord_343481) baseStart_343481 baseEnd_343481 := by
    simpa [prefixWord, tailWord_343481, baseEnd_343481] using wordTrace_append hprefix tailTrace_343481
  have hstable : (prefixWord ++ tailWord_343481).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_343481).length < 2 ^ (prefixWord ++ tailWord_343481).sum := by decide
  have hdescent : baseEnd_343481 < baseStart_343481 := by decide
  rcases family_descends (prefixWord ++ tailWord_343481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_343492 : List Nat := [2, 3, 3, 2, 1, 3, 1, 5]
def baseStart_343492 : Nat := 118140960795 + 343492 * 2 ^ 59
def prefixEnd_343492 : Nat := 4983230072969 + 3 ^ 40 * 343492 * 2
def baseEnd_343492 : Nat := 52259702807192687309723

theorem tailTrace_343492 : CollatzResearch.WordTrace tailWord_343492 prefixEnd_343492 52259702807192687309723 := by
  unfold tailWord_343492
  simp only [CollatzResearch.WordTrace]
  refine ⟨6264091235797311304124365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8352121647729748405499153 6264091235797311304124365)
  ·
    refine ⟨2349034213423991739046637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6264091235797311304124365 2349034213423991739046637)
    ·
      refine ⟨880887830033996902142489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2349034213423991739046637 880887830033996902142489)
      ·
        refine ⟨660665872525497676606867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 880887830033996902142489 660665872525497676606867)
        ·
          refine ⟨990998808788246514910301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 660665872525497676606867 990998808788246514910301)
          ·
            refine ⟨371624553295592443091363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 990998808788246514910301 371624553295592443091363)
            ·
              refine ⟨557436829943388664637045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 371624553295592443091363 557436829943388664637045)
              ·
                refine ⟨52259702807192687309723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 557436829943388664637045 52259702807192687309723)
                ·
                  rfl

theorem cell20_343492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 3, 1, 5].length) (baseStart_343492 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_343492 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_343492 prefixEnd_343492 := by exact prefixLift 343492
  have htrace : WordTrace (prefixWord ++ tailWord_343492) baseStart_343492 baseEnd_343492 := by
    simpa [prefixWord, tailWord_343492, baseEnd_343492] using wordTrace_append hprefix tailTrace_343492
  have hstable : (prefixWord ++ tailWord_343492).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_343492).length < 2 ^ (prefixWord ++ tailWord_343492).sum := by decide
  have hdescent : baseEnd_343492 < baseStart_343492 := by decide
  rcases family_descends (prefixWord ++ tailWord_343492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_343513 : List Nat := [1, 2, 1, 2, 4, 3, 3, 4]
def baseStart_343513 : Nat := 118140960795 + 343513 * 2 ^ 59
def prefixEnd_343513 : Nat := 4983230072969 + 3 ^ 40 * 343513 * 2
def baseEnd_343513 : Nat := 52262897797931774076361

theorem tailTrace_343513 : CollatzResearch.WordTrace tailWord_343513 prefixEnd_343513 52262897797931774076361 := by
  unfold tailWord_343513
  simp only [CollatzResearch.WordTrace]
  refine ⟨12528948404518543194763193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8352632269679028796508795 12528948404518543194763193)
  ·
    refine ⟨9396711303388907396072395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12528948404518543194763193 9396711303388907396072395)
    ·
      refine ⟨14095066955083361094108593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9396711303388907396072395 14095066955083361094108593)
      ·
        refine ⟨10571300216312520820581445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14095066955083361094108593 10571300216312520820581445)
        ·
          refine ⟨1982118790558597653859021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10571300216312520820581445 1982118790558597653859021)
          ·
            refine ⟨743294546459474120197133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1982118790558597653859021 743294546459474120197133)
            ·
              refine ⟨278735454922302795073925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 743294546459474120197133 278735454922302795073925)
              ·
                refine ⟨52262897797931774076361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 278735454922302795073925 52262897797931774076361)
                ·
                  rfl

theorem cell20_343513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 3, 4].length) (baseStart_343513 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_343513 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_343513 prefixEnd_343513 := by exact prefixLift 343513
  have htrace : WordTrace (prefixWord ++ tailWord_343513) baseStart_343513 baseEnd_343513 := by
    simpa [prefixWord, tailWord_343513, baseEnd_343513] using wordTrace_append hprefix tailTrace_343513
  have hstable : (prefixWord ++ tailWord_343513).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_343513).length < 2 ^ (prefixWord ++ tailWord_343513).sum := by decide
  have hdescent : baseEnd_343513 < baseStart_343513 := by decide
  rcases family_descends (prefixWord ++ tailWord_343513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_343523 : List Nat := [1, 1, 1, 6, 2, 2, 2, 3, 2]
def baseStart_343523 : Nat := 118140960795 + 343523 * 2 ^ 59
def prefixEnd_343523 : Nat := 4983230072969 + 3 ^ 40 * 343523 * 2
def baseEnd_343523 : Nat := 156793257666279731895709

theorem tailTrace_343523 : CollatzResearch.WordTrace tailWord_343523 prefixEnd_343523 156793257666279731895709 := by
  unfold tailWord_343523
  simp only [CollatzResearch.WordTrace]
  refine ⟨12529313134482314902627223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8352875422988209935084815 12529313134482314902627223)
  ·
    refine ⟨18793969701723472353940835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12529313134482314902627223 18793969701723472353940835)
    ·
      refine ⟨28190954552585208530911253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18793969701723472353940835 28190954552585208530911253)
      ·
        refine ⟨1321450994652431649886465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 28190954552585208530911253 1321450994652431649886465)
        ·
          refine ⟨991088245989323737414849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1321450994652431649886465 991088245989323737414849)
          ·
            refine ⟨743316184491992803061137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 991088245989323737414849 743316184491992803061137)
            ·
              refine ⟨557487138368994602295853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 743316184491992803061137 557487138368994602295853)
              ·
                refine ⟨209057676888372975860945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 557487138368994602295853 209057676888372975860945)
                ·
                  refine ⟨156793257666279731895709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 209057676888372975860945 156793257666279731895709)
                  ·
                    rfl

theorem cell20_343523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 2, 3, 2].length) (baseStart_343523 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_343523 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_343523 prefixEnd_343523 := by exact prefixLift 343523
  have htrace : WordTrace (prefixWord ++ tailWord_343523) baseStart_343523 baseEnd_343523 := by
    simpa [prefixWord, tailWord_343523, baseEnd_343523] using wordTrace_append hprefix tailTrace_343523
  have hstable : (prefixWord ++ tailWord_343523).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_343523).length < 2 ^ (prefixWord ++ tailWord_343523).sum := by decide
  have hdescent : baseEnd_343523 < baseStart_343523 := by decide
  rcases family_descends (prefixWord ++ tailWord_343523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_343533 : List Nat := [1, 5, 1, 3, 3, 1, 1, 2, 3]
def baseStart_343533 : Nat := 118140960795 + 343533 * 2 ^ 59
def prefixEnd_343533 : Nat := 4983230072969 + 3 ^ 40 * 343533 * 2
def baseEnd_343533 : Nat := 156797821938764141562335

theorem tailTrace_343533 : CollatzResearch.WordTrace tailWord_343533 prefixEnd_343533 156797821938764141562335 := by
  unfold tailWord_343533
  simp only [CollatzResearch.WordTrace]
  refine ⟨12529677864446086610491253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8353118576297391073660835 12529677864446086610491253)
  ·
    refine ⟨1174657299791820619733555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 12529677864446086610491253 1174657299791820619733555)
    ·
      refine ⟨1761985949687730929600333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1174657299791820619733555 1761985949687730929600333)
      ·
        refine ⟨660744731132899098600125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1761985949687730929600333 660744731132899098600125)
        ·
          refine ⟨247779274174837161975047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 660744731132899098600125 247779274174837161975047)
          ·
            refine ⟨371668911262255742962571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 247779274174837161975047 371668911262255742962571)
            ·
              refine ⟨557503366893383614443857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 371668911262255742962571 557503366893383614443857)
              ·
                refine ⟨418127525170037710832893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 557503366893383614443857 418127525170037710832893)
                ·
                  refine ⟨156797821938764141562335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 418127525170037710832893 156797821938764141562335)
                  ·
                    rfl

theorem cell20_343533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 3, 1, 1, 2, 3].length) (baseStart_343533 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_343533 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_343533 prefixEnd_343533 := by exact prefixLift 343533
  have htrace : WordTrace (prefixWord ++ tailWord_343533) baseStart_343533 baseEnd_343533 := by
    simpa [prefixWord, tailWord_343533, baseEnd_343533] using wordTrace_append hprefix tailTrace_343533
  have hstable : (prefixWord ++ tailWord_343533).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_343533).length < 2 ^ (prefixWord ++ tailWord_343533).sum := by decide
  have hdescent : baseEnd_343533 < baseStart_343533 := by decide
  rcases family_descends (prefixWord ++ tailWord_343533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_343534 : List Nat := [4, 1, 2, 1, 2, 1, 9]
def baseStart_343534 : Nat := 118140960795 + 343534 * 2 ^ 59
def prefixEnd_343534 : Nat := 4983230072969 + 3 ^ 40 * 343534 * 2
def baseEnd_343534 : Nat := 17422030929556953614333

theorem tailTrace_343534 : CollatzResearch.WordTrace tailWord_343534 prefixEnd_343534 17422030929556953614333 := by
  unfold tailWord_343534
  simp only [CollatzResearch.WordTrace]
  refine ⟨1566214292180307972659707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8353142891628309187518437 1566214292180307972659707)
  ·
    refine ⟨2349321438270461958989561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1566214292180307972659707 2349321438270461958989561)
    ·
      refine ⟨1761991078702846469242171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2349321438270461958989561 1761991078702846469242171)
      ·
        refine ⟨2642986618054269703863257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1761991078702846469242171 2642986618054269703863257)
        ·
          refine ⟨1982239963540702277897443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2642986618054269703863257 1982239963540702277897443)
          ·
            refine ⟨2973359945311053416846165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1982239963540702277897443 2973359945311053416846165)
            ·
              refine ⟨17422030929556953614333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2973359945311053416846165 17422030929556953614333)
              ·
                rfl

theorem cell20_343534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 9].length) (baseStart_343534 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_343534 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_343534 prefixEnd_343534 := by exact prefixLift 343534
  have htrace : WordTrace (prefixWord ++ tailWord_343534) baseStart_343534 baseEnd_343534 := by
    simpa [prefixWord, tailWord_343534, baseEnd_343534] using wordTrace_append hprefix tailTrace_343534
  have hstable : (prefixWord ++ tailWord_343534).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_343534).length < 2 ^ (prefixWord ++ tailWord_343534).sum := by decide
  have hdescent : baseEnd_343534 < baseStart_343534 := by decide
  rcases family_descends (prefixWord ++ tailWord_343534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_343537 : List Nat := [1, 2, 2, 2, 3, 4, 1, 2, 3]
def baseStart_343537 : Nat := 118140960795 + 343537 * 2 ^ 59
def prefixEnd_343537 : Nat := 4983230072969 + 3 ^ 40 * 343537 * 2
def baseEnd_343537 : Nat := 156799647647757905428985

theorem tailTrace_343537 : CollatzResearch.WordTrace tailWord_343537 prefixEnd_343537 156799647647757905428985 := by
  unfold tailWord_343537
  simp only [CollatzResearch.WordTrace]
  refine ⟨12529823756431595293636865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8353215837621063529091243 12529823756431595293636865)
  ·
    refine ⟨9397367817323696470227649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12529823756431595293636865 9397367817323696470227649)
    ·
      refine ⟨7048025862992772352670737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9397367817323696470227649 7048025862992772352670737)
      ·
        refine ⟨5286019397244579264503053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7048025862992772352670737 5286019397244579264503053)
        ·
          refine ⟨1982257273966717224188645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5286019397244579264503053 1982257273966717224188645)
          ·
            refine ⟨371673238868759479535371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1982257273966717224188645 371673238868759479535371)
            ·
              refine ⟨557509858303139219303057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 371673238868759479535371 557509858303139219303057)
              ·
                refine ⟨418132393727354414477293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 557509858303139219303057 418132393727354414477293)
                ·
                  refine ⟨156799647647757905428985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 418132393727354414477293 156799647647757905428985)
                  ·
                    rfl

theorem cell20_343537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 4, 1, 2, 3].length) (baseStart_343537 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_343537 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_343537 prefixEnd_343537 := by exact prefixLift 343537
  have htrace : WordTrace (prefixWord ++ tailWord_343537) baseStart_343537 baseEnd_343537 := by
    simpa [prefixWord, tailWord_343537, baseEnd_343537] using wordTrace_append hprefix tailTrace_343537
  have hstable : (prefixWord ++ tailWord_343537).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_343537).length < 2 ^ (prefixWord ++ tailWord_343537).sum := by decide
  have hdescent : baseEnd_343537 < baseStart_343537 := by decide
  rcases family_descends (prefixWord ++ tailWord_343537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_343544 : List Nat := [2, 1, 2, 1, 1, 5, 2, 4, 2]
def baseStart_343544 : Nat := 118140960795 + 343544 * 2 ^ 59
def prefixEnd_343544 : Nat := 4983230072969 + 3 ^ 40 * 343544 * 2
def baseEnd_343544 : Nat := 156802842638496992195623

theorem tailTrace_343544 : CollatzResearch.WordTrace tailWord_343544 prefixEnd_343544 156802842638496992195623 := by
  unfold tailWord_343544
  simp only [CollatzResearch.WordTrace]
  refine ⟨6265039533703117744570843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8353386044937490326094457 6265039533703117744570843)
  ·
    refine ⟨9397559300554676616856265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6265039533703117744570843 9397559300554676616856265)
    ·
      refine ⟨7048169475416007462642199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9397559300554676616856265 7048169475416007462642199)
      ·
        refine ⟨10572254213124011193963299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7048169475416007462642199 10572254213124011193963299)
        ·
          refine ⟨15858381319686016790944949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10572254213124011193963299 15858381319686016790944949)
          ·
            refine ⟨1486723248720564074151089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 15858381319686016790944949 1486723248720564074151089)
            ·
              refine ⟨1115042436540423055613317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1486723248720564074151089 1115042436540423055613317)
              ·
                refine ⟨209070456851329322927497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1115042436540423055613317 209070456851329322927497)
                ·
                  refine ⟨156802842638496992195623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 209070456851329322927497 156802842638496992195623)
                  ·
                    rfl

theorem cell20_343544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 2, 4, 2].length) (baseStart_343544 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_343544 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_343544 prefixEnd_343544 := by exact prefixLift 343544
  have htrace : WordTrace (prefixWord ++ tailWord_343544) baseStart_343544 baseEnd_343544 := by
    simpa [prefixWord, tailWord_343544, baseEnd_343544] using wordTrace_append hprefix tailTrace_343544
  have hstable : (prefixWord ++ tailWord_343544).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_343544).length < 2 ^ (prefixWord ++ tailWord_343544).sum := by decide
  have hdescent : baseEnd_343544 < baseStart_343544 := by decide
  rcases family_descends (prefixWord ++ tailWord_343544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_343603 : List Nat := [1, 1, 1, 2, 4, 3, 3, 1, 4]
def baseStart_343603 : Nat := 118140960795 + 343603 * 2 ^ 59
def prefixEnd_343603 : Nat := 4983230072969 + 3 ^ 40 * 343603 * 2
def baseEnd_343603 : Nat := 156829771846155009228715

theorem tailTrace_343603 : CollatzResearch.WordTrace tailWord_343603 prefixEnd_343603 156829771846155009228715 := by
  unfold tailWord_343603
  simp only [CollatzResearch.WordTrace]
  refine ⟨12532230974192488565539463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8354820649461659043692975 12532230974192488565539463)
  ·
    refine ⟨18798346461288732848309195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12532230974192488565539463 18798346461288732848309195)
    ·
      refine ⟨28197519691933099272463793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18798346461288732848309195 28197519691933099272463793)
      ·
        refine ⟨21148139768949824454347845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28197519691933099272463793 21148139768949824454347845)
        ·
          refine ⟨3965276206678092085190221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21148139768949824454347845 3965276206678092085190221)
          ·
            refine ⟨1486978577504284531946333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3965276206678092085190221 1486978577504284531946333)
            ·
              refine ⟨557616966564106699479875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1486978577504284531946333 557616966564106699479875)
              ·
                refine ⟨836425449846160049219813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 557616966564106699479875 836425449846160049219813)
                ·
                  refine ⟨156829771846155009228715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 836425449846160049219813 156829771846155009228715)
                  ·
                    rfl

theorem cell20_343603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 3, 1, 4].length) (baseStart_343603 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_343603 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_343603 prefixEnd_343603 := by exact prefixLift 343603
  have htrace : WordTrace (prefixWord ++ tailWord_343603) baseStart_343603 baseEnd_343603 := by
    simpa [prefixWord, tailWord_343603, baseEnd_343603] using wordTrace_append hprefix tailTrace_343603
  have hstable : (prefixWord ++ tailWord_343603).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_343603).length < 2 ^ (prefixWord ++ tailWord_343603).sum := by decide
  have hdescent : baseEnd_343603 < baseStart_343603 := by decide
  rcases family_descends (prefixWord ++ tailWord_343603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_343606 : List Nat := [5, 1, 2, 1, 3, 1, 2, 5]
def baseStart_343606 : Nat := 118140960795 + 343606 * 2 ^ 59
def prefixEnd_343606 : Nat := 4983230072969 + 3 ^ 40 * 343606 * 2
def baseEnd_343606 : Nat := 52277047042633444042901

theorem tailTrace_343606 : CollatzResearch.WordTrace tailWord_343606 prefixEnd_343606 52277047042633444042901 := by
  unfold tailWord_343606
  simp only [CollatzResearch.WordTrace]
  refine ⟨783271274573851254868667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 8354893595454413385265781 783271274573851254868667)
  ·
    refine ⟨1174906911860776882303001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 783271274573851254868667 1174906911860776882303001)
    ·
      refine ⟨881180183895582661727251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1174906911860776882303001 881180183895582661727251)
      ·
        refine ⟨1321770275843373992590877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 881180183895582661727251 1321770275843373992590877)
        ·
          refine ⟨495663853441265247221579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1321770275843373992590877 495663853441265247221579)
          ·
            refine ⟨743495780161897870832369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 495663853441265247221579 743495780161897870832369)
            ·
              refine ⟨557621835121423403124277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 743495780161897870832369 557621835121423403124277)
              ·
                refine ⟨52277047042633444042901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 557621835121423403124277 52277047042633444042901)
                ·
                  rfl

theorem cell20_343606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 2, 5].length) (baseStart_343606 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_343606 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_343606 prefixEnd_343606 := by exact prefixLift 343606
  have htrace : WordTrace (prefixWord ++ tailWord_343606) baseStart_343606 baseEnd_343606 := by
    simpa [prefixWord, tailWord_343606, baseEnd_343606] using wordTrace_append hprefix tailTrace_343606
  have hstable : (prefixWord ++ tailWord_343606).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_343606).length < 2 ^ (prefixWord ++ tailWord_343606).sum := by decide
  have hdescent : baseEnd_343606 < baseStart_343606 := by decide
  rcases family_descends (prefixWord ++ tailWord_343606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_343610 : List Nat := [3, 1, 1, 1, 3, 2, 4, 5]
def baseStart_343610 : Nat := 118140960795 + 343610 * 2 ^ 59
def prefixEnd_343610 : Nat := 4983230072969 + 3 ^ 40 * 343610 * 2
def baseEnd_343610 : Nat := 52277655612298031998451

theorem tailTrace_343610 : CollatzResearch.WordTrace tailWord_343610 prefixEnd_343610 52277655612298031998451 := by
  unfold tailWord_343610
  simp only [CollatzResearch.WordTrace]
  refine ⟨3133121571291782190261071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8354990856778085840696189 3133121571291782190261071)
  ·
    refine ⟨4699682356937673285391607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3133121571291782190261071 4699682356937673285391607)
    ·
      refine ⟨7049523535406509928087411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4699682356937673285391607 7049523535406509928087411)
      ·
        refine ⟨10574285303109764892131117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7049523535406509928087411 10574285303109764892131117)
        ·
          refine ⟨3965356988666161834549169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10574285303109764892131117 3965356988666161834549169)
          ·
            refine ⟨2974017741499621375911877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3965356988666161834549169 2974017741499621375911877)
            ·
              refine ⟨557628326531179007983477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2974017741499621375911877 557628326531179007983477)
              ·
                refine ⟨52277655612298031998451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 557628326531179007983477 52277655612298031998451)
                ·
                  rfl

theorem cell20_343610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 4, 5].length) (baseStart_343610 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_343610 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_343610 prefixEnd_343610 := by exact prefixLift 343610
  have htrace : WordTrace (prefixWord ++ tailWord_343610) baseStart_343610 baseEnd_343610 := by
    simpa [prefixWord, tailWord_343610, baseEnd_343610] using wordTrace_append hprefix tailTrace_343610
  have hstable : (prefixWord ++ tailWord_343610).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_343610).length < 2 ^ (prefixWord ++ tailWord_343610).sum := by decide
  have hdescent : baseEnd_343610 < baseStart_343610 := by decide
  rcases family_descends (prefixWord ++ tailWord_343610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_343613 : List Nat := [1, 4, 1, 3, 3, 1, 1, 3, 3]
def baseStart_343613 : Nat := 118140960795 + 343613 * 2 ^ 59
def prefixEnd_343613 : Nat := 4983230072969 + 3 ^ 40 * 343613 * 2
def baseEnd_343613 : Nat := 156834336118639418895341

theorem tailTrace_343613 : CollatzResearch.WordTrace tailWord_343613 prefixEnd_343613 156834336118639418895341 := by
  unfold tailWord_343613
  simp only [CollatzResearch.WordTrace]
  refine ⟨12532595704156260273403493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8355063802770840182268995 12532595704156260273403493)
  ·
    refine ⟨2349861694529298801263155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12532595704156260273403493 2349861694529298801263155)
    ·
      refine ⟨3524792541793948201894733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2349861694529298801263155 3524792541793948201894733)
      ·
        refine ⟨1321797203172730575710525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3524792541793948201894733 1321797203172730575710525)
        ·
          refine ⟨495673951189773965891447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1321797203172730575710525 495673951189773965891447)
          ·
            refine ⟨743510926784660948837171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 495673951189773965891447 743510926784660948837171)
            ·
              refine ⟨1115266390176991423255757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 743510926784660948837171 1115266390176991423255757)
              ·
                refine ⟨418224896316371783720909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1115266390176991423255757 418224896316371783720909)
                ·
                  refine ⟨156834336118639418895341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 418224896316371783720909 156834336118639418895341)
                  ·
                    rfl

theorem cell20_343613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 1, 3, 3].length) (baseStart_343613 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_343613 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_343613 prefixEnd_343613 := by exact prefixLift 343613
  have htrace : WordTrace (prefixWord ++ tailWord_343613) baseStart_343613 baseEnd_343613 := by
    simpa [prefixWord, tailWord_343613, baseEnd_343613] using wordTrace_append hprefix tailTrace_343613
  have hstable : (prefixWord ++ tailWord_343613).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_343613).length < 2 ^ (prefixWord ++ tailWord_343613).sum := by decide
  have hdescent : baseEnd_343613 < baseStart_343613 := by decide
  rcases family_descends (prefixWord ++ tailWord_343613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_343655 : List Nat := [1, 1, 5, 1, 1, 1, 2, 3, 5]
def baseStart_343655 : Nat := 118140960795 + 343655 * 2 ^ 59
def prefixEnd_343655 : Nat := 4983230072969 + 3 ^ 40 * 343655 * 2
def baseEnd_343655 : Nat := 156853506063073939495169

theorem tailTrace_343655 : CollatzResearch.WordTrace tailWord_343655 prefixEnd_343655 156853506063073939495169 := by
  unfold tailWord_343655
  simp only [CollatzResearch.WordTrace]
  refine ⟨12534127570004101446432419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8356085046669400964288279 12534127570004101446432419)
  ·
    refine ⟨18801191355006152169648629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12534127570004101446432419 18801191355006152169648629)
    ·
      refine ⟨1762611689531826765904559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 18801191355006152169648629 1762611689531826765904559)
      ·
        refine ⟨2643917534297740148856839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1762611689531826765904559 2643917534297740148856839)
        ·
          refine ⟨3965876301446610223285259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2643917534297740148856839 3965876301446610223285259)
          ·
            refine ⟨5948814452169915334927889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3965876301446610223285259 5948814452169915334927889)
            ·
              refine ⟨4461610839127436501195917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5948814452169915334927889 4461610839127436501195917)
              ·
                refine ⟨1673104064672788687948469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4461610839127436501195917 1673104064672788687948469)
                ·
                  refine ⟨156853506063073939495169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1673104064672788687948469 156853506063073939495169)
                  ·
                    rfl

theorem cell20_343655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 3, 5].length) (baseStart_343655 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_343655 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_343655 prefixEnd_343655 := by exact prefixLift 343655
  have htrace : WordTrace (prefixWord ++ tailWord_343655) baseStart_343655 baseEnd_343655 := by
    simpa [prefixWord, tailWord_343655, baseEnd_343655] using wordTrace_append hprefix tailTrace_343655
  have hstable : (prefixWord ++ tailWord_343655).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_343655).length < 2 ^ (prefixWord ++ tailWord_343655).sum := by decide
  have hdescent : baseEnd_343655 < baseStart_343655 := by decide
  rcases family_descends (prefixWord ++ tailWord_343655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_343762 : List Nat := [3, 2, 2, 2, 2, 1, 8]
def baseStart_343762 : Nat := 118140960795 + 343762 * 2 ^ 59
def prefixEnd_343762 : Nat := 4983230072969 + 3 ^ 40 * 343762 * 2
def baseEnd_343762 : Nat := 17433593753184124769785

theorem tailTrace_343762 : CollatzResearch.WordTrace tailWord_343762 prefixEnd_343762 17433593753184124769785 := by
  unfold tailWord_343762
  simp only [CollatzResearch.WordTrace]
  refine ⟨3134507545154114680144385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8358686787077639147051693 3134507545154114680144385)
  ·
    refine ⟨2350880658865586010108289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3134507545154114680144385 2350880658865586010108289)
    ·
      refine ⟨1763160494149189507581217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2350880658865586010108289 1763160494149189507581217)
      ·
        refine ⟨1322370370611892130685913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1763160494149189507581217 1322370370611892130685913)
        ·
          refine ⟨991777777958919098014435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1322370370611892130685913 991777777958919098014435)
          ·
            refine ⟨1487666666938378647021653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 991777777958919098014435 1487666666938378647021653)
            ·
              refine ⟨17433593753184124769785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1487666666938378647021653 17433593753184124769785)
              ·
                rfl

theorem cell20_343762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 8].length) (baseStart_343762 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_343762 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_343762 prefixEnd_343762 := by exact prefixLift 343762
  have htrace : WordTrace (prefixWord ++ tailWord_343762) baseStart_343762 baseEnd_343762 := by
    simpa [prefixWord, tailWord_343762, baseEnd_343762] using wordTrace_append hprefix tailTrace_343762
  have hstable : (prefixWord ++ tailWord_343762).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_343762).length < 2 ^ (prefixWord ++ tailWord_343762).sum := by decide
  have hdescent : baseEnd_343762 < baseStart_343762 := by decide
  rcases family_descends (prefixWord ++ tailWord_343762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_343769 : List Nat := [1, 2, 1, 2, 3, 3, 2, 1, 5]
def baseStart_343769 : Nat := 118140960795 + 343769 * 2 ^ 59
def prefixEnd_343769 : Nat := 4983230072969 + 3 ^ 40 * 343769 * 2
def baseEnd_343769 : Nat := 156905538769396209694703

theorem tailTrace_343769 : CollatzResearch.WordTrace tailWord_343769 prefixEnd_343769 156905538769396209694703 := by
  unfold tailWord_343769
  simp only [CollatzResearch.WordTrace]
  refine ⟨12538285491591098916082361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8358856994394065944054907 12538285491591098916082361)
  ·
    refine ⟨9403714118693324187061771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12538285491591098916082361 9403714118693324187061771)
    ·
      refine ⟨14105571178039986280592657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9403714118693324187061771 14105571178039986280592657)
      ·
        refine ⟨10579178383529989710444493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14105571178039986280592657 10579178383529989710444493)
        ·
          refine ⟨3967191893823746141416685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10579178383529989710444493 3967191893823746141416685)
          ·
            refine ⟨1487696960183904803031257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3967191893823746141416685 1487696960183904803031257)
            ·
              refine ⟨1115772720137928602273443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1487696960183904803031257 1115772720137928602273443)
              ·
                refine ⟨1673659080206892903410165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1115772720137928602273443 1673659080206892903410165)
                ·
                  refine ⟨156905538769396209694703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1673659080206892903410165 156905538769396209694703)
                  ·
                    rfl

theorem cell20_343769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 2, 1, 5].length) (baseStart_343769 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_343769 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_343769 prefixEnd_343769 := by exact prefixLift 343769
  have htrace : WordTrace (prefixWord ++ tailWord_343769) baseStart_343769 baseEnd_343769 := by
    simpa [prefixWord, tailWord_343769, baseEnd_343769] using wordTrace_append hprefix tailTrace_343769
  have hstable : (prefixWord ++ tailWord_343769).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_343769).length < 2 ^ (prefixWord ++ tailWord_343769).sum := by decide
  have hdescent : baseEnd_343769 < baseStart_343769 := by decide
  rcases family_descends (prefixWord ++ tailWord_343769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_343779 : List Nat := [1, 1, 1, 7, 2, 1, 2, 5]
def baseStart_343779 : Nat := 118140960795 + 343779 * 2 ^ 59
def prefixEnd_343779 : Nat := 4983230072969 + 3 ^ 40 * 343779 * 2
def baseEnd_343779 : Nat := 52303367680626873120443

theorem tailTrace_343779 : CollatzResearch.WordTrace tailWord_343779 prefixEnd_343779 52303367680626873120443 := by
  unfold tailWord_343779
  simp only [CollatzResearch.WordTrace]
  refine ⟨12538650221554870623946391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8359100147703247082630927 12538650221554870623946391)
  ·
    refine ⟨18807975332332305935919587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12538650221554870623946391 18807975332332305935919587)
    ·
      refine ⟨28211962998498458903879381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18807975332332305935919587 28211962998498458903879381)
      ·
        refine ⟨661217882777307630559673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 28211962998498458903879381 661217882777307630559673)
        ·
          refine ⟨495913412082980722919755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 661217882777307630559673 495913412082980722919755)
          ·
            refine ⟨743870118124471084379633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 495913412082980722919755 743870118124471084379633)
            ·
              refine ⟨557902588593353313284725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 743870118124471084379633 557902588593353313284725)
              ·
                refine ⟨52303367680626873120443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 557902588593353313284725 52303367680626873120443)
                ·
                  rfl

theorem cell20_343779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 2, 5].length) (baseStart_343779 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_343779 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_343779 prefixEnd_343779 := by exact prefixLift 343779
  have htrace : WordTrace (prefixWord ++ tailWord_343779) baseStart_343779 baseEnd_343779 := by
    simpa [prefixWord, tailWord_343779, baseEnd_343779] using wordTrace_append hprefix tailTrace_343779
  have hstable : (prefixWord ++ tailWord_343779).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_343779).length < 2 ^ (prefixWord ++ tailWord_343779).sum := by decide
  have hdescent : baseEnd_343779 < baseStart_343779 := by decide
  rcases family_descends (prefixWord ++ tailWord_343779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_343796 : List Nat := [2, 6, 1, 1, 1, 1, 2, 6]
def baseStart_343796 : Nat := 118140960795 + 343796 * 2 ^ 59
def prefixEnd_343796 : Nat := 4983230072969 + 3 ^ 40 * 343796 * 2
def baseEnd_343796 : Nat := 52305954101701371931531

theorem tailTrace_343796 : CollatzResearch.WordTrace tailWord_343796 prefixEnd_343796 52305954101701371931531 := by
  unfold tailWord_343796
  simp only [CollatzResearch.WordTrace]
  refine ⟨6269635131246641263657621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8359513508328855018210161 6269635131246641263657621)
  ·
    refine ⟨293889146777186309233951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 6269635131246641263657621 293889146777186309233951)
    ·
      refine ⟨440833720165779463850927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 293889146777186309233951 440833720165779463850927)
      ·
        refine ⟨661250580248669195776391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 440833720165779463850927 661250580248669195776391)
        ·
          refine ⟨991875870373003793664587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 661250580248669195776391 991875870373003793664587)
          ·
            refine ⟨1487813805559505690496881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 991875870373003793664587 1487813805559505690496881)
            ·
              refine ⟨1115860354169629267872661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1487813805559505690496881 1115860354169629267872661)
              ·
                refine ⟨52305954101701371931531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1115860354169629267872661 52305954101701371931531)
                ·
                  rfl

theorem cell20_343796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 2, 6].length) (baseStart_343796 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_343796 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_343796 prefixEnd_343796 := by exact prefixLift 343796
  have htrace : WordTrace (prefixWord ++ tailWord_343796) baseStart_343796 baseEnd_343796 := by
    simpa [prefixWord, tailWord_343796, baseEnd_343796] using wordTrace_append hprefix tailTrace_343796
  have hstable : (prefixWord ++ tailWord_343796).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_343796).length < 2 ^ (prefixWord ++ tailWord_343796).sum := by decide
  have hdescent : baseEnd_343796 < baseStart_343796 := by decide
  rcases family_descends (prefixWord ++ tailWord_343796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_343852 : List Nat := [2, 2, 1, 1, 1, 5, 1, 1, 6]
def baseStart_343852 : Nat := 118140960795 + 343852 * 2 ^ 59
def prefixEnd_343852 : Nat := 4983230072969 + 3 ^ 40 * 343852 * 2
def baseEnd_343852 : Nat := 156943422231016809927697

theorem tailTrace_343852 : CollatzResearch.WordTrace tailWord_343852 prefixEnd_343852 156943422231016809927697 := by
  unfold tailWord_343852
  simp only [CollatzResearch.WordTrace]
  refine ⟨6270656375145202045676905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8360875166860269394235873 6270656375145202045676905)
  ·
    refine ⟨4702992281358901534257679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6270656375145202045676905 4702992281358901534257679)
    ·
      refine ⟨7054488422038352301386519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4702992281358901534257679 7054488422038352301386519)
      ·
        refine ⟨10581732633057528452079779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7054488422038352301386519 10581732633057528452079779)
        ·
          refine ⟨15872598949586292678119669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10581732633057528452079779 15872598949586292678119669)
          ·
            refine ⟨1488056151523714938573719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 15872598949586292678119669 1488056151523714938573719)
            ·
              refine ⟨2232084227285572407860579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1488056151523714938573719 2232084227285572407860579)
              ·
                refine ⟨3348126340928358611790869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2232084227285572407860579 3348126340928358611790869)
                ·
                  refine ⟨156943422231016809927697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3348126340928358611790869 156943422231016809927697)
                  ·
                    rfl

theorem cell20_343852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 6].length) (baseStart_343852 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_343852 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_343852 prefixEnd_343852 := by exact prefixLift 343852
  have htrace : WordTrace (prefixWord ++ tailWord_343852) baseStart_343852 baseEnd_343852 := by
    simpa [prefixWord, tailWord_343852, baseEnd_343852] using wordTrace_append hprefix tailTrace_343852
  have hstable : (prefixWord ++ tailWord_343852).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_343852).length < 2 ^ (prefixWord ++ tailWord_343852).sum := by decide
  have hdescent : baseEnd_343852 < baseStart_343852 := by decide
  rcases family_descends (prefixWord ++ tailWord_343852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_343897 : List Nat := [1, 2, 1, 2, 2, 3, 2, 7]
def baseStart_343897 : Nat := 118140960795 + 343897 * 2 ^ 59
def prefixEnd_343897 : Nat := 4983230072969 + 3 ^ 40 * 343897 * 2
def baseEnd_343897 : Nat := 52321320485732217809171

theorem tailTrace_343897 : CollatzResearch.WordTrace tailWord_343897 prefixEnd_343897 52321320485732217809171 := by
  unfold tailWord_343897
  simp only [CollatzResearch.WordTrace]
  refine ⟨12542954035127376776741945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8361969356751584517827963 12542954035127376776741945)
  ·
    refine ⟨9407215526345532582556459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12542954035127376776741945 9407215526345532582556459)
    ·
      refine ⟨14110823289518298873834689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9407215526345532582556459 14110823289518298873834689)
      ·
        refine ⟨10583117467138724155376017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14110823289518298873834689 10583117467138724155376017)
        ·
          refine ⟨7937338100354043116532013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10583117467138724155376017 7937338100354043116532013)
          ·
            refine ⟨2976501787632766168699505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7937338100354043116532013 2976501787632766168699505)
            ·
              refine ⟨2232376340724574626524629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2976501787632766168699505 2232376340724574626524629)
              ·
                refine ⟨52321320485732217809171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2232376340724574626524629 52321320485732217809171)
                ·
                  rfl

theorem cell20_343897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 2, 7].length) (baseStart_343897 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_343897 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_343897 prefixEnd_343897 := by exact prefixLift 343897
  have htrace : WordTrace (prefixWord ++ tailWord_343897) baseStart_343897 baseEnd_343897 := by
    simpa [prefixWord, tailWord_343897, baseEnd_343897] using wordTrace_append hprefix tailTrace_343897
  have hstable : (prefixWord ++ tailWord_343897).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_343897).length < 2 ^ (prefixWord ++ tailWord_343897).sum := by decide
  have hdescent : baseEnd_343897 < baseStart_343897 := by decide
  rcases family_descends (prefixWord ++ tailWord_343897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_343983 : List Nat := [1, 1, 2, 1, 2, 2, 4, 5, 2]
def baseStart_343983 : Nat := 118140960795 + 343983 * 2 ^ 59
def prefixEnd_343983 : Nat := 4983230072969 + 3 ^ 40 * 343983 * 2
def baseEnd_343983 : Nat := 157003214200562576560495

theorem tailTrace_343983 : CollatzResearch.WordTrace tailWord_343983 prefixEnd_343983 157003214200562576560495 := by
  unfold tailWord_343983
  simp only [CollatzResearch.WordTrace]
  refine ⟨12546090712815813464372603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8364060475210542309581735 12546090712815813464372603)
  ·
    refine ⟨18819136069223720196558905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12546090712815813464372603 18819136069223720196558905)
    ·
      refine ⟨14114352051917790147419179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18819136069223720196558905 14114352051917790147419179)
      ·
        refine ⟨21171528077876685221128769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14114352051917790147419179 21171528077876685221128769)
        ·
          refine ⟨15878646058407513915846577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21171528077876685221128769 15878646058407513915846577)
          ·
            refine ⟨11908984543805635436884933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15878646058407513915846577 11908984543805635436884933)
            ·
              refine ⟨2232934601963556644415925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11908984543805635436884933 2232934601963556644415925)
              ·
                refine ⟨209337618934083435413993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2232934601963556644415925 209337618934083435413993)
                ·
                  refine ⟨157003214200562576560495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 209337618934083435413993 157003214200562576560495)
                  ·
                    rfl

theorem cell20_343983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 4, 5, 2].length) (baseStart_343983 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_343983 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_343983 prefixEnd_343983 := by exact prefixLift 343983
  have htrace : WordTrace (prefixWord ++ tailWord_343983) baseStart_343983 baseEnd_343983 := by
    simpa [prefixWord, tailWord_343983, baseEnd_343983] using wordTrace_append hprefix tailTrace_343983
  have hstable : (prefixWord ++ tailWord_343983).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_343983).length < 2 ^ (prefixWord ++ tailWord_343983).sum := by decide
  have hdescent : baseEnd_343983 < baseStart_343983 := by decide
  rcases family_descends (prefixWord ++ tailWord_343983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_344021 : List Nat := [1, 3, 2, 3, 2, 2, 1, 2, 4]
def baseStart_344021 : Nat := 118140960795 + 344021 * 2 ^ 59
def prefixEnd_344021 : Nat := 4983230072969 + 3 ^ 40 * 344021 * 2
def baseEnd_344021 : Nat := 157020558436003333293673

theorem tailTrace_344021 : CollatzResearch.WordTrace tailWord_344021 prefixEnd_344021 157020558436003333293673 := by
  unfold tailWord_344021
  simp only [CollatzResearch.WordTrace]
  refine ⟨12547476686678145954255917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8364984457785430636170611 12547476686678145954255917)
  ·
    refine ⟨4705303757504304732845969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12547476686678145954255917 4705303757504304732845969)
    ·
      refine ⟨3528977818128228549634477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4705303757504304732845969 3528977818128228549634477)
      ·
        refine ⟨1323366681798085706112929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3528977818128228549634477 1323366681798085706112929)
        ·
          refine ⟨992525011348564279584697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1323366681798085706112929 992525011348564279584697)
          ·
            refine ⟨744393758511423209688523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 992525011348564279584697 744393758511423209688523)
            ·
              refine ⟨1116590637767134814532785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 744393758511423209688523 1116590637767134814532785)
              ·
                refine ⟨837442978325351110899589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1116590637767134814532785 837442978325351110899589)
                ·
                  refine ⟨157020558436003333293673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 837442978325351110899589 157020558436003333293673)
                  ·
                    rfl

theorem cell20_344021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 1, 2, 4].length) (baseStart_344021 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_344021 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_344021 prefixEnd_344021 := by exact prefixLift 344021
  have htrace : WordTrace (prefixWord ++ tailWord_344021) baseStart_344021 baseEnd_344021 := by
    simpa [prefixWord, tailWord_344021, baseEnd_344021] using wordTrace_append hprefix tailTrace_344021
  have hstable : (prefixWord ++ tailWord_344021).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_344021).length < 2 ^ (prefixWord ++ tailWord_344021).sum := by decide
  have hdescent : baseEnd_344021 < baseStart_344021 := by decide
  rcases family_descends (prefixWord ++ tailWord_344021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_344034 : List Nat := [3, 3, 3, 1, 2, 1, 2, 3, 2]
def baseStart_344034 : Nat := 118140960795 + 344034 * 2 ^ 59
def prefixEnd_344034 : Nat := 4983230072969 + 3 ^ 40 * 344034 * 2
def baseEnd_344034 : Nat := 157026491990233065860287

theorem tailTrace_344034 : CollatzResearch.WordTrace tailWord_344034 prefixEnd_344034 157026491990233065860287 := by
  unfold tailWord_344034
  simp only [CollatzResearch.WordTrace]
  refine ⟨3136987708907762293619789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8365300557087366116319437 3136987708907762293619789)
  ·
    refine ⟨1176370390840410860107421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3136987708907762293619789 1176370390840410860107421)
    ·
      refine ⟨441138896565154072540283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1176370390840410860107421 441138896565154072540283)
      ·
        refine ⟨661708344847731108810425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 441138896565154072540283 661708344847731108810425)
        ·
          refine ⟨496281258635798331607819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 661708344847731108810425 496281258635798331607819)
          ·
            refine ⟨744421887953697497411729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 496281258635798331607819 744421887953697497411729)
            ·
              refine ⟨558316415965273123058797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 744421887953697497411729 558316415965273123058797)
              ·
                refine ⟨209368655986977421147049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 558316415965273123058797 209368655986977421147049)
                ·
                  refine ⟨157026491990233065860287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 209368655986977421147049 157026491990233065860287)
                  ·
                    rfl

theorem cell20_344034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 2, 3, 2].length) (baseStart_344034 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_344034 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_344034 prefixEnd_344034 := by exact prefixLift 344034
  have htrace : WordTrace (prefixWord ++ tailWord_344034) baseStart_344034 baseEnd_344034 := by
    simpa [prefixWord, tailWord_344034, baseEnd_344034] using wordTrace_append hprefix tailTrace_344034
  have hstable : (prefixWord ++ tailWord_344034).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_344034).length < 2 ^ (prefixWord ++ tailWord_344034).sum := by decide
  have hdescent : baseEnd_344034 < baseStart_344034 := by decide
  rcases family_descends (prefixWord ++ tailWord_344034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_344042 : List Nat := [3, 1, 3, 1, 2, 1, 1, 2, 6]
def baseStart_344042 : Nat := 118140960795 + 344042 * 2 ^ 59
def prefixEnd_344042 : Nat := 4983230072969 + 3 ^ 40 * 344042 * 2
def baseEnd_344042 : Nat := 157030143408220593593587

theorem tailTrace_344042 : CollatzResearch.WordTrace tailWord_344042 prefixEnd_344042 157030143408220593593587 := by
  unfold tailWord_344042
  simp only [CollatzResearch.WordTrace]
  refine ⟨3137060654900516635192595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8365495079734711027180253 3137060654900516635192595)
  ·
    refine ⟨4705590982350774952788893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3137060654900516635192595 4705590982350774952788893)
    ·
      refine ⟨1764596618381540607295835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4705590982350774952788893 1764596618381540607295835)
      ·
        refine ⟨2646894927572310910943753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1764596618381540607295835 2646894927572310910943753)
        ·
          refine ⟨1985171195679233183207815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2646894927572310910943753 1985171195679233183207815)
          ·
            refine ⟨2977756793518849774811723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1985171195679233183207815 2977756793518849774811723)
            ·
              refine ⟨4466635190278274662217585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2977756793518849774811723 4466635190278274662217585)
              ·
                refine ⟨3349976392708705996663189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4466635190278274662217585 3349976392708705996663189)
                ·
                  refine ⟨157030143408220593593587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3349976392708705996663189 157030143408220593593587)
                  ·
                    rfl

theorem cell20_344042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 2, 6].length) (baseStart_344042 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_344042 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_344042 prefixEnd_344042 := by exact prefixLift 344042
  have htrace : WordTrace (prefixWord ++ tailWord_344042) baseStart_344042 baseEnd_344042 := by
    simpa [prefixWord, tailWord_344042, baseEnd_344042] using wordTrace_append hprefix tailTrace_344042
  have hstable : (prefixWord ++ tailWord_344042).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_344042).length < 2 ^ (prefixWord ++ tailWord_344042).sum := by decide
  have hdescent : baseEnd_344042 < baseStart_344042 := by decide
  rcases family_descends (prefixWord ++ tailWord_344042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_344045 : List Nat := [1, 5, 1, 4, 1, 1, 7]
def baseStart_344045 : Nat := 118140960795 + 344045 * 2 ^ 59
def prefixEnd_344045 : Nat := 4983230072969 + 3 ^ 40 * 344045 * 2
def baseEnd_344045 : Nat := 17447945854440657388175

theorem tailTrace_344045 : CollatzResearch.WordTrace tailWord_344045 prefixEnd_344045 17447945854440657388175 := by
  unfold tailWord_344045
  simp only [CollatzResearch.WordTrace]
  refine ⟨12548352038591198053129589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8365568025727465368753059 12548352038591198053129589)
  ·
    refine ⟨1176408003617924817480899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 12548352038591198053129589 1176408003617924817480899)
    ·
      refine ⟨1764612005426887226221349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1176408003617924817480899 1764612005426887226221349)
      ·
        refine ⟨330864751017541354916503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1764612005426887226221349 330864751017541354916503)
        ·
          refine ⟨496297126526312032374755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 330864751017541354916503 496297126526312032374755)
          ·
            refine ⟨744445689789468048562133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 496297126526312032374755 744445689789468048562133)
            ·
              refine ⟨17447945854440657388175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 744445689789468048562133 17447945854440657388175)
              ·
                rfl

theorem cell20_344045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 7].length) (baseStart_344045 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_344045 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_344045 prefixEnd_344045 := by exact prefixLift 344045
  have htrace : WordTrace (prefixWord ++ tailWord_344045) baseStart_344045 baseEnd_344045 := by
    simpa [prefixWord, tailWord_344045, baseEnd_344045] using wordTrace_append hprefix tailTrace_344045
  have hstable : (prefixWord ++ tailWord_344045).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_344045).length < 2 ^ (prefixWord ++ tailWord_344045).sum := by decide
  have hdescent : baseEnd_344045 < baseStart_344045 := by decide
  rcases family_descends (prefixWord ++ tailWord_344045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_344059 : List Nat := [1, 1, 1, 1, 1, 3, 6, 4, 2]
def baseStart_344059 : Nat := 118140960795 + 344059 * 2 ^ 59
def prefixEnd_344059 : Nat := 4983230072969 + 3 ^ 40 * 344059 * 2
def baseEnd_344059 : Nat := 157037902671444090026851

theorem tailTrace_344059 : CollatzResearch.WordTrace tailWord_344059 prefixEnd_344059 157037902671444090026851 := by
  unfold tailWord_344059
  simp only [CollatzResearch.WordTrace]
  refine ⟨12548862660540478444139231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8365908440360318962759487 12548862660540478444139231)
  ·
    refine ⟨18823293990810717666208847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12548862660540478444139231 18823293990810717666208847)
    ·
      refine ⟨28234940986216076499313271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18823293990810717666208847 28234940986216076499313271)
      ·
        refine ⟨42352411479324114748969907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28234940986216076499313271 42352411479324114748969907)
        ·
          refine ⟨63528617218986172123454861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42352411479324114748969907 63528617218986172123454861)
          ·
            refine ⟨23823231457119814546295573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 63528617218986172123454861 23823231457119814546295573)
            ·
              refine ⟨1116713974552491306857605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 23823231457119814546295573 1116713974552491306857605)
              ·
                refine ⟨209383870228592120035801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1116713974552491306857605 209383870228592120035801)
                ·
                  refine ⟨157037902671444090026851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 209383870228592120035801 157037902671444090026851)
                  ·
                    rfl

theorem cell20_344059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 6, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 6, 4, 2].length) (baseStart_344059 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_344059 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_344059 prefixEnd_344059 := by exact prefixLift 344059
  have htrace : WordTrace (prefixWord ++ tailWord_344059) baseStart_344059 baseEnd_344059 := by
    simpa [prefixWord, tailWord_344059, baseEnd_344059] using wordTrace_append hprefix tailTrace_344059
  have hstable : (prefixWord ++ tailWord_344059).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_344059).length < 2 ^ (prefixWord ++ tailWord_344059).sum := by decide
  have hdescent : baseEnd_344059 < baseStart_344059 := by decide
  rcases family_descends (prefixWord ++ tailWord_344059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_344093 : List Nat := [1, 4, 2, 2, 2, 3, 1, 3, 2]
def baseStart_344093 : Nat := 118140960795 + 344093 * 2 ^ 59
def prefixEnd_344093 : Nat := 4983230072969 + 3 ^ 40 * 344093 * 2
def baseEnd_344093 : Nat := 157053421197891082893379

theorem tailTrace_344093 : CollatzResearch.WordTrace tailWord_344093 prefixEnd_344093 157053421197891082893379 := by
  unfold tailWord_344093
  simp only [CollatzResearch.WordTrace]
  refine ⟨12550102742417302250876933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8366735161611534833917955 12550102742417302250876933)
  ·
    refine ⟨2353144264203244172039425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12550102742417302250876933 2353144264203244172039425)
    ·
      refine ⟨1764858198152433129029569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2353144264203244172039425 1764858198152433129029569)
      ·
        refine ⟨1323643648614324846772177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1764858198152433129029569 1323643648614324846772177)
        ·
          refine ⟨992732736460743635079133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1323643648614324846772177 992732736460743635079133)
          ·
            refine ⟨372274776172778863154675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 992732736460743635079133 372274776172778863154675)
            ·
              refine ⟨558412164259168294732013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 372274776172778863154675 558412164259168294732013)
              ·
                refine ⟨209404561597188110524505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 558412164259168294732013 209404561597188110524505)
                ·
                  refine ⟨157053421197891082893379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 209404561597188110524505 157053421197891082893379)
                  ·
                    rfl

theorem cell20_344093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 3, 1, 3, 2].length) (baseStart_344093 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_344093 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_344093 prefixEnd_344093 := by exact prefixLift 344093
  have htrace : WordTrace (prefixWord ++ tailWord_344093) baseStart_344093 baseEnd_344093 := by
    simpa [prefixWord, tailWord_344093, baseEnd_344093] using wordTrace_append hprefix tailTrace_344093
  have hstable : (prefixWord ++ tailWord_344093).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_344093).length < 2 ^ (prefixWord ++ tailWord_344093).sum := by decide
  have hdescent : baseEnd_344093 < baseStart_344093 := by decide
  rcases family_descends (prefixWord ++ tailWord_344093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_344128 : List Nat := [2, 1, 1, 2, 2, 4, 4, 1, 3]
def baseStart_344128 : Nat := 118140960795 + 344128 * 2 ^ 59
def prefixEnd_344128 : Nat := 4983230072969 + 3 ^ 40 * 344128 * 2
def baseEnd_344128 : Nat := 157069396151586516726569

theorem tailTrace_344128 : CollatzResearch.WordTrace tailWord_344128 prefixEnd_344128 157069396151586516726569 := by
  unfold tailWord_344128
  simp only [CollatzResearch.WordTrace]
  refine ⟨6275689648645251614200519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8367586198193668818934025 6275689648645251614200519)
  ·
    refine ⟨9413534472967877421300779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6275689648645251614200519 9413534472967877421300779)
    ·
      refine ⟨14120301709451816131951169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9413534472967877421300779 14120301709451816131951169)
      ·
        refine ⟨10590226282088862098963377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14120301709451816131951169 10590226282088862098963377)
        ·
          refine ⟨7942669711566646574222533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10590226282088862098963377 7942669711566646574222533)
          ·
            refine ⟨1489250570918746232666725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7942669711566646574222533 1489250570918746232666725)
            ·
              refine ⟨279234482047264918625011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1489250570918746232666725 279234482047264918625011)
              ·
                refine ⟨418851723070897377937517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 279234482047264918625011 418851723070897377937517)
                ·
                  refine ⟨157069396151586516726569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 418851723070897377937517 157069396151586516726569)
                  ·
                    rfl

theorem cell20_344128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 4, 1, 3].length) (baseStart_344128 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_344128 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_344128 prefixEnd_344128 := by exact prefixLift 344128
  have htrace : WordTrace (prefixWord ++ tailWord_344128) baseStart_344128 baseEnd_344128 := by
    simpa [prefixWord, tailWord_344128, baseEnd_344128] using wordTrace_append hprefix tailTrace_344128
  have hstable : (prefixWord ++ tailWord_344128).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_344128).length < 2 ^ (prefixWord ++ tailWord_344128).sum := by decide
  have hdescent : baseEnd_344128 < baseStart_344128 := by decide
  rcases family_descends (prefixWord ++ tailWord_344128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_344208 : List Nat := [2, 1, 1, 1, 1, 1, 6, 2, 5]
def baseStart_344208 : Nat := 118140960795 + 344208 * 2 ^ 59
def prefixEnd_344208 : Nat := 4983230072969 + 3 ^ 40 * 344208 * 2
def baseEnd_344208 : Nat := 157105910331461794059575

theorem tailTrace_344208 : CollatzResearch.WordTrace tailWord_344208 prefixEnd_344208 157105910331461794059575 := by
  unfold tailWord_344208
  simp only [CollatzResearch.WordTrace]
  refine ⟨6277148568500338445656639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8369531424667117927542185 6277148568500338445656639)
  ·
    refine ⟨9415722852750507668484959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6277148568500338445656639 9415722852750507668484959)
    ·
      refine ⟨14123584279125761502727439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9415722852750507668484959 14123584279125761502727439)
      ·
        refine ⟨21185376418688642254091159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14123584279125761502727439 21185376418688642254091159)
        ·
          refine ⟨31778064628032963381136739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21185376418688642254091159 31778064628032963381136739)
          ·
            refine ⟨47667096942049445071705109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31778064628032963381136739 47667096942049445071705109)
            ·
              refine ⟨2234395169158567737736177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 47667096942049445071705109 2234395169158567737736177)
              ·
                refine ⟨1675796376868925803302133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2234395169158567737736177 1675796376868925803302133)
                ·
                  refine ⟨157105910331461794059575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1675796376868925803302133 157105910331461794059575)
                  ·
                    rfl

theorem cell20_344208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 6, 2, 5].length) (baseStart_344208 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_344208 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_344208 prefixEnd_344208 := by exact prefixLift 344208
  have htrace : WordTrace (prefixWord ++ tailWord_344208) baseStart_344208 baseEnd_344208 := by
    simpa [prefixWord, tailWord_344208, baseEnd_344208] using wordTrace_append hprefix tailTrace_344208
  have hstable : (prefixWord ++ tailWord_344208).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_344208).length < 2 ^ (prefixWord ++ tailWord_344208).sum := by decide
  have hdescent : baseEnd_344208 < baseStart_344208 := by decide
  rcases family_descends (prefixWord ++ tailWord_344208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_344218 : List Nat := [3, 1, 1, 5, 2, 1, 7]
def baseStart_344218 : Nat := 118140960795 + 344218 * 2 ^ 59
def prefixEnd_344218 : Nat := 4983230072969 + 3 ^ 40 * 344218 * 2
def baseEnd_344218 : Nat := 17456719400438467080689

theorem tailTrace_344218 : CollatzResearch.WordTrace tailWord_344218 prefixEnd_344218 17456719400438467080689 := by
  unfold tailWord_344218
  simp only [CollatzResearch.WordTrace]
  refine ⟨3138665466741112149794327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8369774577976299066118205 3138665466741112149794327)
  ·
    refine ⟨4707998200111668224691491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3138665466741112149794327 4707998200111668224691491)
    ·
      refine ⟨7061997300167502337037237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4707998200111668224691491 7061997300167502337037237)
      ·
        refine ⟨662062246890703344097241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 7061997300167502337037237 662062246890703344097241)
        ·
          refine ⟨496546685168027508072931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 662062246890703344097241 496546685168027508072931)
          ·
            refine ⟨744820027752041262109397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 496546685168027508072931 744820027752041262109397)
            ·
              refine ⟨17456719400438467080689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 744820027752041262109397 17456719400438467080689)
              ·
                rfl

theorem cell20_344218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 7].length) (baseStart_344218 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_344218 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_344218 prefixEnd_344218 := by exact prefixLift 344218
  have htrace : WordTrace (prefixWord ++ tailWord_344218) baseStart_344218 baseEnd_344218 := by
    simpa [prefixWord, tailWord_344218, baseEnd_344218] using wordTrace_append hprefix tailTrace_344218
  have hstable : (prefixWord ++ tailWord_344218).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_344218).length < 2 ^ (prefixWord ++ tailWord_344218).sum := by decide
  have hdescent : baseEnd_344218 < baseStart_344218 := by decide
  rcases family_descends (prefixWord ++ tailWord_344218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_344225 : List Nat := [1, 2, 3, 3, 1, 3, 1, 1, 5]
def baseStart_344225 : Nat := 118140960795 + 344225 * 2 ^ 59
def prefixEnd_344225 : Nat := 4983230072969 + 3 ^ 40 * 344225 * 2
def baseEnd_344225 : Nat := 157113669594685290492839

theorem tailTrace_344225 : CollatzResearch.WordTrace tailWord_344225 prefixEnd_344225 157113669594685290492839 := by
  unfold tailWord_344225
  simp only [CollatzResearch.WordTrace]
  refine ⟨12554917177939088794682129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8369944785292725863121419 12554917177939088794682129)
  ·
    refine ⟨9416187883454316596011597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12554917177939088794682129 9416187883454316596011597)
    ·
      refine ⟨3531070456295368723504349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9416187883454316596011597 3531070456295368723504349)
      ·
        refine ⟨1324151421110763271314131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3531070456295368723504349 1324151421110763271314131)
        ·
          refine ⟨1986227131666144906971197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1324151421110763271314131 1986227131666144906971197)
          ·
            refine ⟨744835174374804340114199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1986227131666144906971197 744835174374804340114199)
            ·
              refine ⟨1117252761562206510171299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 744835174374804340114199 1117252761562206510171299)
              ·
                refine ⟨1675879142343309765256949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1117252761562206510171299 1675879142343309765256949)
                ·
                  refine ⟨157113669594685290492839, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1675879142343309765256949 157113669594685290492839)
                  ·
                    rfl

theorem cell20_344225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 1, 1, 5].length) (baseStart_344225 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_344225 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_344225 prefixEnd_344225 := by exact prefixLift 344225
  have htrace : WordTrace (prefixWord ++ tailWord_344225) baseStart_344225 baseEnd_344225 := by
    simpa [prefixWord, tailWord_344225, baseEnd_344225] using wordTrace_append hprefix tailTrace_344225
  have hstable : (prefixWord ++ tailWord_344225).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_344225).length < 2 ^ (prefixWord ++ tailWord_344225).sum := by decide
  have hdescent : baseEnd_344225 < baseStart_344225 := by decide
  rcases family_descends (prefixWord ++ tailWord_344225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_344242 : List Nat := [3, 2, 1, 1, 1, 3, 5, 1, 3]
def baseStart_344242 : Nat := 118140960795 + 344242 * 2 ^ 59
def prefixEnd_344242 : Nat := 4983230072969 + 3 ^ 40 * 344242 * 2
def baseEnd_344242 : Nat := 157121428857908786926103

theorem tailTrace_344242 : CollatzResearch.WordTrace tailWord_344242 prefixEnd_344242 157121428857908786926103 := by
  unfold tailWord_344242
  simp only [CollatzResearch.WordTrace]
  refine ⟨3138884304719375174512745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8370358145918333798700653 3138884304719375174512745)
  ·
    refine ⟨2354163228539531380884559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3138884304719375174512745 2354163228539531380884559)
    ·
      refine ⟨3531244842809297071326839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2354163228539531380884559 3531244842809297071326839)
      ·
        refine ⟨5296867264213945606990259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3531244842809297071326839 5296867264213945606990259)
        ·
          refine ⟨7945300896320918410485389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5296867264213945606990259 7945300896320918410485389)
          ·
            refine ⟨2979487836120344403932021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7945300896320918410485389 2979487836120344403932021)
            ·
              refine ⟨279326984636282287868627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2979487836120344403932021 279326984636282287868627)
              ·
                refine ⟨418990476954423431802941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 279326984636282287868627 418990476954423431802941)
                ·
                  refine ⟨157121428857908786926103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 418990476954423431802941 157121428857908786926103)
                  ·
                    rfl

theorem cell20_344242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 5, 1, 3].length) (baseStart_344242 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_344242 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_344242 prefixEnd_344242 := by exact prefixLift 344242
  have htrace : WordTrace (prefixWord ++ tailWord_344242) baseStart_344242 baseEnd_344242 := by
    simpa [prefixWord, tailWord_344242, baseEnd_344242] using wordTrace_append hprefix tailTrace_344242
  have hstable : (prefixWord ++ tailWord_344242).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_344242).length < 2 ^ (prefixWord ++ tailWord_344242).sum := by decide
  have hdescent : baseEnd_344242 < baseStart_344242 := by decide
  rcases family_descends (prefixWord ++ tailWord_344242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_344252 : List Nat := [2, 2, 2, 3, 4, 1, 2, 4]
def baseStart_344252 : Nat := 118140960795 + 344252 * 2 ^ 59
def prefixEnd_344252 : Nat := 4983230072969 + 3 ^ 40 * 344252 * 2
def baseEnd_344252 : Nat := 52375331043464398864243

theorem tailTrace_344252 : CollatzResearch.WordTrace tailWord_344252 prefixEnd_344252 52375331043464398864243 := by
  unfold tailWord_344252
  simp only [CollatzResearch.WordTrace]
  refine ⟨6277950974420636202957505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8370601299227514937276673 6277950974420636202957505)
  ·
    refine ⟨4708463230815477152218129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6277950974420636202957505 4708463230815477152218129)
    ·
      refine ⟨3531347423111607864163597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4708463230815477152218129 3531347423111607864163597)
      ·
        refine ⟨1324255283666852949061349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3531347423111607864163597 1324255283666852949061349)
        ·
          refine ⟨248297865687534927949003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1324255283666852949061349 248297865687534927949003)
          ·
            refine ⟨372446798531302391923505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 248297865687534927949003 372446798531302391923505)
            ·
              refine ⟨279335098898476793942629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 372446798531302391923505 279335098898476793942629)
              ·
                refine ⟨52375331043464398864243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 279335098898476793942629 52375331043464398864243)
                ·
                  rfl

theorem cell20_344252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 4, 1, 2, 4].length) (baseStart_344252 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_344252 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_344252 prefixEnd_344252 := by exact prefixLift 344252
  have htrace : WordTrace (prefixWord ++ tailWord_344252) baseStart_344252 baseEnd_344252 := by
    simpa [prefixWord, tailWord_344252, baseEnd_344252] using wordTrace_append hprefix tailTrace_344252
  have hstable : (prefixWord ++ tailWord_344252).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_344252).length < 2 ^ (prefixWord ++ tailWord_344252).sum := by decide
  have hdescent : baseEnd_344252 < baseStart_344252 := by decide
  rcases family_descends (prefixWord ++ tailWord_344252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_344256 : List Nat := [2, 1, 1, 2, 5, 1, 4, 4]
def baseStart_344256 : Nat := 118140960795 + 344256 * 2 ^ 59
def prefixEnd_344256 : Nat := 4983230072969 + 3 ^ 40 * 344256 * 2
def baseEnd_344256 : Nat := 52375939613128986819793

theorem tailTrace_344256 : CollatzResearch.WordTrace tailWord_344256 prefixEnd_344256 52375939613128986819793 := by
  unfold tailWord_344256
  simp only [CollatzResearch.WordTrace]
  refine ⟨6278023920413390544530311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8370698560551187392707081 6278023920413390544530311)
  ·
    refine ⟨9417035880620085816795467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6278023920413390544530311 9417035880620085816795467)
    ·
      refine ⟨14125553820930128725193201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9417035880620085816795467 14125553820930128725193201)
      ·
        refine ⟨10594165365697596543894901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14125553820930128725193201 10594165365697596543894901)
        ·
          refine ⟨993203003034149675990147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 10594165365697596543894901 993203003034149675990147)
          ·
            refine ⟨1489804504551224513985221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 993203003034149675990147 1489804504551224513985221)
            ·
              refine ⟨279338344603354596372229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1489804504551224513985221 279338344603354596372229)
              ·
                refine ⟨52375939613128986819793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 279338344603354596372229 52375939613128986819793)
                ·
                  rfl

theorem cell20_344256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 4, 4].length) (baseStart_344256 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_344256 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_344256 prefixEnd_344256 := by exact prefixLift 344256
  have htrace : WordTrace (prefixWord ++ tailWord_344256) baseStart_344256 baseEnd_344256 := by
    simpa [prefixWord, tailWord_344256, baseEnd_344256] using wordTrace_append hprefix tailTrace_344256
  have hstable : (prefixWord ++ tailWord_344256).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_344256).length < 2 ^ (prefixWord ++ tailWord_344256).sum := by decide
  have hdescent : baseEnd_344256 < baseStart_344256 := by decide
  rcases family_descends (prefixWord ++ tailWord_344256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_344349 : List Nat := [1, 4, 2, 3, 2, 2, 1, 5]
def baseStart_344349 : Nat := 118140960795 + 344349 * 2 ^ 59
def prefixEnd_344349 : Nat := 4983230072969 + 3 ^ 40 * 344349 * 2
def baseEnd_344349 : Nat := 52390088857830656786333

theorem tailTrace_344349 : CollatzResearch.WordTrace tailWord_344349 prefixEnd_344349 52390088857830656786333 := by
  unfold tailWord_344349
  simp only [CollatzResearch.WordTrace]
  refine ⟨12559439829489857972196101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8372959886326571981464067 12559439829489857972196101)
  ·
    refine ⟨2354894968029348369786769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12559439829489857972196101 2354894968029348369786769)
    ·
      refine ⟨1766171226022011277340077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2354894968029348369786769 1766171226022011277340077)
      ·
        refine ⟨662314209758254229002529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1766171226022011277340077 662314209758254229002529)
        ·
          refine ⟨496735657318690671751897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 662314209758254229002529 496735657318690671751897)
          ·
            refine ⟨372551742989018003813923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 496735657318690671751897 372551742989018003813923)
            ·
              refine ⟨558827614483527005720885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 372551742989018003813923 558827614483527005720885)
              ·
                refine ⟨52390088857830656786333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 558827614483527005720885 52390088857830656786333)
                ·
                  rfl

theorem cell20_344349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 2, 1, 5].length) (baseStart_344349 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_344349 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_344349 prefixEnd_344349 := by exact prefixLift 344349
  have htrace : WordTrace (prefixWord ++ tailWord_344349) baseStart_344349 baseEnd_344349 := by
    simpa [prefixWord, tailWord_344349, baseEnd_344349] using wordTrace_append hprefix tailTrace_344349
  have hstable : (prefixWord ++ tailWord_344349).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_344349).length < 2 ^ (prefixWord ++ tailWord_344349).sum := by decide
  have hdescent : baseEnd_344349 < baseStart_344349 := by decide
  rcases family_descends (prefixWord ++ tailWord_344349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_344353 : List Nat := [1, 2, 3, 2, 1, 1, 5, 5]
def baseStart_344353 : Nat := 118140960795 + 344353 * 2 ^ 59
def prefixEnd_344353 : Nat := 4983230072969 + 3 ^ 40 * 344353 * 2
def baseEnd_344353 : Nat := 52390697427495244741883

theorem tailTrace_344353 : CollatzResearch.WordTrace tailWord_344353 prefixEnd_344353 52390697427495244741883 := by
  unfold tailWord_344353
  simp only [CollatzResearch.WordTrace]
  refine ⟨12559585721475366655341713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8373057147650244436894475 12559585721475366655341713)
  ·
    refine ⟨9419689291106524991506285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12559585721475366655341713 9419689291106524991506285)
    ·
      refine ⟨3532383484164946871814857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9419689291106524991506285 3532383484164946871814857)
      ·
        refine ⟨2649287613123710153861143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3532383484164946871814857 2649287613123710153861143)
        ·
          refine ⟨3973931419685565230791715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2649287613123710153861143 3973931419685565230791715)
          ·
            refine ⟨5960897129528347846187573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3973931419685565230791715 5960897129528347846187573)
            ·
              refine ⟨558834105893282610580085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5960897129528347846187573 558834105893282610580085)
              ·
                refine ⟨52390697427495244741883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 558834105893282610580085 52390697427495244741883)
                ·
                  rfl

theorem cell20_344353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 5, 5].length) (baseStart_344353 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_344353 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_344353 prefixEnd_344353 := by exact prefixLift 344353
  have htrace : WordTrace (prefixWord ++ tailWord_344353) baseStart_344353 baseEnd_344353 := by
    simpa [prefixWord, tailWord_344353, baseEnd_344353] using wordTrace_append hprefix tailTrace_344353
  have hstable : (prefixWord ++ tailWord_344353).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_344353).length < 2 ^ (prefixWord ++ tailWord_344353).sum := by decide
  have hdescent : baseEnd_344353 < baseStart_344353 := by decide
  rcases family_descends (prefixWord ++ tailWord_344353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_344359 : List Nat := [1, 1, 8, 1, 1, 1, 1, 2, 4]
def baseStart_344359 : Nat := 118140960795 + 344359 * 2 ^ 59
def prefixEnd_344359 : Nat := 4983230072969 + 3 ^ 40 * 344359 * 2
def baseEnd_344359 : Nat := 157174830845976380025625

theorem tailTrace_344359 : CollatzResearch.WordTrace tailWord_344359 prefixEnd_344359 157174830845976380025625 := by
  unfold tailWord_344359
  simp only [CollatzResearch.WordTrace]
  refine ⟨12559804559453629680060131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8373203039635753120040087 12559804559453629680060131)
  ·
    refine ⟨18839706839180444520090197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12559804559453629680060131 18839706839180444520090197)
    ·
      refine ⟨220777814521645834219807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 18839706839180444520090197 220777814521645834219807)
      ·
        refine ⟨331166721782468751329711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 220777814521645834219807 331166721782468751329711)
        ·
          refine ⟨496750082673703126994567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 331166721782468751329711 496750082673703126994567)
          ·
            refine ⟨745125124010554690491851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 496750082673703126994567 745125124010554690491851)
            ·
              refine ⟨1117687686015832035737777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 745125124010554690491851 1117687686015832035737777)
              ·
                refine ⟨838265764511874026803333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1117687686015832035737777 838265764511874026803333)
                ·
                  refine ⟨157174830845976380025625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 838265764511874026803333 157174830845976380025625)
                  ·
                    rfl

theorem cell20_344359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 1, 2, 4].length) (baseStart_344359 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_344359 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_344359 prefixEnd_344359 := by exact prefixLift 344359
  have htrace : WordTrace (prefixWord ++ tailWord_344359) baseStart_344359 baseEnd_344359 := by
    simpa [prefixWord, tailWord_344359, baseEnd_344359] using wordTrace_append hprefix tailTrace_344359
  have hstable : (prefixWord ++ tailWord_344359).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_344359).length < 2 ^ (prefixWord ++ tailWord_344359).sum := by decide
  have hdescent : baseEnd_344359 < baseStart_344359 := by decide
  rcases family_descends (prefixWord ++ tailWord_344359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_344366 : List Nat := [4, 1, 3, 3, 1, 1, 3, 4]
def baseStart_344366 : Nat := 118140960795 + 344366 * 2 ^ 59
def prefixEnd_344366 : Nat := 4983230072969 + 3 ^ 40 * 344366 * 2
def baseEnd_344366 : Nat := 52392675278905155597421

theorem tailTrace_344366 : CollatzResearch.WordTrace tailWord_344366 prefixEnd_344366 52392675278905155597421 := by
  unfold tailWord_344366
  simp only [CollatzResearch.WordTrace]
  refine ⟨1570007483803533734445619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8373373246952179917043301 1570007483803533734445619)
  ·
    refine ⟨2355011225705300601668429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1570007483803533734445619 2355011225705300601668429)
    ·
      refine ⟨883129209639487725625661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2355011225705300601668429 883129209639487725625661)
      ·
        refine ⟨331173453614807897109623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 883129209639487725625661 331173453614807897109623)
        ·
          refine ⟨496760180422211845664435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 331173453614807897109623 496760180422211845664435)
          ·
            refine ⟨745140270633317768496653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 496760180422211845664435 745140270633317768496653)
            ·
              refine ⟨279427601487494163186245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 745140270633317768496653 279427601487494163186245)
              ·
                refine ⟨52392675278905155597421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 279427601487494163186245 52392675278905155597421)
                ·
                  rfl

theorem cell20_344366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 3, 4].length) (baseStart_344366 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_344366 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_344366 prefixEnd_344366 := by exact prefixLift 344366
  have htrace : WordTrace (prefixWord ++ tailWord_344366) baseStart_344366 baseEnd_344366 := by
    simpa [prefixWord, tailWord_344366, baseEnd_344366] using wordTrace_append hprefix tailTrace_344366
  have hstable : (prefixWord ++ tailWord_344366).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_344366).length < 2 ^ (prefixWord ++ tailWord_344366).sum := by decide
  have hdescent : baseEnd_344366 < baseStart_344366 := by decide
  rcases family_descends (prefixWord ++ tailWord_344366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_344367 : List Nat := [1, 1, 2, 1, 2, 1, 5, 1, 6]
def baseStart_344367 : Nat := 118140960795 + 344367 * 2 ^ 59
def prefixEnd_344367 : Nat := 4983230072969 + 3 ^ 40 * 344367 * 2
def baseEnd_344367 : Nat := 157178482263963907758925

theorem tailTrace_344367 : CollatzResearch.WordTrace tailWord_344367 prefixEnd_344367 157178482263963907758925 := by
  unfold tailWord_344367
  simp only [CollatzResearch.WordTrace]
  refine ⟨12560096343424647046351355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8373397562283098030900903 12560096343424647046351355)
  ·
    refine ⟨18840144515136970569527033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12560096343424647046351355 18840144515136970569527033)
    ·
      refine ⟨14130108386352727927145275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18840144515136970569527033 14130108386352727927145275)
      ·
        refine ⟨21195162579529091890717913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14130108386352727927145275 21195162579529091890717913)
        ·
          refine ⟨15896371934646818918038435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21195162579529091890717913 15896371934646818918038435)
          ·
            refine ⟨23844557901970228377057653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15896371934646818918038435 23844557901970228377057653)
            ·
              refine ⟨2235427303309708910349155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 23844557901970228377057653 2235427303309708910349155)
              ·
                refine ⟨3353140954964563365523733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2235427303309708910349155 3353140954964563365523733)
                ·
                  refine ⟨157178482263963907758925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3353140954964563365523733 157178482263963907758925)
                  ·
                    rfl

theorem cell20_344367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 5, 1, 6].length) (baseStart_344367 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_344367 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_344367 prefixEnd_344367 := by exact prefixLift 344367
  have htrace : WordTrace (prefixWord ++ tailWord_344367) baseStart_344367 baseEnd_344367 := by
    simpa [prefixWord, tailWord_344367, baseEnd_344367] using wordTrace_append hprefix tailTrace_344367
  have hstable : (prefixWord ++ tailWord_344367).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_344367).length < 2 ^ (prefixWord ++ tailWord_344367).sum := by decide
  have hdescent : baseEnd_344367 < baseStart_344367 := by decide
  rcases family_descends (prefixWord ++ tailWord_344367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_344401 : List Nat := [1, 2, 2, 1, 4, 2, 2, 4, 2]
def baseStart_344401 : Nat := 118140960795 + 344401 * 2 ^ 59
def prefixEnd_344401 : Nat := 4983230072969 + 3 ^ 40 * 344401 * 2
def baseEnd_344401 : Nat := 157194000790410900625453

theorem tailTrace_344401 : CollatzResearch.WordTrace tailWord_344401 prefixEnd_344401 157194000790410900625453 := by
  unfold tailWord_344401
  simp only [CollatzResearch.WordTrace]
  refine ⟨12561336425301470853089057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8374224283534313902059371 12561336425301470853089057)
  ·
    refine ⟨9421002318976103139816793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12561336425301470853089057 9421002318976103139816793)
    ·
      refine ⟨7065751739232077354862595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9421002318976103139816793 7065751739232077354862595)
      ·
        refine ⟨10598627608848116032293893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7065751739232077354862595 10598627608848116032293893)
        ·
          refine ⟨1987242676659021756055105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10598627608848116032293893 1987242676659021756055105)
          ·
            refine ⟨1490432007494266317041329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1987242676659021756055105 1490432007494266317041329)
            ·
              refine ⟨1117824005620699737780997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1490432007494266317041329 1117824005620699737780997)
              ·
                refine ⟨209592001053881200833937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1117824005620699737780997 209592001053881200833937)
                ·
                  refine ⟨157194000790410900625453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 209592001053881200833937 157194000790410900625453)
                  ·
                    rfl

theorem cell20_344401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 2, 4, 2].length) (baseStart_344401 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_344401 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_344401 prefixEnd_344401 := by exact prefixLift 344401
  have htrace : WordTrace (prefixWord ++ tailWord_344401) baseStart_344401 baseEnd_344401 := by
    simpa [prefixWord, tailWord_344401, baseEnd_344401] using wordTrace_append hprefix tailTrace_344401
  have hstable : (prefixWord ++ tailWord_344401).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_344401).length < 2 ^ (prefixWord ++ tailWord_344401).sum := by decide
  have hdescent : baseEnd_344401 < baseStart_344401 := by decide
  rcases family_descends (prefixWord ++ tailWord_344401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_344429 : List Nat := [1, 5, 1, 1, 1, 2, 3, 6]
def baseStart_344429 : Nat := 118140960795 + 344429 * 2 ^ 59
def prefixEnd_344429 : Nat := 4983230072969 + 3 ^ 40 * 344429 * 2
def baseEnd_344429 : Nat := 52402260251122415897335

theorem tailTrace_344429 : CollatzResearch.WordTrace tailWord_344429 prefixEnd_344429 52402260251122415897335 := by
  unfold tailWord_344429
  simp only [CollatzResearch.WordTrace]
  refine ⟨12562357669200031635108341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8374905112800021090072227 12562357669200031635108341)
  ·
    refine ⟨1177721031487502965791407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 12562357669200031635108341 1177721031487502965791407)
    ·
      refine ⟨1766581547231254448687111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1177721031487502965791407 1766581547231254448687111)
      ·
        refine ⟨2649872320846881673030667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1766581547231254448687111 2649872320846881673030667)
        ·
          refine ⟨3974808481270322509546001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2649872320846881673030667 3974808481270322509546001)
          ·
            refine ⟨2981106360952741882159501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3974808481270322509546001 2981106360952741882159501)
            ·
              refine ⟨1117914885357278205809813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2981106360952741882159501 1117914885357278205809813)
              ·
                refine ⟨52402260251122415897335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1117914885357278205809813 52402260251122415897335)
                ·
                  rfl

theorem cell20_344429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 3, 6].length) (baseStart_344429 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_344429 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_344429 prefixEnd_344429 := by exact prefixLift 344429
  have htrace : WordTrace (prefixWord ++ tailWord_344429) baseStart_344429 baseEnd_344429 := by
    simpa [prefixWord, tailWord_344429, baseEnd_344429] using wordTrace_append hprefix tailTrace_344429
  have hstable : (prefixWord ++ tailWord_344429).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_344429).length < 2 ^ (prefixWord ++ tailWord_344429).sum := by decide
  have hdescent : baseEnd_344429 < baseStart_344429 := by decide
  rcases family_descends (prefixWord ++ tailWord_344429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_344456 : List Nat := [2, 1, 3, 3, 1, 1, 5, 2, 2]
def baseStart_344456 : Nat := 118140960795 + 344456 * 2 ^ 59
def prefixEnd_344456 : Nat := 4983230072969 + 3 ^ 40 * 344456 * 2
def baseEnd_344456 : Nat := 157219104289075153791895

theorem tailTrace_344456 : CollatzResearch.WordTrace tailWord_344456 prefixEnd_344456 157219104289075153791895 := by
  unfold tailWord_344456
  simp only [CollatzResearch.WordTrace]
  refine ⟨6281671220051107623170611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8375561626734810164227481 6281671220051107623170611)
  ·
    refine ⟨9422506830076661434755917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6281671220051107623170611 9422506830076661434755917)
    ·
      refine ⟨3533440061278748038033469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9422506830076661434755917 3533440061278748038033469)
      ·
        refine ⟨1325040022979530514262551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3533440061278748038033469 1325040022979530514262551)
        ·
          refine ⟨1987560034469295771393827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1325040022979530514262551 1987560034469295771393827)
          ·
            refine ⟨2981340051703943657090741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1987560034469295771393827 2981340051703943657090741)
            ·
              refine ⟨279500629847244717852257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2981340051703943657090741 279500629847244717852257)
              ·
                refine ⟨209625472385433538389193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 279500629847244717852257 209625472385433538389193)
                ·
                  refine ⟨157219104289075153791895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 209625472385433538389193 157219104289075153791895)
                  ·
                    rfl

theorem cell20_344456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 5, 2, 2].length) (baseStart_344456 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_344456 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_344456 prefixEnd_344456 := by exact prefixLift 344456
  have htrace : WordTrace (prefixWord ++ tailWord_344456) baseStart_344456 baseEnd_344456 := by
    simpa [prefixWord, tailWord_344456, baseEnd_344456] using wordTrace_append hprefix tailTrace_344456
  have hstable : (prefixWord ++ tailWord_344456).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_344456).length < 2 ^ (prefixWord ++ tailWord_344456).sum := by decide
  have hdescent : baseEnd_344456 < baseStart_344456 := by decide
  rcases family_descends (prefixWord ++ tailWord_344456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_344460 : List Nat := [2, 2, 1, 2, 1, 4, 3, 1, 4]
def baseStart_344460 : Nat := 118140960795 + 344460 * 2 ^ 59
def prefixEnd_344460 : Nat := 4983230072969 + 3 ^ 40 * 344460 * 2
def baseEnd_344460 : Nat := 157220929998068917658545

theorem tailTrace_344460 : CollatzResearch.WordTrace tailWord_344460 prefixEnd_344460 157220929998068917658545 := by
  unfold tailWord_344460
  simp only [CollatzResearch.WordTrace]
  refine ⟨6281744166043861964743417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8375658888058482619657889 6281744166043861964743417)
  ·
    refine ⟨4711308124532896473557563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6281744166043861964743417 4711308124532896473557563)
    ·
      refine ⟨7066962186799344710336345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4711308124532896473557563 7066962186799344710336345)
      ·
        refine ⟨5300221640099508532752259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7066962186799344710336345 5300221640099508532752259)
        ·
          refine ⟨7950332460149262799128389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5300221640099508532752259 7950332460149262799128389)
          ·
            refine ⟨1490687336277986774836573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7950332460149262799128389 1490687336277986774836573)
            ·
              refine ⟨559007751104245040563715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1490687336277986774836573 559007751104245040563715)
              ·
                refine ⟨838511626656367560845573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 559007751104245040563715 838511626656367560845573)
                ·
                  refine ⟨157220929998068917658545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 838511626656367560845573 157220929998068917658545)
                  ·
                    rfl

theorem cell20_344460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 3, 1, 4].length) (baseStart_344460 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_344460 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_344460 prefixEnd_344460 := by exact prefixLift 344460
  have htrace : WordTrace (prefixWord ++ tailWord_344460) baseStart_344460 baseEnd_344460 := by
    simpa [prefixWord, tailWord_344460, baseEnd_344460] using wordTrace_append hprefix tailTrace_344460
  have hstable : (prefixWord ++ tailWord_344460).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_344460).length < 2 ^ (prefixWord ++ tailWord_344460).sum := by decide
  have hdescent : baseEnd_344460 < baseStart_344460 := by decide
  rcases family_descends (prefixWord ++ tailWord_344460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_344508 : List Nat := [2, 2, 2, 4, 1, 2, 2, 2, 3]
def baseStart_344508 : Nat := 118140960795 + 344508 * 2 ^ 59
def prefixEnd_344508 : Nat := 4983230072969 + 3 ^ 40 * 344508 * 2
def baseEnd_344508 : Nat := 157242838505994084058349

theorem tailTrace_344508 : CollatzResearch.WordTrace tailWord_344508 prefixEnd_344508 157242838505994084058349 := by
  unfold tailWord_344508
  simp only [CollatzResearch.WordTrace]
  refine ⟨6282619517956914063617089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8376826023942552084822785 6282619517956914063617089)
  ·
    refine ⟨4711964638467685547712817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6282619517956914063617089 4711964638467685547712817)
    ·
      refine ⟨3533973478850764160784613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4711964638467685547712817 3533973478850764160784613)
      ·
        refine ⟨662620027284518280147115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3533973478850764160784613 662620027284518280147115)
        ·
          refine ⟨993930040926777420220673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 662620027284518280147115 993930040926777420220673)
          ·
            refine ⟨745447530695083065165505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 993930040926777420220673 745447530695083065165505)
            ·
              refine ⟨559085648021312298874129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 745447530695083065165505 559085648021312298874129)
              ·
                refine ⟨419314236015984224155597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 559085648021312298874129 419314236015984224155597)
                ·
                  refine ⟨157242838505994084058349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 419314236015984224155597 157242838505994084058349)
                  ·
                    rfl

theorem cell20_344508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 2, 2, 3].length) (baseStart_344508 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_344508 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_344508 prefixEnd_344508 := by exact prefixLift 344508
  have htrace : WordTrace (prefixWord ++ tailWord_344508) baseStart_344508 baseEnd_344508 := by
    simpa [prefixWord, tailWord_344508, baseEnd_344508] using wordTrace_append hprefix tailTrace_344508
  have hstable : (prefixWord ++ tailWord_344508).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_344508).length < 2 ^ (prefixWord ++ tailWord_344508).sum := by decide
  have hdescent : baseEnd_344508 < baseStart_344508 := by decide
  rcases family_descends (prefixWord ++ tailWord_344508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_344595 : List Nat := [1, 1, 1, 2, 1, 5, 1, 4, 4]
def baseStart_344595 : Nat := 118140960795 + 344595 * 2 ^ 59
def prefixEnd_344595 : Nat := 4983230072969 + 3 ^ 40 * 344595 * 2
def baseEnd_344595 : Nat := 157282547676608448157993

theorem tailTrace_344595 : CollatzResearch.WordTrace tailWord_344595 prefixEnd_344595 157282547676608448157993 := by
  unfold tailWord_344595
  simp only [CollatzResearch.WordTrace]
  refine ⟨12568412186598641985651239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8378941457732427990434159 12568412186598641985651239)
  ·
    refine ⟨18852618279897962978476859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12568412186598641985651239 18852618279897962978476859)
    ·
      refine ⟨28278927419846944467715289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18852618279897962978476859 28278927419846944467715289)
      ·
        refine ⟨21209195564885208350786467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28278927419846944467715289 21209195564885208350786467)
        ·
          refine ⟨31813793347327812526179701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21209195564885208350786467 31813793347327812526179701)
          ·
            refine ⟨2982543126311982424329347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 31813793347327812526179701 2982543126311982424329347)
            ·
              refine ⟨4473814689467973636494021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2982543126311982424329347 4473814689467973636494021)
              ·
                refine ⟨838840254275245056842629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4473814689467973636494021 838840254275245056842629)
                ·
                  refine ⟨157282547676608448157993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 838840254275245056842629 157282547676608448157993)
                  ·
                    rfl

theorem cell20_344595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 4, 4].length) (baseStart_344595 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_344595 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_344595 prefixEnd_344595 := by exact prefixLift 344595
  have htrace : WordTrace (prefixWord ++ tailWord_344595) baseStart_344595 baseEnd_344595 := by
    simpa [prefixWord, tailWord_344595, baseEnd_344595] using wordTrace_append hprefix tailTrace_344595
  have hstable : (prefixWord ++ tailWord_344595).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_344595).length < 2 ^ (prefixWord ++ tailWord_344595).sum := by decide
  have hdescent : baseEnd_344595 < baseStart_344595 := by decide
  rcases family_descends (prefixWord ++ tailWord_344595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_344615 : List Nat := [1, 1, 7, 2, 1, 2, 6]
def baseStart_344615 : Nat := 118140960795 + 344615 * 2 ^ 59
def prefixEnd_344615 : Nat := 4983230072969 + 3 ^ 40 * 344615 * 2
def baseEnd_344615 : Nat := 17476852913508585276805

theorem tailTrace_344615 : CollatzResearch.WordTrace tailWord_344615 prefixEnd_344615 17476852913508585276805 := by
  unfold tailWord_344615
  simp only [CollatzResearch.WordTrace]
  refine ⟨12569141646526185401379299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8379427764350790267586199 12569141646526185401379299)
  ·
    refine ⟨18853712469789278102068949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12569141646526185401379299 18853712469789278102068949)
    ·
      refine ⟨441883886010686205517241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 18853712469789278102068949 441883886010686205517241)
      ·
        refine ⟨331412914508014654137931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 441883886010686205517241 331412914508014654137931)
        ·
          refine ⟨497119371762021981206897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 331412914508014654137931 497119371762021981206897)
          ·
            refine ⟨372839528821516485905173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 497119371762021981206897 372839528821516485905173)
            ·
              refine ⟨17476852913508585276805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 372839528821516485905173 17476852913508585276805)
              ·
                rfl

theorem cell20_344615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 2, 6].length) (baseStart_344615 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_344615 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_344615 prefixEnd_344615 := by exact prefixLift 344615
  have htrace : WordTrace (prefixWord ++ tailWord_344615) baseStart_344615 baseEnd_344615 := by
    simpa [prefixWord, tailWord_344615, baseEnd_344615] using wordTrace_append hprefix tailTrace_344615
  have hstable : (prefixWord ++ tailWord_344615).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_344615).length < 2 ^ (prefixWord ++ tailWord_344615).sum := by decide
  have hdescent : baseEnd_344615 < baseStart_344615 := by decide
  rcases family_descends (prefixWord ++ tailWord_344615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_344621 : List Nat := [1, 5, 4, 1, 1, 1, 3, 2, 2]
def baseStart_344621 : Nat := 118140960795 + 344621 * 2 ^ 59
def prefixEnd_344621 : Nat := 4983230072969 + 3 ^ 40 * 344621 * 2
def baseEnd_344621 : Nat := 157294414785067913291221

theorem tailTrace_344621 : CollatzResearch.WordTrace tailWord_344621 prefixEnd_344621 157294414785067913291221 := by
  unfold tailWord_344621
  simp only [CollatzResearch.WordTrace]
  refine ⟨12569360484504448426097717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8379573656336298950731811 12569360484504448426097717)
  ·
    refine ⟨1178377545422292039946661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 12569360484504448426097717 1178377545422292039946661)
    ·
      refine ⟨220945789766679757489999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1178377545422292039946661 220945789766679757489999)
      ·
        refine ⟨331418684650019636234999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 220945789766679757489999 331418684650019636234999)
        ·
          refine ⟨497128026975029454352499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 331418684650019636234999 497128026975029454352499)
          ·
            refine ⟨745692040462544181528749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 497128026975029454352499 745692040462544181528749)
            ·
              refine ⟨279634515173454068073281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 745692040462544181528749 279634515173454068073281)
              ·
                refine ⟨209725886380090551054961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 279634515173454068073281 209725886380090551054961)
                ·
                  refine ⟨157294414785067913291221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 209725886380090551054961 157294414785067913291221)
                  ·
                    rfl

theorem cell20_344621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 3, 2, 2].length) (baseStart_344621 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_344621 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_344621 prefixEnd_344621 := by exact prefixLift 344621
  have htrace : WordTrace (prefixWord ++ tailWord_344621) baseStart_344621 baseEnd_344621 := by
    simpa [prefixWord, tailWord_344621, baseEnd_344621] using wordTrace_append hprefix tailTrace_344621
  have hstable : (prefixWord ++ tailWord_344621).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_344621).length < 2 ^ (prefixWord ++ tailWord_344621).sum := by decide
  have hdescent : baseEnd_344621 < baseStart_344621 := by decide
  rcases family_descends (prefixWord ++ tailWord_344621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_344626 : List Nat := [3, 2, 1, 1, 2, 1, 4, 1, 5]
def baseStart_344626 : Nat := 118140960795 + 344626 * 2 ^ 59
def prefixEnd_344626 : Nat := 4983230072969 + 3 ^ 40 * 344626 * 2
def baseEnd_344626 : Nat := 157296696921310118124533

theorem tailTrace_344626 : CollatzResearch.WordTrace tailWord_344626 prefixEnd_344626 157296696921310118124533 := by
  unfold tailWord_344626
  simp only [CollatzResearch.WordTrace]
  refine ⟨3142385712371583570007433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8379695232990889520019821 3142385712371583570007433)
  ·
    refine ⟨2356789284278687677505575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3142385712371583570007433 2356789284278687677505575)
    ·
      refine ⟨3535183926418031516258363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2356789284278687677505575 3535183926418031516258363)
      ·
        refine ⟨5302775889627047274387545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3535183926418031516258363 5302775889627047274387545)
        ·
          refine ⟨3977081917220285455790659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5302775889627047274387545 3977081917220285455790659)
          ·
            refine ⟨5965622875830428183685989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3977081917220285455790659 5965622875830428183685989)
            ·
              refine ⟨1118554289218205284441123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5965622875830428183685989 1118554289218205284441123)
              ·
                refine ⟨1677831433827307926661685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1118554289218205284441123 1677831433827307926661685)
                ·
                  refine ⟨157296696921310118124533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1677831433827307926661685 157296696921310118124533)
                  ·
                    rfl

theorem cell20_344626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 4, 1, 5].length) (baseStart_344626 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_344626 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_344626 prefixEnd_344626 := by exact prefixLift 344626
  have htrace : WordTrace (prefixWord ++ tailWord_344626) baseStart_344626 baseEnd_344626 := by
    simpa [prefixWord, tailWord_344626, baseEnd_344626] using wordTrace_append hprefix tailTrace_344626
  have hstable : (prefixWord ++ tailWord_344626).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_344626).length < 2 ^ (prefixWord ++ tailWord_344626).sum := by decide
  have hdescent : baseEnd_344626 < baseStart_344626 := by decide
  rcases family_descends (prefixWord ++ tailWord_344626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_344640 : List Nat := [2, 1, 1, 2, 2, 2, 3, 7]
def baseStart_344640 : Nat := 118140960795 + 344640 * 2 ^ 59
def prefixEnd_344640 : Nat := 4983230072969 + 3 ^ 40 * 344640 * 2
def baseEnd_344640 : Nat := 52434362300929430552603

theorem tailTrace_344640 : CollatzResearch.WordTrace tailWord_344640 prefixEnd_344640 52434362300929430552603 := by
  unfold tailWord_344640
  simp only [CollatzResearch.WordTrace]
  refine ⟨6285026735717807335519687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8380035647623743114026249 6285026735717807335519687)
  ·
    refine ⟨9427540103576711003279531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6285026735717807335519687 9427540103576711003279531)
    ·
      refine ⟨14141310155365066504919297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9427540103576711003279531 14141310155365066504919297)
      ·
        refine ⟨10605982616523799878689473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14141310155365066504919297 10605982616523799878689473)
        ·
          refine ⟨7954486962392849909017105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10605982616523799878689473 7954486962392849909017105)
          ·
            refine ⟨5965865221794637431762829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7954486962392849909017105 5965865221794637431762829)
            ·
              refine ⟨2237199458172989036911061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5965865221794637431762829 2237199458172989036911061)
              ·
                refine ⟨52434362300929430552603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2237199458172989036911061 52434362300929430552603)
                ·
                  rfl

theorem cell20_344640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 3, 7].length) (baseStart_344640 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_344640 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_344640 prefixEnd_344640 := by exact prefixLift 344640
  have htrace : WordTrace (prefixWord ++ tailWord_344640) baseStart_344640 baseEnd_344640 := by
    simpa [prefixWord, tailWord_344640, baseEnd_344640] using wordTrace_append hprefix tailTrace_344640
  have hstable : (prefixWord ++ tailWord_344640).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_344640).length < 2 ^ (prefixWord ++ tailWord_344640).sum := by decide
  have hdescent : baseEnd_344640 < baseStart_344640 := by decide
  rcases family_descends (prefixWord ++ tailWord_344640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_344670 : List Nat := [4, 4, 1, 2, 2, 7]
def baseStart_344670 : Nat := 118140960795 + 344670 * 2 ^ 59
def prefixEnd_344670 : Nat := 4983230072969 + 3 ^ 40 * 344670 * 2
def baseEnd_344670 : Nat := 5826547397045982246581

theorem tailTrace_344670 : CollatzResearch.WordTrace tailWord_344670 prefixEnd_344670 5826547397045982246581 := by
  unfold tailWord_344670
  simp only [CollatzResearch.WordTrace]
  refine ⟨1571393457665866224328933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8380765107551286529754309 1571393457665866224328933)
  ·
    refine ⟨294636273312349917061675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1571393457665866224328933 294636273312349917061675)
    ·
      refine ⟨441954409968524875592513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 294636273312349917061675 441954409968524875592513)
      ·
        refine ⟨331465807476393656694385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 441954409968524875592513 331465807476393656694385)
        ·
          refine ⟨248599355607295242520789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 331465807476393656694385 248599355607295242520789)
          ·
            refine ⟨5826547397045982246581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 248599355607295242520789 5826547397045982246581)
            ·
              rfl

theorem cell20_344670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 2, 7].length) (baseStart_344670 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_344670 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_344670 prefixEnd_344670 := by exact prefixLift 344670
  have htrace : WordTrace (prefixWord ++ tailWord_344670) baseStart_344670 baseEnd_344670 := by
    simpa [prefixWord, tailWord_344670, baseEnd_344670] using wordTrace_append hprefix tailTrace_344670
  have hstable : (prefixWord ++ tailWord_344670).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_344670).length < 2 ^ (prefixWord ++ tailWord_344670).sum := by decide
  have hdescent : baseEnd_344670 < baseStart_344670 := by decide
  rcases family_descends (prefixWord ++ tailWord_344670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_344674 : List Nat := [3, 3, 2, 3, 1, 8]
def baseStart_344674 : Nat := 118140960795 + 344674 * 2 ^ 59
def prefixEnd_344674 : Nat := 4983230072969 + 3 ^ 40 * 344674 * 2
def baseEnd_344674 : Nat := 5826615015897603130531

theorem tailTrace_344674 : CollatzResearch.WordTrace tailWord_344674 prefixEnd_344674 5826615015897603130531 := by
  unfold tailWord_344674
  simp only [CollatzResearch.WordTrace]
  refine ⟨3142823388328109619444269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8380862368874958985184717 3142823388328109619444269)
  ·
    refine ⟨1178558770623041107291601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3142823388328109619444269 1178558770623041107291601)
    ·
      refine ⟨883919077967280830468701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1178558770623041107291601 883919077967280830468701)
      ·
        refine ⟨331469654237730311425763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 883919077967280830468701 331469654237730311425763)
        ·
          refine ⟨497204481356595467138645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 331469654237730311425763 497204481356595467138645)
          ·
            refine ⟨5826615015897603130531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 497204481356595467138645 5826615015897603130531)
            ·
              rfl

theorem cell20_344674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 8].length) (baseStart_344674 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_344674 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_344674 prefixEnd_344674 := by exact prefixLift 344674
  have htrace : WordTrace (prefixWord ++ tailWord_344674) baseStart_344674 baseEnd_344674 := by
    simpa [prefixWord, tailWord_344674, baseEnd_344674] using wordTrace_append hprefix tailTrace_344674
  have hstable : (prefixWord ++ tailWord_344674).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_344674).length < 2 ^ (prefixWord ++ tailWord_344674).sum := by decide
  have hdescent : baseEnd_344674 < baseStart_344674 := by decide
  rcases family_descends (prefixWord ++ tailWord_344674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_344680 : List Nat := [2, 1, 4, 3, 3, 1, 2, 2, 2]
def baseStart_344680 : Nat := 118140960795 + 344680 * 2 ^ 59
def prefixEnd_344680 : Nat := 4983230072969 + 3 ^ 40 * 344680 * 2
def baseEnd_344680 : Nat := 157321343992725930324313

theorem tailTrace_344680 : CollatzResearch.WordTrace tailWord_344680 prefixEnd_344680 157321343992725930324313 := by
  unfold tailWord_344680
  simp only [CollatzResearch.WordTrace]
  refine ⟨6285756195645350751247747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8381008260860467668330329 6285756195645350751247747)
  ·
    refine ⟨9428634293468026126871621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6285756195645350751247747 9428634293468026126871621)
    ·
      refine ⟨1767868930025254898788429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9428634293468026126871621 1767868930025254898788429)
      ·
        refine ⟨662950848759470587045661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1767868930025254898788429 662950848759470587045661)
        ·
          refine ⟨248606568284801470142123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 662950848759470587045661 248606568284801470142123)
          ·
            refine ⟨372909852427202205213185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 248606568284801470142123 372909852427202205213185)
            ·
              refine ⟨279682389320401653909889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 372909852427202205213185 279682389320401653909889)
              ·
                refine ⟨209761791990301240432417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 279682389320401653909889 209761791990301240432417)
                ·
                  refine ⟨157321343992725930324313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 209761791990301240432417 157321343992725930324313)
                  ·
                    rfl

theorem cell20_344680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 3, 1, 2, 2, 2].length) (baseStart_344680 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_344680 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_344680 prefixEnd_344680 := by exact prefixLift 344680
  have htrace : WordTrace (prefixWord ++ tailWord_344680) baseStart_344680 baseEnd_344680 := by
    simpa [prefixWord, tailWord_344680, baseEnd_344680] using wordTrace_append hprefix tailTrace_344680
  have hstable : (prefixWord ++ tailWord_344680).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_344680).length < 2 ^ (prefixWord ++ tailWord_344680).sum := by decide
  have hdescent : baseEnd_344680 < baseStart_344680 := by decide
  rcases family_descends (prefixWord ++ tailWord_344680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_344709 : List Nat := [1, 3, 1, 1, 4, 2, 1, 1, 6]
def baseStart_344709 : Nat := 118140960795 + 344709 * 2 ^ 59
def prefixEnd_344709 : Nat := 4983230072969 + 3 ^ 40 * 344709 * 2
def baseEnd_344709 : Nat := 157334580382930718357527

theorem tailTrace_344709 : CollatzResearch.WordTrace tailWord_344709 prefixEnd_344709 157334580382930718357527 := by
  unfold tailWord_344709
  simp only [CollatzResearch.WordTrace]
  refine ⟨12572570108185639455301181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8381713405457092970200787 12572570108185639455301181)
  ·
    refine ⟨4714713790569614795737943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12572570108185639455301181 4714713790569614795737943)
    ·
      refine ⟨7072070685854422193606915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4714713790569614795737943 7072070685854422193606915)
      ·
        refine ⟨10608106028781633290410373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7072070685854422193606915 10608106028781633290410373)
        ·
          refine ⟨1989019880396556241951945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10608106028781633290410373 1989019880396556241951945)
          ·
            refine ⟨1491764910297417181463959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1989019880396556241951945 1491764910297417181463959)
            ·
              refine ⟨2237647365446125772195939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1491764910297417181463959 2237647365446125772195939)
              ·
                refine ⟨3356471048169188658293909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2237647365446125772195939 3356471048169188658293909)
                ·
                  refine ⟨157334580382930718357527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3356471048169188658293909 157334580382930718357527)
                  ·
                    rfl

theorem cell20_344709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 1, 1, 6].length) (baseStart_344709 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_344709 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_344709 prefixEnd_344709 := by exact prefixLift 344709
  have htrace : WordTrace (prefixWord ++ tailWord_344709) baseStart_344709 baseEnd_344709 := by
    simpa [prefixWord, tailWord_344709, baseEnd_344709] using wordTrace_append hprefix tailTrace_344709
  have hstable : (prefixWord ++ tailWord_344709).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_344709).length < 2 ^ (prefixWord ++ tailWord_344709).sum := by decide
  have hdescent : baseEnd_344709 < baseStart_344709 := by decide
  rcases family_descends (prefixWord ++ tailWord_344709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_344722 : List Nat := [3, 2, 3, 1, 2, 2, 2, 3, 2]
def baseStart_344722 : Nat := 118140960795 + 344722 * 2 ^ 59
def prefixEnd_344722 : Nat := 4983230072969 + 3 ^ 40 * 344722 * 2
def baseEnd_344722 : Nat := 157340513937160450924141

theorem tailTrace_344722 : CollatzResearch.WordTrace tailWord_344722 prefixEnd_344722 157340513937160450924141 := by
  unfold tailWord_344722
  simp only [CollatzResearch.WordTrace]
  refine ⟨3143261064284635668881105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8382029504759028450349613 3143261064284635668881105)
  ·
    refine ⟨2357445798213476751660829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3143261064284635668881105 2357445798213476751660829)
    ·
      refine ⟨884042174330053781872811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2357445798213476751660829 884042174330053781872811)
      ·
        refine ⟨1326063261495080672809217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 884042174330053781872811 1326063261495080672809217)
        ·
          refine ⟨994547446121310504606913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1326063261495080672809217 994547446121310504606913)
          ·
            refine ⟨745910584590982878455185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 994547446121310504606913 745910584590982878455185)
            ·
              refine ⟨559432938443237158841389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 745910584590982878455185 559432938443237158841389)
              ·
                refine ⟨209787351916213934565521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 559432938443237158841389 209787351916213934565521)
                ·
                  refine ⟨157340513937160450924141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 209787351916213934565521 157340513937160450924141)
                  ·
                    rfl

theorem cell20_344722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 2, 3, 2].length) (baseStart_344722 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_344722 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_344722 prefixEnd_344722 := by exact prefixLift 344722
  have htrace : WordTrace (prefixWord ++ tailWord_344722) baseStart_344722 baseEnd_344722 := by
    simpa [prefixWord, tailWord_344722, baseEnd_344722] using wordTrace_append hprefix tailTrace_344722
  have hstable : (prefixWord ++ tailWord_344722).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_344722).length < 2 ^ (prefixWord ++ tailWord_344722).sum := by decide
  have hdescent : baseEnd_344722 < baseStart_344722 := by decide
  rcases family_descends (prefixWord ++ tailWord_344722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_344723 : List Nat := [1, 1, 1, 2, 1, 2, 2, 3, 7]
def baseStart_344723 : Nat := 118140960795 + 344723 * 2 ^ 59
def prefixEnd_344723 : Nat := 4983230072969 + 3 ^ 40 * 344723 * 2
def baseEnd_344723 : Nat := 157340970364408891890803

theorem tailTrace_344723 : CollatzResearch.WordTrace tailWord_344723 prefixEnd_344723 157340970364408891890803 := by
  unfold tailWord_344723
  simp only [CollatzResearch.WordTrace]
  refine ⟨12573080730134919846310823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8382053820089946564207215 12573080730134919846310823)
  ·
    refine ⟨18859621095202379769466235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12573080730134919846310823 18859621095202379769466235)
    ·
      refine ⟨28289431642803569654199353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18859621095202379769466235 28289431642803569654199353)
      ·
        refine ⟨21217073732102677240649515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28289431642803569654199353 21217073732102677240649515)
        ·
          refine ⟨31825610598154015860974273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21217073732102677240649515 31825610598154015860974273)
          ·
            refine ⟨23869207948615511895730705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31825610598154015860974273 23869207948615511895730705)
            ·
              refine ⟨17901905961461633921798029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23869207948615511895730705 17901905961461633921798029)
              ·
                refine ⟨6713214735548112720674261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17901905961461633921798029 6713214735548112720674261)
                ·
                  refine ⟨157340970364408891890803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6713214735548112720674261 157340970364408891890803)
                  ·
                    rfl

theorem cell20_344723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 3, 7].length) (baseStart_344723 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_344723 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_344723 prefixEnd_344723 := by exact prefixLift 344723
  have htrace : WordTrace (prefixWord ++ tailWord_344723) baseStart_344723 baseEnd_344723 := by
    simpa [prefixWord, tailWord_344723, baseEnd_344723] using wordTrace_append hprefix tailTrace_344723
  have hstable : (prefixWord ++ tailWord_344723).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_344723).length < 2 ^ (prefixWord ++ tailWord_344723).sum := by decide
  have hdescent : baseEnd_344723 < baseStart_344723 := by decide
  rcases family_descends (prefixWord ++ tailWord_344723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_344736 : List Nat := [2, 1, 1, 4, 4, 2, 1, 2, 3]
def baseStart_344736 : Nat := 118140960795 + 344736 * 2 ^ 59
def prefixEnd_344736 : Nat := 4983230072969 + 3 ^ 40 * 344736 * 2
def baseEnd_344736 : Nat := 157346903918638624457417

theorem tailTrace_344736 : CollatzResearch.WordTrace tailWord_344736 prefixEnd_344736 157346903918638624457417 := by
  unfold tailWord_344736
  simp only [CollatzResearch.WordTrace]
  refine ⟨6286777439543911533267031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8382369919391882044356041 6286777439543911533267031)
  ·
    refine ⟨9430166159315867299900547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6286777439543911533267031 9430166159315867299900547)
    ·
      refine ⟨14145249238973800949850821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9430166159315867299900547 14145249238973800949850821)
      ·
        refine ⟨2652234232307587678097029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14145249238973800949850821 2652234232307587678097029)
        ·
          refine ⟨497293918557672689643193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2652234232307587678097029 497293918557672689643193)
          ·
            refine ⟨372970438918254517232395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 497293918557672689643193 372970438918254517232395)
            ·
              refine ⟨559455658377381775848593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 372970438918254517232395 559455658377381775848593)
              ·
                refine ⟨419591743783036331886445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 559455658377381775848593 419591743783036331886445)
                ·
                  refine ⟨157346903918638624457417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 419591743783036331886445 157346903918638624457417)
                  ·
                    rfl

theorem cell20_344736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 2, 1, 2, 3].length) (baseStart_344736 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_344736 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_344736 prefixEnd_344736 := by exact prefixLift 344736
  have htrace : WordTrace (prefixWord ++ tailWord_344736) baseStart_344736 baseEnd_344736 := by
    simpa [prefixWord, tailWord_344736, baseEnd_344736] using wordTrace_append hprefix tailTrace_344736
  have hstable : (prefixWord ++ tailWord_344736).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_344736).length < 2 ^ (prefixWord ++ tailWord_344736).sum := by decide
  have hdescent : baseEnd_344736 < baseStart_344736 := by decide
  rcases family_descends (prefixWord ++ tailWord_344736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_344740 : List Nat := [2, 3, 1, 2, 2, 1, 3, 1, 5]
def baseStart_344740 : Nat := 118140960795 + 344740 * 2 ^ 59
def prefixEnd_344740 : Nat := 4983230072969 + 3 ^ 40 * 344740 * 2
def baseEnd_344740 : Nat := 157348729627632388324067

theorem tailTrace_344740 : CollatzResearch.WordTrace tailWord_344740 prefixEnd_344740 157348729627632388324067 := by
  unfold tailWord_344740
  simp only [CollatzResearch.WordTrace]
  refine ⟨6286850385536665874839837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8382467180715554499786449 6286850385536665874839837)
  ·
    refine ⟨2357568894576249703064939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6286850385536665874839837 2357568894576249703064939)
    ·
      refine ⟨3536353341864374554597409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2357568894576249703064939 3536353341864374554597409)
      ·
        refine ⟨2652265006398280915948057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3536353341864374554597409 2652265006398280915948057)
        ·
          refine ⟨1989198754798710686961043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2652265006398280915948057 1989198754798710686961043)
          ·
            refine ⟨2983798132198066030441565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1989198754798710686961043 2983798132198066030441565)
            ·
              refine ⟨1118924299574274761415587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2983798132198066030441565 1118924299574274761415587)
              ·
                refine ⟨1678386449361412142123381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1118924299574274761415587 1678386449361412142123381)
                ·
                  refine ⟨157348729627632388324067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1678386449361412142123381 157348729627632388324067)
                  ·
                    rfl

theorem cell20_344740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 3, 1, 5].length) (baseStart_344740 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_344740 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_344740 prefixEnd_344740 := by exact prefixLift 344740
  have htrace : WordTrace (prefixWord ++ tailWord_344740) baseStart_344740 baseEnd_344740 := by
    simpa [prefixWord, tailWord_344740, baseEnd_344740] using wordTrace_append hprefix tailTrace_344740
  have hstable : (prefixWord ++ tailWord_344740).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_344740).length < 2 ^ (prefixWord ++ tailWord_344740).sum := by decide
  have hdescent : baseEnd_344740 < baseStart_344740 := by decide
  rcases family_descends (prefixWord ++ tailWord_344740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_344753 : List Nat := [1, 2, 2, 6, 1, 1, 3, 1, 3]
def baseStart_344753 : Nat := 118140960795 + 344753 * 2 ^ 59
def prefixEnd_344753 : Nat := 4983230072969 + 3 ^ 40 * 344753 * 2
def baseEnd_344753 : Nat := 157354663181862120890681

theorem tailTrace_344753 : CollatzResearch.WordTrace tailWord_344753 prefixEnd_344753 157354663181862120890681 := by
  unfold tailWord_344753
  simp only [CollatzResearch.WordTrace]
  refine ⟨12574174920026234969902913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8382783280017489979935275 12574174920026234969902913)
  ·
    refine ⟨9430631190019676227427185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12574174920026234969902913 9430631190019676227427185)
    ·
      refine ⟨7072973392514757170570389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9430631190019676227427185 7072973392514757170570389)
      ·
        refine ⟨331545627774129242370487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 7072973392514757170570389 331545627774129242370487)
        ·
          refine ⟨497318441661193863555731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 331545627774129242370487 497318441661193863555731)
          ·
            refine ⟨745977662491790795333597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 497318441661193863555731 745977662491790795333597)
            ·
              refine ⟨279741623434421548250099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 745977662491790795333597 279741623434421548250099)
              ·
                refine ⟨419612435151632322375149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 279741623434421548250099 419612435151632322375149)
                ·
                  refine ⟨157354663181862120890681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 419612435151632322375149 157354663181862120890681)
                  ·
                    rfl

theorem cell20_344753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 3, 1, 3].length) (baseStart_344753 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_344753 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_344753 prefixEnd_344753 := by exact prefixLift 344753
  have htrace : WordTrace (prefixWord ++ tailWord_344753) baseStart_344753 baseEnd_344753 := by
    simpa [prefixWord, tailWord_344753, baseEnd_344753] using wordTrace_append hprefix tailTrace_344753
  have hstable : (prefixWord ++ tailWord_344753).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_344753).length < 2 ^ (prefixWord ++ tailWord_344753).sum := by decide
  have hdescent : baseEnd_344753 < baseStart_344753 := by decide
  rcases family_descends (prefixWord ++ tailWord_344753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_344754 : List Nat := [3, 2, 1, 1, 1, 2, 1, 9]
def baseStart_344754 : Nat := 118140960795 + 344754 * 2 ^ 59
def prefixEnd_344754 : Nat := 4983230072969 + 3 ^ 40 * 344754 * 2
def baseEnd_344754 : Nat := 52451706536370187285781

theorem tailTrace_344754 : CollatzResearch.WordTrace tailWord_344754 prefixEnd_344754 52451706536370187285781 := by
  unfold tailWord_344754
  simp only [CollatzResearch.WordTrace]
  refine ⟨3143552848255653035172329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8382807595348408093792877 3143552848255653035172329)
  ·
    refine ⟨2357664636191739776379247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3143552848255653035172329 2357664636191739776379247)
    ·
      refine ⟨3536496954287609664568871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2357664636191739776379247 3536496954287609664568871)
      ·
        refine ⟨5304745431431414496853307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3536496954287609664568871 5304745431431414496853307)
        ·
          refine ⟨7957118147147121745279961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5304745431431414496853307 7957118147147121745279961)
          ·
            refine ⟨5967838610360341308959971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7957118147147121745279961 5967838610360341308959971)
            ·
              refine ⟨8951757915540511963439957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5967838610360341308959971 8951757915540511963439957)
              ·
                refine ⟨52451706536370187285781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 8951757915540511963439957 52451706536370187285781)
                ·
                  rfl

theorem cell20_344754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 9].length) (baseStart_344754 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_344754 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_344754 prefixEnd_344754 := by exact prefixLift 344754
  have htrace : WordTrace (prefixWord ++ tailWord_344754) baseStart_344754 baseEnd_344754 := by
    simpa [prefixWord, tailWord_344754, baseEnd_344754] using wordTrace_append hprefix tailTrace_344754
  have hstable : (prefixWord ++ tailWord_344754).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_344754).length < 2 ^ (prefixWord ++ tailWord_344754).sum := by decide
  have hdescent : baseEnd_344754 < baseStart_344754 := by decide
  rcases family_descends (prefixWord ++ tailWord_344754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_344778 : List Nat := [3, 1, 2, 1, 4, 1, 1, 2, 5]
def baseStart_344778 : Nat := 118140960795 + 344778 * 2 ^ 59
def prefixEnd_344778 : Nat := 4983230072969 + 3 ^ 40 * 344778 * 2
def baseEnd_344778 : Nat := 157366073863073145057245

theorem tailTrace_344778 : CollatzResearch.WordTrace tailWord_344778 prefixEnd_344778 157366073863073145057245 := by
  unfold tailWord_344778
  simp only [CollatzResearch.WordTrace]
  refine ⟨3143771686233916059890747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8383391163290442826375325 3143771686233916059890747)
  ·
    refine ⟨4715657529350874089836121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3143771686233916059890747 4715657529350874089836121)
    ·
      refine ⟨3536743147013155567377091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4715657529350874089836121 3536743147013155567377091)
      ·
        refine ⟨5305114720519733351065637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3536743147013155567377091 5305114720519733351065637)
        ·
          refine ⟨994709010097450003324807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5305114720519733351065637 994709010097450003324807)
          ·
            refine ⟨1492063515146175004987211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 994709010097450003324807 1492063515146175004987211)
            ·
              refine ⟨2238095272719262507480817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1492063515146175004987211 2238095272719262507480817)
              ·
                refine ⟨1678571454539446880610613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2238095272719262507480817 1678571454539446880610613)
                ·
                  refine ⟨157366073863073145057245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1678571454539446880610613 157366073863073145057245)
                  ·
                    rfl

theorem cell20_344778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 1, 2, 5].length) (baseStart_344778 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_344778 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_344778 prefixEnd_344778 := by exact prefixLift 344778
  have htrace : WordTrace (prefixWord ++ tailWord_344778) baseStart_344778 baseEnd_344778 := by
    simpa [prefixWord, tailWord_344778, baseEnd_344778] using wordTrace_append hprefix tailTrace_344778
  have hstable : (prefixWord ++ tailWord_344778).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_344778).length < 2 ^ (prefixWord ++ tailWord_344778).sum := by decide
  have hdescent : baseEnd_344778 < baseStart_344778 := by decide
  rcases family_descends (prefixWord ++ tailWord_344778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_344788 : List Nat := [2, 4, 1, 3, 2, 2, 6]
def baseStart_344788 : Nat := 118140960795 + 344788 * 2 ^ 59
def prefixEnd_344788 : Nat := 4983230072969 + 3 ^ 40 * 344788 * 2
def baseEnd_344788 : Nat := 17485626459506394969319

theorem tailTrace_344788 : CollatzResearch.WordTrace tailWord_344788 prefixEnd_344788 17485626459506394969319 := by
  unfold tailWord_344788
  simp only [CollatzResearch.WordTrace]
  refine ⟨6287725737449717973713509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8383634316599623964951345 6287725737449717973713509)
  ·
    refine ⟨1178948575771822120071283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6287725737449717973713509 1178948575771822120071283)
    ·
      refine ⟨1768422863657733180106925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1178948575771822120071283 1768422863657733180106925)
      ·
        refine ⟨663158573871649942540097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1768422863657733180106925 663158573871649942540097)
        ·
          refine ⟨497368930403737456905073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 663158573871649942540097 497368930403737456905073)
          ·
            refine ⟨373026697802803092678805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 497368930403737456905073 373026697802803092678805)
            ·
              refine ⟨17485626459506394969319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 373026697802803092678805 17485626459506394969319)
              ·
                rfl

theorem cell20_344788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 2, 6].length) (baseStart_344788 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_344788 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_344788 prefixEnd_344788 := by exact prefixLift 344788
  have htrace : WordTrace (prefixWord ++ tailWord_344788) baseStart_344788 baseEnd_344788 := by
    simpa [prefixWord, tailWord_344788, baseEnd_344788] using wordTrace_append hprefix tailTrace_344788
  have hstable : (prefixWord ++ tailWord_344788).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_344788).length < 2 ^ (prefixWord ++ tailWord_344788).sum := by decide
  have hdescent : baseEnd_344788 < baseStart_344788 := by decide
  rcases family_descends (prefixWord ++ tailWord_344788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_344792 : List Nat := [2, 1, 2, 2, 3, 2, 8]
def baseStart_344792 : Nat := 118140960795 + 344792 * 2 ^ 59
def prefixEnd_344792 : Nat := 4983230072969 + 3 ^ 40 * 344792 * 2
def baseEnd_344792 : Nat := 17485829316061257621169

theorem tailTrace_344792 : CollatzResearch.WordTrace tailWord_344792 prefixEnd_344792 17485829316061257621169 := by
  unfold tailWord_344792
  simp only [CollatzResearch.WordTrace]
  refine ⟨6287798683442472315286315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8383731577923296420381753 6287798683442472315286315)
  ·
    refine ⟨9431698025163708472929473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6287798683442472315286315 9431698025163708472929473)
    ·
      refine ⟨7073773518872781354697105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9431698025163708472929473 7073773518872781354697105)
      ·
        refine ⟨5305330139154586016022829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7073773518872781354697105 5305330139154586016022829)
        ·
          refine ⟨1989498802182969756008561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5305330139154586016022829 1989498802182969756008561)
          ·
            refine ⟨1492124101637227317006421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1989498802182969756008561 1492124101637227317006421)
            ·
              refine ⟨17485829316061257621169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1492124101637227317006421 17485829316061257621169)
              ·
                rfl

theorem cell20_344792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 8].length) (baseStart_344792 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_344792 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_344792 prefixEnd_344792 := by exact prefixLift 344792
  have htrace : WordTrace (prefixWord ++ tailWord_344792) baseStart_344792 baseEnd_344792 := by
    simpa [prefixWord, tailWord_344792, baseEnd_344792] using wordTrace_append hprefix tailTrace_344792
  have hstable : (prefixWord ++ tailWord_344792).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_344792).length < 2 ^ (prefixWord ++ tailWord_344792).sum := by decide
  have hdescent : baseEnd_344792 < baseStart_344792 := by decide
  rcases family_descends (prefixWord ++ tailWord_344792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_344816 : List Nat := [2, 1, 1, 1, 3, 1, 5, 3, 3]
def baseStart_344816 : Nat := 118140960795 + 344816 * 2 ^ 59
def prefixEnd_344816 : Nat := 4983230072969 + 3 ^ 40 * 344816 * 2
def baseEnd_344816 : Nat := 157383418098513901790423

theorem tailTrace_344816 : CollatzResearch.WordTrace tailWord_344816 prefixEnd_344816 157383418098513901790423 := by
  unfold tailWord_344816
  simp only [CollatzResearch.WordTrace]
  refine ⟨6288236359398998364723151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8384315145865331152964201 6288236359398998364723151)
  ·
    refine ⟨9432354539098497547084727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6288236359398998364723151 9432354539098497547084727)
    ·
      refine ⟨14148531808647746320627091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9432354539098497547084727 14148531808647746320627091)
      ·
        refine ⟨21222797712971619480940637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14148531808647746320627091 21222797712971619480940637)
        ·
          refine ⟨7958549142364357305352739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21222797712971619480940637 7958549142364357305352739)
          ·
            refine ⟨11937823713546535958029109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7958549142364357305352739 11937823713546535958029109)
            ·
              refine ⟨1119170973144987746065229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11937823713546535958029109 1119170973144987746065229)
              ·
                refine ⟨419689114929370404774461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1119170973144987746065229 419689114929370404774461)
                ·
                  refine ⟨157383418098513901790423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 419689114929370404774461 157383418098513901790423)
                  ·
                    rfl

theorem cell20_344816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 5, 3, 3].length) (baseStart_344816 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_344816 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_344816 prefixEnd_344816 := by exact prefixLift 344816
  have htrace : WordTrace (prefixWord ++ tailWord_344816) baseStart_344816 baseEnd_344816 := by
    simpa [prefixWord, tailWord_344816, baseEnd_344816] using wordTrace_append hprefix tailTrace_344816
  have hstable : (prefixWord ++ tailWord_344816).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_344816).length < 2 ^ (prefixWord ++ tailWord_344816).sum := by decide
  have hdescent : baseEnd_344816 < baseStart_344816 := by decide
  rcases family_descends (prefixWord ++ tailWord_344816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_344837 : List Nat := [1, 3, 1, 1, 2, 1, 1, 3, 7]
def baseStart_344837 : Nat := 118140960795 + 344837 * 2 ^ 59
def prefixEnd_344837 : Nat := 4983230072969 + 3 ^ 40 * 344837 * 2
def baseEnd_344837 : Nat := 157393003070731162090337

theorem tailTrace_344837 : CollatzResearch.WordTrace tailWord_344837 prefixEnd_344837 157393003070731162090337 := by
  unfold tailWord_344837
  simp only [CollatzResearch.WordTrace]
  refine ⟨12577238651721917315960765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8384825767814611543973843 12577238651721917315960765)
  ·
    refine ⟨4716464494395718993485287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12577238651721917315960765 4716464494395718993485287)
    ·
      refine ⟨7074696741593578490227931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4716464494395718993485287 7074696741593578490227931)
      ·
        refine ⟨10612045112390367735341897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7074696741593578490227931 10612045112390367735341897)
        ·
          refine ⟨7959033834292775801506423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10612045112390367735341897 7959033834292775801506423)
          ·
            refine ⟨11938550751439163702259635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7959033834292775801506423 11938550751439163702259635)
            ·
              refine ⟨17907826127158745553389453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11938550751439163702259635 17907826127158745553389453)
              ·
                refine ⟨6715434797684529582521045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17907826127158745553389453 6715434797684529582521045)
                ·
                  refine ⟨157393003070731162090337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6715434797684529582521045 157393003070731162090337)
                  ·
                    rfl

theorem cell20_344837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 3, 7].length) (baseStart_344837 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_344837 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_344837 prefixEnd_344837 := by exact prefixLift 344837
  have htrace : WordTrace (prefixWord ++ tailWord_344837) baseStart_344837 baseEnd_344837 := by
    simpa [prefixWord, tailWord_344837, baseEnd_344837] using wordTrace_append hprefix tailTrace_344837
  have hstable : (prefixWord ++ tailWord_344837).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_344837).length < 2 ^ (prefixWord ++ tailWord_344837).sum := by decide
  have hdescent : baseEnd_344837 < baseStart_344837 := by decide
  rcases family_descends (prefixWord ++ tailWord_344837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_344878 : List Nat := [4, 1, 3, 2, 1, 1, 1, 1, 6]
def baseStart_344878 : Nat := 118140960795 + 344878 * 2 ^ 59
def prefixEnd_344878 : Nat := 4983230072969 + 3 ^ 40 * 344878 * 2
def baseEnd_344878 : Nat := 157411716587917241723503

theorem tailTrace_344878 : CollatzResearch.WordTrace tailWord_344878 prefixEnd_344878 157411716587917241723503 := by
  unfold tailWord_344878
  simp only [CollatzResearch.WordTrace]
  refine ⟨1572341755571672664775411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8385822696382254212135525 1572341755571672664775411)
  ·
    refine ⟨2358512633357508997163117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1572341755571672664775411 2358512633357508997163117)
    ·
      refine ⟨884442237509065873936169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2358512633357508997163117 884442237509065873936169)
      ·
        refine ⟨663331678131799405452127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 884442237509065873936169 663331678131799405452127)
        ·
          refine ⟨994997517197699108178191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 663331678131799405452127 994997517197699108178191)
          ·
            refine ⟨1492496275796548662267287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 994997517197699108178191 1492496275796548662267287)
            ·
              refine ⟨2238744413694822993400931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1492496275796548662267287 2238744413694822993400931)
              ·
                refine ⟨3358116620542234490101397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2238744413694822993400931 3358116620542234490101397)
                ·
                  refine ⟨157411716587917241723503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3358116620542234490101397 157411716587917241723503)
                  ·
                    rfl

theorem cell20_344878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 1, 1, 6].length) (baseStart_344878 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_344878 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_344878 prefixEnd_344878 := by exact prefixLift 344878
  have htrace : WordTrace (prefixWord ++ tailWord_344878) baseStart_344878 baseEnd_344878 := by
    simpa [prefixWord, tailWord_344878, baseEnd_344878] using wordTrace_append hprefix tailTrace_344878
  have hstable : (prefixWord ++ tailWord_344878).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_344878).length < 2 ^ (prefixWord ++ tailWord_344878).sum := by decide
  have hdescent : baseEnd_344878 < baseStart_344878 := by decide
  rcases family_descends (prefixWord ++ tailWord_344878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_344895 : List Nat := [1, 1, 2, 2, 5, 2, 2, 3, 2]
def baseStart_344895 : Nat := 118140960795 + 344895 * 2 ^ 59
def prefixEnd_344895 : Nat := 4983230072969 + 3 ^ 40 * 344895 * 2
def baseEnd_344895 : Nat := 157419475851140738156767

theorem tailTrace_344895 : CollatzResearch.WordTrace tailWord_344895 prefixEnd_344895 157419475851140738156767 := by
  unfold tailWord_344895
  simp only [CollatzResearch.WordTrace]
  refine ⟨12579354085511793221572139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8386236057007862147714759 12579354085511793221572139)
  ·
    refine ⟨18869031128267689832358209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12579354085511793221572139 18869031128267689832358209)
    ·
      refine ⟨14151773346200767374268657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18869031128267689832358209 14151773346200767374268657)
      ·
        refine ⟨10613830009650575530701493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14151773346200767374268657 10613830009650575530701493)
        ·
          refine ⟨995046563404741456003265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 10613830009650575530701493 995046563404741456003265)
          ·
            refine ⟨746284922553556092002449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 995046563404741456003265 746284922553556092002449)
            ·
              refine ⟨559713691915167069001837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 746284922553556092002449 559713691915167069001837)
              ·
                refine ⟨209892634468187650875689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 559713691915167069001837 209892634468187650875689)
                ·
                  refine ⟨157419475851140738156767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 209892634468187650875689 157419475851140738156767)
                  ·
                    rfl

theorem cell20_344895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 2, 3, 2].length) (baseStart_344895 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_344895 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_344895 prefixEnd_344895 := by exact prefixLift 344895
  have htrace : WordTrace (prefixWord ++ tailWord_344895) baseStart_344895 baseEnd_344895 := by
    simpa [prefixWord, tailWord_344895, baseEnd_344895] using wordTrace_append hprefix tailTrace_344895
  have hstable : (prefixWord ++ tailWord_344895).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_344895).length < 2 ^ (prefixWord ++ tailWord_344895).sum := by decide
  have hdescent : baseEnd_344895 < baseStart_344895 := by decide
  rcases family_descends (prefixWord ++ tailWord_344895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_344950 : List Nat := [5, 1, 1, 3, 1, 1, 3, 3, 2]
def baseStart_344950 : Nat := 118140960795 + 344950 * 2 ^ 59
def prefixEnd_344950 : Nat := 4983230072969 + 3 ^ 40 * 344950 * 2
def baseEnd_344950 : Nat := 157444579349804991323209

theorem tailTrace_344950 : CollatzResearch.WordTrace tailWord_344950 prefixEnd_344950 157444579349804991323209 := by
  unfold tailWord_344950
  simp only [CollatzResearch.WordTrace]
  refine ⟨786335006269533600926519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 8387573400208358409882869 786335006269533600926519)
  ·
    refine ⟨1179502509404300401389779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 786335006269533600926519 1179502509404300401389779)
    ·
      refine ⟨1769253764106450602084669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1179502509404300401389779 1769253764106450602084669)
      ·
        refine ⟨663470161539918975781751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1769253764106450602084669 663470161539918975781751)
        ·
          refine ⟨995205242309878463672627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 663470161539918975781751 995205242309878463672627)
          ·
            refine ⟨1492807863464817695508941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 995205242309878463672627 1492807863464817695508941)
            ·
              refine ⟨559802948799306635815853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1492807863464817695508941 559802948799306635815853)
              ·
                refine ⟨209926105799739988430945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 559802948799306635815853 209926105799739988430945)
                ·
                  refine ⟨157444579349804991323209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 209926105799739988430945 157444579349804991323209)
                  ·
                    rfl

theorem cell20_344950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 3, 3, 2].length) (baseStart_344950 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_344950 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_344950 prefixEnd_344950 := by exact prefixLift 344950
  have htrace : WordTrace (prefixWord ++ tailWord_344950) baseStart_344950 baseEnd_344950 := by
    simpa [prefixWord, tailWord_344950, baseEnd_344950] using wordTrace_append hprefix tailTrace_344950
  have hstable : (prefixWord ++ tailWord_344950).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_344950).length < 2 ^ (prefixWord ++ tailWord_344950).sum := by decide
  have hdescent : baseEnd_344950 < baseStart_344950 := by decide
  rcases family_descends (prefixWord ++ tailWord_344950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_344968 : List Nat := [2, 1, 3, 3, 2, 1, 2, 1, 5]
def baseStart_344968 : Nat := 118140960795 + 344968 * 2 ^ 59
def prefixEnd_344968 : Nat := 4983230072969 + 3 ^ 40 * 344968 * 2
def baseEnd_344968 : Nat := 157452795040276928723135

theorem tailTrace_344968 : CollatzResearch.WordTrace tailWord_344968 prefixEnd_344968 157452795040276928723135 := by
  unfold tailWord_344968
  simp only [CollatzResearch.WordTrace]
  refine ⟨6291008307123663344489779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8388011076164884459319705 6291008307123663344489779)
  ·
    refine ⟨9436512460685495016734669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6291008307123663344489779 9436512460685495016734669)
    ·
      refine ⟨3538692172757060631275501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9436512460685495016734669 3538692172757060631275501)
      ·
        refine ⟨1327009564783897736728313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3538692172757060631275501 1327009564783897736728313)
        ·
          refine ⟨995257173587923302546235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1327009564783897736728313 995257173587923302546235)
          ·
            refine ⟨1492885760381884953819353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 995257173587923302546235 1492885760381884953819353)
            ·
              refine ⟨1119664320286413715364515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1492885760381884953819353 1119664320286413715364515)
              ·
                refine ⟨1679496480429620573046773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1119664320286413715364515 1679496480429620573046773)
                ·
                  refine ⟨157452795040276928723135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1679496480429620573046773 157452795040276928723135)
                  ·
                    rfl

theorem cell20_344968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 2, 1, 5].length) (baseStart_344968 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_344968 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_344968 prefixEnd_344968 := by exact prefixLift 344968
  have htrace : WordTrace (prefixWord ++ tailWord_344968) baseStart_344968 baseEnd_344968 := by
    simpa [prefixWord, tailWord_344968, baseEnd_344968] using wordTrace_append hprefix tailTrace_344968
  have hstable : (prefixWord ++ tailWord_344968).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_344968).length < 2 ^ (prefixWord ++ tailWord_344968).sum := by decide
  have hdescent : baseEnd_344968 < baseStart_344968 := by decide
  rcases family_descends (prefixWord ++ tailWord_344968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_344978 : List Nat := [3, 2, 3, 2, 2, 1, 2, 5]
def baseStart_344978 : Nat := 118140960795 + 344978 * 2 ^ 59
def prefixEnd_344978 : Nat := 4983230072969 + 3 ^ 40 * 344978 * 2
def baseEnd_344978 : Nat := 52485786437587112796587

theorem tailTrace_344978 : CollatzResearch.WordTrace tailWord_344978 prefixEnd_344978 52485786437587112796587 := by
  unfold tailWord_344978
  simp only [CollatzResearch.WordTrace]
  refine ⟨3145595336052774599210897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8388254229474065597895725 3145595336052774599210897)
  ·
    refine ⟨2359196502039580949408173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3145595336052774599210897 2359196502039580949408173)
    ·
      refine ⟨884698688264842856028065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2359196502039580949408173 884698688264842856028065)
      ·
        refine ⟨663524016198632142021049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 884698688264842856028065 663524016198632142021049)
        ·
          refine ⟨497643012148974106515787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 663524016198632142021049 497643012148974106515787)
          ·
            refine ⟨746464518223461159773681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 497643012148974106515787 746464518223461159773681)
            ·
              refine ⟨559848388667595869830261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 746464518223461159773681 559848388667595869830261)
              ·
                refine ⟨52485786437587112796587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 559848388667595869830261 52485786437587112796587)
                ·
                  rfl

theorem cell20_344978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 2, 5].length) (baseStart_344978 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_344978 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_344978 prefixEnd_344978 := by exact prefixLift 344978
  have htrace : WordTrace (prefixWord ++ tailWord_344978) baseStart_344978 baseEnd_344978 := by
    simpa [prefixWord, tailWord_344978, baseEnd_344978] using wordTrace_append hprefix tailTrace_344978
  have hstable : (prefixWord ++ tailWord_344978).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_344978).length < 2 ^ (prefixWord ++ tailWord_344978).sum := by decide
  have hdescent : baseEnd_344978 < baseStart_344978 := by decide
  rcases family_descends (prefixWord ++ tailWord_344978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_345072 : List Nat := [2, 1, 1, 1, 3, 2, 1, 1, 8]
def baseStart_345072 : Nat := 118140960795 + 345072 * 2 ^ 59
def prefixEnd_345072 : Nat := 4983230072969 + 3 ^ 40 * 345072 * 2
def baseEnd_345072 : Nat := 157500263474114789256043

theorem tailTrace_345072 : CollatzResearch.WordTrace tailWord_345072 prefixEnd_345072 157500263474114789256043 := by
  unfold tailWord_345072
  simp only [CollatzResearch.WordTrace]
  refine ⟨6292904902935276225382735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8390539870580368300510313 6292904902935276225382735)
  ·
    refine ⟨9439357354402914338074103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6292904902935276225382735 9439357354402914338074103)
    ·
      refine ⟨14159036031604371507111155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9439357354402914338074103 14159036031604371507111155)
      ·
        refine ⟨21238554047406557260666733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14159036031604371507111155 21238554047406557260666733)
        ·
          refine ⟨7964457767777458972750025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21238554047406557260666733 7964457767777458972750025)
          ·
            refine ⟨5973343325833094229562519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7964457767777458972750025 5973343325833094229562519)
            ·
              refine ⟨8960014988749641344343779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5973343325833094229562519 8960014988749641344343779)
              ·
                refine ⟨13440022483124462016515669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8960014988749641344343779 13440022483124462016515669)
                ·
                  refine ⟨157500263474114789256043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 13440022483124462016515669 157500263474114789256043)
                  ·
                    rfl

theorem cell20_345072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 1, 8].length) (baseStart_345072 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_345072 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_345072 prefixEnd_345072 := by exact prefixLift 345072
  have htrace : WordTrace (prefixWord ++ tailWord_345072) baseStart_345072 baseEnd_345072 := by
    simpa [prefixWord, tailWord_345072, baseEnd_345072] using wordTrace_append hprefix tailTrace_345072
  have hstable : (prefixWord ++ tailWord_345072).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_345072).length < 2 ^ (prefixWord ++ tailWord_345072).sum := by decide
  have hdescent : baseEnd_345072 < baseStart_345072 := by decide
  rcases family_descends (prefixWord ++ tailWord_345072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_345078 : List Nat := [5, 1, 1, 1, 3, 3, 1, 2, 3]
def baseStart_345078 : Nat := 118140960795 + 345078 * 2 ^ 59
def prefixEnd_345078 : Nat := 4983230072969 + 3 ^ 40 * 345078 * 2
def baseEnd_345078 : Nat := 157503002037605435056019

theorem tailTrace_345078 : CollatzResearch.WordTrace tailWord_345078 prefixEnd_345078 157503002037605435056019 := by
  unfold tailWord_345078
  simp only [CollatzResearch.WordTrace]
  refine ⟨786626790240550967217743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 8390685762565876983655925 786626790240550967217743)
  ·
    refine ⟨1179940185360826450826615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 786626790240550967217743 1179940185360826450826615)
    ·
      refine ⟨1769910278041239676239923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1179940185360826450826615 1769910278041239676239923)
      ·
        refine ⟨2654865417061859514359885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1769910278041239676239923 2654865417061859514359885)
        ·
          refine ⟨995574531398197317884957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2654865417061859514359885 995574531398197317884957)
          ·
            refine ⟨373340449274323994206859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 995574531398197317884957 373340449274323994206859)
            ·
              refine ⟨560010673911485991310289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 373340449274323994206859 560010673911485991310289)
              ·
                refine ⟨420008005433614493482717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 560010673911485991310289 420008005433614493482717)
                ·
                  refine ⟨157503002037605435056019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 420008005433614493482717 157503002037605435056019)
                  ·
                    rfl

theorem cell20_345078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 3, 1, 2, 3].length) (baseStart_345078 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_345078 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_345078 prefixEnd_345078 := by exact prefixLift 345078
  have htrace : WordTrace (prefixWord ++ tailWord_345078) baseStart_345078 baseEnd_345078 := by
    simpa [prefixWord, tailWord_345078, baseEnd_345078] using wordTrace_append hprefix tailTrace_345078
  have hstable : (prefixWord ++ tailWord_345078).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_345078).length < 2 ^ (prefixWord ++ tailWord_345078).sum := by decide
  have hdescent : baseEnd_345078 < baseStart_345078 := by decide
  rcases family_descends (prefixWord ++ tailWord_345078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_345089 : List Nat := [1, 2, 4, 1, 2, 2, 1, 3, 4]
def baseStart_345089 : Nat := 118140960795 + 345089 * 2 ^ 59
def prefixEnd_345089 : Nat := 4983230072969 + 3 ^ 40 * 345089 * 2
def baseEnd_345089 : Nat := 157508022737338285689307

theorem tailTrace_345089 : CollatzResearch.WordTrace tailWord_345089 prefixEnd_345089 157508022737338285689307 := by
  unfold tailWord_345089
  simp only [CollatzResearch.WordTrace]
  refine ⟨12586429846808964354134321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8390953231205976236089547 12586429846808964354134321)
  ·
    refine ⟨9439822385106723265600741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12586429846808964354134321 9439822385106723265600741)
    ·
      refine ⟨1769966697207510612300139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9439822385106723265600741 1769966697207510612300139)
      ·
        refine ⟨2654950045811265918450209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1769966697207510612300139 2654950045811265918450209)
        ·
          refine ⟨1991212534358449438837657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2654950045811265918450209 1991212534358449438837657)
          ·
            refine ⟨1493409400768837079128243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1991212534358449438837657 1493409400768837079128243)
            ·
              refine ⟨2240114101153255618692365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1493409400768837079128243 2240114101153255618692365)
              ·
                refine ⟨840042787932470857009637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2240114101153255618692365 840042787932470857009637)
                ·
                  refine ⟨157508022737338285689307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 840042787932470857009637 157508022737338285689307)
                  ·
                    rfl

theorem cell20_345089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 1, 3, 4].length) (baseStart_345089 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_345089 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_345089 prefixEnd_345089 := by exact prefixLift 345089
  have htrace : WordTrace (prefixWord ++ tailWord_345089) baseStart_345089 baseEnd_345089 := by
    simpa [prefixWord, tailWord_345089, baseEnd_345089] using wordTrace_append hprefix tailTrace_345089
  have hstable : (prefixWord ++ tailWord_345089).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_345089).length < 2 ^ (prefixWord ++ tailWord_345089).sum := by decide
  have hdescent : baseEnd_345089 < baseStart_345089 := by decide
  rcases family_descends (prefixWord ++ tailWord_345089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_345099 : List Nat := [1, 1, 1, 1, 6, 3, 3, 1, 3]
def baseStart_345099 : Nat := 118140960795 + 345099 * 2 ^ 59
def prefixEnd_345099 : Nat := 4983230072969 + 3 ^ 40 * 345099 * 2
def baseEnd_345099 : Nat := 157512587009822695355933

theorem tailTrace_345099 : CollatzResearch.WordTrace tailWord_345099 prefixEnd_345099 157512587009822695355933 := by
  unfold tailWord_345099
  simp only [CollatzResearch.WordTrace]
  refine ⟨12586794576772736061998351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8391196384515157374665567 12586794576772736061998351)
  ·
    refine ⟨18880191865159104092997527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12586794576772736061998351 18880191865159104092997527)
    ·
      refine ⟨28320287797738656139496291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18880191865159104092997527 28320287797738656139496291)
      ·
        refine ⟨42480431696607984209244437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28320287797738656139496291 42480431696607984209244437)
        ·
          refine ⟨1991270235778499259808333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 42480431696607984209244437 1991270235778499259808333)
          ·
            refine ⟨746726338416937222428125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1991270235778499259808333 746726338416937222428125)
            ·
              refine ⟨280022376906351458410547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 746726338416937222428125 280022376906351458410547)
              ·
                refine ⟨420033565359527187615821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 280022376906351458410547 420033565359527187615821)
                ·
                  refine ⟨157512587009822695355933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 420033565359527187615821 157512587009822695355933)
                  ·
                    rfl

theorem cell20_345099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 3, 1, 3].length) (baseStart_345099 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_345099 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_345099 prefixEnd_345099 := by exact prefixLift 345099
  have htrace : WordTrace (prefixWord ++ tailWord_345099) baseStart_345099 baseEnd_345099 := by
    simpa [prefixWord, tailWord_345099, baseEnd_345099] using wordTrace_append hprefix tailTrace_345099
  have hstable : (prefixWord ++ tailWord_345099).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_345099).length < 2 ^ (prefixWord ++ tailWord_345099).sum := by decide
  have hdescent : baseEnd_345099 < baseStart_345099 := by decide
  rcases family_descends (prefixWord ++ tailWord_345099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_345123 : List Nat := [1, 1, 1, 4, 3, 4, 1, 3, 2]
def baseStart_345123 : Nat := 118140960795 + 345123 * 2 ^ 59
def prefixEnd_345123 : Nat := 4983230072969 + 3 ^ 40 * 345123 * 2
def baseEnd_345123 : Nat := 157523541263785278555835

theorem tailTrace_345123 : CollatzResearch.WordTrace tailWord_345123 prefixEnd_345123 157523541263785278555835 := by
  unfold tailWord_345123
  simp only [CollatzResearch.WordTrace]
  refine ⟨12587669928685788160872023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8391779952457192107248015 12587669928685788160872023)
  ·
    refine ⟨18881504893028682241308035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12587669928685788160872023 18881504893028682241308035)
    ·
      refine ⟨28322257339543023361962053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18881504893028682241308035 28322257339543023361962053)
      ·
        refine ⟨5310423251164316880367885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28322257339543023361962053 5310423251164316880367885)
        ·
          refine ⟨1991408719186618830137957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5310423251164316880367885 1991408719186618830137957)
          ·
            refine ⟨373389134847491030650867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1991408719186618830137957 373389134847491030650867)
            ·
              refine ⟨560083702271236545976301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 373389134847491030650867 560083702271236545976301)
              ·
                refine ⟨210031388351713704741113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 560083702271236545976301 210031388351713704741113)
                ·
                  refine ⟨157523541263785278555835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 210031388351713704741113 157523541263785278555835)
                  ·
                    rfl

theorem cell20_345123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 4, 1, 3, 2].length) (baseStart_345123 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_345123 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_345123 prefixEnd_345123 := by exact prefixLift 345123
  have htrace : WordTrace (prefixWord ++ tailWord_345123) baseStart_345123 baseEnd_345123 := by
    simpa [prefixWord, tailWord_345123, baseEnd_345123] using wordTrace_append hprefix tailTrace_345123
  have hstable : (prefixWord ++ tailWord_345123).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_345123).length < 2 ^ (prefixWord ++ tailWord_345123).sum := by decide
  have hdescent : baseEnd_345123 < baseStart_345123 := by decide
  rcases family_descends (prefixWord ++ tailWord_345123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_345130 : List Nat := [3, 1, 4, 1, 4, 1, 6]
def baseStart_345130 : Nat := 118140960795 + 345130 * 2 ^ 59
def prefixEnd_345130 : Nat := 4983230072969 + 3 ^ 40 * 345130 * 2
def baseEnd_345130 : Nat := 17502970694947151702497

theorem tailTrace_345130 : CollatzResearch.WordTrace tailWord_345130 prefixEnd_345130 17502970694947151702497 := by
  unfold tailWord_345130
  simp only [CollatzResearch.WordTrace]
  refine ⟨3146981309915107089094211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8391950159773618904251229 3146981309915107089094211)
  ·
    refine ⟨4720471964872660633641317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3146981309915107089094211 4720471964872660633641317)
    ·
      refine ⟨885088493413623868807747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4720471964872660633641317 885088493413623868807747)
      ·
        refine ⟨1327632740120435803211621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 885088493413623868807747 1327632740120435803211621)
        ·
          refine ⟨248931138772581713102179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1327632740120435803211621 248931138772581713102179)
          ·
            refine ⟨373396708158872569653269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 248931138772581713102179 373396708158872569653269)
            ·
              refine ⟨17502970694947151702497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 373396708158872569653269 17502970694947151702497)
              ·
                rfl

theorem cell20_345130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 4, 1, 6].length) (baseStart_345130 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_345130 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_345130 prefixEnd_345130 := by exact prefixLift 345130
  have htrace : WordTrace (prefixWord ++ tailWord_345130) baseStart_345130 baseEnd_345130 := by
    simpa [prefixWord, tailWord_345130, baseEnd_345130] using wordTrace_append hprefix tailTrace_345130
  have hstable : (prefixWord ++ tailWord_345130).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_345130).length < 2 ^ (prefixWord ++ tailWord_345130).sum := by decide
  have hdescent : baseEnd_345130 < baseStart_345130 := by decide
  rcases family_descends (prefixWord ++ tailWord_345130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_345144 : List Nat := [2, 1, 2, 1, 5, 3, 1, 1, 4]
def baseStart_345144 : Nat := 118140960795 + 345144 * 2 ^ 59
def prefixEnd_345144 : Nat := 4983230072969 + 3 ^ 40 * 345144 * 2
def baseEnd_345144 : Nat := 157533126236002538855749

theorem tailTrace_345144 : CollatzResearch.WordTrace tailWord_345144 prefixEnd_345144 157533126236002538855749 := by
  unfold tailWord_345144
  simp only [CollatzResearch.WordTrace]
  refine ⟨6294217930804854373693243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8392290574406472498257657 6294217930804854373693243)
  ·
    refine ⟨9441326896207281560539865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6294217930804854373693243 9441326896207281560539865)
    ·
      refine ⟨7080995172155461170404899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9441326896207281560539865 7080995172155461170404899)
      ·
        refine ⟨10621492758233191755607349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7080995172155461170404899 10621492758233191755607349)
        ·
          refine ⟨995764946084361727088189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 10621492758233191755607349 995764946084361727088189)
          ·
            refine ⟨373411854781635647658071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 995764946084361727088189 373411854781635647658071)
            ·
              refine ⟨560117782172453471487107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 373411854781635647658071 560117782172453471487107)
              ·
                refine ⟨840176673258680207230661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 560117782172453471487107 840176673258680207230661)
                ·
                  refine ⟨157533126236002538855749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 840176673258680207230661 157533126236002538855749)
                  ·
                    rfl

theorem cell20_345144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 3, 1, 1, 4].length) (baseStart_345144 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_345144 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_345144 prefixEnd_345144 := by exact prefixLift 345144
  have htrace : WordTrace (prefixWord ++ tailWord_345144) baseStart_345144 baseEnd_345144 := by
    simpa [prefixWord, tailWord_345144, baseEnd_345144] using wordTrace_append hprefix tailTrace_345144
  have hstable : (prefixWord ++ tailWord_345144).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_345144).length < 2 ^ (prefixWord ++ tailWord_345144).sum := by decide
  have hdescent : baseEnd_345144 < baseStart_345144 := by decide
  rcases family_descends (prefixWord ++ tailWord_345144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_345172 : List Nat := [2, 4, 1, 1, 1, 1, 4, 6]
def baseStart_345172 : Nat := 118140960795 + 345172 * 2 ^ 59
def prefixEnd_345172 : Nat := 4983230072969 + 3 ^ 40 * 345172 * 2
def baseEnd_345172 : Nat := 52515302066319628640767

theorem tailTrace_345172 : CollatzResearch.WordTrace tailWord_345172 prefixEnd_345172 52515302066319628640767 := by
  unfold tailWord_345172
  simp only [CollatzResearch.WordTrace]
  refine ⟨6294728552754134764702885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8392971403672179686270513 6294728552754134764702885)
  ·
    refine ⟨1180261603641400268381791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6294728552754134764702885 1180261603641400268381791)
    ·
      refine ⟨1770392405462100402572687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1180261603641400268381791 1770392405462100402572687)
      ·
        refine ⟨2655588608193150603859031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1770392405462100402572687 2655588608193150603859031)
        ·
          refine ⟨3983382912289725905788547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2655588608193150603859031 3983382912289725905788547)
          ·
            refine ⟨5975074368434588858682821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3983382912289725905788547 5975074368434588858682821)
            ·
              refine ⟨1120326444081485411003029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5975074368434588858682821 1120326444081485411003029)
              ·
                refine ⟨52515302066319628640767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1120326444081485411003029 52515302066319628640767)
                ·
                  rfl

theorem cell20_345172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 4, 6].length) (baseStart_345172 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_345172 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_345172 prefixEnd_345172 := by exact prefixLift 345172
  have htrace : WordTrace (prefixWord ++ tailWord_345172) baseStart_345172 baseEnd_345172 := by
    simpa [prefixWord, tailWord_345172, baseEnd_345172] using wordTrace_append hprefix tailTrace_345172
  have hstable : (prefixWord ++ tailWord_345172).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_345172).length < 2 ^ (prefixWord ++ tailWord_345172).sum := by decide
  have hdescent : baseEnd_345172 < baseStart_345172 := by decide
  rcases family_descends (prefixWord ++ tailWord_345172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_345192 : List Nat := [2, 1, 4, 4, 1, 1, 2, 2, 3]
def baseStart_345192 : Nat := 118140960795 + 345192 * 2 ^ 59
def prefixEnd_345192 : Nat := 4983230072969 + 3 ^ 40 * 345192 * 2
def baseEnd_345192 : Nat := 157555034743927705255553

theorem tailTrace_345192 : CollatzResearch.WordTrace tailWord_345192 prefixEnd_345192 157555034743927705255553 := by
  unfold tailWord_345192
  simp only [CollatzResearch.WordTrace]
  refine ⟨6295093282717906472566915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8393457710290541963422553 6295093282717906472566915)
  ·
    refine ⟨9442639924076859708850373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6295093282717906472566915 9442639924076859708850373)
    ·
      refine ⟨1770494985764411195409445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9442639924076859708850373 1770494985764411195409445)
      ·
        refine ⟨331967809830827099139271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1770494985764411195409445 331967809830827099139271)
        ·
          refine ⟨497951714746240648708907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 331967809830827099139271 497951714746240648708907)
          ·
            refine ⟨746927572119360973063361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 497951714746240648708907 746927572119360973063361)
            ·
              refine ⟨560195679089520729797521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 746927572119360973063361 560195679089520729797521)
              ·
                refine ⟨420146759317140547348141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 560195679089520729797521 420146759317140547348141)
                ·
                  refine ⟨157555034743927705255553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 420146759317140547348141 157555034743927705255553)
                  ·
                    rfl

theorem cell20_345192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 2, 2, 3].length) (baseStart_345192 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_345192 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_345192 prefixEnd_345192 := by exact prefixLift 345192
  have htrace : WordTrace (prefixWord ++ tailWord_345192) baseStart_345192 baseEnd_345192 := by
    simpa [prefixWord, tailWord_345192, baseEnd_345192] using wordTrace_append hprefix tailTrace_345192
  have hstable : (prefixWord ++ tailWord_345192).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_345192).length < 2 ^ (prefixWord ++ tailWord_345192).sum := by decide
  have hdescent : baseEnd_345192 < baseStart_345192 := by decide
  rcases family_descends (prefixWord ++ tailWord_345192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_345193 : List Nat := [1, 2, 1, 1, 1, 14]
def baseStart_345193 : Nat := 118140960795 + 345193 * 2 ^ 59
def prefixEnd_345193 : Nat := 4983230072969 + 3 ^ 40 * 345193 * 2
def baseEnd_345193 : Nat := 5835388561895412823045

theorem tailTrace_345193 : CollatzResearch.WordTrace tailWord_345193 prefixEnd_345193 5835388561895412823045 := by
  unfold tailWord_345193
  simp only [CollatzResearch.WordTrace]
  refine ⟨12590223038432190115920233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8393482025621460077280155 12590223038432190115920233)
  ·
    refine ⟨9442667278824142586940175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12590223038432190115920233 9442667278824142586940175)
    ·
      refine ⟨14164000918236213880410263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9442667278824142586940175 14164000918236213880410263)
      ·
        refine ⟨21246001377354320820615395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14164000918236213880410263 21246001377354320820615395)
        ·
          refine ⟨31869002066031481230923093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21246001377354320820615395 31869002066031481230923093)
          ·
            refine ⟨5835388561895412823045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 14 31869002066031481230923093 5835388561895412823045)
            ·
              rfl

theorem cell20_345193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 14].length) (baseStart_345193 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_345193 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_345193 prefixEnd_345193 := by exact prefixLift 345193
  have htrace : WordTrace (prefixWord ++ tailWord_345193) baseStart_345193 baseEnd_345193 := by
    simpa [prefixWord, tailWord_345193, baseEnd_345193] using wordTrace_append hprefix tailTrace_345193
  have hstable : (prefixWord ++ tailWord_345193).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_345193).length < 2 ^ (prefixWord ++ tailWord_345193).sum := by decide
  have hdescent : baseEnd_345193 < baseStart_345193 := by decide
  rcases family_descends (prefixWord ++ tailWord_345193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_345196 : List Nat := [2, 2, 1, 1, 3, 2, 4, 2, 3]
def baseStart_345196 : Nat := 118140960795 + 345196 * 2 ^ 59
def prefixEnd_345196 : Nat := 4983230072969 + 3 ^ 40 * 345196 * 2
def baseEnd_345196 : Nat := 157556860452921469122203

theorem tailTrace_345196 : CollatzResearch.WordTrace tailWord_345196 prefixEnd_345196 157556860452921469122203 := by
  unfold tailWord_345196
  simp only [CollatzResearch.WordTrace]
  refine ⟨6295166228710660814139721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8393554971614214418852961 6295166228710660814139721)
  ·
    refine ⟨4721374671532995610604791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6295166228710660814139721 4721374671532995610604791)
    ·
      refine ⟨7082062007299493415907187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4721374671532995610604791 7082062007299493415907187)
      ·
        refine ⟨10623093010949240123860781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7082062007299493415907187 10623093010949240123860781)
        ·
          refine ⟨3983659879105965046447793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10623093010949240123860781 3983659879105965046447793)
          ·
            refine ⟨2987744909329473784835845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3983659879105965046447793 2987744909329473784835845)
            ·
              refine ⟨560202170499276334656721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2987744909329473784835845 560202170499276334656721)
              ·
                refine ⟨420151627874457250992541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 560202170499276334656721 420151627874457250992541)
                ·
                  refine ⟨157556860452921469122203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 420151627874457250992541 157556860452921469122203)
                  ·
                    rfl

theorem cell20_345196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 3].length) (baseStart_345196 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_345196 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_345196 prefixEnd_345196 := by exact prefixLift 345196
  have htrace : WordTrace (prefixWord ++ tailWord_345196) baseStart_345196 baseEnd_345196 := by
    simpa [prefixWord, tailWord_345196, baseEnd_345196] using wordTrace_append hprefix tailTrace_345196
  have hstable : (prefixWord ++ tailWord_345196).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_345196).length < 2 ^ (prefixWord ++ tailWord_345196).sum := by decide
  have hdescent : baseEnd_345196 < baseStart_345196 := by decide
  rcases family_descends (prefixWord ++ tailWord_345196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_345258 : List Nat := [3, 1, 5, 1, 1, 1, 1, 3, 4]
def baseStart_345258 : Nat := 118140960795 + 345258 * 2 ^ 59
def prefixEnd_345258 : Nat := 4983230072969 + 3 ^ 40 * 345258 * 2
def baseEnd_345258 : Nat := 157585158942324809055283

theorem tailTrace_345258 : CollatzResearch.WordTrace tailWord_345258 prefixEnd_345258 157585158942324809055283 := by
  unfold tailWord_345258
  simp only [CollatzResearch.WordTrace]
  refine ⟨3148148445799176554259107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8395062522131137478024285 3148148445799176554259107)
  ·
    refine ⟨4722222668698764831388661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3148148445799176554259107 4722222668698764831388661)
    ·
      refine ⟨442708375190509202942687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4722222668698764831388661 442708375190509202942687)
      ·
        refine ⟨664062562785763804414031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 442708375190509202942687 664062562785763804414031)
        ·
          refine ⟨996093844178645706621047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 664062562785763804414031 996093844178645706621047)
          ·
            refine ⟨1494140766267968559931571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 996093844178645706621047 1494140766267968559931571)
            ·
              refine ⟨2241211149401952839897357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1494140766267968559931571 2241211149401952839897357)
              ·
                refine ⟨840454181025732314961509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2241211149401952839897357 840454181025732314961509)
                ·
                  refine ⟨157585158942324809055283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 840454181025732314961509 157585158942324809055283)
                  ·
                    rfl

theorem cell20_345258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 1, 3, 4].length) (baseStart_345258 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_345258 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_345258 prefixEnd_345258 := by exact prefixLift 345258
  have htrace : WordTrace (prefixWord ++ tailWord_345258) baseStart_345258 baseEnd_345258 := by
    simpa [prefixWord, tailWord_345258, baseEnd_345258] using wordTrace_append hprefix tailTrace_345258
  have hstable : (prefixWord ++ tailWord_345258).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_345258).length < 2 ^ (prefixWord ++ tailWord_345258).sum := by decide
  have hdescent : baseEnd_345258 < baseStart_345258 := by decide
  rcases family_descends (prefixWord ++ tailWord_345258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_345313 : List Nat := [1, 2, 3, 1, 3, 3, 3, 2, 2]
def baseStart_345313 : Nat := 118140960795 + 345313 * 2 ^ 59
def prefixEnd_345313 : Nat := 4983230072969 + 3 ^ 40 * 345313 * 2
def baseEnd_345313 : Nat := 157610262440989062221725

theorem tailTrace_345313 : CollatzResearch.WordTrace tailWord_345313 prefixEnd_345313 157610262440989062221725 := by
  unfold tailWord_345313
  simp only [CollatzResearch.WordTrace]
  refine ⟨12594599797997450610288593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8396399865331633740192395 12594599797997450610288593)
  ·
    refine ⟨9445949848498087957716445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12594599797997450610288593 9445949848498087957716445)
    ·
      refine ⟨3542231193186782984143667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9445949848498087957716445 3542231193186782984143667)
      ·
        refine ⟨5313346789780174476215501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3542231193186782984143667 5313346789780174476215501)
        ·
          refine ⟨1992505046167565428580813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5313346789780174476215501 1992505046167565428580813)
          ·
            refine ⟨747189392312837035717805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1992505046167565428580813 747189392312837035717805)
            ·
              refine ⟨280196022117313888394177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 747189392312837035717805 280196022117313888394177)
              ·
                refine ⟨210147016587985416295633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 280196022117313888394177 210147016587985416295633)
                ·
                  refine ⟨157610262440989062221725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 210147016587985416295633 157610262440989062221725)
                  ·
                    rfl

theorem cell20_345313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 3, 2, 2].length) (baseStart_345313 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_345313 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_345313 prefixEnd_345313 := by exact prefixLift 345313
  have htrace : WordTrace (prefixWord ++ tailWord_345313) baseStart_345313 baseEnd_345313 := by
    simpa [prefixWord, tailWord_345313, baseEnd_345313] using wordTrace_append hprefix tailTrace_345313
  have hstable : (prefixWord ++ tailWord_345313).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_345313).length < 2 ^ (prefixWord ++ tailWord_345313).sum := by decide
  have hdescent : baseEnd_345313 < baseStart_345313 := by decide
  rcases family_descends (prefixWord ++ tailWord_345313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_345324 : List Nat := [2, 2, 1, 1, 2, 5, 2, 5]
def baseStart_345324 : Nat := 118140960795 + 345324 * 2 ^ 59
def prefixEnd_345324 : Nat := 4983230072969 + 3 ^ 40 * 345324 * 2
def baseEnd_345324 : Nat := 52538427713573970951671

theorem tailTrace_345324 : CollatzResearch.WordTrace tailWord_345324 prefixEnd_345324 52538427713573970951671 := by
  unfold tailWord_345324
  simp only [CollatzResearch.WordTrace]
  refine ⟨6297500500478799744469513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8396667333971732992626017 6297500500478799744469513)
  ·
    refine ⟨4723125375359099808352135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6297500500478799744469513 4723125375359099808352135)
    ·
      refine ⟨7084688063038649712528203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4723125375359099808352135 7084688063038649712528203)
      ·
        refine ⟨10627032094557974568792305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7084688063038649712528203 10627032094557974568792305)
        ·
          refine ⟨7970274070918480926594229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10627032094557974568792305 7970274070918480926594229)
          ·
            refine ⟨747213194148607586868209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 7970274070918480926594229 747213194148607586868209)
            ·
              refine ⟨560409895611455690151157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 747213194148607586868209 560409895611455690151157)
              ·
                refine ⟨52538427713573970951671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 560409895611455690151157 52538427713573970951671)
                ·
                  rfl

theorem cell20_345324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 2, 5].length) (baseStart_345324 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_345324 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_345324 prefixEnd_345324 := by exact prefixLift 345324
  have htrace : WordTrace (prefixWord ++ tailWord_345324) baseStart_345324 baseEnd_345324 := by
    simpa [prefixWord, tailWord_345324, baseEnd_345324] using wordTrace_append hprefix tailTrace_345324
  have hstable : (prefixWord ++ tailWord_345324).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_345324).length < 2 ^ (prefixWord ++ tailWord_345324).sum := by decide
  have hdescent : baseEnd_345324 < baseStart_345324 := by decide
  rcases family_descends (prefixWord ++ tailWord_345324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_345338 : List Nat := [3, 1, 1, 1, 1, 4, 2, 1, 6]
def baseStart_345338 : Nat := 118140960795 + 345338 * 2 ^ 59
def prefixEnd_345338 : Nat := 4983230072969 + 3 ^ 40 * 345338 * 2
def baseEnd_345338 : Nat := 157621673122200086388289

theorem tailTrace_345338 : CollatzResearch.WordTrace tailWord_345338 prefixEnd_345338 157621673122200086388289 := by
  unfold tailWord_345338
  simp only [CollatzResearch.WordTrace]
  refine ⟨3148877905726719969987167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8397007748604586586632445 3148877905726719969987167)
  ·
    refine ⟨4723316858590079954980751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3148877905726719969987167 4723316858590079954980751)
    ·
      refine ⟨7084975287885119932471127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4723316858590079954980751 7084975287885119932471127)
      ·
        refine ⟨10627462931827679898706691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7084975287885119932471127 10627462931827679898706691)
        ·
          refine ⟨15941194397741519848060037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10627462931827679898706691 15941194397741519848060037)
          ·
            refine ⟨2988973949576534971511257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15941194397741519848060037 2988973949576534971511257)
            ·
              refine ⟨2241730462182401228633443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2988973949576534971511257 2241730462182401228633443)
              ·
                refine ⟨3362595693273601842950165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2241730462182401228633443 3362595693273601842950165)
                ·
                  refine ⟨157621673122200086388289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3362595693273601842950165 157621673122200086388289)
                  ·
                    rfl

theorem cell20_345338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 2, 1, 6].length) (baseStart_345338 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_345338 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_345338 prefixEnd_345338 := by exact prefixLift 345338
  have htrace : WordTrace (prefixWord ++ tailWord_345338) baseStart_345338 baseEnd_345338 := by
    simpa [prefixWord, tailWord_345338, baseEnd_345338] using wordTrace_append hprefix tailTrace_345338
  have hstable : (prefixWord ++ tailWord_345338).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_345338).length < 2 ^ (prefixWord ++ tailWord_345338).sum := by decide
  have hdescent : baseEnd_345338 < baseStart_345338 := by decide
  rcases family_descends (prefixWord ++ tailWord_345338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_345393 : List Nat := [1, 2, 2, 3, 3, 2, 1, 2, 4]
def baseStart_345393 : Nat := 118140960795 + 345393 * 2 ^ 59
def prefixEnd_345393 : Nat := 4983230072969 + 3 ^ 40 * 345393 * 2
def baseEnd_345393 : Nat := 157646776620864339554731

theorem tailTrace_345393 : CollatzResearch.WordTrace tailWord_345393 prefixEnd_345393 157646776620864339554731 := by
  unfold tailWord_345393
  simp only [CollatzResearch.WordTrace]
  refine ⟨12597517637707624273200833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8398345091805082848800555 12597517637707624273200833)
  ·
    refine ⟨9448138228280718204900625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12597517637707624273200833 9448138228280718204900625)
    ·
      refine ⟨7086103671210538653675469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9448138228280718204900625 7086103671210538653675469)
      ·
        refine ⟨2657288876703951995128301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7086103671210538653675469 2657288876703951995128301)
        ·
          refine ⟨996483328763981998173113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2657288876703951995128301 996483328763981998173113)
          ·
            refine ⟨747362496572986498629835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 996483328763981998173113 747362496572986498629835)
            ·
              refine ⟨1121043744859479747944753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 747362496572986498629835 1121043744859479747944753)
              ·
                refine ⟨840782808644609810958565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1121043744859479747944753 840782808644609810958565)
                ·
                  refine ⟨157646776620864339554731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 840782808644609810958565 157646776620864339554731)
                  ·
                    rfl

theorem cell20_345393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 1, 2, 4].length) (baseStart_345393 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_345393 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_345393 prefixEnd_345393 := by exact prefixLift 345393
  have htrace : WordTrace (prefixWord ++ tailWord_345393) baseStart_345393 baseEnd_345393 := by
    simpa [prefixWord, tailWord_345393, baseEnd_345393] using wordTrace_append hprefix tailTrace_345393
  have hstable : (prefixWord ++ tailWord_345393).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_345393).length < 2 ^ (prefixWord ++ tailWord_345393).sum := by decide
  have hdescent : baseEnd_345393 < baseStart_345393 := by decide
  rcases family_descends (prefixWord ++ tailWord_345393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_345431 : List Nat := [1, 1, 3, 2, 3, 3, 2, 1, 4]
def baseStart_345431 : Nat := 118140960795 + 345431 * 2 ^ 59
def prefixEnd_345431 : Nat := 4983230072969 + 3 ^ 40 * 345431 * 2
def baseEnd_345431 : Nat := 157664120856305096287909

theorem tailTrace_345431 : CollatzResearch.WordTrace tailWord_345431 prefixEnd_345431 157664120856305096287909 := by
  unfold tailWord_345431
  simp only [CollatzResearch.WordTrace]
  refine ⟨12598903611569956763084147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8399269074379971175389431 12598903611569956763084147)
  ·
    refine ⟨18898355417354935144626221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12598903611569956763084147 18898355417354935144626221)
    ·
      refine ⟨7086883281508100679234833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18898355417354935144626221 7086883281508100679234833)
      ·
        refine ⟨5315162461131075509426125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7086883281508100679234833 5315162461131075509426125)
        ·
          refine ⟨1993185922924153316034797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5315162461131075509426125 1993185922924153316034797)
          ·
            refine ⟨747444721096557493513049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1993185922924153316034797 747444721096557493513049)
            ·
              refine ⟨560583540822418120134787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 747444721096557493513049 560583540822418120134787)
              ·
                refine ⟨840875311233627180202181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 560583540822418120134787 840875311233627180202181)
                ·
                  refine ⟨157664120856305096287909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 840875311233627180202181 157664120856305096287909)
                  ·
                    rfl

theorem cell20_345431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 2, 1, 4].length) (baseStart_345431 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_345431 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_345431 prefixEnd_345431 := by exact prefixLift 345431
  have htrace : WordTrace (prefixWord ++ tailWord_345431) baseStart_345431 baseEnd_345431 := by
    simpa [prefixWord, tailWord_345431, baseEnd_345431] using wordTrace_append hprefix tailTrace_345431
  have hstable : (prefixWord ++ tailWord_345431).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_345431).length < 2 ^ (prefixWord ++ tailWord_345431).sum := by decide
  have hdescent : baseEnd_345431 < baseStart_345431 := by decide
  rcases family_descends (prefixWord ++ tailWord_345431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_345476 : List Nat := [2, 3, 2, 1, 1, 5, 6]
def baseStart_345476 : Nat := 118140960795 + 345476 * 2 ^ 59
def prefixEnd_345476 : Nat := 4983230072969 + 3 ^ 40 * 345476 * 2
def baseEnd_345476 : Nat := 17520517786942771087525

theorem tailTrace_345476 : CollatzResearch.WordTrace tailWord_345476 prefixEnd_345476 17520517786942771087525 := by
  unfold tailWord_345476
  simp only [CollatzResearch.WordTrace]
  refine ⟨6300272448203464724236141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8400363264271286298981521 6300272448203464724236141)
  ·
    refine ⟨2362602168076299271588553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6300272448203464724236141 2362602168076299271588553)
    ·
      refine ⟨1771951626057224453691415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2362602168076299271588553 1771951626057224453691415)
      ·
        refine ⟨2657927439085836680537123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1771951626057224453691415 2657927439085836680537123)
        ·
          refine ⟨3986891158628755020805685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2657927439085836680537123 3986891158628755020805685)
          ·
            refine ⟨373771046121445783200533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3986891158628755020805685 373771046121445783200533)
            ·
              refine ⟨17520517786942771087525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 373771046121445783200533 17520517786942771087525)
              ·
                rfl

theorem cell20_345476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 5, 6].length) (baseStart_345476 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_345476 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_345476 prefixEnd_345476 := by exact prefixLift 345476
  have htrace : WordTrace (prefixWord ++ tailWord_345476) baseStart_345476 baseEnd_345476 := by
    simpa [prefixWord, tailWord_345476, baseEnd_345476] using wordTrace_append hprefix tailTrace_345476
  have hstable : (prefixWord ++ tailWord_345476).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_345476).length < 2 ^ (prefixWord ++ tailWord_345476).sum := by decide
  have hdescent : baseEnd_345476 < baseStart_345476 := by decide
  rcases family_descends (prefixWord ++ tailWord_345476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_345483 : List Nat := [1, 1, 1, 1, 4, 3, 2, 4, 3]
def baseStart_345483 : Nat := 118140960795 + 345483 * 2 ^ 59
def prefixEnd_345483 : Nat := 4983230072969 + 3 ^ 40 * 345483 * 2
def baseEnd_345483 : Nat := 157687855073224026554363

theorem tailTrace_345483 : CollatzResearch.WordTrace tailWord_345483 prefixEnd_345483 157687855073224026554363 := by
  unfold tailWord_345483
  simp only [CollatzResearch.WordTrace]
  refine ⟨12600800207381569643977103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8400533471587713095984735 12600800207381569643977103)
  ·
    refine ⟨18901200311072354465965655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12600800207381569643977103 18901200311072354465965655)
    ·
      refine ⟨28351800466608531698948483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18901200311072354465965655 28351800466608531698948483)
      ·
        refine ⟨42527700699912797548422725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28351800466608531698948483 42527700699912797548422725)
        ·
          refine ⟨7973943881233649540329261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 42527700699912797548422725 7973943881233649540329261)
          ·
            refine ⟨2990228955462618577623473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7973943881233649540329261 2990228955462618577623473)
            ·
              refine ⟨2242671716596963933217605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2990228955462618577623473 2242671716596963933217605)
              ·
                refine ⟨420500946861930737478301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2242671716596963933217605 420500946861930737478301)
                ·
                  refine ⟨157687855073224026554363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 420500946861930737478301 157687855073224026554363)
                  ·
                    rfl

theorem cell20_345483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 2, 4, 3].length) (baseStart_345483 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_345483 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_345483 prefixEnd_345483 := by exact prefixLift 345483
  have htrace : WordTrace (prefixWord ++ tailWord_345483) baseStart_345483 baseEnd_345483 := by
    simpa [prefixWord, tailWord_345483, baseEnd_345483] using wordTrace_append hprefix tailTrace_345483
  have hstable : (prefixWord ++ tailWord_345483).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_345483).length < 2 ^ (prefixWord ++ tailWord_345483).sum := by decide
  have hdescent : baseEnd_345483 < baseStart_345483 := by decide
  rcases family_descends (prefixWord ++ tailWord_345483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_345496 : List Nat := [2, 1, 2, 5, 2, 2, 2, 1, 3]
def baseStart_345496 : Nat := 118140960795 + 345496 * 2 ^ 59
def prefixEnd_345496 : Nat := 4983230072969 + 3 ^ 40 * 345496 * 2
def baseEnd_345496 : Nat := 157693788627453759120977

theorem tailTrace_345496 : CollatzResearch.WordTrace tailWord_345496 prefixEnd_345496 157693788627453759120977 := by
  unfold tailWord_345496
  simp only [CollatzResearch.WordTrace]
  refine ⟨6300637178167236432100171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8400849570889648576133561 6300637178167236432100171)
  ·
    refine ⟨9450955767250854648150257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6300637178167236432100171 9450955767250854648150257)
    ·
      refine ⟨7088216825438140986112693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9450955767250854648150257 7088216825438140986112693)
      ·
        refine ⟨664520327384825717448065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 7088216825438140986112693 664520327384825717448065)
        ·
          refine ⟨498390245538619288086049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 664520327384825717448065 498390245538619288086049)
          ·
            refine ⟨373792684153964466064537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 498390245538619288086049 373792684153964466064537)
            ·
              refine ⟨280344513115473349548403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 373792684153964466064537 280344513115473349548403)
              ·
                refine ⟨420516769673210024322605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 280344513115473349548403 420516769673210024322605)
                ·
                  refine ⟨157693788627453759120977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 420516769673210024322605 157693788627453759120977)
                  ·
                    rfl

theorem cell20_345496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 2, 2, 1, 3].length) (baseStart_345496 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_345496 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_345496 prefixEnd_345496 := by exact prefixLift 345496
  have htrace : WordTrace (prefixWord ++ tailWord_345496) baseStart_345496 baseEnd_345496 := by
    simpa [prefixWord, tailWord_345496, baseEnd_345496] using wordTrace_append hprefix tailTrace_345496
  have hstable : (prefixWord ++ tailWord_345496).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_345496).length < 2 ^ (prefixWord ++ tailWord_345496).sum := by decide
  have hdescent : baseEnd_345496 < baseStart_345496 := by decide
  rcases family_descends (prefixWord ++ tailWord_345496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_345497 : List Nat := [1, 2, 1, 2, 1, 5, 1, 7]
def baseStart_345497 : Nat := 118140960795 + 345497 * 2 ^ 59
def prefixEnd_345497 : Nat := 4983230072969 + 3 ^ 40 * 345497 * 2
def baseEnd_345497 : Nat := 52564748351567400029213

theorem tailTrace_345497 : CollatzResearch.WordTrace tailWord_345497 prefixEnd_345497 52564748351567400029213 := by
  unfold tailWord_345497
  simp only [CollatzResearch.WordTrace]
  refine ⟨12601310829330850034986745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8400873886220566689991163 12601310829330850034986745)
  ·
    refine ⟨9450983121998137526240059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12601310829330850034986745 9450983121998137526240059)
    ·
      refine ⟨14176474682997206289360089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9450983121998137526240059 14176474682997206289360089)
      ·
        refine ⟨10632356012247904717020067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14176474682997206289360089 10632356012247904717020067)
        ·
          refine ⟨15948534018371857075530101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10632356012247904717020067 15948534018371857075530101)
          ·
            refine ⟨1495175064222361600830947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 15948534018371857075530101 1495175064222361600830947)
            ·
              refine ⟨2242762596333542401246421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1495175064222361600830947 2242762596333542401246421)
              ·
                refine ⟨52564748351567400029213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2242762596333542401246421 52564748351567400029213)
                ·
                  rfl

theorem cell20_345497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 1, 7].length) (baseStart_345497 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_345497 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_345497 prefixEnd_345497 := by exact prefixLift 345497
  have htrace : WordTrace (prefixWord ++ tailWord_345497) baseStart_345497 baseEnd_345497 := by
    simpa [prefixWord, tailWord_345497, baseEnd_345497] using wordTrace_append hprefix tailTrace_345497
  have hstable : (prefixWord ++ tailWord_345497).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_345497).length < 2 ^ (prefixWord ++ tailWord_345497).sum := by decide
  have hdescent : baseEnd_345497 < baseStart_345497 := by decide
  rcases family_descends (prefixWord ++ tailWord_345497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_345583 : List Nat := [1, 1, 2, 1, 4, 1, 3, 5, 2]
def baseStart_345583 : Nat := 118140960795 + 345583 * 2 ^ 59
def prefixEnd_345583 : Nat := 4983230072969 + 3 ^ 40 * 345583 * 2
def baseEnd_345583 : Nat := 157733497798068123220621

theorem tailTrace_345583 : CollatzResearch.WordTrace tailWord_345583 prefixEnd_345583 157733497798068123220621 := by
  unfold tailWord_345583
  simp only [CollatzResearch.WordTrace]
  refine ⟨12604447507019286722617403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8402965004679524481744935 12604447507019286722617403)
  ·
    refine ⟨18906671260528930083926105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12604447507019286722617403 18906671260528930083926105)
    ·
      refine ⟨14180003445396697562944579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18906671260528930083926105 14180003445396697562944579)
      ·
        refine ⟨21270005168095046344416869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14180003445396697562944579 21270005168095046344416869)
        ·
          refine ⟨3988125969017821189578163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21270005168095046344416869 3988125969017821189578163)
          ·
            refine ⟨5982188953526731784367245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3988125969017821189578163 5982188953526731784367245)
            ·
              refine ⟨2243320857572524419137717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5982188953526731784367245 2243320857572524419137717)
              ·
                refine ⟨210311330397424164294161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2243320857572524419137717 210311330397424164294161)
                ·
                  refine ⟨157733497798068123220621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 210311330397424164294161 157733497798068123220621)
                  ·
                    rfl

theorem cell20_345583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 3, 5, 2].length) (baseStart_345583 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_345583 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_345583 prefixEnd_345583 := by exact prefixLift 345583
  have htrace : WordTrace (prefixWord ++ tailWord_345583) baseStart_345583 baseEnd_345583 := by
    simpa [prefixWord, tailWord_345583, baseEnd_345583] using wordTrace_append hprefix tailTrace_345583
  have hstable : (prefixWord ++ tailWord_345583).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_345583).length < 2 ^ (prefixWord ++ tailWord_345583).sum := by decide
  have hdescent : baseEnd_345583 < baseStart_345583 := by decide
  rcases family_descends (prefixWord ++ tailWord_345583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_345590 : List Nat := [5, 1, 1, 1, 2, 3, 7]
def baseStart_345590 : Nat := 118140960795 + 345590 * 2 ^ 59
def prefixEnd_345590 : Nat := 4983230072969 + 3 ^ 40 * 345590 * 2
def baseEnd_345590 : Nat := 17526299198756356665251

theorem tailTrace_345590 : CollatzResearch.WordTrace tailWord_345590 prefixEnd_345590 17526299198756356665251 := by
  unfold tailWord_345590
  simp only [CollatzResearch.WordTrace]
  refine ⟨787793926124620432382639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 8403135211995951278748149 787793926124620432382639)
  ·
    refine ⟨1181690889186930648573959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 787793926124620432382639 1181690889186930648573959)
    ·
      refine ⟨1772536333780395972860939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1181690889186930648573959 1772536333780395972860939)
      ·
        refine ⟨2658804500670593959291409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1772536333780395972860939 2658804500670593959291409)
        ·
          refine ⟨1994103375502945469468557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2658804500670593959291409 1994103375502945469468557)
          ·
            refine ⟨747788765813604551050709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1994103375502945469468557 747788765813604551050709)
            ·
              refine ⟨17526299198756356665251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 747788765813604551050709 17526299198756356665251)
              ·
                rfl

theorem cell20_345590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 7].length) (baseStart_345590 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_345590 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_345590 prefixEnd_345590 := by exact prefixLift 345590
  have htrace : WordTrace (prefixWord ++ tailWord_345590) baseStart_345590 baseEnd_345590 := by
    simpa [prefixWord, tailWord_345590, baseEnd_345590] using wordTrace_append hprefix tailTrace_345590
  have hstable : (prefixWord ++ tailWord_345590).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_345590).length < 2 ^ (prefixWord ++ tailWord_345590).sum := by decide
  have hdescent : baseEnd_345590 < baseStart_345590 := by decide
  rcases family_descends (prefixWord ++ tailWord_345590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_345597 : List Nat := [1, 4, 1, 1, 1, 5, 1, 1, 5]
def baseStart_345597 : Nat := 118140960795 + 345597 * 2 ^ 59
def prefixEnd_345597 : Nat := 4983230072969 + 3 ^ 40 * 345597 * 2
def baseEnd_345597 : Nat := 157739887779546296753897

theorem tailTrace_345597 : CollatzResearch.WordTrace tailWord_345597 prefixEnd_345597 157739887779546296753897 := by
  unfold tailWord_345597
  simp only [CollatzResearch.WordTrace]
  refine ⟨12604958128968567113627045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8403305419312378075751363 12604958128968567113627045)
  ·
    refine ⟨2363429649181606333805071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12604958128968567113627045 2363429649181606333805071)
    ·
      refine ⟨3545144473772409500707607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2363429649181606333805071 3545144473772409500707607)
      ·
        refine ⟨5317716710658614251061411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3545144473772409500707607 5317716710658614251061411)
        ·
          refine ⟨7976575065987921376592117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5317716710658614251061411 7976575065987921376592117)
          ·
            refine ⟨747803912436367629055511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 7976575065987921376592117 747803912436367629055511)
            ·
              refine ⟨1121705868654551443583267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 747803912436367629055511 1121705868654551443583267)
              ·
                refine ⟨1682558802981827165374901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1121705868654551443583267 1682558802981827165374901)
                ·
                  refine ⟨157739887779546296753897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1682558802981827165374901 157739887779546296753897)
                  ·
                    rfl

theorem cell20_345597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 1, 1, 5].length) (baseStart_345597 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_345597 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_345597 prefixEnd_345597 := by exact prefixLift 345597
  have htrace : WordTrace (prefixWord ++ tailWord_345597) baseStart_345597 baseEnd_345597 := by
    simpa [prefixWord, tailWord_345597, baseEnd_345597] using wordTrace_append hprefix tailTrace_345597
  have hstable : (prefixWord ++ tailWord_345597).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_345597).length < 2 ^ (prefixWord ++ tailWord_345597).sum := by decide
  have hdescent : baseEnd_345597 < baseStart_345597 := by decide
  rcases family_descends (prefixWord ++ tailWord_345597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_345606 : List Nat := [6, 2, 1, 1, 2, 1, 3, 1, 3]
def baseStart_345606 : Nat := 118140960795 + 345606 * 2 ^ 59
def prefixEnd_345606 : Nat := 4983230072969 + 3 ^ 40 * 345606 * 2
def baseEnd_345606 : Nat := 157743995624782265453861

theorem tailTrace_345606 : CollatzResearch.WordTrace tailWord_345606 prefixEnd_345606 157743995624782265453861 := by
  unfold tailWord_345606
  simp only [CollatzResearch.WordTrace]
  refine ⟨393915199560498801584521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 8403524257290641100469781 393915199560498801584521)
  ·
    refine ⟨295436399670374101188391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 393915199560498801584521 295436399670374101188391)
    ·
      refine ⟨443154599505561151782587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 295436399670374101188391 443154599505561151782587)
      ·
        refine ⟨664731899258341727673881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 443154599505561151782587 664731899258341727673881)
        ·
          refine ⟨498548924443756295755411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 664731899258341727673881 498548924443756295755411)
          ·
            refine ⟨747823386665634443633117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 498548924443756295755411 747823386665634443633117)
            ·
              refine ⟨280433769999612916362419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 747823386665634443633117 280433769999612916362419)
              ·
                refine ⟨420650654999419374543629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 280433769999612916362419 420650654999419374543629)
                ·
                  refine ⟨157743995624782265453861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 420650654999419374543629 157743995624782265453861)
                  ·
                    rfl

theorem cell20_345606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 3, 1, 3].length) (baseStart_345606 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_345606 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_345606 prefixEnd_345606 := by exact prefixLift 345606
  have htrace : WordTrace (prefixWord ++ tailWord_345606) baseStart_345606 baseEnd_345606 := by
    simpa [prefixWord, tailWord_345606, baseEnd_345606] using wordTrace_append hprefix tailTrace_345606
  have hstable : (prefixWord ++ tailWord_345606).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_345606).length < 2 ^ (prefixWord ++ tailWord_345606).sum := by decide
  have hdescent : baseEnd_345606 < baseStart_345606 := by decide
  rcases family_descends (prefixWord ++ tailWord_345606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_345624 : List Nat := [2, 1, 2, 3, 5, 1, 2, 4]
def baseStart_345624 : Nat := 118140960795 + 345624 * 2 ^ 59
def prefixEnd_345624 : Nat := 4983230072969 + 3 ^ 40 * 345624 * 2
def baseEnd_345624 : Nat := 52584070438418067617929

theorem tailTrace_345624 : CollatzResearch.WordTrace tailWord_345624 prefixEnd_345624 52584070438418067617929 := by
  unfold tailWord_345624
  simp only [CollatzResearch.WordTrace]
  refine ⟨6302971449935375362429963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8403961933247167149906617 6302971449935375362429963)
  ·
    refine ⟨9454457174903063043644945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6302971449935375362429963 9454457174903063043644945)
    ·
      refine ⟨7090842881177297282733709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9454457174903063043644945 7090842881177297282733709)
      ·
        refine ⟨2659066080441486481025141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7090842881177297282733709 2659066080441486481025141)
        ·
          refine ⟨249287445041389357596107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2659066080441486481025141 249287445041389357596107)
          ·
            refine ⟨373931167562084036394161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 249287445041389357596107 373931167562084036394161)
            ·
              refine ⟨280448375671563027295621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 373931167562084036394161 280448375671563027295621)
              ·
                refine ⟨52584070438418067617929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 280448375671563027295621 52584070438418067617929)
                ·
                  rfl

theorem cell20_345624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 5, 1, 2, 4].length) (baseStart_345624 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_345624 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_345624 prefixEnd_345624 := by exact prefixLift 345624
  have htrace : WordTrace (prefixWord ++ tailWord_345624) baseStart_345624 baseEnd_345624 := by
    simpa [prefixWord, tailWord_345624, baseEnd_345624] using wordTrace_append hprefix tailTrace_345624
  have hstable : (prefixWord ++ tailWord_345624).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_345624).length < 2 ^ (prefixWord ++ tailWord_345624).sum := by decide
  have hdescent : baseEnd_345624 < baseStart_345624 := by decide
  rcases family_descends (prefixWord ++ tailWord_345624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_345630 : List Nat := [4, 3, 3, 1, 1, 2, 1, 3, 2]
def baseStart_345630 : Nat := 118140960795 + 345630 * 2 ^ 59
def prefixEnd_345630 : Nat := 4983230072969 + 3 ^ 40 * 345630 * 2
def baseEnd_345630 : Nat := 157754949878744848653763

theorem tailTrace_345630 : CollatzResearch.WordTrace tailWord_345630 prefixEnd_345630 157754949878744848653763 := by
  unfold tailWord_345630
  simp only [CollatzResearch.WordTrace]
  refine ⟨1575770217231126718697293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8404107825232675833052229 1575770217231126718697293)
  ·
    refine ⟨590913831461672519511485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1575770217231126718697293 590913831461672519511485)
    ·
      refine ⟨221592686798127194816807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 590913831461672519511485 221592686798127194816807)
      ·
        refine ⟨332389030197190792225211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 221592686798127194816807 332389030197190792225211)
        ·
          refine ⟨498583545295786188337817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 332389030197190792225211 498583545295786188337817)
          ·
            refine ⟨373937658971839641253363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 498583545295786188337817 373937658971839641253363)
            ·
              refine ⟨560906488457759461880045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 373937658971839641253363 560906488457759461880045)
              ·
                refine ⟨210339933171659798205017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 560906488457759461880045 210339933171659798205017)
                ·
                  refine ⟨157754949878744848653763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 210339933171659798205017 157754949878744848653763)
                  ·
                    rfl

theorem cell20_345630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 2, 1, 3, 2].length) (baseStart_345630 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_345630 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_345630 prefixEnd_345630 := by exact prefixLift 345630
  have htrace : WordTrace (prefixWord ++ tailWord_345630) baseStart_345630 baseEnd_345630 := by
    simpa [prefixWord, tailWord_345630, baseEnd_345630] using wordTrace_append hprefix tailTrace_345630
  have hstable : (prefixWord ++ tailWord_345630).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_345630).length < 2 ^ (prefixWord ++ tailWord_345630).sum := by decide
  have hdescent : baseEnd_345630 < baseStart_345630 := by decide
  rcases family_descends (prefixWord ++ tailWord_345630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_345687 : List Nat := [1, 1, 3, 2, 2, 3, 2, 6]
def baseStart_345687 : Nat := 118140960795 + 345687 * 2 ^ 59
def prefixEnd_345687 : Nat := 4983230072969 + 3 ^ 40 * 345687 * 2
def baseEnd_345687 : Nat := 52593655410635327917843

theorem tailTrace_345687 : CollatzResearch.WordTrace tailWord_345687 prefixEnd_345687 52593655410635327917843 := by
  unfold tailWord_345687
  simp only [CollatzResearch.WordTrace]
  refine ⟨12608240698642512484403315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8405493799095008322935543 12608240698642512484403315)
  ·
    refine ⟨18912361047963768726604973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12608240698642512484403315 18912361047963768726604973)
    ·
      refine ⟨7092135392986413272476865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18912361047963768726604973 7092135392986413272476865)
      ·
        refine ⟨5319101544739809954357649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7092135392986413272476865 5319101544739809954357649)
        ·
          refine ⟨3989326158554857465768237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5319101544739809954357649 3989326158554857465768237)
          ·
            refine ⟨1495997309458071549663089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3989326158554857465768237 1495997309458071549663089)
            ·
              refine ⟨1121997982093553662247317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1495997309458071549663089 1121997982093553662247317)
              ·
                refine ⟨52593655410635327917843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1121997982093553662247317 52593655410635327917843)
                ·
                  rfl

theorem cell20_345687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 2, 6].length) (baseStart_345687 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_345687 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_345687 prefixEnd_345687 := by exact prefixLift 345687
  have htrace : WordTrace (prefixWord ++ tailWord_345687) baseStart_345687 baseEnd_345687 := by
    simpa [prefixWord, tailWord_345687, baseEnd_345687] using wordTrace_append hprefix tailTrace_345687
  have hstable : (prefixWord ++ tailWord_345687).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_345687).length < 2 ^ (prefixWord ++ tailWord_345687).sum := by decide
  have hdescent : baseEnd_345687 < baseStart_345687 := by decide
  rcases family_descends (prefixWord ++ tailWord_345687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_345697 : List Nat := [1, 2, 3, 1, 1, 3, 2, 5, 2]
def baseStart_345697 : Nat := 118140960795 + 345697 * 2 ^ 59
def prefixEnd_345697 : Nat := 4983230072969 + 3 ^ 40 * 345697 * 2
def baseEnd_345697 : Nat := 157785530504390393420155

theorem tailTrace_345697 : CollatzResearch.WordTrace tailWord_345697 prefixEnd_345697 157785530504390393420155 := by
  unfold tailWord_345697
  simp only [CollatzResearch.WordTrace]
  refine ⟨12608605428606284192267345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8405736952404189461511563 12608605428606284192267345)
  ·
    refine ⟨9456454071454713144200509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12608605428606284192267345 9456454071454713144200509)
    ·
      refine ⟨3546170276795517429075191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9456454071454713144200509 3546170276795517429075191)
      ·
        refine ⟨5319255415193276143612787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3546170276795517429075191 5319255415193276143612787)
        ·
          refine ⟨7978883122789914215419181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5319255415193276143612787 7978883122789914215419181)
          ·
            refine ⟨2992081171046217830782193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7978883122789914215419181 2992081171046217830782193)
            ·
              refine ⟨2244060878284663373086645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2992081171046217830782193 2244060878284663373086645)
              ·
                refine ⟨210380707339187191226873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2244060878284663373086645 210380707339187191226873)
                ·
                  refine ⟨157785530504390393420155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 210380707339187191226873 157785530504390393420155)
                  ·
                    rfl

theorem cell20_345697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 2, 5, 2].length) (baseStart_345697 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_345697 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_345697 prefixEnd_345697 := by exact prefixLift 345697
  have htrace : WordTrace (prefixWord ++ tailWord_345697) baseStart_345697 baseEnd_345697 := by
    simpa [prefixWord, tailWord_345697, baseEnd_345697] using wordTrace_append hprefix tailTrace_345697
  have hstable : (prefixWord ++ tailWord_345697).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_345697).length < 2 ^ (prefixWord ++ tailWord_345697).sum := by decide
  have hdescent : baseEnd_345697 < baseStart_345697 := by decide
  rcases family_descends (prefixWord ++ tailWord_345697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_345710 : List Nat := [4, 1, 2, 2, 3, 2, 2, 2, 2]
def baseStart_345710 : Nat := 118140960795 + 345710 * 2 ^ 59
def prefixEnd_345710 : Nat := 4983230072969 + 3 ^ 40 * 345710 * 2
def baseEnd_345710 : Nat := 157791464058620125986769

theorem tailTrace_345710 : CollatzResearch.WordTrace tailWord_345710 prefixEnd_345710 157791464058620125986769 := by
  unfold tailWord_345710
  simp only [CollatzResearch.WordTrace]
  refine ⟨1576134947194898426561323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8406053051706124941660389 1576134947194898426561323)
  ·
    refine ⟨2364202420792347639841985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1576134947194898426561323 2364202420792347639841985)
    ·
      refine ⟨1773151815594260729881489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2364202420792347639841985 1773151815594260729881489)
      ·
        refine ⟨1329863861695695547411117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1773151815594260729881489 1329863861695695547411117)
        ·
          refine ⟨498698948135885830279169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1329863861695695547411117 498698948135885830279169)
          ·
            refine ⟨374024211101914372709377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 498698948135885830279169 374024211101914372709377)
            ·
              refine ⟨280518158326435779532033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 374024211101914372709377 280518158326435779532033)
              ·
                refine ⟨210388618744826834649025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 280518158326435779532033 210388618744826834649025)
                ·
                  refine ⟨157791464058620125986769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 210388618744826834649025 157791464058620125986769)
                  ·
                    rfl

theorem cell20_345710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 2, 2, 2, 2].length) (baseStart_345710 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_345710 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_345710 prefixEnd_345710 := by exact prefixLift 345710
  have htrace : WordTrace (prefixWord ++ tailWord_345710) baseStart_345710 baseEnd_345710 := by
    simpa [prefixWord, tailWord_345710, baseEnd_345710] using wordTrace_append hprefix tailTrace_345710
  have hstable : (prefixWord ++ tailWord_345710).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_345710).length < 2 ^ (prefixWord ++ tailWord_345710).sum := by decide
  have hdescent : baseEnd_345710 < baseStart_345710 := by decide
  rcases family_descends (prefixWord ++ tailWord_345710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_345714 : List Nat := [3, 2, 1, 2, 3, 2, 1, 4, 2]
def baseStart_345714 : Nat := 118140960795 + 345714 * 2 ^ 59
def prefixEnd_345714 : Nat := 4983230072969 + 3 ^ 40 * 345714 * 2
def baseEnd_345714 : Nat := 157793289767613889853419

theorem tailTrace_345714 : CollatzResearch.WordTrace tailWord_345714 prefixEnd_345714 157793289767613889853419 := by
  unfold tailWord_345714
  simp only [CollatzResearch.WordTrace]
  refine ⟨3152306367386174023909049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8406150313029797397090797 3152306367386174023909049)
  ·
    refine ⟨2364229775539630517931787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3152306367386174023909049 2364229775539630517931787)
    ·
      refine ⟨3546344663309445776897681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2364229775539630517931787 3546344663309445776897681)
      ·
        refine ⟨2659758497482084332673261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3546344663309445776897681 2659758497482084332673261)
        ·
          refine ⟨997409436555781624752473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2659758497482084332673261 997409436555781624752473)
          ·
            refine ⟨748057077416836218564355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 997409436555781624752473 748057077416836218564355)
            ·
              refine ⟨1122085616125254327846533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 748057077416836218564355 1122085616125254327846533)
              ·
                refine ⟨210391053023485186471225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1122085616125254327846533 210391053023485186471225)
                ·
                  refine ⟨157793289767613889853419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 210391053023485186471225 157793289767613889853419)
                  ·
                    rfl

theorem cell20_345714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 1, 4, 2].length) (baseStart_345714 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_345714 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_345714 prefixEnd_345714 := by exact prefixLift 345714
  have htrace : WordTrace (prefixWord ++ tailWord_345714) baseStart_345714 baseEnd_345714 := by
    simpa [prefixWord, tailWord_345714, baseEnd_345714] using wordTrace_append hprefix tailTrace_345714
  have hstable : (prefixWord ++ tailWord_345714).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_345714).length < 2 ^ (prefixWord ++ tailWord_345714).sum := by decide
  have hdescent : baseEnd_345714 < baseStart_345714 := by decide
  rcases family_descends (prefixWord ++ tailWord_345714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_345752 : List Nat := [2, 1, 2, 4, 1, 3, 2, 3, 2]
def baseStart_345752 : Nat := 118140960795 + 345752 * 2 ^ 59
def prefixEnd_345752 : Nat := 4983230072969 + 3 ^ 40 * 345752 * 2
def baseEnd_345752 : Nat := 157810634003054646586597

theorem tailTrace_345752 : CollatzResearch.WordTrace tailWord_345752 prefixEnd_345752 157810634003054646586597 := by
  unfold tailWord_345752
  simp only [CollatzResearch.WordTrace]
  refine ⟨6305305721703514292759755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8407074295604685723679673 6305305721703514292759755)
  ·
    refine ⟨9457958582555271439139633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6305305721703514292759755 9457958582555271439139633)
    ·
      refine ⟨7093468936916453579354725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9457958582555271439139633 7093468936916453579354725)
      ·
        refine ⟨1330025425671835046129011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7093468936916453579354725 1330025425671835046129011)
        ·
          refine ⟨1995038138507752569193517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1330025425671835046129011 1995038138507752569193517)
          ·
            refine ⟨748139301940407213447569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1995038138507752569193517 748139301940407213447569)
            ·
              refine ⟨561104476455305410085677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 748139301940407213447569 561104476455305410085677)
              ·
                refine ⟨210414178670739528782129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 561104476455305410085677 210414178670739528782129)
                ·
                  refine ⟨157810634003054646586597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 210414178670739528782129 157810634003054646586597)
                  ·
                    rfl

theorem cell20_345752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 2, 3, 2].length) (baseStart_345752 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_345752 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_345752 prefixEnd_345752 := by exact prefixLift 345752
  have htrace : WordTrace (prefixWord ++ tailWord_345752) baseStart_345752 baseEnd_345752 := by
    simpa [prefixWord, tailWord_345752, baseEnd_345752] using wordTrace_append hprefix tailTrace_345752
  have hstable : (prefixWord ++ tailWord_345752).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_345752).length < 2 ^ (prefixWord ++ tailWord_345752).sum := by decide
  have hdescent : baseEnd_345752 < baseStart_345752 := by decide
  rcases family_descends (prefixWord ++ tailWord_345752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_345762 : List Nat := [3, 3, 1, 4, 1, 2, 1, 2, 3]
def baseStart_345762 : Nat := 118140960795 + 345762 * 2 ^ 59
def prefixEnd_345762 : Nat := 4983230072969 + 3 ^ 40 * 345762 * 2
def baseEnd_345762 : Nat := 157815198275539056253223

theorem tailTrace_345762 : CollatzResearch.WordTrace tailWord_345762 prefixEnd_345762 157815198275539056253223 := by
  unfold tailWord_345762
  simp only [CollatzResearch.WordTrace]
  refine ⟨3152744043342700073345885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8407317448913866862255693 3152744043342700073345885)
  ·
    refine ⟨1182279016253512527504707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3152744043342700073345885 1182279016253512527504707)
    ·
      refine ⟨1773418524380268791257061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1182279016253512527504707 1773418524380268791257061)
      ·
        refine ⟨332515973321300398360699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1773418524380268791257061 332515973321300398360699)
        ·
          refine ⟨498773959981950597541049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 332515973321300398360699 498773959981950597541049)
          ·
            refine ⟨374080469986462948155787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 498773959981950597541049 374080469986462948155787)
            ·
              refine ⟨561120704979694422233681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 374080469986462948155787 561120704979694422233681)
              ·
                refine ⟨420840528734770816675261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 561120704979694422233681 420840528734770816675261)
                ·
                  refine ⟨157815198275539056253223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 420840528734770816675261 157815198275539056253223)
                  ·
                    rfl

theorem cell20_345762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 2, 1, 2, 3].length) (baseStart_345762 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_345762 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_345762 prefixEnd_345762 := by exact prefixLift 345762
  have htrace : WordTrace (prefixWord ++ tailWord_345762) baseStart_345762 baseEnd_345762 := by
    simpa [prefixWord, tailWord_345762, baseEnd_345762] using wordTrace_append hprefix tailTrace_345762
  have hstable : (prefixWord ++ tailWord_345762).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_345762).length < 2 ^ (prefixWord ++ tailWord_345762).sum := by decide
  have hdescent : baseEnd_345762 < baseStart_345762 := by decide
  rcases family_descends (prefixWord ++ tailWord_345762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_345773 : List Nat := [1, 5, 2, 1, 1, 1, 4, 1, 4]
def baseStart_345773 : Nat := 118140960795 + 345773 * 2 ^ 59
def prefixEnd_345773 : Nat := 4983230072969 + 3 ^ 40 * 345773 * 2
def baseEnd_345773 : Nat := 157820218975271906886511

theorem tailTrace_345773 : CollatzResearch.WordTrace tailWord_345773 prefixEnd_345773 157820218975271906886511 := by
  unfold tailWord_345773
  simp only [CollatzResearch.WordTrace]
  refine ⟨12611377376330949172033973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8407584917553966114689315 12611377376330949172033973)
  ·
    refine ⟨1182316629031026484878185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 12611377376330949172033973 1182316629031026484878185)
    ·
      refine ⟨886737471773269863658639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1182316629031026484878185 886737471773269863658639)
      ·
        refine ⟨1330106207659904795487959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 886737471773269863658639 1330106207659904795487959)
        ·
          refine ⟨1995159311489857193231939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1330106207659904795487959 1995159311489857193231939)
          ·
            refine ⟨2992738967234785789847909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1995159311489857193231939 2992738967234785789847909)
            ·
              refine ⟨561138556356522335596483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2992738967234785789847909 561138556356522335596483)
              ·
                refine ⟨841707834534783503394725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 561138556356522335596483 841707834534783503394725)
                ·
                  refine ⟨157820218975271906886511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 841707834534783503394725 157820218975271906886511)
                  ·
                    rfl

theorem cell20_345773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 4, 1, 4].length) (baseStart_345773 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_345773 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_345773 prefixEnd_345773 := by exact prefixLift 345773
  have htrace : WordTrace (prefixWord ++ tailWord_345773) baseStart_345773 baseEnd_345773 := by
    simpa [prefixWord, tailWord_345773, baseEnd_345773] using wordTrace_append hprefix tailTrace_345773
  have hstable : (prefixWord ++ tailWord_345773).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_345773).length < 2 ^ (prefixWord ++ tailWord_345773).sum := by decide
  have hdescent : baseEnd_345773 < baseStart_345773 := by decide
  rcases family_descends (prefixWord ++ tailWord_345773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_345814 : List Nat := [5, 2, 1, 3, 1, 2, 6]
def baseStart_345814 : Nat := 118140960795 + 345814 * 2 ^ 59
def prefixEnd_345814 : Nat := 4983230072969 + 3 ^ 40 * 345814 * 2
def baseEnd_345814 : Nat := 17537659165828665168853

theorem tailTrace_345814 : CollatzResearch.WordTrace tailWord_345814 prefixEnd_345814 17537659165828665168853 := by
  unfold tailWord_345814
  simp only [CollatzResearch.WordTrace]
  refine ⟨788304548073900823392281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 8408581846121608782850997 788304548073900823392281)
  ·
    refine ⟨591228411055425617544211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 788304548073900823392281 591228411055425617544211)
    ·
      refine ⟨886842616583138426316317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 591228411055425617544211 886842616583138426316317)
      ·
        refine ⟨332565981218676909868619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 886842616583138426316317 332565981218676909868619)
        ·
          refine ⟨498848971828015364802929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 332565981218676909868619 498848971828015364802929)
          ·
            refine ⟨374136728871011523602197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 498848971828015364802929 374136728871011523602197)
            ·
              refine ⟨17537659165828665168853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 374136728871011523602197 17537659165828665168853)
              ·
                rfl

theorem cell20_345814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 2, 6].length) (baseStart_345814 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_345814 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_345814 prefixEnd_345814 := by exact prefixLift 345814
  have htrace : WordTrace (prefixWord ++ tailWord_345814) baseStart_345814 baseEnd_345814 := by
    simpa [prefixWord, tailWord_345814, baseEnd_345814] using wordTrace_append hprefix tailTrace_345814
  have hstable : (prefixWord ++ tailWord_345814).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_345814).length < 2 ^ (prefixWord ++ tailWord_345814).sum := by decide
  have hdescent : baseEnd_345814 < baseStart_345814 := by decide
  rcases family_descends (prefixWord ++ tailWord_345814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_345828 : List Nat := [2, 3, 1, 1, 1, 3, 5, 2, 2]
def baseStart_345828 : Nat := 118140960795 + 345828 * 2 ^ 59
def prefixEnd_345828 : Nat := 4983230072969 + 3 ^ 40 * 345828 * 2
def baseEnd_345828 : Nat := 157845322473936160052953

theorem tailTrace_345828 : CollatzResearch.WordTrace tailWord_345828 prefixEnd_345828 157845322473936160052953 := by
  unfold tailWord_345828
  simp only [CollatzResearch.WordTrace]
  refine ⟨6306691695565846782643069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8408922260754462376857425 6306691695565846782643069)
  ·
    refine ⟨2365009385837192543491151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6306691695565846782643069 2365009385837192543491151)
    ·
      refine ⟨3547514078755788815236727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2365009385837192543491151 3547514078755788815236727)
      ·
        refine ⟨5321271118133683222855091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3547514078755788815236727 5321271118133683222855091)
        ·
          refine ⟨7981906677200524834282637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5321271118133683222855091 7981906677200524834282637)
          ·
            refine ⟨2993215003950196812855989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7981906677200524834282637 2993215003950196812855989)
            ·
              refine ⟨280613906620330951205249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2993215003950196812855989 280613906620330951205249)
              ·
                refine ⟨210460429965248213403937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 280613906620330951205249 210460429965248213403937)
                ·
                  refine ⟨157845322473936160052953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 210460429965248213403937 157845322473936160052953)
                  ·
                    rfl

theorem cell20_345828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 5, 2, 2].length) (baseStart_345828 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_345828 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_345828 prefixEnd_345828 := by exact prefixLift 345828
  have htrace : WordTrace (prefixWord ++ tailWord_345828) baseStart_345828 baseEnd_345828 := by
    simpa [prefixWord, tailWord_345828, baseEnd_345828] using wordTrace_append hprefix tailTrace_345828
  have hstable : (prefixWord ++ tailWord_345828).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_345828).length < 2 ^ (prefixWord ++ tailWord_345828).sum := by decide
  have hdescent : baseEnd_345828 < baseStart_345828 := by decide
  rcases family_descends (prefixWord ++ tailWord_345828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_345839 : List Nat := [1, 1, 2, 1, 5, 1, 4, 5]
def baseStart_345839 : Nat := 118140960795 + 345839 * 2 ^ 59
def prefixEnd_345839 : Nat := 4983230072969 + 3 ^ 40 * 345839 * 2
def baseEnd_345839 : Nat := 52616781057889670228747

theorem tailTrace_345839 : CollatzResearch.WordTrace tailWord_345839 prefixEnd_345839 52616781057889670228747 := by
  unfold tailWord_345839
  simp only [CollatzResearch.WordTrace]
  refine ⟨12613784594091842443936571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8409189729394561629291047 12613784594091842443936571)
  ·
    refine ⟨18920676891137763665904857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12613784594091842443936571 18920676891137763665904857)
    ·
      refine ⟨14190507668353322749428643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18920676891137763665904857 14190507668353322749428643)
      ·
        refine ⟨21285761502529984124142965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14190507668353322749428643 21285761502529984124142965)
        ·
          refine ⟨1995540140862186011638403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 21285761502529984124142965 1995540140862186011638403)
          ·
            refine ⟨2993310211293279017457605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1995540140862186011638403 2993310211293279017457605)
            ·
              refine ⟨561245664617489815773301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2993310211293279017457605 561245664617489815773301)
              ·
                refine ⟨52616781057889670228747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 561245664617489815773301 52616781057889670228747)
                ·
                  rfl

theorem cell20_345839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 4, 5].length) (baseStart_345839 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_345839 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_345839 prefixEnd_345839 := by exact prefixLift 345839
  have htrace : WordTrace (prefixWord ++ tailWord_345839) baseStart_345839 baseEnd_345839 := by
    simpa [prefixWord, tailWord_345839, baseEnd_345839] using wordTrace_append hprefix tailTrace_345839
  have hstable : (prefixWord ++ tailWord_345839).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_345839).length < 2 ^ (prefixWord ++ tailWord_345839).sum := by decide
  have hdescent : baseEnd_345839 < baseStart_345839 := by decide
  rcases family_descends (prefixWord ++ tailWord_345839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_345869 : List Nat := [1, 7, 2, 1, 2, 7]
def baseStart_345869 : Nat := 118140960795 + 345869 * 2 ^ 59
def prefixEnd_345869 : Nat := 4983230072969 + 3 ^ 40 * 345869 * 2
def baseEnd_345869 : Nat := 5846816147819342210597

theorem tailTrace_345869 : CollatzResearch.WordTrace tailWord_345869 prefixEnd_345869 5846816147819342210597 := by
  unfold tailWord_345869
  simp only [CollatzResearch.WordTrace]
  refine ⟨12614878783983157567528661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8409919189322105045019107 12614878783983157567528661)
  ·
    refine ⟨295661221499605255488953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 12614878783983157567528661 295661221499605255488953)
    ·
      refine ⟨221745916124703941616715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 295661221499605255488953 221745916124703941616715)
      ·
        refine ⟨332618874187055912425073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 221745916124703941616715 332618874187055912425073)
        ·
          refine ⟨249464155640291934318805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 332618874187055912425073 249464155640291934318805)
          ·
            refine ⟨5846816147819342210597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 249464155640291934318805 5846816147819342210597)
            ·
              rfl

theorem cell20_345869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 2, 7].length) (baseStart_345869 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_345869 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_345869 prefixEnd_345869 := by exact prefixLift 345869
  have htrace : WordTrace (prefixWord ++ tailWord_345869) baseStart_345869 baseEnd_345869 := by
    simpa [prefixWord, tailWord_345869, baseEnd_345869] using wordTrace_append hprefix tailTrace_345869
  have hstable : (prefixWord ++ tailWord_345869).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_345869).length < 2 ^ (prefixWord ++ tailWord_345869).sum := by decide
  have hdescent : baseEnd_345869 < baseStart_345869 := by decide
  rcases family_descends (prefixWord ++ tailWord_345869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_345887 : List Nat := [1, 1, 2, 4, 2, 1, 3, 4, 2]
def baseStart_345887 : Nat := 118140960795 + 345887 * 2 ^ 59
def prefixEnd_345887 : Nat := 4983230072969 + 3 ^ 40 * 345887 * 2
def baseEnd_345887 : Nat := 157872251681594177086045

theorem tailTrace_345887 : CollatzResearch.WordTrace tailWord_345887 prefixEnd_345887 157872251681594177086045 := by
  unfold tailWord_345887
  simp only [CollatzResearch.WordTrace]
  refine ⟨12615535297917946641683915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8410356865278631094455943 12615535297917946641683915)
  ·
    refine ⟨18923302946876919962525873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12615535297917946641683915 18923302946876919962525873)
    ·
      refine ⟨14192477210157689971894405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18923302946876919962525873 14192477210157689971894405)
      ·
        refine ⟨2661089476904566869730201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14192477210157689971894405 2661089476904566869730201)
        ·
          refine ⟨1995817107678425152297651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2661089476904566869730201 1995817107678425152297651)
          ·
            refine ⟨2993725661517637728446477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1995817107678425152297651 2993725661517637728446477)
            ·
              refine ⟨1122647123069114148167429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2993725661517637728446477 1122647123069114148167429)
              ·
                refine ⟨210496335575458902781393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1122647123069114148167429 210496335575458902781393)
                ·
                  refine ⟨157872251681594177086045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 210496335575458902781393 157872251681594177086045)
                  ·
                    rfl

theorem cell20_345887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 3, 4, 2].length) (baseStart_345887 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_345887 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_345887 prefixEnd_345887 := by exact prefixLift 345887
  have htrace : WordTrace (prefixWord ++ tailWord_345887) baseStart_345887 baseEnd_345887 := by
    simpa [prefixWord, tailWord_345887, baseEnd_345887] using wordTrace_append hprefix tailTrace_345887
  have hstable : (prefixWord ++ tailWord_345887).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_345887).length < 2 ^ (prefixWord ++ tailWord_345887).sum := by decide
  have hdescent : baseEnd_345887 < baseStart_345887 := by decide
  rcases family_descends (prefixWord ++ tailWord_345887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_345925 : List Nat := [1, 3, 1, 1, 1, 2, 6, 3, 2]
def baseStart_345925 : Nat := 118140960795 + 345925 * 2 ^ 59
def prefixEnd_345925 : Nat := 4983230072969 + 3 ^ 40 * 345925 * 2
def baseEnd_345925 : Nat := 157889595917034933819223

theorem tailTrace_345925 : CollatzResearch.WordTrace tailWord_345925 prefixEnd_345925 157889595917034933819223 := by
  unfold tailWord_345925
  simp only [CollatzResearch.WordTrace]
  refine ⟨12616921271780279131567229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8411280847853519421044819 12616921271780279131567229)
  ·
    refine ⟨4731345476917604674337711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12616921271780279131567229 4731345476917604674337711)
    ·
      refine ⟨7097018215376407011506567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4731345476917604674337711 7097018215376407011506567)
      ·
        refine ⟨10645527323064610517259851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7097018215376407011506567 10645527323064610517259851)
        ·
          refine ⟨15968290984596915775889777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10645527323064610517259851 15968290984596915775889777)
          ·
            refine ⟨11976218238447686831917333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15968290984596915775889777 11976218238447686831917333)
            ·
              refine ⟨561385229927235320246125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 11976218238447686831917333 561385229927235320246125)
              ·
                refine ⟨210519461222713245092297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 561385229927235320246125 210519461222713245092297)
                ·
                  refine ⟨157889595917034933819223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 210519461222713245092297 157889595917034933819223)
                  ·
                    rfl

theorem cell20_345925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 6, 3, 2].length) (baseStart_345925 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_345925 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_345925 prefixEnd_345925 := by exact prefixLift 345925
  have htrace : WordTrace (prefixWord ++ tailWord_345925) baseStart_345925 baseEnd_345925 := by
    simpa [prefixWord, tailWord_345925, baseEnd_345925] using wordTrace_append hprefix tailTrace_345925
  have hstable : (prefixWord ++ tailWord_345925).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_345925).length < 2 ^ (prefixWord ++ tailWord_345925).sum := by decide
  have hdescent : baseEnd_345925 < baseStart_345925 := by decide
  rcases family_descends (prefixWord ++ tailWord_345925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_345929 : List Nat := [1, 2, 1, 1, 2, 4, 1, 2, 6]
def baseStart_345929 : Nat := 118140960795 + 345929 * 2 ^ 59
def prefixEnd_345929 : Nat := 4983230072969 + 3 ^ 40 * 345929 * 2
def baseEnd_345929 : Nat := 157891421626028697685873

theorem tailTrace_345929 : CollatzResearch.WordTrace tailWord_345929 prefixEnd_345929 157891421626028697685873 := by
  unfold tailWord_345929
  simp only [CollatzResearch.WordTrace]
  refine ⟨12617067163765787814712841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8411378109177191876475227 12617067163765787814712841)
  ·
    refine ⟨9462800372824340861034631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12617067163765787814712841 9462800372824340861034631)
    ·
      refine ⟨14194200559236511291551947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9462800372824340861034631 14194200559236511291551947)
      ·
        refine ⟨21291300838854766937327921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14194200559236511291551947 21291300838854766937327921)
        ·
          refine ⟨15968475629141075202995941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21291300838854766937327921 15968475629141075202995941)
          ·
            refine ⟨2994089180463951600561739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15968475629141075202995941 2994089180463951600561739)
            ·
              refine ⟨4491133770695927400842609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2994089180463951600561739 4491133770695927400842609)
              ·
                refine ⟨3368350328021945550631957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4491133770695927400842609 3368350328021945550631957)
                ·
                  refine ⟨157891421626028697685873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3368350328021945550631957 157891421626028697685873)
                  ·
                    rfl

theorem cell20_345929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 2, 6].length) (baseStart_345929 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_345929 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_345929 prefixEnd_345929 := by exact prefixLift 345929
  have htrace : WordTrace (prefixWord ++ tailWord_345929) baseStart_345929 baseEnd_345929 := by
    simpa [prefixWord, tailWord_345929, baseEnd_345929] using wordTrace_append hprefix tailTrace_345929
  have hstable : (prefixWord ++ tailWord_345929).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_345929).length < 2 ^ (prefixWord ++ tailWord_345929).sum := by decide
  have hdescent : baseEnd_345929 < baseStart_345929 := by decide
  rcases family_descends (prefixWord ++ tailWord_345929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_345946 : List Nat := [3, 1, 1, 2, 1, 3, 4, 1, 4]
def baseStart_345946 : Nat := 118140960795 + 345946 * 2 ^ 59
def prefixEnd_345946 : Nat := 4983230072969 + 3 ^ 40 * 345946 * 2
def baseEnd_345946 : Nat := 157899180889252194119137

theorem tailTrace_345946 : CollatzResearch.WordTrace tailWord_345946 prefixEnd_345946 157899180889252194119137 := by
  unfold tailWord_345946
  simp only [CollatzResearch.WordTrace]
  refine ⟨3154421801176049929520423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8411791469802799812054461 3154421801176049929520423)
  ·
    refine ⟨4731632701764074894280635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3154421801176049929520423 4731632701764074894280635)
    ·
      refine ⟨7097449052646112341420953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4731632701764074894280635 7097449052646112341420953)
      ·
        refine ⟨5323086789484584256065715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7097449052646112341420953 5323086789484584256065715)
        ·
          refine ⟨7984630184226876384098573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5323086789484584256065715 7984630184226876384098573)
          ·
            refine ⟨2994236319085078644036965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7984630184226876384098573 2994236319085078644036965)
            ·
              refine ⟨561419309828452245756931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2994236319085078644036965 561419309828452245756931)
              ·
                refine ⟨842128964742678368635397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 561419309828452245756931 842128964742678368635397)
                ·
                  refine ⟨157899180889252194119137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 842128964742678368635397 157899180889252194119137)
                  ·
                    rfl

theorem cell20_345946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 4, 1, 4].length) (baseStart_345946 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_345946 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_345946 prefixEnd_345946 := by exact prefixLift 345946
  have htrace : WordTrace (prefixWord ++ tailWord_345946) baseStart_345946 baseEnd_345946 := by
    simpa [prefixWord, tailWord_345946, baseEnd_345946] using wordTrace_append hprefix tailTrace_345946
  have hstable : (prefixWord ++ tailWord_345946).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_345946).length < 2 ^ (prefixWord ++ tailWord_345946).sum := by decide
  have hdescent : baseEnd_345946 < baseStart_345946 := by decide
  rcases family_descends (prefixWord ++ tailWord_345946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan20Incremental
