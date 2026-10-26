import V185TrunkScan22Chunk268

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_2398637 : List Nat := [1, 5, 2, 2, 3, 1, 1, 7]
def baseStart_2398637 : Nat := 118140960795 + 2398637 * 2 ^ 59
def prefixEnd_2398637 : Nat := 4983230072969 + 3 ^ 40 * 2398637 * 2
def baseEnd_2398637 : Nat := 91233607159899041141213

theorem tailTrace_2398637 : CollatzResearch.WordTrace tailWord_2398637 prefixEnd_2398637 91233607159899041141213 := by
  unfold tailWord_2398637
  simp only [CollatzResearch.WordTrace]
  refine ⟨87485478611155278430442165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58323652407436852286961443 87485478611155278430442165)
  ·
    refine ⟨8201763619795807352853953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 87485478611155278430442165 8201763619795807352853953)
    ·
      refine ⟨6151322714846855514640465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8201763619795807352853953 6151322714846855514640465)
      ·
        refine ⟨4613492036135141635980349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6151322714846855514640465 4613492036135141635980349)
        ·
          refine ⟨1730059513550678113492631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4613492036135141635980349 1730059513550678113492631)
          ·
            refine ⟨2595089270326017170238947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1730059513550678113492631 2595089270326017170238947)
            ·
              refine ⟨3892633905489025755358421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2595089270326017170238947 3892633905489025755358421)
              ·
                refine ⟨91233607159899041141213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3892633905489025755358421 91233607159899041141213)
                ·
                  rfl

theorem cell22_2398637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 3, 1, 1, 7].length) (baseStart_2398637 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2398637 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2398637 prefixEnd_2398637 := by exact prefixLift 2398637
  have htrace : WordTrace (prefixWord ++ tailWord_2398637) baseStart_2398637 baseEnd_2398637 := by
    simpa [prefixWord, tailWord_2398637, baseEnd_2398637] using wordTrace_append hprefix tailTrace_2398637
  have hstable : (prefixWord ++ tailWord_2398637).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2398637).length < 2 ^ (prefixWord ++ tailWord_2398637).sum := by decide
  have hdescent : baseEnd_2398637 < baseStart_2398637 := by decide
  rcases family_descends (prefixWord ++ tailWord_2398637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2398723 : List Nat := [1, 1, 1, 3, 2, 1, 4, 3, 2, 4]
def baseStart_2398723 : Nat := 118140960795 + 2398723 * 2 ^ 59
def prefixEnd_2398723 : Nat := 4983230072969 + 3 ^ 40 * 2398723 * 2
def baseEnd_2398723 : Nat := 821131903996615812620653

theorem tailTrace_2398723 : CollatzResearch.WordTrace tailWord_2398723 prefixEnd_2398723 821131903996615812620653 := by
  unfold tailWord_2398723
  simp only [CollatzResearch.WordTrace]
  refine ⟨87488615288843715118072823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58325743525895810078715215 87488615288843715118072823)
  ·
    refine ⟨131232922933265572677109235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87488615288843715118072823 131232922933265572677109235)
    ·
      refine ⟨196849384399898359015663853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131232922933265572677109235 196849384399898359015663853)
      ·
        refine ⟨73818519149961884630873945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 196849384399898359015663853 73818519149961884630873945)
        ·
          refine ⟨55363889362471413473155459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73818519149961884630873945 55363889362471413473155459)
          ·
            refine ⟨83045834043707120209733189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55363889362471413473155459 83045834043707120209733189)
            ·
              refine ⟨15571093883195085039324973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 83045834043707120209733189 15571093883195085039324973)
              ·
                refine ⟨5839160206198156889746865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15571093883195085039324973 5839160206198156889746865)
                ·
                  refine ⟨4379370154648617667310149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5839160206198156889746865 4379370154648617667310149)
                  ·
                    refine ⟨821131903996615812620653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4379370154648617667310149 821131903996615812620653)
                    ·
                      rfl

theorem cell22_2398723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 4, 3, 2, 4].length) (baseStart_2398723 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2398723 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2398723 prefixEnd_2398723 := by exact prefixLift 2398723
  have htrace : WordTrace (prefixWord ++ tailWord_2398723) baseStart_2398723 baseEnd_2398723 := by
    simpa [prefixWord, tailWord_2398723, baseEnd_2398723] using wordTrace_append hprefix tailTrace_2398723
  have hstable : (prefixWord ++ tailWord_2398723).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2398723).length < 2 ^ (prefixWord ++ tailWord_2398723).sum := by decide
  have hdescent : baseEnd_2398723 < baseStart_2398723 := by decide
  rcases family_descends (prefixWord ++ tailWord_2398723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2398770 : List Nat := [3, 2, 1, 1, 2, 1, 2, 4, 3, 3]
def baseStart_2398770 : Nat := 118140960795 + 2398770 * 2 ^ 59
def prefixEnd_2398770 : Nat := 4983230072969 + 3 ^ 40 * 2398770 * 2
def baseEnd_2398770 : Nat := 821147993057123356695509

theorem tailTrace_2398770 : CollatzResearch.WordTrace tailWord_2398770 prefixEnd_2398770 821147993057123356695509 := by
  unfold tailWord_2398770
  simp only [CollatzResearch.WordTrace]
  refine ⟨21872582379918360536258441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58326886346448961430022509 21872582379918360536258441)
  ·
    refine ⟨16404436784938770402193831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21872582379918360536258441 16404436784938770402193831)
    ·
      refine ⟨24606655177408155603290747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16404436784938770402193831 24606655177408155603290747)
      ·
        refine ⟨36909982766112233404936121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24606655177408155603290747 36909982766112233404936121)
        ·
          refine ⟨27682487074584175053702091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36909982766112233404936121 27682487074584175053702091)
          ·
            refine ⟨41523730611876262580553137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27682487074584175053702091 41523730611876262580553137)
            ·
              refine ⟨31142797958907196935414853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41523730611876262580553137 31142797958907196935414853)
              ·
                refine ⟨5839274617295099425390285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31142797958907196935414853 5839274617295099425390285)
                ·
                  refine ⟨2189727981485662284521357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5839274617295099425390285 2189727981485662284521357)
                  ·
                    refine ⟨821147993057123356695509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2189727981485662284521357 821147993057123356695509)
                    ·
                      rfl

theorem cell22_2398770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 4, 3, 3].length) (baseStart_2398770 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2398770 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2398770 prefixEnd_2398770 := by exact prefixLift 2398770
  have htrace : WordTrace (prefixWord ++ tailWord_2398770) baseStart_2398770 baseEnd_2398770 := by
    simpa [prefixWord, tailWord_2398770, baseEnd_2398770] using wordTrace_append hprefix tailTrace_2398770
  have hstable : (prefixWord ++ tailWord_2398770).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2398770).length < 2 ^ (prefixWord ++ tailWord_2398770).sum := by decide
  have hdescent : baseEnd_2398770 < baseStart_2398770 := by decide
  rcases family_descends (prefixWord ++ tailWord_2398770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2398804 : List Nat := [2, 4, 1, 1, 1, 4, 1, 4, 1, 3]
def baseStart_2398804 : Nat := 118140960795 + 2398804 * 2 ^ 59
def prefixEnd_2398804 : Nat := 4983230072969 + 3 ^ 40 * 2398804 * 2
def baseEnd_2398804 : Nat := 821159631951958601345405

theorem tailTrace_2398804 : CollatzResearch.WordTrace tailWord_2398804 prefixEnd_2398804 821159631951958601345405 := by
  unfold tailWord_2398804
  simp only [CollatzResearch.WordTrace]
  refine ⟨43745784800775132975885733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58327713067700177301180977 43745784800775132975885733)
  ·
    refine ⟨8202334650145337432978575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 43745784800775132975885733 8202334650145337432978575)
    ·
      refine ⟨12303501975218006149467863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8202334650145337432978575 12303501975218006149467863)
      ·
        refine ⟨18455252962827009224201795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12303501975218006149467863 18455252962827009224201795)
        ·
          refine ⟨27682879444240513836302693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18455252962827009224201795 27682879444240513836302693)
          ·
            refine ⟨5190539895795096344306755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27682879444240513836302693 5190539895795096344306755)
            ·
              refine ⟨7785809843692644516460133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5190539895795096344306755 7785809843692644516460133)
              ·
                refine ⟨1459839345692370846836275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7785809843692644516460133 1459839345692370846836275)
                ·
                  refine ⟨2189759018538556270254413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1459839345692370846836275 2189759018538556270254413)
                  ·
                    refine ⟨821159631951958601345405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2189759018538556270254413 821159631951958601345405)
                    ·
                      rfl

theorem cell22_2398804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 1, 4, 1, 3].length) (baseStart_2398804 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2398804 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2398804 prefixEnd_2398804 := by exact prefixLift 2398804
  have htrace : WordTrace (prefixWord ++ tailWord_2398804) baseStart_2398804 baseEnd_2398804 := by
    simpa [prefixWord, tailWord_2398804, baseEnd_2398804] using wordTrace_append hprefix tailTrace_2398804
  have hstable : (prefixWord ++ tailWord_2398804).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2398804).length < 2 ^ (prefixWord ++ tailWord_2398804).sum := by decide
  have hdescent : baseEnd_2398804 < baseStart_2398804 := by decide
  rcases family_descends (prefixWord ++ tailWord_2398804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2398828 : List Nat := [2, 2, 1, 1, 3, 1, 3, 1, 8]
def baseStart_2398828 : Nat := 118140960795 + 2398828 * 2 ^ 59
def prefixEnd_2398828 : Nat := 4983230072969 + 3 ^ 40 * 2398828 * 2
def baseEnd_2398828 : Nat := 273722615880810179581777

theorem tailTrace_2398828 : CollatzResearch.WordTrace tailWord_2398828 prefixEnd_2398828 273722615880810179581777 := by
  unfold tailWord_2398828
  simp only [CollatzResearch.WordTrace]
  refine ⟨43746222476731659025322569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58328296635642212033763425 43746222476731659025322569)
  ·
    refine ⟨32809666857548744268991927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43746222476731659025322569 32809666857548744268991927)
    ·
      refine ⟨49214500286323116403487891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32809666857548744268991927 49214500286323116403487891)
      ·
        refine ⟨73821750429484674605231837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49214500286323116403487891 73821750429484674605231837)
        ·
          refine ⟨27683156411056752976961939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 73821750429484674605231837 27683156411056752976961939)
          ·
            refine ⟨41524734616585129465442909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27683156411056752976961939 41524734616585129465442909)
            ·
              refine ⟨15571775481219423549541091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41524734616585129465442909 15571775481219423549541091)
              ·
                refine ⟨23357663221829135324311637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15571775481219423549541091 23357663221829135324311637)
                ·
                  refine ⟨273722615880810179581777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 23357663221829135324311637 273722615880810179581777)
                  ·
                    rfl

theorem cell22_2398828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 8].length) (baseStart_2398828 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2398828 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2398828 prefixEnd_2398828 := by exact prefixLift 2398828
  have htrace : WordTrace (prefixWord ++ tailWord_2398828) baseStart_2398828 baseEnd_2398828 := by
    simpa [prefixWord, tailWord_2398828, baseEnd_2398828] using wordTrace_append hprefix tailTrace_2398828
  have hstable : (prefixWord ++ tailWord_2398828).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2398828).length < 2 ^ (prefixWord ++ tailWord_2398828).sum := by decide
  have hdescent : baseEnd_2398828 < baseStart_2398828 := by decide
  rcases family_descends (prefixWord ++ tailWord_2398828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2398843 : List Nat := [1, 1, 1, 1, 1, 4, 2, 3, 3, 5]
def baseStart_2398843 : Nat := 118140960795 + 2398843 * 2 ^ 59
def prefixEnd_2398843 : Nat := 4983230072969 + 3 ^ 40 * 2398843 * 2
def baseEnd_2398843 : Nat := 821172982448975499620285

theorem tailTrace_2398843 : CollatzResearch.WordTrace tailWord_2398843 prefixEnd_2398843 821172982448975499620285 := by
  unfold tailWord_2398843
  simp only [CollatzResearch.WordTrace]
  refine ⟨87492992048408975612441183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58328661365605983741627455 87492992048408975612441183)
  ·
    refine ⟨131239488072613463418661775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87492992048408975612441183 131239488072613463418661775)
    ·
      refine ⟨196859232108920195127992663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131239488072613463418661775 196859232108920195127992663)
      ·
        refine ⟨295288848163380292691988995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 196859232108920195127992663 295288848163380292691988995)
        ·
          refine ⟨442933272245070439037983493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 295288848163380292691988995 442933272245070439037983493)
          ·
            refine ⟨83049988545950707319621905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 442933272245070439037983493 83049988545950707319621905)
            ·
              refine ⟨62287491409463030489716429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 83049988545950707319621905 62287491409463030489716429)
              ·
                refine ⟨23357809278548636433643661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 62287491409463030489716429 23357809278548636433643661)
                ·
                  refine ⟨8759178479455738662616373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23357809278548636433643661 8759178479455738662616373)
                  ·
                    refine ⟨821172982448975499620285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8759178479455738662616373 821172982448975499620285)
                    ·
                      rfl

theorem cell22_2398843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 3, 3, 5].length) (baseStart_2398843 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2398843 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2398843 prefixEnd_2398843 := by exact prefixLift 2398843
  have htrace : WordTrace (prefixWord ++ tailWord_2398843) baseStart_2398843 baseEnd_2398843 := by
    simpa [prefixWord, tailWord_2398843, baseEnd_2398843] using wordTrace_append hprefix tailTrace_2398843
  have hstable : (prefixWord ++ tailWord_2398843).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2398843).length < 2 ^ (prefixWord ++ tailWord_2398843).sum := by decide
  have hdescent : baseEnd_2398843 < baseStart_2398843 := by decide
  rcases family_descends (prefixWord ++ tailWord_2398843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2398862 : List Nat := [4, 1, 1, 3, 1, 1, 1, 6, 4]
def baseStart_2398862 : Nat := 118140960795 + 2398862 * 2 ^ 59
def prefixEnd_2398862 : Nat := 4983230072969 + 3 ^ 40 * 2398862 * 2
def baseEnd_2398862 : Nat := 273726495512421927798409

theorem tailTrace_2398862 : CollatzResearch.WordTrace tailWord_2398862 prefixEnd_2398862 273726495512421927798409 := by
  unfold tailWord_2398862
  simp only [CollatzResearch.WordTrace]
  refine ⟨10936710629417517732172855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 58329123356893427904921893 10936710629417517732172855)
  ·
    refine ⟨16405065944126276598259283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10936710629417517732172855 16405065944126276598259283)
    ·
      refine ⟨24607598916189414897388925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16405065944126276598259283 24607598916189414897388925)
      ·
        refine ⟨9227849593571030586520847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24607598916189414897388925 9227849593571030586520847)
        ·
          refine ⟨13841774390356545879781271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9227849593571030586520847 13841774390356545879781271)
          ·
            refine ⟨20762661585534818819671907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13841774390356545879781271 20762661585534818819671907)
            ·
              refine ⟨31143992378302228229507861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20762661585534818819671907 31143992378302228229507861)
              ·
                refine ⟨1459874642732916948258181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 31143992378302228229507861 1459874642732916948258181)
                ·
                  refine ⟨273726495512421927798409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1459874642732916948258181 273726495512421927798409)
                  ·
                    rfl

theorem cell22_2398862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 6, 4].length) (baseStart_2398862 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2398862 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2398862 prefixEnd_2398862 := by exact prefixLift 2398862
  have htrace : WordTrace (prefixWord ++ tailWord_2398862) baseStart_2398862 baseEnd_2398862 := by
    simpa [prefixWord, tailWord_2398862, baseEnd_2398862] using wordTrace_append hprefix tailTrace_2398862
  have hstable : (prefixWord ++ tailWord_2398862).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2398862).length < 2 ^ (prefixWord ++ tailWord_2398862).sum := by decide
  have hdescent : baseEnd_2398862 < baseStart_2398862 := by decide
  rcases family_descends (prefixWord ++ tailWord_2398862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2398873 : List Nat := [1, 2, 1, 2, 1, 2, 4, 9]
def baseStart_2398873 : Nat := 118140960795 + 2398873 * 2 ^ 59
def prefixEnd_2398873 : Nat := 4983230072969 + 3 ^ 40 * 2398873 * 2
def baseEnd_2398873 : Nat := 91242583562451713485577

theorem tailTrace_2398873 : CollatzResearch.WordTrace tailWord_2398873 prefixEnd_2398873 91242583562451713485577 := by
  unfold tailWord_2398873
  simp only [CollatzResearch.WordTrace]
  refine ⟨87494086238300290736033273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58329390825533527157355515 87494086238300290736033273)
  ·
    refine ⟨65620564678725218052024955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87494086238300290736033273 65620564678725218052024955)
    ·
      refine ⟨98430847018087827078037433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65620564678725218052024955 98430847018087827078037433)
      ·
        refine ⟨73823135263565870308528075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 98430847018087827078037433 73823135263565870308528075)
        ·
          refine ⟨110734702895348805462792113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73823135263565870308528075 110734702895348805462792113)
          ·
            refine ⟨83051027171511604097094085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 110734702895348805462792113 83051027171511604097094085)
            ·
              refine ⟨15572067594658425768205141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 83051027171511604097094085 15572067594658425768205141)
              ·
                refine ⟨91242583562451713485577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 15572067594658425768205141 91242583562451713485577)
                ·
                  rfl

theorem cell22_2398873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 4, 9].length) (baseStart_2398873 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2398873 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2398873 prefixEnd_2398873 := by exact prefixLift 2398873
  have htrace : WordTrace (prefixWord ++ tailWord_2398873) baseStart_2398873 baseEnd_2398873 := by
    simpa [prefixWord, tailWord_2398873, baseEnd_2398873] using wordTrace_append hprefix tailTrace_2398873
  have hstable : (prefixWord ++ tailWord_2398873).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2398873).length < 2 ^ (prefixWord ++ tailWord_2398873).sum := by decide
  have hdescent : baseEnd_2398873 < baseStart_2398873 := by decide
  rcases family_descends (prefixWord ++ tailWord_2398873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2398877 : List Nat := [1, 4, 2, 1, 1, 1, 2, 5, 2, 3]
def baseStart_2398877 : Nat := 118140960795 + 2398877 * 2 ^ 59
def prefixEnd_2398877 : Nat := 4983230072969 + 3 ^ 40 * 2398877 * 2
def baseEnd_2398877 : Nat := 821184621343810744270181

theorem tailTrace_2398877 : CollatzResearch.WordTrace tailWord_2398877 prefixEnd_2398877 821184621343810744270181 := by
  unfold tailWord_2398877
  simp only [CollatzResearch.WordTrace]
  refine ⟨87494232130285799419178885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58329488086857199612785923 87494232130285799419178885)
  ·
    refine ⟨16405168524428587391096041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 87494232130285799419178885 16405168524428587391096041)
    ·
      refine ⟨12303876393321440543322031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16405168524428587391096041 12303876393321440543322031)
      ·
        refine ⟨18455814589982160814983047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12303876393321440543322031 18455814589982160814983047)
        ·
          refine ⟨27683721884973241222474571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18455814589982160814983047 27683721884973241222474571)
          ·
            refine ⟨41525582827459861833711857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27683721884973241222474571 41525582827459861833711857)
            ·
              refine ⟨31144187120594896375283893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41525582827459861833711857 31144187120594896375283893)
              ·
                refine ⟨2919767542555771535182865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 31144187120594896375283893 2919767542555771535182865)
                ·
                  refine ⟨2189825656916828651387149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2919767542555771535182865 2189825656916828651387149)
                  ·
                    refine ⟨821184621343810744270181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2189825656916828651387149 821184621343810744270181)
                    ·
                      rfl

theorem cell22_2398877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 5, 2, 3].length) (baseStart_2398877 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2398877 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2398877 prefixEnd_2398877 := by exact prefixLift 2398877
  have htrace : WordTrace (prefixWord ++ tailWord_2398877) baseStart_2398877 baseEnd_2398877 := by
    simpa [prefixWord, tailWord_2398877, baseEnd_2398877] using wordTrace_append hprefix tailTrace_2398877
  have hstable : (prefixWord ++ tailWord_2398877).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2398877).length < 2 ^ (prefixWord ++ tailWord_2398877).sum := by decide
  have hdescent : baseEnd_2398877 < baseStart_2398877 := by decide
  rcases family_descends (prefixWord ++ tailWord_2398877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2398894 : List Nat := [4, 1, 4, 1, 1, 1, 1, 2, 4, 3]
def baseStart_2398894 : Nat := 118140960795 + 2398894 * 2 ^ 59
def prefixEnd_2398894 : Nat := 4983230072969 + 3 ^ 40 * 2398894 * 2
def baseEnd_2398894 : Nat := 821190440791228366595129

theorem tailTrace_2398894 : CollatzResearch.WordTrace tailWord_2398894 prefixEnd_2398894 821190440791228366595129 := by
  unfold tailWord_2398894
  simp only [CollatzResearch.WordTrace]
  refine ⟨10936856521403026415318467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 58329901447482807548365157 10936856521403026415318467)
  ·
    refine ⟨16405284782104539622977701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10936856521403026415318467 16405284782104539622977701)
    ·
      refine ⟨3075990896644601179308319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16405284782104539622977701 3075990896644601179308319)
      ·
        refine ⟨4613986344966901768962479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3075990896644601179308319 4613986344966901768962479)
        ·
          refine ⟨6920979517450352653443719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4613986344966901768962479 6920979517450352653443719)
          ·
            refine ⟨10381469276175528980165579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6920979517450352653443719 10381469276175528980165579)
            ·
              refine ⟨15572203914263293470248369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10381469276175528980165579 15572203914263293470248369)
              ·
                refine ⟨11679152935697470102686277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15572203914263293470248369 11679152935697470102686277)
                ·
                  refine ⟨2189841175443275644253677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11679152935697470102686277 2189841175443275644253677)
                  ·
                    refine ⟨821190440791228366595129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2189841175443275644253677 821190440791228366595129)
                    ·
                      rfl

theorem cell22_2398894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 1, 2, 4, 3].length) (baseStart_2398894 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2398894 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2398894 prefixEnd_2398894 := by exact prefixLift 2398894
  have htrace : WordTrace (prefixWord ++ tailWord_2398894) baseStart_2398894 baseEnd_2398894 := by
    simpa [prefixWord, tailWord_2398894, baseEnd_2398894] using wordTrace_append hprefix tailTrace_2398894
  have hstable : (prefixWord ++ tailWord_2398894).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2398894).length < 2 ^ (prefixWord ++ tailWord_2398894).sum := by decide
  have hdescent : baseEnd_2398894 < baseStart_2398894 := by decide
  rcases family_descends (prefixWord ++ tailWord_2398894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2398913 : List Nat := [1, 2, 6, 2, 1, 1, 3, 2, 4]
def baseStart_2398913 : Nat := 118140960795 + 2398913 * 2 ^ 59
def prefixEnd_2398913 : Nat := 4983230072969 + 3 ^ 40 * 2398913 * 2
def baseEnd_2398913 : Nat := 273732314959839550123357

theorem tailTrace_2398913 : CollatzResearch.WordTrace tailWord_2398913 prefixEnd_2398913 273732314959839550123357 := by
  unfold tailWord_2398913
  simp only [CollatzResearch.WordTrace]
  refine ⟨87495545158155377567489393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58330363438770251711659595 87495545158155377567489393)
  ·
    refine ⟨65621658868616533175617045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87495545158155377567489393 65621658868616533175617045)
    ·
      refine ⟨3076015259466399992607049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 65621658868616533175617045 3076015259466399992607049)
      ·
        refine ⟨2307011444599799994455287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3076015259466399992607049 2307011444599799994455287)
        ·
          refine ⟨3460517166899699991682931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2307011444599799994455287 3460517166899699991682931)
          ·
            refine ⟨5190775750349549987524397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3460517166899699991682931 5190775750349549987524397)
            ·
              refine ⟨1946540906381081245321649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5190775750349549987524397 1946540906381081245321649)
              ·
                refine ⟨1459905679785810933991237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1946540906381081245321649 1459905679785810933991237)
                ·
                  refine ⟨273732314959839550123357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1459905679785810933991237 273732314959839550123357)
                  ·
                    rfl

theorem cell22_2398913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 3, 2, 4].length) (baseStart_2398913 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2398913 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2398913 prefixEnd_2398913 := by exact prefixLift 2398913
  have htrace : WordTrace (prefixWord ++ tailWord_2398913) baseStart_2398913 baseEnd_2398913 := by
    simpa [prefixWord, tailWord_2398913, baseEnd_2398913] using wordTrace_append hprefix tailTrace_2398913
  have hstable : (prefixWord ++ tailWord_2398913).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2398913).length < 2 ^ (prefixWord ++ tailWord_2398913).sum := by decide
  have hdescent : baseEnd_2398913 < baseStart_2398913 := by decide
  rcases family_descends (prefixWord ++ tailWord_2398913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2399025 : List Nat := [1, 2, 2, 3, 2, 1, 11]
def baseStart_2399025 : Nat := 118140960795 + 2399025 * 2 ^ 59
def prefixEnd_2399025 : Nat := 4983230072969 + 3 ^ 40 * 2399025 * 2
def baseEnd_2399025 : Nat := 30416121658088433021101

theorem tailTrace_2399025 : CollatzResearch.WordTrace tailWord_2399025 prefixEnd_2399025 30416121658088433021101 := by
  unfold tailWord_2399025
  simp only [CollatzResearch.WordTrace]
  refine ⟨87499630133749620695566529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58333086755833080463711019 87499630133749620695566529)
  ·
    refine ⟨65624722600312215521674897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87499630133749620695566529 65624722600312215521674897)
    ·
      refine ⟨49218541950234161641256173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65624722600312215521674897 49218541950234161641256173)
      ·
        refine ⟨18456953231337810615471065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49218541950234161641256173 18456953231337810615471065)
        ·
          refine ⟨13842714923503357961603299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18456953231337810615471065 13842714923503357961603299)
          ·
            refine ⟨20764072385255036942404949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13842714923503357961603299 20764072385255036942404949)
            ·
              refine ⟨30416121658088433021101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 20764072385255036942404949 30416121658088433021101)
              ·
                rfl

theorem cell22_2399025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 11].length) (baseStart_2399025 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2399025 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2399025 prefixEnd_2399025 := by exact prefixLift 2399025
  have htrace : WordTrace (prefixWord ++ tailWord_2399025) baseStart_2399025 baseEnd_2399025 := by
    simpa [prefixWord, tailWord_2399025, baseEnd_2399025] using wordTrace_append hprefix tailTrace_2399025
  have hstable : (prefixWord ++ tailWord_2399025).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2399025).length < 2 ^ (prefixWord ++ tailWord_2399025).sum := by decide
  have hdescent : baseEnd_2399025 < baseStart_2399025 := by decide
  rcases family_descends (prefixWord ++ tailWord_2399025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2399029 : List Nat := [1, 3, 3, 1, 3, 2, 1, 1, 4, 3]
def baseStart_2399029 : Nat := 118140960795 + 2399029 * 2 ^ 59
def prefixEnd_2399029 : Nat := 4983230072969 + 3 ^ 40 * 2399029 * 2
def baseEnd_2399029 : Nat := 821236654050133014469715

theorem tailTrace_2399029 : CollatzResearch.WordTrace tailWord_2399029 prefixEnd_2399029 821236654050133014469715 := by
  unfold tailWord_2399029
  simp only [CollatzResearch.WordTrace]
  refine ⟨87499776025735129378712141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58333184017156752919141427 87499776025735129378712141)
  ·
    refine ⟨32812416009650673517017053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 87499776025735129378712141 32812416009650673517017053)
    ·
      refine ⟨12304656003619002568881395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32812416009650673517017053 12304656003619002568881395)
      ·
        refine ⟨18456984005428503853322093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12304656003619002568881395 18456984005428503853322093)
        ·
          refine ⟨6921369002035688944995785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18456984005428503853322093 6921369002035688944995785)
          ·
            refine ⟨5191026751526766708746839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6921369002035688944995785 5191026751526766708746839)
            ·
              refine ⟨7786540127290150063120259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5191026751526766708746839 7786540127290150063120259)
              ·
                refine ⟨11679810190935225094680389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7786540127290150063120259 11679810190935225094680389)
                ·
                  refine ⟨2189964410800354705252573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11679810190935225094680389 2189964410800354705252573)
                  ·
                    refine ⟨821236654050133014469715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2189964410800354705252573 821236654050133014469715)
                    ·
                      rfl

theorem cell22_2399029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 1, 1, 4, 3].length) (baseStart_2399029 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2399029 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2399029 prefixEnd_2399029 := by exact prefixLift 2399029
  have htrace : WordTrace (prefixWord ++ tailWord_2399029) baseStart_2399029 baseEnd_2399029 := by
    simpa [prefixWord, tailWord_2399029, baseEnd_2399029] using wordTrace_append hprefix tailTrace_2399029
  have hstable : (prefixWord ++ tailWord_2399029).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2399029).length < 2 ^ (prefixWord ++ tailWord_2399029).sum := by decide
  have hdescent : baseEnd_2399029 < baseStart_2399029 := by decide
  rcases family_descends (prefixWord ++ tailWord_2399029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2399162 : List Nat := [3, 1, 1, 1, 2, 1, 4, 2, 1, 6]
def baseStart_2399162 : Nat := 118140960795 + 2399162 * 2 ^ 59
def prefixEnd_2399162 : Nat := 4983230072969 + 3 ^ 40 * 2399162 * 2
def baseEnd_2399162 : Nat := 821282182668165000894307

theorem tailTrace_2399162 : CollatzResearch.WordTrace tailWord_2399162 prefixEnd_2399162 821282182668165000894307 := by
  unfold tailWord_2399162
  simp only [CollatzResearch.WordTrace]
  refine ⟨21876156733563323273325935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58336417956168862062202493 21876156733563323273325935)
  ·
    refine ⟨32814235100344984909988903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21876156733563323273325935 32814235100344984909988903)
    ·
      refine ⟨49221352650517477364983355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32814235100344984909988903 49221352650517477364983355)
      ·
        refine ⟨73832028975776216047475033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49221352650517477364983355 73832028975776216047475033)
        ·
          refine ⟨55374021731832162035606275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73832028975776216047475033 55374021731832162035606275)
          ·
            refine ⟨83061032597748243053409413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55374021731832162035606275 83061032597748243053409413)
            ·
              refine ⟨15573943612077795572514265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 83061032597748243053409413 15573943612077795572514265)
              ·
                refine ⟨11680457709058346679385699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15573943612077795572514265 11680457709058346679385699)
                ·
                  refine ⟨17520686563587520019078549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11680457709058346679385699 17520686563587520019078549)
                  ·
                    refine ⟨821282182668165000894307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17520686563587520019078549 821282182668165000894307)
                    ·
                      rfl

theorem cell22_2399162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 4, 2, 1, 6].length) (baseStart_2399162 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2399162 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2399162 prefixEnd_2399162 := by exact prefixLift 2399162
  have htrace : WordTrace (prefixWord ++ tailWord_2399162) baseStart_2399162 baseEnd_2399162 := by
    simpa [prefixWord, tailWord_2399162, baseEnd_2399162] using wordTrace_append hprefix tailTrace_2399162
  have hstable : (prefixWord ++ tailWord_2399162).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2399162).length < 2 ^ (prefixWord ++ tailWord_2399162).sum := by decide
  have hdescent : baseEnd_2399162 < baseStart_2399162 := by decide
  rcases family_descends (prefixWord ++ tailWord_2399162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2399179 : List Nat := [1, 1, 1, 1, 3, 5, 3, 1, 2, 4]
def baseStart_2399179 : Nat := 118140960795 + 2399179 * 2 ^ 59
def prefixEnd_2399179 : Nat := 4983230072969 + 3 ^ 40 * 2399179 * 2
def baseEnd_2399179 : Nat := 821288002115582623219255

theorem tailTrace_2399179 : CollatzResearch.WordTrace tailWord_2399179 prefixEnd_2399179 821288002115582623219255 := by
  unfold tailWord_2399179
  simp only [CollatzResearch.WordTrace]
  refine ⟨87505246975191704996672591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58336831316794469997781727 87505246975191704996672591)
  ·
    refine ⟨131257870462787557495008887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87505246975191704996672591 131257870462787557495008887)
    ·
      refine ⟨196886805694181336242513331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131257870462787557495008887 196886805694181336242513331)
      ·
        refine ⟨295330208541272004363769997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 196886805694181336242513331 295330208541272004363769997)
        ·
          refine ⟨110748828202977001636413749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 295330208541272004363769997 110748828202977001636413749)
          ·
            refine ⟨10382702644029093903413789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 110748828202977001636413749 10382702644029093903413789)
            ·
              refine ⟨3893513491510910213780171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10382702644029093903413789 3893513491510910213780171)
              ·
                refine ⟨5840270237266365320670257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3893513491510910213780171 5840270237266365320670257)
                ·
                  refine ⟨4380202677949773990502693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5840270237266365320670257 4380202677949773990502693)
                  ·
                    refine ⟨821288002115582623219255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4380202677949773990502693 821288002115582623219255)
                    ·
                      rfl

theorem cell22_2399179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 3, 1, 2, 4].length) (baseStart_2399179 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2399179 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2399179 prefixEnd_2399179 := by exact prefixLift 2399179
  have htrace : WordTrace (prefixWord ++ tailWord_2399179) baseStart_2399179 baseEnd_2399179 := by
    simpa [prefixWord, tailWord_2399179, baseEnd_2399179] using wordTrace_append hprefix tailTrace_2399179
  have hstable : (prefixWord ++ tailWord_2399179).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2399179).length < 2 ^ (prefixWord ++ tailWord_2399179).sum := by decide
  have hdescent : baseEnd_2399179 < baseStart_2399179 := by decide
  rcases family_descends (prefixWord ++ tailWord_2399179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2399243 : List Nat := [1, 1, 1, 1, 6, 2, 3, 3, 1, 3]
def baseStart_2399243 : Nat := 118140960795 + 2399243 * 2 ^ 59
def prefixEnd_2399243 : Nat := 4983230072969 + 3 ^ 40 * 2399243 * 2
def baseEnd_2399243 : Nat := 821309910623507789619059

theorem tailTrace_2399243 : CollatzResearch.WordTrace tailWord_2399243 prefixEnd_2399243 821309910623507789619059 := by
  unfold tailWord_2399243
  simp only [CollatzResearch.WordTrace]
  refine ⟨87507581246959843927002383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58338387497973229284668255 87507581246959843927002383)
  ·
    refine ⟨131261371870439765890503575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87507581246959843927002383 131261371870439765890503575)
    ·
      refine ⟨196892057805659648835755363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131261371870439765890503575 196892057805659648835755363)
      ·
        refine ⟨295338086708489473253633045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 196892057805659648835755363 295338086708489473253633045)
        ·
          refine ⟨13843972814460444058764049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 295338086708489473253633045 13843972814460444058764049)
          ·
            refine ⟨10382979610845333044073037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13843972814460444058764049 10382979610845333044073037)
            ·
              refine ⟨3893617354066999891527389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10382979610845333044073037 3893617354066999891527389)
              ·
                refine ⟨1460106507775124959322771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3893617354066999891527389 1460106507775124959322771)
                ·
                  refine ⟨2190159761662687438984157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1460106507775124959322771 2190159761662687438984157)
                  ·
                    refine ⟨821309910623507789619059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2190159761662687438984157 821309910623507789619059)
                    ·
                      rfl

theorem cell22_2399243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 3, 3, 1, 3].length) (baseStart_2399243 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2399243 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2399243 prefixEnd_2399243 := by exact prefixLift 2399243
  have htrace : WordTrace (prefixWord ++ tailWord_2399243) baseStart_2399243 baseEnd_2399243 := by
    simpa [prefixWord, tailWord_2399243, baseEnd_2399243] using wordTrace_append hprefix tailTrace_2399243
  have hstable : (prefixWord ++ tailWord_2399243).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2399243).length < 2 ^ (prefixWord ++ tailWord_2399243).sum := by decide
  have hdescent : baseEnd_2399243 < baseStart_2399243 := by decide
  rcases family_descends (prefixWord ++ tailWord_2399243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2399260 : List Nat := [2, 2, 3, 1, 5, 1, 1, 1, 3, 3]
def baseStart_2399260 : Nat := 118140960795 + 2399260 * 2 ^ 59
def prefixEnd_2399260 : Nat := 4983230072969 + 3 ^ 40 * 2399260 * 2
def baseEnd_2399260 : Nat := 821315730070925411944007

theorem tailTrace_2399260 : CollatzResearch.WordTrace tailWord_2399260 prefixEnd_2399260 821315730070925411944007 := by
  unfold tailWord_2399260
  simp only [CollatzResearch.WordTrace]
  refine ⟨43754100643949127915185617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58338800858598837220247489 43754100643949127915185617)
  ·
    refine ⟨32815575482961845936389213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43754100643949127915185617 32815575482961845936389213)
    ·
      refine ⟨12305840806110692226145955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32815575482961845936389213 12305840806110692226145955)
      ·
        refine ⟨18458761209166038339218933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12305840806110692226145955 18458761209166038339218933)
        ·
          refine ⟨1730508863359316094301775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 18458761209166038339218933 1730508863359316094301775)
          ·
            refine ⟨2595763295038974141452663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1730508863359316094301775 2595763295038974141452663)
            ·
              refine ⟨3893644942558461212178995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2595763295038974141452663 3893644942558461212178995)
              ·
                refine ⟨5840467413837691818268493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3893644942558461212178995 5840467413837691818268493)
                ·
                  refine ⟨2190175280189134431850685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5840467413837691818268493 2190175280189134431850685)
                  ·
                    refine ⟨821315730070925411944007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2190175280189134431850685 821315730070925411944007)
                    ·
                      rfl

theorem cell22_2399260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 5, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 5, 1, 1, 1, 3, 3].length) (baseStart_2399260 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2399260 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2399260 prefixEnd_2399260 := by exact prefixLift 2399260
  have htrace : WordTrace (prefixWord ++ tailWord_2399260) baseStart_2399260 baseEnd_2399260 := by
    simpa [prefixWord, tailWord_2399260, baseEnd_2399260] using wordTrace_append hprefix tailTrace_2399260
  have hstable : (prefixWord ++ tailWord_2399260).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2399260).length < 2 ^ (prefixWord ++ tailWord_2399260).sum := by decide
  have hdescent : baseEnd_2399260 < baseStart_2399260 := by decide
  rcases family_descends (prefixWord ++ tailWord_2399260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2399269 : List Nat := [1, 3, 1, 2, 2, 2, 2, 2, 3, 4]
def baseStart_2399269 : Nat := 118140960795 + 2399269 * 2 ^ 59
def prefixEnd_2399269 : Nat := 4983230072969 + 3 ^ 40 * 2399269 * 2
def baseEnd_2399269 : Nat := 821318810954852388468979

theorem tailTrace_2399269 : CollatzResearch.WordTrace tailWord_2399269 prefixEnd_2399269 821318810954852388468979 := by
  unfold tailWord_2399269
  simp only [CollatzResearch.WordTrace]
  refine ⟨87508529544865650367448861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58339019696577100244965907 87508529544865650367448861)
  ·
    refine ⟨32815698579324618887793323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 87508529544865650367448861 32815698579324618887793323)
    ·
      refine ⟨49223547868986928331689985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32815698579324618887793323 49223547868986928331689985)
      ·
        refine ⟨36917660901740196248767489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49223547868986928331689985 36917660901740196248767489)
        ·
          refine ⟨27688245676305147186575617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36917660901740196248767489 27688245676305147186575617)
          ·
            refine ⟨20766184257228860389931713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27688245676305147186575617 20766184257228860389931713)
            ·
              refine ⟨15574638192921645292448785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20766184257228860389931713 15574638192921645292448785)
              ·
                refine ⟨11680978644691233969336589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15574638192921645292448785 11680978644691233969336589)
                ·
                  refine ⟨4380366991759212738501221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11680978644691233969336589 4380366991759212738501221)
                  ·
                    refine ⟨821318810954852388468979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4380366991759212738501221 821318810954852388468979)
                    ·
                      rfl

theorem cell22_2399269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 2, 2, 3, 4].length) (baseStart_2399269 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2399269 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2399269 prefixEnd_2399269 := by exact prefixLift 2399269
  have htrace : WordTrace (prefixWord ++ tailWord_2399269) baseStart_2399269 baseEnd_2399269 := by
    simpa [prefixWord, tailWord_2399269, baseEnd_2399269] using wordTrace_append hprefix tailTrace_2399269
  have hstable : (prefixWord ++ tailWord_2399269).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2399269).length < 2 ^ (prefixWord ++ tailWord_2399269).sum := by decide
  have hdescent : baseEnd_2399269 < baseStart_2399269 := by decide
  rcases family_descends (prefixWord ++ tailWord_2399269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2399299 : List Nat := [1, 1, 1, 3, 1, 2, 5, 2, 1, 5]
def baseStart_2399299 : Nat := 118140960795 + 2399299 * 2 ^ 59
def prefixEnd_2399299 : Nat := 4983230072969 + 3 ^ 40 * 2399299 * 2
def baseEnd_2399299 : Nat := 821329080567942310218887

theorem tailTrace_2399299 : CollatzResearch.WordTrace tailWord_2399299 prefixEnd_2399299 821329080567942310218887 := by
  unfold tailWord_2399299
  simp only [CollatzResearch.WordTrace]
  refine ⟨87509623734756965491040951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58339749156504643660693967 87509623734756965491040951)
  ·
    refine ⟨131264435602135448236561427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87509623734756965491040951 131264435602135448236561427)
    ·
      refine ⟨196896653403203172354842141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131264435602135448236561427 196896653403203172354842141)
      ·
        refine ⟨73836245026201189633065803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 196896653403203172354842141 73836245026201189633065803)
        ·
          refine ⟨110754367539301784449598705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73836245026201189633065803 110754367539301784449598705)
          ·
            refine ⟨83065775654476338337199029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 110754367539301784449598705 83065775654476338337199029)
            ·
              refine ⟨7787416467607156719112409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 83065775654476338337199029 7787416467607156719112409)
              ·
                refine ⟨5840562350705367539334307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7787416467607156719112409 5840562350705367539334307)
                ·
                  refine ⟨8760843526058051309001461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5840562350705367539334307 8760843526058051309001461)
                  ·
                    refine ⟨821329080567942310218887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8760843526058051309001461 821329080567942310218887)
                    ·
                      rfl

theorem cell22_2399299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 5, 2, 1, 5].length) (baseStart_2399299 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2399299 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2399299 prefixEnd_2399299 := by exact prefixLift 2399299
  have htrace : WordTrace (prefixWord ++ tailWord_2399299) baseStart_2399299 baseEnd_2399299 := by
    simpa [prefixWord, tailWord_2399299, baseEnd_2399299] using wordTrace_append hprefix tailTrace_2399299
  have hstable : (prefixWord ++ tailWord_2399299).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2399299).length < 2 ^ (prefixWord ++ tailWord_2399299).sum := by decide
  have hdescent : baseEnd_2399299 < baseStart_2399299 := by decide
  rcases family_descends (prefixWord ++ tailWord_2399299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2399303 : List Nat := [1, 1, 4, 1, 3, 3, 3, 1, 1, 4]
def baseStart_2399303 : Nat := 118140960795 + 2399303 * 2 ^ 59
def prefixEnd_2399303 : Nat := 4983230072969 + 3 ^ 40 * 2399303 * 2
def baseEnd_2399303 : Nat := 821330449849687633118875

theorem tailTrace_2399303 : CollatzResearch.WordTrace tailWord_2399303 prefixEnd_2399303 821330449849687633118875 := by
  unfold tailWord_2399303
  simp only [CollatzResearch.WordTrace]
  refine ⟨87509769626742474174186563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58339846417828316116124375 87509769626742474174186563)
  ·
    refine ⟨131264654440113711261279845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87509769626742474174186563 131264654440113711261279845)
    ·
      refine ⟨24612122707521320861489971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 131264654440113711261279845 24612122707521320861489971)
      ·
        refine ⟨36918184061281981292234957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24612122707521320861489971 36918184061281981292234957)
        ·
          refine ⟨13844319022980742984588109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36918184061281981292234957 13844319022980742984588109)
          ·
            refine ⟨5191619633617778619220541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13844319022980742984588109 5191619633617778619220541)
            ·
              refine ⟨1946857362606666982207703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5191619633617778619220541 1946857362606666982207703)
              ·
                refine ⟨2920286043910000473311555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1946857362606666982207703 2920286043910000473311555)
                ·
                  refine ⟨4380429065865000709967333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2920286043910000473311555 4380429065865000709967333)
                  ·
                    refine ⟨821330449849687633118875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4380429065865000709967333 821330449849687633118875)
                    ·
                      rfl

theorem cell22_2399303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 3, 1, 1, 4].length) (baseStart_2399303 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2399303 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2399303 prefixEnd_2399303 := by exact prefixLift 2399303
  have htrace : WordTrace (prefixWord ++ tailWord_2399303) baseStart_2399303 baseEnd_2399303 := by
    simpa [prefixWord, tailWord_2399303, baseEnd_2399303] using wordTrace_append hprefix tailTrace_2399303
  have hstable : (prefixWord ++ tailWord_2399303).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2399303).length < 2 ^ (prefixWord ++ tailWord_2399303).sum := by decide
  have hdescent : baseEnd_2399303 < baseStart_2399303 := by decide
  rcases family_descends (prefixWord ++ tailWord_2399303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2399316 : List Nat := [2, 4, 1, 1, 1, 1, 2, 3, 4, 3]
def baseStart_2399316 : Nat := 118140960795 + 2399316 * 2 ^ 59
def prefixEnd_2399316 : Nat := 4983230072969 + 3 ^ 40 * 2399316 * 2
def baseEnd_2399316 : Nat := 821334900015359932543835

theorem tailTrace_2399316 : CollatzResearch.WordTrace tailWord_2399316 prefixEnd_2399316 821334900015359932543835 := by
  unfold tailWord_2399316
  simp only [CollatzResearch.WordTrace]
  refine ⟨43755121887847688697204901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58340162517130251596273201 43755121887847688697204901)
  ·
    refine ⟨8204085353971441630725919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 43755121887847688697204901 8204085353971441630725919)
    ·
      refine ⟨12306128030957162446088879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8204085353971441630725919 12306128030957162446088879)
      ·
        refine ⟨18459192046435743669133319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12306128030957162446088879 18459192046435743669133319)
        ·
          refine ⟨27688788069653615503699979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18459192046435743669133319 27688788069653615503699979)
          ·
            refine ⟨41533182104480423255549969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27688788069653615503699979 41533182104480423255549969)
            ·
              refine ⟨31149886578360317441662477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41533182104480423255549969 31149886578360317441662477)
              ·
                refine ⟨11681207466885119040623429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31149886578360317441662477 11681207466885119040623429)
                ·
                  refine ⟨2190226400040959820116893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11681207466885119040623429 2190226400040959820116893)
                  ·
                    refine ⟨821334900015359932543835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2190226400040959820116893 821334900015359932543835)
                    ·
                      rfl

theorem cell22_2399316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 3, 4, 3].length) (baseStart_2399316 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2399316 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2399316 prefixEnd_2399316 := by exact prefixLift 2399316
  have htrace : WordTrace (prefixWord ++ tailWord_2399316) baseStart_2399316 baseEnd_2399316 := by
    simpa [prefixWord, tailWord_2399316, baseEnd_2399316] using wordTrace_append hprefix tailTrace_2399316
  have hstable : (prefixWord ++ tailWord_2399316).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2399316).length < 2 ^ (prefixWord ++ tailWord_2399316).sum := by decide
  have hdescent : baseEnd_2399316 < baseStart_2399316 := by decide
  rcases family_descends (prefixWord ++ tailWord_2399316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2399329 : List Nat := [1, 2, 3, 1, 1, 2, 5, 7]
def baseStart_2399329 : Nat := 118140960795 + 2399329 * 2 ^ 59
def prefixEnd_2399329 : Nat := 4983230072969 + 3 ^ 40 * 2399329 * 2
def baseEnd_2399329 : Nat := 91259927797892470218755

theorem tailTrace_2399329 : CollatzResearch.WordTrace tailWord_2399329 prefixEnd_2399329 91259927797892470218755 := by
  unfold tailWord_2399329
  simp only [CollatzResearch.WordTrace]
  refine ⟨87510717924648280614633041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58340478616432187076422027 87510717924648280614633041)
  ·
    refine ⟨65633038443486210460974781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87510717924648280614633041 65633038443486210460974781)
    ·
      refine ⟨24612389416307328922865543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65633038443486210460974781 24612389416307328922865543)
      ·
        refine ⟨36918584124460993384298315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24612389416307328922865543 36918584124460993384298315)
        ·
          refine ⟨55377876186691490076447473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36918584124460993384298315 55377876186691490076447473)
          ·
            refine ⟨41533407140018617557335605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55377876186691490076447473 41533407140018617557335605)
            ·
              refine ⟨3893756919376745396000213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 41533407140018617557335605 3893756919376745396000213)
              ·
                refine ⟨91259927797892470218755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3893756919376745396000213 91259927797892470218755)
                ·
                  rfl

theorem cell22_2399329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 5, 7].length) (baseStart_2399329 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2399329 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2399329 prefixEnd_2399329 := by exact prefixLift 2399329
  have htrace : WordTrace (prefixWord ++ tailWord_2399329) baseStart_2399329 baseEnd_2399329 := by
    simpa [prefixWord, tailWord_2399329, baseEnd_2399329] using wordTrace_append hprefix tailTrace_2399329
  have hstable : (prefixWord ++ tailWord_2399329).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2399329).length < 2 ^ (prefixWord ++ tailWord_2399329).sum := by decide
  have hdescent : baseEnd_2399329 < baseStart_2399329 := by decide
  rcases family_descends (prefixWord ++ tailWord_2399329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2399346 : List Nat := [3, 2, 1, 2, 2, 1, 5, 6]
def baseStart_2399346 : Nat := 118140960795 + 2399346 * 2 ^ 59
def prefixEnd_2399346 : Nat := 4983230072969 + 3 ^ 40 * 2399346 * 2
def baseEnd_2399346 : Nat := 91260574403161094921527

theorem tailTrace_2399346 : CollatzResearch.WordTrace tailWord_2399346 prefixEnd_2399346 91260574403161094921527 := by
  unfold tailWord_2399346
  simp only [CollatzResearch.WordTrace]
  refine ⟨21877834491396673129500473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58340891977057795012001261 21877834491396673129500473)
  ·
    refine ⟨16408375868547504847125355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21877834491396673129500473 16408375868547504847125355)
    ·
      refine ⟨24612563802821257270688033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16408375868547504847125355 24612563802821257270688033)
      ·
        refine ⟨18459422852115942953016025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24612563802821257270688033 18459422852115942953016025)
        ·
          refine ⟨13844567139086957214762019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18459422852115942953016025 13844567139086957214762019)
          ·
            refine ⟨20766850708630435822143029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13844567139086957214762019 20766850708630435822143029)
            ·
              refine ⟨1946892253934103358325909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 20766850708630435822143029 1946892253934103358325909)
              ·
                refine ⟨91260574403161094921527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1946892253934103358325909 91260574403161094921527)
                ·
                  rfl

theorem cell22_2399346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 5, 6].length) (baseStart_2399346 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2399346 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2399346 prefixEnd_2399346 := by exact prefixLift 2399346
  have htrace : WordTrace (prefixWord ++ tailWord_2399346) baseStart_2399346 baseEnd_2399346 := by
    simpa [prefixWord, tailWord_2399346, baseEnd_2399346] using wordTrace_append hprefix tailTrace_2399346
  have hstable : (prefixWord ++ tailWord_2399346).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2399346).length < 2 ^ (prefixWord ++ tailWord_2399346).sum := by decide
  have hdescent : baseEnd_2399346 < baseStart_2399346 := by decide
  rcases family_descends (prefixWord ++ tailWord_2399346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2399378 : List Nat := [3, 2, 3, 1, 1, 2, 1, 3, 3, 3]
def baseStart_2399378 : Nat := 118140960795 + 2399378 * 2 ^ 59
def prefixEnd_2399378 : Nat := 4983230072969 + 3 ^ 40 * 2399378 * 2
def baseEnd_2399378 : Nat := 821356123882412437493645

theorem tailTrace_2399378 : CollatzResearch.WordTrace tailWord_2399378 prefixEnd_2399378 821356123882412437493645 := by
  unfold tailWord_2399378
  simp only [CollatzResearch.WordTrace]
  refine ⟨21878126275367690495791697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58341670067647174655444525 21878126275367690495791697)
  ·
    refine ⟨16408594706525767871843773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21878126275367690495791697 16408594706525767871843773)
    ·
      refine ⟨6153223014947162951941415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16408594706525767871843773 6153223014947162951941415)
      ·
        refine ⟨9229834522420744427912123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6153223014947162951941415 9229834522420744427912123)
        ·
          refine ⟨13844751783631116641868185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9229834522420744427912123 13844751783631116641868185)
          ·
            refine ⟨10383563837723337481401139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13844751783631116641868185 10383563837723337481401139)
            ·
              refine ⟨15575345756585006222101709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10383563837723337481401139 15575345756585006222101709)
              ·
                refine ⟨5840754658719377333288141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15575345756585006222101709 5840754658719377333288141)
                ·
                  refine ⟨2190282997019766499983053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5840754658719377333288141 2190282997019766499983053)
                  ·
                    refine ⟨821356123882412437493645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2190282997019766499983053 821356123882412437493645)
                    ·
                      rfl

theorem cell22_2399378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 1, 3, 3, 3].length) (baseStart_2399378 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2399378 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2399378 prefixEnd_2399378 := by exact prefixLift 2399378
  have htrace : WordTrace (prefixWord ++ tailWord_2399378) baseStart_2399378 baseEnd_2399378 := by
    simpa [prefixWord, tailWord_2399378, baseEnd_2399378] using wordTrace_append hprefix tailTrace_2399378
  have hstable : (prefixWord ++ tailWord_2399378).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2399378).length < 2 ^ (prefixWord ++ tailWord_2399378).sum := by decide
  have hdescent : baseEnd_2399378 < baseStart_2399378 := by decide
  rcases family_descends (prefixWord ++ tailWord_2399378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2399511 : List Nat := [1, 1, 3, 4, 1, 1, 1, 2, 2, 6]
def baseStart_2399511 : Nat := 118140960795 + 2399511 * 2 ^ 59
def prefixEnd_2399511 : Nat := 4983230072969 + 3 ^ 40 * 2399511 * 2
def baseEnd_2399511 : Nat := 821401652500444423918237

theorem tailTrace_2399511 : CollatzResearch.WordTrace tailWord_2399511 prefixEnd_2399511 821401652500444423918237 := by
  unfold tailWord_2399511
  simp only [CollatzResearch.WordTrace]
  refine ⟨87517356009988925697758387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58344904006659283798505591 87517356009988925697758387)
  ·
    refine ⟨131276034014983388546637581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87517356009988925697758387 131276034014983388546637581)
    ·
      refine ⟨49228512755618770704989093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 131276034014983388546637581 49228512755618770704989093)
      ·
        refine ⟨9230346141678519507185455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 49228512755618770704989093 9230346141678519507185455)
        ·
          refine ⟨13845519212517779260778183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9230346141678519507185455 13845519212517779260778183)
          ·
            refine ⟨20768278818776668891167275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13845519212517779260778183 20768278818776668891167275)
            ·
              refine ⟨31152418228165003336750913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20768278818776668891167275 31152418228165003336750913)
              ·
                refine ⟨23364313671123752502563185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31152418228165003336750913 23364313671123752502563185)
                ·
                  refine ⟨17523235253342814376922389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23364313671123752502563185 17523235253342814376922389)
                  ·
                    refine ⟨821401652500444423918237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17523235253342814376922389 821401652500444423918237)
                    ·
                      rfl

theorem cell22_2399511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 2, 2, 6].length) (baseStart_2399511 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2399511 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2399511 prefixEnd_2399511 := by exact prefixLift 2399511
  have htrace : WordTrace (prefixWord ++ tailWord_2399511) baseStart_2399511 baseEnd_2399511 := by
    simpa [prefixWord, tailWord_2399511, baseEnd_2399511] using wordTrace_append hprefix tailTrace_2399511
  have hstable : (prefixWord ++ tailWord_2399511).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2399511).length < 2 ^ (prefixWord ++ tailWord_2399511).sum := by decide
  have hdescent : baseEnd_2399511 < baseStart_2399511 := by decide
  rcases family_descends (prefixWord ++ tailWord_2399511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2399571 : List Nat := [1, 1, 1, 2, 1, 1, 5, 4, 6]
def baseStart_2399571 : Nat := 118140960795 + 2399571 * 2 ^ 59
def prefixEnd_2399571 : Nat := 4983230072969 + 3 ^ 40 * 2399571 * 2
def baseEnd_2399571 : Nat := 273807397242208089139351

theorem tailTrace_2399571 : CollatzResearch.WordTrace tailWord_2399571 prefixEnd_2399571 273807397242208089139351 := by
  unfold tailWord_2399571
  simp only [CollatzResearch.WordTrace]
  refine ⟨87519544389771555944942567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58346362926514370629961711 87519544389771555944942567)
  ·
    refine ⟨131279316584657333917413851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87519544389771555944942567 131279316584657333917413851)
    ·
      refine ⟨196918974876986000876120777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131279316584657333917413851 196918974876986000876120777)
      ·
        refine ⟨147689231157739500657090583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 196918974876986000876120777 147689231157739500657090583)
        ·
          refine ⟨221533846736609250985635875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 147689231157739500657090583 221533846736609250985635875)
          ·
            refine ⟨332300770104913876478453813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 221533846736609250985635875 332300770104913876478453813)
            ·
              refine ⟨31153197197335675919855045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 332300770104913876478453813 31153197197335675919855045)
              ·
                refine ⟨5841224474500439234972821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31153197197335675919855045 5841224474500439234972821)
                ·
                  refine ⟨273807397242208089139351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5841224474500439234972821 273807397242208089139351)
                  ·
                    rfl

theorem cell22_2399571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 4, 6].length) (baseStart_2399571 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2399571 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2399571 prefixEnd_2399571 := by exact prefixLift 2399571
  have htrace : WordTrace (prefixWord ++ tailWord_2399571) baseStart_2399571 baseEnd_2399571 := by
    simpa [prefixWord, tailWord_2399571, baseEnd_2399571] using wordTrace_append hprefix tailTrace_2399571
  have hstable : (prefixWord ++ tailWord_2399571).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2399571).length < 2 ^ (prefixWord ++ tailWord_2399571).sum := by decide
  have hdescent : baseEnd_2399571 < baseStart_2399571 := by decide
  rcases family_descends (prefixWord ++ tailWord_2399571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2399656 : List Nat := [2, 1, 6, 1, 2, 2, 2, 2, 4]
def baseStart_2399656 : Nat := 118140960795 + 2399656 * 2 ^ 59
def prefixEnd_2399656 : Nat := 4983230072969 + 3 ^ 40 * 2399656 * 2
def baseEnd_2399656 : Nat := 273817096321237459680931

theorem tailTrace_2399656 : CollatzResearch.WordTrace tailWord_2399656 prefixEnd_2399656 273817096321237459680931 := by
  unfold tailWord_2399656
  simp only [CollatzResearch.WordTrace]
  refine ⟨43761322297231807730893411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58348429729642410307857881 43761322297231807730893411)
  ·
    refine ⟨65641983445847711596340117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43761322297231807730893411 65641983445847711596340117)
    ·
      refine ⟨3076967974024111481078443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 65641983445847711596340117 3076967974024111481078443)
      ·
        refine ⟨4615451961036167221617665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3076967974024111481078443 4615451961036167221617665)
        ·
          refine ⟨3461588970777125416213249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4615451961036167221617665 3461588970777125416213249)
          ·
            refine ⟨2596191728082844062159937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3461588970777125416213249 2596191728082844062159937)
            ·
              refine ⟨1947143796062133046619953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2596191728082844062159937 1947143796062133046619953)
              ·
                refine ⟨1460357847046599784964965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1947143796062133046619953 1460357847046599784964965)
                ·
                  refine ⟨273817096321237459680931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1460357847046599784964965 273817096321237459680931)
                  ·
                    rfl

theorem cell22_2399656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 2, 2, 2, 4].length) (baseStart_2399656 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2399656 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2399656 prefixEnd_2399656 := by exact prefixLift 2399656
  have htrace : WordTrace (prefixWord ++ tailWord_2399656) baseStart_2399656 baseEnd_2399656 := by
    simpa [prefixWord, tailWord_2399656, baseEnd_2399656] using wordTrace_append hprefix tailTrace_2399656
  have hstable : (prefixWord ++ tailWord_2399656).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2399656).length < 2 ^ (prefixWord ++ tailWord_2399656).sum := by decide
  have hdescent : baseEnd_2399656 < baseStart_2399656 := by decide
  rcases family_descends (prefixWord ++ tailWord_2399656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2399665 : List Nat := [1, 2, 2, 4, 1, 1, 2, 3, 3, 3]
def baseStart_2399665 : Nat := 118140960795 + 2399665 * 2 ^ 59
def prefixEnd_2399665 : Nat := 4983230072969 + 3 ^ 40 * 2399665 * 2
def baseEnd_2399665 : Nat := 821454369847639355567765

theorem tailTrace_2399665 : CollatzResearch.WordTrace tailWord_2399665 prefixEnd_2399665 821454369847639355567765 := by
  unfold tailWord_2399665
  simp only [CollatzResearch.WordTrace]
  refine ⟨87522972851431009998864449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58348648567620673332576299 87522972851431009998864449)
  ·
    refine ⟨65642229638573257499148337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87522972851431009998864449 65642229638573257499148337)
    ·
      refine ⟨49231672228929943124361253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65642229638573257499148337 49231672228929943124361253)
      ·
        refine ⟨9230938542924364335817735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 49231672228929943124361253 9230938542924364335817735)
        ·
          refine ⟨13846407814386546503726603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9230938542924364335817735 13846407814386546503726603)
          ·
            refine ⟨20769611721579819755589905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13846407814386546503726603 20769611721579819755589905)
            ·
              refine ⟨15577208791184864816692429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20769611721579819755589905 15577208791184864816692429)
              ·
                refine ⟨5841453296694324306259661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15577208791184864816692429 5841453296694324306259661)
                ·
                  refine ⟨2190544986260371614847373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5841453296694324306259661 2190544986260371614847373)
                  ·
                    refine ⟨821454369847639355567765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2190544986260371614847373 821454369847639355567765)
                    ·
                      rfl

theorem cell22_2399665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 2, 3, 3, 3].length) (baseStart_2399665 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2399665 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2399665 prefixEnd_2399665 := by exact prefixLift 2399665
  have htrace : WordTrace (prefixWord ++ tailWord_2399665) baseStart_2399665 baseEnd_2399665 := by
    simpa [prefixWord, tailWord_2399665, baseEnd_2399665] using wordTrace_append hprefix tailTrace_2399665
  have hstable : (prefixWord ++ tailWord_2399665).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2399665).length < 2 ^ (prefixWord ++ tailWord_2399665).sum := by decide
  have hdescent : baseEnd_2399665 < baseStart_2399665 := by decide
  rcases family_descends (prefixWord ++ tailWord_2399665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2399678 : List Nat := [4, 2, 1, 1, 1, 1, 1, 2, 9]
def baseStart_2399678 : Nat := 118140960795 + 2399678 * 2 ^ 59
def prefixEnd_2399678 : Nat := 4983230072969 + 3 ^ 40 * 2399678 * 2
def baseEnd_2399678 : Nat := 273819606671103884997575

theorem tailTrace_2399678 : CollatzResearch.WordTrace tailWord_2399678 prefixEnd_2399678 273819606671103884997575 := by
  unfold tailWord_2399678
  simp only [CollatzResearch.WordTrace]
  refine ⟨10940430875047989152385961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 58348964666922608812725125 10940430875047989152385961)
  ·
    refine ⟨8205323156285991864289471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10940430875047989152385961 8205323156285991864289471)
    ·
      refine ⟨12307984734428987796434207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8205323156285991864289471 12307984734428987796434207)
      ·
        refine ⟨18461977101643481694651311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12307984734428987796434207 18461977101643481694651311)
        ·
          refine ⟨27692965652465222541976967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18461977101643481694651311 27692965652465222541976967)
          ·
            refine ⟨41539448478697833812965451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27692965652465222541976967 41539448478697833812965451)
            ·
              refine ⟨62309172718046750719448177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41539448478697833812965451 62309172718046750719448177)
              ·
                refine ⟨46731879538535063039586133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 62309172718046750719448177 46731879538535063039586133)
                ·
                  refine ⟨273819606671103884997575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 46731879538535063039586133 273819606671103884997575)
                  ·
                    rfl

theorem cell22_2399678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 2, 9].length) (baseStart_2399678 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2399678 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2399678 prefixEnd_2399678 := by exact prefixLift 2399678
  have htrace : WordTrace (prefixWord ++ tailWord_2399678) baseStart_2399678 baseEnd_2399678 := by
    simpa [prefixWord, tailWord_2399678, baseEnd_2399678] using wordTrace_append hprefix tailTrace_2399678
  have hstable : (prefixWord ++ tailWord_2399678).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2399678).length < 2 ^ (prefixWord ++ tailWord_2399678).sum := by decide
  have hdescent : baseEnd_2399678 < baseStart_2399678 := by decide
  rcases family_descends (prefixWord ++ tailWord_2399678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2399753 : List Nat := [1, 2, 1, 1, 3, 1, 3, 3, 1, 6]
def baseStart_2399753 : Nat := 118140960795 + 2399753 * 2 ^ 59
def prefixEnd_2399753 : Nat := 4983230072969 + 3 ^ 40 * 2399753 * 2
def baseEnd_2399753 : Nat := 821484494046036459367495

theorem tailTrace_2399753 : CollatzResearch.WordTrace tailWord_2399753 prefixEnd_2399753 821484494046036459367495 := by
  unfold tailWord_2399753
  simp only [CollatzResearch.WordTrace]
  refine ⟨87526182475112201028067913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58350788316741467352045275 87526182475112201028067913)
  ·
    refine ⟨65644636856334150771050935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87526182475112201028067913 65644636856334150771050935)
    ·
      refine ⟨98466955284501226156576403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65644636856334150771050935 98466955284501226156576403)
      ·
        refine ⟨147700432926751839234864605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98466955284501226156576403 147700432926751839234864605)
        ·
          refine ⟨55387662347531939713074227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 147700432926751839234864605 55387662347531939713074227)
          ·
            refine ⟨83081493521297909569611341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55387662347531939713074227 83081493521297909569611341)
            ·
              refine ⟨31155560070486716088604253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 83081493521297909569611341 31155560070486716088604253)
              ·
                refine ⟨11683335026432518533226595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31155560070486716088604253 11683335026432518533226595)
                ·
                  refine ⟨17525002539648777799839893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11683335026432518533226595 17525002539648777799839893)
                  ·
                    refine ⟨821484494046036459367495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17525002539648777799839893 821484494046036459367495)
                    ·
                      rfl

theorem cell22_2399753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 3, 1, 6].length) (baseStart_2399753 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2399753 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2399753 prefixEnd_2399753 := by exact prefixLift 2399753
  have htrace : WordTrace (prefixWord ++ tailWord_2399753) baseStart_2399753 baseEnd_2399753 := by
    simpa [prefixWord, tailWord_2399753, baseEnd_2399753] using wordTrace_append hprefix tailTrace_2399753
  have hstable : (prefixWord ++ tailWord_2399753).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2399753).length < 2 ^ (prefixWord ++ tailWord_2399753).sum := by decide
  have hdescent : baseEnd_2399753 < baseStart_2399753 := by decide
  rcases family_descends (prefixWord ++ tailWord_2399753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2399772 : List Nat := [2, 2, 3, 1, 2, 1, 2, 4, 2, 3]
def baseStart_2399772 : Nat := 118140960795 + 2399772 * 2 ^ 59
def prefixEnd_2399772 : Nat := 4983230072969 + 3 ^ 40 * 2399772 * 2
def baseEnd_2399772 : Nat := 821490998134326743142437

theorem tailTrace_2399772 : CollatzResearch.WordTrace tailWord_2399772 prefixEnd_2399772 821490998134326743142437 := by
  unfold tailWord_2399772
  simp only [CollatzResearch.WordTrace]
  refine ⟨43763437731021683636504785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58351250308028911515339713 43763437731021683636504785)
  ·
    refine ⟨32822578298266262727378589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43763437731021683636504785 32822578298266262727378589)
    ·
      refine ⟨12308466861849848522766971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32822578298266262727378589 12308466861849848522766971)
      ·
        refine ⟨18462700292774772784150457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12308466861849848522766971 18462700292774772784150457)
        ·
          refine ⟨13847025219581079588112843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18462700292774772784150457 13847025219581079588112843)
          ·
            refine ⟨20770537829371619382169265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13847025219581079588112843 20770537829371619382169265)
            ·
              refine ⟨15577903372028714536626949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20770537829371619382169265 15577903372028714536626949)
              ·
                refine ⟨2920856882255383975617553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15577903372028714536626949 2920856882255383975617553)
                ·
                  refine ⟨2190642661691537981713165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2920856882255383975617553 2190642661691537981713165)
                  ·
                    refine ⟨821490998134326743142437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2190642661691537981713165 821490998134326743142437)
                    ·
                      rfl

theorem cell22_2399772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 2, 4, 2, 3].length) (baseStart_2399772 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2399772 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2399772 prefixEnd_2399772 := by exact prefixLift 2399772
  have htrace : WordTrace (prefixWord ++ tailWord_2399772) baseStart_2399772 baseEnd_2399772 := by
    simpa [prefixWord, tailWord_2399772, baseEnd_2399772] using wordTrace_append hprefix tailTrace_2399772
  have hstable : (prefixWord ++ tailWord_2399772).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2399772).length < 2 ^ (prefixWord ++ tailWord_2399772).sum := by decide
  have hdescent : baseEnd_2399772 < baseStart_2399772 := by decide
  rcases family_descends (prefixWord ++ tailWord_2399772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2399845 : List Nat := [1, 3, 1, 3, 3, 1, 1, 1, 1, 7]
def baseStart_2399845 : Nat := 118140960795 + 2399845 * 2 ^ 59
def prefixEnd_2399845 : Nat := 4983230072969 + 3 ^ 40 * 2399845 * 2
def baseEnd_2399845 : Nat := 821515987526178886067213

theorem tailTrace_2399845 : CollatzResearch.WordTrace tailWord_2399845 prefixEnd_2399845 821515987526178886067213 := by
  unfold tailWord_2399845
  simp only [CollatzResearch.WordTrace]
  refine ⟨87529537990778900740416989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58353025327185933826944659 87529537990778900740416989)
  ·
    refine ⟨32823576746542087777656371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 87529537990778900740416989 32823576746542087777656371)
    ·
      refine ⟨49235365119813131666484557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32823576746542087777656371 49235365119813131666484557)
      ·
        refine ⟨18463261919929924374931709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49235365119813131666484557 18463261919929924374931709)
        ·
          refine ⟨6923723219973721640599391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18463261919929924374931709 6923723219973721640599391)
          ·
            refine ⟨10385584829960582460899087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6923723219973721640599391 10385584829960582460899087)
            ·
              refine ⟨15578377244940873691348631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10385584829960582460899087 15578377244940873691348631)
              ·
                refine ⟨23367565867411310537022947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15578377244940873691348631 23367565867411310537022947)
                ·
                  refine ⟨35051348801116965805534421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23367565867411310537022947 35051348801116965805534421)
                  ·
                    refine ⟨821515987526178886067213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 35051348801116965805534421 821515987526178886067213)
                    ·
                      rfl

theorem cell22_2399845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 1, 1, 1, 7].length) (baseStart_2399845 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2399845 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2399845 prefixEnd_2399845 := by exact prefixLift 2399845
  have htrace : WordTrace (prefixWord ++ tailWord_2399845) baseStart_2399845 baseEnd_2399845 := by
    simpa [prefixWord, tailWord_2399845, baseEnd_2399845] using wordTrace_append hprefix tailTrace_2399845
  have hstable : (prefixWord ++ tailWord_2399845).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2399845).length < 2 ^ (prefixWord ++ tailWord_2399845).sum := by decide
  have hdescent : baseEnd_2399845 < baseStart_2399845 := by decide
  rcases family_descends (prefixWord ++ tailWord_2399845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2399877 : List Nat := [1, 3, 1, 1, 4, 1, 3, 3, 1, 4]
def baseStart_2399877 : Nat := 118140960795 + 2399877 * 2 ^ 59
def prefixEnd_2399877 : Nat := 4983230072969 + 3 ^ 40 * 2399877 * 2
def baseEnd_2399877 : Nat := 821526941780141469267115

theorem tailTrace_2399877 : CollatzResearch.WordTrace tailWord_2399877 prefixEnd_2399877 821526941780141469267115 := by
  unfold tailWord_2399877
  simp only [CollatzResearch.WordTrace]
  refine ⟨87530705126662970205581885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58353803417775313470387923 87530705126662970205581885)
  ·
    refine ⟨32824014422498613827093207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 87530705126662970205581885 32824014422498613827093207)
    ·
      refine ⟨49236021633747920740639811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32824014422498613827093207 49236021633747920740639811)
      ·
        refine ⟨73854032450621881110959717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49236021633747920740639811 73854032450621881110959717)
        ·
          refine ⟨13847631084491602708304947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 73854032450621881110959717 13847631084491602708304947)
          ·
            refine ⟨20771446626737404062457421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13847631084491602708304947 20771446626737404062457421)
            ·
              refine ⟨7789292485026526523421533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20771446626737404062457421 7789292485026526523421533)
              ·
                refine ⟨2920984681884947446283075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7789292485026526523421533 2920984681884947446283075)
                ·
                  refine ⟨4381477022827421169424613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2920984681884947446283075 4381477022827421169424613)
                  ·
                    refine ⟨821526941780141469267115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4381477022827421169424613 821526941780141469267115)
                    ·
                      rfl

theorem cell22_2399877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 3, 3, 1, 4].length) (baseStart_2399877 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2399877 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2399877 prefixEnd_2399877 := by exact prefixLift 2399877
  have htrace : WordTrace (prefixWord ++ tailWord_2399877) baseStart_2399877 baseEnd_2399877 := by
    simpa [prefixWord, tailWord_2399877, baseEnd_2399877] using wordTrace_append hprefix tailTrace_2399877
  have hstable : (prefixWord ++ tailWord_2399877).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2399877).length < 2 ^ (prefixWord ++ tailWord_2399877).sum := by decide
  have hdescent : baseEnd_2399877 < baseStart_2399877 := by decide
  rcases family_descends (prefixWord ++ tailWord_2399877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2399952 : List Nat := [2, 1, 1, 1, 1, 2, 1, 7, 3, 3]
def baseStart_2399952 : Nat := 118140960795 + 2399952 * 2 ^ 59
def prefixEnd_2399952 : Nat := 4983230072969 + 3 ^ 40 * 2399952 * 2
def baseEnd_2399952 : Nat := 821552615812866273641885

theorem tailTrace_2399952 : CollatzResearch.WordTrace tailWord_2399952 prefixEnd_2399952 821552615812866273641885 := by
  unfold tailWord_2399952
  simp only [CollatzResearch.WordTrace]
  refine ⟨43766720300695629007281055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58355627067594172009708073 43766720300695629007281055)
  ·
    refine ⟨65650080451043443510921583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43766720300695629007281055 65650080451043443510921583)
    ·
      refine ⟨98475120676565165266382375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65650080451043443510921583 98475120676565165266382375)
      ·
        refine ⟨147712681014847747899573563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98475120676565165266382375 147712681014847747899573563)
        ·
          refine ⟨221569021522271621849360345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 147712681014847747899573563 221569021522271621849360345)
          ·
            refine ⟨166176766141703716387020259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 221569021522271621849360345 166176766141703716387020259)
            ·
              refine ⟨249265149212555574580530389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 166176766141703716387020259 249265149212555574580530389)
              ·
                refine ⟨5842151934669271279231181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 249265149212555574580530389 5842151934669271279231181)
                ·
                  refine ⟨2190806975500976729711693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5842151934669271279231181 2190806975500976729711693)
                  ·
                    refine ⟨821552615812866273641885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2190806975500976729711693 821552615812866273641885)
                    ·
                      rfl

theorem cell22_2399952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 7, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 7, 3, 3].length) (baseStart_2399952 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2399952 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2399952 prefixEnd_2399952 := by exact prefixLift 2399952
  have htrace : WordTrace (prefixWord ++ tailWord_2399952) baseStart_2399952 baseEnd_2399952 := by
    simpa [prefixWord, tailWord_2399952, baseEnd_2399952] using wordTrace_append hprefix tailTrace_2399952
  have hstable : (prefixWord ++ tailWord_2399952).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2399952).length < 2 ^ (prefixWord ++ tailWord_2399952).sum := by decide
  have hdescent : baseEnd_2399952 < baseStart_2399952 := by decide
  rcases family_descends (prefixWord ++ tailWord_2399952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2399986 : List Nat := [3, 2, 1, 3, 1, 1, 2, 5, 1, 3]
def baseStart_2399986 : Nat := 118140960795 + 2399986 * 2 ^ 59
def prefixEnd_2399986 : Nat := 4983230072969 + 3 ^ 40 * 2399986 * 2
def baseEnd_2399986 : Nat := 821564254707701518291781

theorem tailTrace_2399986 : CollatzResearch.WordTrace tailWord_2399986 prefixEnd_2399986 821564254707701518291781 := by
  unfold tailWord_2399986
  simp only [CollatzResearch.WordTrace]
  refine ⟨21883670170817020455324953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58356453788845387880866541 21883670170817020455324953)
  ·
    refine ⟨16412752628112765341493715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21883670170817020455324953 16412752628112765341493715)
    ·
      refine ⟨24619128942169148012240573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16412752628112765341493715 24619128942169148012240573)
      ·
        refine ⟨9232173353313430504590215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24619128942169148012240573 9232173353313430504590215)
        ·
          refine ⟨13848260029970145756885323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9232173353313430504590215 13848260029970145756885323)
          ·
            refine ⟨20772390044955218635327985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13848260029970145756885323 20772390044955218635327985)
            ·
              refine ⟨15579292533716413976495989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20772390044955218635327985 15579292533716413976495989)
              ·
                refine ⟨1460558675035913810296499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15579292533716413976495989 1460558675035913810296499)
                ·
                  refine ⟨2190838012553870715444749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1460558675035913810296499 2190838012553870715444749)
                  ·
                    refine ⟨821564254707701518291781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2190838012553870715444749 821564254707701518291781)
                    ·
                      rfl

theorem cell22_2399986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 2, 5, 1, 3].length) (baseStart_2399986 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2399986 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2399986 prefixEnd_2399986 := by exact prefixLift 2399986
  have htrace : WordTrace (prefixWord ++ tailWord_2399986) baseStart_2399986 baseEnd_2399986 := by
    simpa [prefixWord, tailWord_2399986, baseEnd_2399986] using wordTrace_append hprefix tailTrace_2399986
  have hstable : (prefixWord ++ tailWord_2399986).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2399986).length < 2 ^ (prefixWord ++ tailWord_2399986).sum := by decide
  have hdescent : baseEnd_2399986 < baseStart_2399986 := by decide
  rcases family_descends (prefixWord ++ tailWord_2399986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2400012 : List Nat := [2, 2, 1, 2, 2, 1, 3, 2, 3, 4]
def baseStart_2400012 : Nat := 118140960795 + 2400012 * 2 ^ 59
def prefixEnd_2400012 : Nat := 4983230072969 + 3 ^ 40 * 2400012 * 2
def baseEnd_2400012 : Nat := 821573155039046117141701

theorem tailTrace_2400012 : CollatzResearch.WordTrace tailWord_2400012 prefixEnd_2400012 821573155039046117141701 := by
  unfold tailWord_2400012
  simp only [CollatzResearch.WordTrace]
  refine ⟨43767814490586944130873145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58357085987449258841164193 43767814490586944130873145)
  ·
    refine ⟨32825860867940208098154859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43767814490586944130873145 32825860867940208098154859)
    ·
      refine ⟨49238791301910312147232289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32825860867940208098154859 49238791301910312147232289)
      ·
        refine ⟨36929093476432734110424217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49238791301910312147232289 36929093476432734110424217)
        ·
          refine ⟨27696820107324550582818163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36929093476432734110424217 27696820107324550582818163)
          ·
            refine ⟨41545230160986825874227245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27696820107324550582818163 41545230160986825874227245)
            ·
              refine ⟨15579461310370059702835217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41545230160986825874227245 15579461310370059702835217)
              ·
                refine ⟨11684595982777544777126413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15579461310370059702835217 11684595982777544777126413)
                ·
                  refine ⟨4381723493541579291422405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11684595982777544777126413 4381723493541579291422405)
                  ·
                    refine ⟨821573155039046117141701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4381723493541579291422405 821573155039046117141701)
                    ·
                      rfl

theorem cell22_2400012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 3, 2, 3, 4].length) (baseStart_2400012 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2400012 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2400012 prefixEnd_2400012 := by exact prefixLift 2400012
  have htrace : WordTrace (prefixWord ++ tailWord_2400012) baseStart_2400012 baseEnd_2400012 := by
    simpa [prefixWord, tailWord_2400012, baseEnd_2400012] using wordTrace_append hprefix tailTrace_2400012
  have hstable : (prefixWord ++ tailWord_2400012).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2400012).length < 2 ^ (prefixWord ++ tailWord_2400012).sum := by decide
  have hdescent : baseEnd_2400012 < baseStart_2400012 := by decide
  rcases family_descends (prefixWord ++ tailWord_2400012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2400020 : List Nat := [2, 4, 4, 1, 1, 1, 1, 2, 3, 3]
def baseStart_2400020 : Nat := 118140960795 + 2400020 * 2 ^ 59
def prefixEnd_2400020 : Nat := 4983230072969 + 3 ^ 40 * 2400020 * 2
def baseEnd_2400020 : Nat := 821575893602536762941677

theorem tailTrace_2400020 : CollatzResearch.WordTrace tailWord_2400020 prefixEnd_2400020 821575893602536762941677 := by
  unfold tailWord_2400020
  simp only [CollatzResearch.WordTrace]
  refine ⟨43767960382572452814018757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58357280510096603752025009 43767960382572452814018757)
  ·
    refine ⟨8206492571732334902628517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 43767960382572452814018757 8206492571732334902628517)
    ·
      refine ⟨1538717357199812794242847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8206492571732334902628517 1538717357199812794242847)
      ·
        refine ⟨2308076035799719191364271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1538717357199812794242847 2308076035799719191364271)
        ·
          refine ⟨3462114053699578787046407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2308076035799719191364271 3462114053699578787046407)
          ·
            refine ⟨5193171080549368180569611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3462114053699578787046407 5193171080549368180569611)
            ·
              refine ⟨7789756620824052270854417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5193171080549368180569611 7789756620824052270854417)
              ·
                refine ⟨5842317465618039203140813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7789756620824052270854417 5842317465618039203140813)
                ·
                  refine ⟨2190869049606764701177805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5842317465618039203140813 2190869049606764701177805)
                  ·
                    refine ⟨821575893602536762941677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2190869049606764701177805 821575893602536762941677)
                    ·
                      rfl

theorem cell22_2400020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 1, 2, 3, 3].length) (baseStart_2400020 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2400020 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2400020 prefixEnd_2400020 := by exact prefixLift 2400020
  have htrace : WordTrace (prefixWord ++ tailWord_2400020) baseStart_2400020 baseEnd_2400020 := by
    simpa [prefixWord, tailWord_2400020, baseEnd_2400020] using wordTrace_append hprefix tailTrace_2400020
  have hstable : (prefixWord ++ tailWord_2400020).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2400020).length < 2 ^ (prefixWord ++ tailWord_2400020).sum := by decide
  have hdescent : baseEnd_2400020 < baseStart_2400020 := by decide
  rcases family_descends (prefixWord ++ tailWord_2400020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2400044 : List Nat := [2, 2, 1, 1, 1, 5, 1, 5, 4]
def baseStart_2400044 : Nat := 118140960795 + 2400044 * 2 ^ 59
def prefixEnd_2400044 : Nat := 4983230072969 + 3 ^ 40 * 2400044 * 2
def baseEnd_2400044 : Nat := 273861369764336233447201

theorem tailTrace_2400044 : CollatzResearch.WordTrace tailWord_2400044 prefixEnd_2400044 273861369764336233447201 := by
  unfold tailWord_2400044
  simp only [CollatzResearch.WordTrace]
  refine ⟨43768398058528978863455593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58357864078038638484607457 43768398058528978863455593)
  ·
    refine ⟨32826298543896734147591695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43768398058528978863455593 32826298543896734147591695)
    ·
      refine ⟨49239447815845101221387543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32826298543896734147591695 49239447815845101221387543)
      ·
        refine ⟨73859171723767651832081315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49239447815845101221387543 73859171723767651832081315)
        ·
          refine ⟨110788757585651477748121973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73859171723767651832081315 110788757585651477748121973)
          ·
            refine ⟨10386446023654826038886435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 110788757585651477748121973 10386446023654826038886435)
            ·
              refine ⟨15579669035482239058329653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10386446023654826038886435 15579669035482239058329653)
              ·
                refine ⟨1460593972076459911718405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15579669035482239058329653 1460593972076459911718405)
                ·
                  refine ⟨273861369764336233447201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1460593972076459911718405 273861369764336233447201)
                  ·
                    rfl

theorem cell22_2400044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 1, 5, 4].length) (baseStart_2400044 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2400044 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2400044 prefixEnd_2400044 := by exact prefixLift 2400044
  have htrace : WordTrace (prefixWord ++ tailWord_2400044) baseStart_2400044 baseEnd_2400044 := by
    simpa [prefixWord, tailWord_2400044, baseEnd_2400044] using wordTrace_append hprefix tailTrace_2400044
  have hstable : (prefixWord ++ tailWord_2400044).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2400044).length < 2 ^ (prefixWord ++ tailWord_2400044).sum := by decide
  have hdescent : baseEnd_2400044 < baseStart_2400044 := by decide
  rcases family_descends (prefixWord ++ tailWord_2400044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2400061 : List Nat := [1, 4, 1, 4, 1, 1, 2, 4, 4]
def baseStart_2400061 : Nat := 118140960795 + 2400061 * 2 ^ 59
def prefixEnd_2400061 : Nat := 4983230072969 + 3 ^ 40 * 2400061 * 2
def baseEnd_2400061 : Nat := 273863309580142107555517

theorem tailTrace_2400061 : CollatzResearch.WordTrace tailWord_2400061 prefixEnd_2400061 273863309580142107555517 := by
  unfold tailWord_2400061
  simp only [CollatzResearch.WordTrace]
  refine ⟨87537416157996369630280037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58358277438664246420186691 87537416157996369630280037)
  ·
    refine ⟨16413265529624319305677507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 87537416157996369630280037 16413265529624319305677507)
    ·
      refine ⟨24619898294436478958516261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16413265529624319305677507 24619898294436478958516261)
      ·
        refine ⟨4616230930206839804721799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24619898294436478958516261 4616230930206839804721799)
        ·
          refine ⟨6924346395310259707082699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4616230930206839804721799 6924346395310259707082699)
          ·
            refine ⟨10386519592965389560624049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6924346395310259707082699 10386519592965389560624049)
            ·
              refine ⟨7789889694724042170468037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10386519592965389560624049 7789889694724042170468037)
              ·
                refine ⟨1460604317760757906962757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7789889694724042170468037 1460604317760757906962757)
                ·
                  refine ⟨273863309580142107555517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1460604317760757906962757 273863309580142107555517)
                  ·
                    rfl

theorem cell22_2400061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 2, 4, 4].length) (baseStart_2400061 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2400061 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2400061 prefixEnd_2400061 := by exact prefixLift 2400061
  have htrace : WordTrace (prefixWord ++ tailWord_2400061) baseStart_2400061 baseEnd_2400061 := by
    simpa [prefixWord, tailWord_2400061, baseEnd_2400061] using wordTrace_append hprefix tailTrace_2400061
  have hstable : (prefixWord ++ tailWord_2400061).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2400061).length < 2 ^ (prefixWord ++ tailWord_2400061).sum := by decide
  have hdescent : baseEnd_2400061 < baseStart_2400061 := by decide
  rcases family_descends (prefixWord ++ tailWord_2400061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2400076 : List Nat := [2, 2, 1, 3, 4, 2, 1, 1, 1, 5]
def baseStart_2400076 : Nat := 118140960795 + 2400076 * 2 ^ 59
def prefixEnd_2400076 : Nat := 4983230072969 + 3 ^ 40 * 2400076 * 2
def baseEnd_2400076 : Nat := 821595063546971283541505

theorem tailTrace_2400076 : CollatzResearch.WordTrace tailWord_2400076 prefixEnd_2400076 821595063546971283541505 := by
  unfold tailWord_2400076
  simp only [CollatzResearch.WordTrace]
  refine ⟨43768981626471013596038041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58358642168628018128050721 43768981626471013596038041)
  ·
    refine ⟨32826736219853260197028531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43768981626471013596038041 32826736219853260197028531)
    ·
      refine ⟨49240104329779890295542797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32826736219853260197028531 49240104329779890295542797)
      ·
        refine ⟨18465039123667458860828549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49240104329779890295542797 18465039123667458860828549)
        ·
          refine ⟨3462194835687648536405353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18465039123667458860828549 3462194835687648536405353)
          ·
            refine ⟨2596646126765736402304015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3462194835687648536405353 2596646126765736402304015)
            ·
              refine ⟨3894969190148604603456023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2596646126765736402304015 3894969190148604603456023)
              ·
                refine ⟨5842453785222906905184035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3894969190148604603456023 5842453785222906905184035)
                ·
                  refine ⟨8763680677834360357776053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5842453785222906905184035 8763680677834360357776053)
                  ·
                    refine ⟨821595063546971283541505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8763680677834360357776053 821595063546971283541505)
                    ·
                      rfl

theorem cell22_2400076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 2, 1, 1, 1, 5].length) (baseStart_2400076 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2400076 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2400076 prefixEnd_2400076 := by exact prefixLift 2400076
  have htrace : WordTrace (prefixWord ++ tailWord_2400076) baseStart_2400076 baseEnd_2400076 := by
    simpa [prefixWord, tailWord_2400076, baseEnd_2400076] using wordTrace_append hprefix tailTrace_2400076
  have hstable : (prefixWord ++ tailWord_2400076).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2400076).length < 2 ^ (prefixWord ++ tailWord_2400076).sum := by decide
  have hdescent : baseEnd_2400076 < baseStart_2400076 := by decide
  rcases family_descends (prefixWord ++ tailWord_2400076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2400106 : List Nat := [3, 1, 3, 4, 1, 2, 8]
def baseStart_2400106 : Nat := 118140960795 + 2400106 * 2 ^ 59
def prefixEnd_2400106 : Nat := 4983230072969 + 3 ^ 40 * 2400106 * 2
def baseEnd_2400106 : Nat := 30429827154076340936719

theorem tailTrace_2400106 : CollatzResearch.WordTrace tailWord_2400106 prefixEnd_2400106 30429827154076340936719 := by
  unfold tailWord_2400106
  simp only [CollatzResearch.WordTrace]
  refine ⟨21884764360708335578917043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58359371628555561543778781 21884764360708335578917043)
  ·
    refine ⟨32827146541062503368375565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21884764360708335578917043 32827146541062503368375565)
    ·
      refine ⟨12310179952898438763140837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32827146541062503368375565 12310179952898438763140837)
      ·
        refine ⟨2308158741168457268088907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12310179952898438763140837 2308158741168457268088907)
        ·
          refine ⟨3462238111752685902133361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2308158741168457268088907 3462238111752685902133361)
          ·
            refine ⟨2596678583814514426600021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3462238111752685902133361 2596678583814514426600021)
            ·
              refine ⟨30429827154076340936719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2596678583814514426600021 30429827154076340936719)
              ·
                rfl

theorem cell22_2400106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 2, 8].length) (baseStart_2400106 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2400106 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2400106 prefixEnd_2400106 := by exact prefixLift 2400106
  have htrace : WordTrace (prefixWord ++ tailWord_2400106) baseStart_2400106 baseEnd_2400106 := by
    simpa [prefixWord, tailWord_2400106, baseEnd_2400106] using wordTrace_append hprefix tailTrace_2400106
  have hstable : (prefixWord ++ tailWord_2400106).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2400106).length < 2 ^ (prefixWord ++ tailWord_2400106).sum := by decide
  have hdescent : baseEnd_2400106 < baseStart_2400106 := by decide
  rcases family_descends (prefixWord ++ tailWord_2400106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2400209 : List Nat := [1, 2, 2, 1, 2, 1, 2, 5, 2, 4]
def baseStart_2400209 : Nat := 118140960795 + 2400209 * 2 ^ 59
def prefixEnd_2400209 : Nat := 4983230072969 + 3 ^ 40 * 2400209 * 2
def baseEnd_2400209 : Nat := 821640592165003269966097

theorem tailTrace_2400209 : CollatzResearch.WordTrace tailWord_2400209 prefixEnd_2400209 821640592165003269966097 := by
  unfold tailWord_2400209
  simp only [CollatzResearch.WordTrace]
  refine ⟨87542814161460190906667681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58361876107640127271111787 87542814161460190906667681)
  ·
    refine ⟨65657110621095143180000761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87542814161460190906667681 65657110621095143180000761)
    ·
      refine ⟨49242832965821357385000571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65657110621095143180000761 49242832965821357385000571)
      ·
        refine ⟨73864249448732036077500857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49242832965821357385000571 73864249448732036077500857)
        ·
          refine ⟨55398187086549027058125643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73864249448732036077500857 55398187086549027058125643)
          ·
            refine ⟨83097280629823540587188465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55398187086549027058125643 83097280629823540587188465)
            ·
              refine ⟨62322960472367655440391349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 83097280629823540587188465 62322960472367655440391349)
              ·
                refine ⟨5842777544284467697536689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 62322960472367655440391349 5842777544284467697536689)
                ·
                  refine ⟨4382083158213350773152517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5842777544284467697536689 4382083158213350773152517)
                  ·
                    refine ⟨821640592165003269966097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4382083158213350773152517 821640592165003269966097)
                    ·
                      rfl

theorem cell22_2400209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 5, 2, 4].length) (baseStart_2400209 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2400209 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2400209 prefixEnd_2400209 := by exact prefixLift 2400209
  have htrace : WordTrace (prefixWord ++ tailWord_2400209) baseStart_2400209 baseEnd_2400209 := by
    simpa [prefixWord, tailWord_2400209, baseEnd_2400209] using wordTrace_append hprefix tailTrace_2400209
  have hstable : (prefixWord ++ tailWord_2400209).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2400209).length < 2 ^ (prefixWord ++ tailWord_2400209).sum := by decide
  have hdescent : baseEnd_2400209 < baseStart_2400209 := by decide
  rcases family_descends (prefixWord ++ tailWord_2400209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2400213 : List Nat := [1, 3, 2, 3, 2, 2, 2, 3, 4]
def baseStart_2400213 : Nat := 118140960795 + 2400213 * 2 ^ 59
def prefixEnd_2400213 : Nat := 4983230072969 + 3 ^ 40 * 2400213 * 2
def baseEnd_2400213 : Nat := 273880653815582864288695

theorem tailTrace_2400213 : CollatzResearch.WordTrace tailWord_2400213 prefixEnd_2400213 273880653815582864288695 := by
  unfold tailWord_2400213
  simp only [CollatzResearch.WordTrace]
  refine ⟨87542960053445699589813293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58361973368963799726542195 87542960053445699589813293)
  ·
    refine ⟨32828610020042137346179985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 87542960053445699589813293 32828610020042137346179985)
    ·
      refine ⟨24621457515031603009634989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32828610020042137346179985 24621457515031603009634989)
      ·
        refine ⟨9233046568136851128613121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24621457515031603009634989 9233046568136851128613121)
        ·
          refine ⟨6924784926102638346459841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9233046568136851128613121 6924784926102638346459841)
          ·
            refine ⟨5193588694576978759844881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6924784926102638346459841 5193588694576978759844881)
            ·
              refine ⟨3895191520932734069883661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5193588694576978759844881 3895191520932734069883661)
              ·
                refine ⟨1460696820349775276206373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3895191520932734069883661 1460696820349775276206373)
                ·
                  refine ⟨273880653815582864288695, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1460696820349775276206373 273880653815582864288695)
                  ·
                    rfl

theorem cell22_2400213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 2, 3, 4].length) (baseStart_2400213 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2400213 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2400213 prefixEnd_2400213 := by exact prefixLift 2400213
  have htrace : WordTrace (prefixWord ++ tailWord_2400213) baseStart_2400213 baseEnd_2400213 := by
    simpa [prefixWord, tailWord_2400213, baseEnd_2400213] using wordTrace_append hprefix tailTrace_2400213
  have hstable : (prefixWord ++ tailWord_2400213).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2400213).length < 2 ^ (prefixWord ++ tailWord_2400213).sum := by decide
  have hdescent : baseEnd_2400213 < baseStart_2400213 := by decide
  rcases family_descends (prefixWord ++ tailWord_2400213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2400314 : List Nat := [3, 1, 1, 1, 3, 1, 1, 3, 8]
def baseStart_2400314 : Nat := 118140960795 + 2400314 * 2 ^ 59
def prefixEnd_2400314 : Nat := 4983230072969 + 3 ^ 40 * 2400314 * 2
def baseEnd_2400314 : Nat := 273892178603605998696925

theorem tailTrace_2400314 : CollatzResearch.WordTrace tailWord_2400314 prefixEnd_2400314 273892178603605998696925 := by
  unfold tailWord_2400314
  simp only [CollatzResearch.WordTrace]
  refine ⟨21886660956519948459809999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58364429217386529226159997 21886660956519948459809999)
  ·
    refine ⟨32829991434779922689714999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21886660956519948459809999 32829991434779922689714999)
    ·
      refine ⟨49244987152169884034572499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32829991434779922689714999 49244987152169884034572499)
      ·
        refine ⟨73867480728254826051858749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49244987152169884034572499 73867480728254826051858749)
        ·
          refine ⟨27700305273095559769447031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 73867480728254826051858749 27700305273095559769447031)
          ·
            refine ⟨41550457909643339654170547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27700305273095559769447031 41550457909643339654170547)
            ·
              refine ⟨62325686864465009481255821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41550457909643339654170547 62325686864465009481255821)
              ·
                refine ⟨23372132574174378555470933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 62325686864465009481255821 23372132574174378555470933)
                ·
                  refine ⟨273892178603605998696925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 23372132574174378555470933 273892178603605998696925)
                  ·
                    rfl

theorem cell22_2400314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 3, 8].length) (baseStart_2400314 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2400314 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2400314 prefixEnd_2400314 := by exact prefixLift 2400314
  have htrace : WordTrace (prefixWord ++ tailWord_2400314) baseStart_2400314 baseEnd_2400314 := by
    simpa [prefixWord, tailWord_2400314, baseEnd_2400314] using wordTrace_append hprefix tailTrace_2400314
  have hstable : (prefixWord ++ tailWord_2400314).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2400314).length < 2 ^ (prefixWord ++ tailWord_2400314).sum := by decide
  have hdescent : baseEnd_2400314 < baseStart_2400314 := by decide
  rcases family_descends (prefixWord ++ tailWord_2400314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2400316 : List Nat := [2, 2, 2, 2, 2, 1, 3, 1, 3, 4]
def baseStart_2400316 : Nat := 118140960795 + 2400316 * 2 ^ 59
def prefixEnd_2400316 : Nat := 4983230072969 + 3 ^ 40 * 2400316 * 2
def baseEnd_2400316 : Nat := 821677220451690657540769

theorem tailTrace_2400316 : CollatzResearch.WordTrace tailWord_2400316 prefixEnd_2400316 821677220451690657540769 := by
  unfold tailWord_2400316
  simp only [CollatzResearch.WordTrace]
  refine ⟨43773358386036274090406401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58364477848048365453875201 43773358386036274090406401)
  ·
    refine ⟨32830018789527205567804801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43773358386036274090406401 32830018789527205567804801)
    ·
      refine ⟨24622514092145404175853601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32830018789527205567804801 24622514092145404175853601)
      ·
        refine ⟨18466885569109053131890201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24622514092145404175853601 18466885569109053131890201)
        ·
          refine ⟨13850164176831789848917651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18466885569109053131890201 13850164176831789848917651)
          ·
            refine ⟨20775246265247684773376477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13850164176831789848917651 20775246265247684773376477)
            ·
              refine ⟨7790717349467881790016179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20775246265247684773376477 7790717349467881790016179)
              ·
                refine ⟨11686076024201822685024269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7790717349467881790016179 11686076024201822685024269)
                ·
                  refine ⟨4382278509075683506884101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11686076024201822685024269 4382278509075683506884101)
                  ·
                    refine ⟨821677220451690657540769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4382278509075683506884101 821677220451690657540769)
                    ·
                      rfl

theorem cell22_2400316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 3, 1, 3, 4].length) (baseStart_2400316 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2400316 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2400316 prefixEnd_2400316 := by exact prefixLift 2400316
  have htrace : WordTrace (prefixWord ++ tailWord_2400316) baseStart_2400316 baseEnd_2400316 := by
    simpa [prefixWord, tailWord_2400316, baseEnd_2400316] using wordTrace_append hprefix tailTrace_2400316
  have hstable : (prefixWord ++ tailWord_2400316).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2400316).length < 2 ^ (prefixWord ++ tailWord_2400316).sum := by decide
  have hdescent : baseEnd_2400316 < baseStart_2400316 := by decide
  rcases family_descends (prefixWord ++ tailWord_2400316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2400414 : List Nat := [4, 3, 1, 1, 3, 1, 3, 1, 2, 3]
def baseStart_2400414 : Nat := 118140960795 + 2400414 * 2 ^ 59
def prefixEnd_2400414 : Nat := 4983230072969 + 3 ^ 40 * 2400414 * 2
def baseEnd_2400414 : Nat := 821710767854451068590469

theorem tailTrace_2400414 : CollatzResearch.WordTrace tailWord_2400414 prefixEnd_2400414 821710767854451068590469 := by
  unfold tailWord_2400414
  simp only [CollatzResearch.WordTrace]
  refine ⟨10943786390714688864735037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 58366860750478340611920197 10943786390714688864735037)
  ·
    refine ⟨4103919896518008324275639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10943786390714688864735037 4103919896518008324275639)
    ·
      refine ⟨6155879844777012486413459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4103919896518008324275639 6155879844777012486413459)
      ·
        refine ⟨9233819767165518729620189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6155879844777012486413459 9233819767165518729620189)
        ·
          refine ⟨3462682412687069523607571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9233819767165518729620189 3462682412687069523607571)
          ·
            refine ⟨5194023619030604285411357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3462682412687069523607571 5194023619030604285411357)
            ·
              refine ⟨1947758857136476607029259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5194023619030604285411357 1947758857136476607029259)
              ·
                refine ⟨2921638285704714910543889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1947758857136476607029259 2921638285704714910543889)
                ·
                  refine ⟨2191228714278536182907917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2921638285704714910543889 2191228714278536182907917)
                  ·
                    refine ⟨821710767854451068590469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2191228714278536182907917 821710767854451068590469)
                    ·
                      rfl

theorem cell22_2400414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 3, 1, 2, 3].length) (baseStart_2400414 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2400414 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2400414 prefixEnd_2400414 := by exact prefixLift 2400414
  have htrace : WordTrace (prefixWord ++ tailWord_2400414) baseStart_2400414 baseEnd_2400414 := by
    simpa [prefixWord, tailWord_2400414, baseEnd_2400414] using wordTrace_append hprefix tailTrace_2400414
  have hstable : (prefixWord ++ tailWord_2400414).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2400414).length < 2 ^ (prefixWord ++ tailWord_2400414).sum := by decide
  have hdescent : baseEnd_2400414 < baseStart_2400414 := by decide
  rcases family_descends (prefixWord ++ tailWord_2400414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2400485 : List Nat := [1, 3, 1, 4, 2, 1, 3, 2, 1, 4]
def baseStart_2400485 : Nat := 118140960795 + 2400485 * 2 ^ 59
def prefixEnd_2400485 : Nat := 4983230072969 + 3 ^ 40 * 2400485 * 2
def baseEnd_2400485 : Nat := 821735072605430550065251

theorem tailTrace_2400485 : CollatzResearch.WordTrace tailWord_2400485 prefixEnd_2400485 821735072605430550065251 := by
  unfold tailWord_2400485
  simp only [CollatzResearch.WordTrace]
  refine ⟨87552880708460290043714909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58368587138973526695809939 87552880708460290043714909)
  ·
    refine ⟨32832330265672608766393091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 87552880708460290043714909 32832330265672608766393091)
    ·
      refine ⟨49248495398508913149589637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32832330265672608766393091 49248495398508913149589637)
      ·
        refine ⟨9234092887220421215548057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 49248495398508913149589637 9234092887220421215548057)
        ·
          refine ⟨6925569665415315911661043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9234092887220421215548057 6925569665415315911661043)
          ·
            refine ⟨10388354498122973867491565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6925569665415315911661043 10388354498122973867491565)
            ·
              refine ⟨3895632936796115200309337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10388354498122973867491565 3895632936796115200309337)
              ·
                refine ⟨2921724702597086400232003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3895632936796115200309337 2921724702597086400232003)
                ·
                  refine ⟨4382587053895629600348005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2921724702597086400232003 4382587053895629600348005)
                  ·
                    refine ⟨821735072605430550065251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4382587053895629600348005 821735072605430550065251)
                    ·
                      rfl

theorem cell22_2400485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 3, 2, 1, 4].length) (baseStart_2400485 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2400485 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2400485 prefixEnd_2400485 := by exact prefixLift 2400485
  have htrace : WordTrace (prefixWord ++ tailWord_2400485) baseStart_2400485 baseEnd_2400485 := by
    simpa [prefixWord, tailWord_2400485, baseEnd_2400485] using wordTrace_append hprefix tailTrace_2400485
  have hstable : (prefixWord ++ tailWord_2400485).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2400485).length < 2 ^ (prefixWord ++ tailWord_2400485).sum := by decide
  have hdescent : baseEnd_2400485 < baseStart_2400485 := by decide
  rcases family_descends (prefixWord ++ tailWord_2400485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2400496 : List Nat := [2, 1, 1, 1, 3, 1, 1, 5, 1, 6]
def baseStart_2400496 : Nat := 118140960795 + 2400496 * 2 ^ 59
def prefixEnd_2400496 : Nat := 4983230072969 + 3 ^ 40 * 2400496 * 2
def baseEnd_2400496 : Nat := 821738838130230188040217

theorem tailTrace_2400496 : CollatzResearch.WordTrace tailWord_2400496 prefixEnd_2400496 821738838130230188040217 := by
  unfold tailWord_2400496
  simp only [CollatzResearch.WordTrace]
  refine ⟨43776640955710219461182671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58368854607613625948243561 43776640955710219461182671)
  ·
    refine ⟨65664961433565329191774007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43776640955710219461182671 65664961433565329191774007)
    ·
      refine ⟨98497442150347993787661011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65664961433565329191774007 98497442150347993787661011)
      ·
        refine ⟨147746163225521990681491517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98497442150347993787661011 147746163225521990681491517)
        ·
          refine ⟨55404811209570746505559319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 147746163225521990681491517 55404811209570746505559319)
          ·
            refine ⟨83107216814356119758338979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55404811209570746505559319 83107216814356119758338979)
            ·
              refine ⟨124660825221534179637508469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83107216814356119758338979 124660825221534179637508469)
              ·
                refine ⟨11686952364518829341016419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 124660825221534179637508469 11686952364518829341016419)
                ·
                  refine ⟨17530428546778244011524629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11686952364518829341016419 17530428546778244011524629)
                  ·
                    refine ⟨821738838130230188040217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17530428546778244011524629 821738838130230188040217)
                    ·
                      rfl

theorem cell22_2400496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 5, 1, 6].length) (baseStart_2400496 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2400496 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2400496 prefixEnd_2400496 := by exact prefixLift 2400496
  have htrace : WordTrace (prefixWord ++ tailWord_2400496) baseStart_2400496 baseEnd_2400496 := by
    simpa [prefixWord, tailWord_2400496, baseEnd_2400496] using wordTrace_append hprefix tailTrace_2400496
  have hstable : (prefixWord ++ tailWord_2400496).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2400496).length < 2 ^ (prefixWord ++ tailWord_2400496).sum := by decide
  have hdescent : baseEnd_2400496 < baseStart_2400496 := by decide
  rcases family_descends (prefixWord ++ tailWord_2400496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2400498 : List Nat := [3, 2, 1, 3, 2, 1, 1, 1, 3, 5]
def baseStart_2400498 : Nat := 118140960795 + 2400498 * 2 ^ 59
def prefixEnd_2400498 : Nat := 4983230072969 + 3 ^ 40 * 2400498 * 2
def baseEnd_2400498 : Nat := 821739522771102849490211

theorem tailTrace_2400498 : CollatzResearch.WordTrace tailWord_2400498 prefixEnd_2400498 821739522771102849490211 := by
  unfold tailWord_2400498
  simp only [CollatzResearch.WordTrace]
  refine ⟨21888338714353298315984537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58368903238275462175958765 21888338714353298315984537)
  ·
    refine ⟨16416254035764973736988403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21888338714353298315984537 16416254035764973736988403)
    ·
      refine ⟨24624381053647460605482605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16416254035764973736988403 24624381053647460605482605)
      ·
        refine ⟨9234142895117797727055977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24624381053647460605482605 9234142895117797727055977)
        ·
          refine ⟨6925607171338348295291983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9234142895117797727055977 6925607171338348295291983)
          ·
            refine ⟨10388410757007522442937975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6925607171338348295291983 10388410757007522442937975)
            ·
              refine ⟨15582616135511283664406963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10388410757007522442937975 15582616135511283664406963)
              ·
                refine ⟨23373924203266925496610445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15582616135511283664406963 23373924203266925496610445)
                ·
                  refine ⟨8765221576225097061228917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23373924203266925496610445 8765221576225097061228917)
                  ·
                    refine ⟨821739522771102849490211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8765221576225097061228917 821739522771102849490211)
                    ·
                      rfl

theorem cell22_2400498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 1, 1, 3, 5].length) (baseStart_2400498 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2400498 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2400498 prefixEnd_2400498 := by exact prefixLift 2400498
  have htrace : WordTrace (prefixWord ++ tailWord_2400498) baseStart_2400498 baseEnd_2400498 := by
    simpa [prefixWord, tailWord_2400498, baseEnd_2400498] using wordTrace_append hprefix tailTrace_2400498
  have hstable : (prefixWord ++ tailWord_2400498).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2400498).length < 2 ^ (prefixWord ++ tailWord_2400498).sum := by decide
  have hdescent : baseEnd_2400498 < baseStart_2400498 := by decide
  rcases family_descends (prefixWord ++ tailWord_2400498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2400513 : List Nat := [1, 2, 4, 1, 1, 2, 1, 4, 2, 4]
def baseStart_2400513 : Nat := 118140960795 + 2400513 * 2 ^ 59
def prefixEnd_2400513 : Nat := 4983230072969 + 3 ^ 40 * 2400513 * 2
def baseEnd_2400513 : Nat := 821744657577647810365165

theorem tailTrace_2400513 : CollatzResearch.WordTrace tailWord_2400513 prefixEnd_2400513 821744657577647810365165 := by
  unfold tailWord_2400513
  simp only [CollatzResearch.WordTrace]
  refine ⟨87553901952358850825734193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58369267968239233883822795 87553901952358850825734193)
  ·
    refine ⟨65665426464269138119300645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87553901952358850825734193 65665426464269138119300645)
    ·
      refine ⟨12312267462050463397368871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 65665426464269138119300645 12312267462050463397368871)
      ·
        refine ⟨18468401193075695096053307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12312267462050463397368871 18468401193075695096053307)
        ·
          refine ⟨27702601789613542644079961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18468401193075695096053307 27702601789613542644079961)
          ·
            refine ⟨20776951342210156983059971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27702601789613542644079961 20776951342210156983059971)
            ·
              refine ⟨31165427013315235474589957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20776951342210156983059971 31165427013315235474589957)
              ·
                refine ⟨5843517564996606651485617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31165427013315235474589957 5843517564996606651485617)
                ·
                  refine ⟨4382638173747454988614213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5843517564996606651485617 4382638173747454988614213)
                  ·
                    refine ⟨821744657577647810365165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4382638173747454988614213 821744657577647810365165)
                    ·
                      rfl

theorem cell22_2400513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 4, 2, 4].length) (baseStart_2400513 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2400513 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2400513 prefixEnd_2400513 := by exact prefixLift 2400513
  have htrace : WordTrace (prefixWord ++ tailWord_2400513) baseStart_2400513 baseEnd_2400513 := by
    simpa [prefixWord, tailWord_2400513, baseEnd_2400513] using wordTrace_append hprefix tailTrace_2400513
  have hstable : (prefixWord ++ tailWord_2400513).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2400513).length < 2 ^ (prefixWord ++ tailWord_2400513).sum := by decide
  have hdescent : baseEnd_2400513 < baseStart_2400513 := by decide
  rcases family_descends (prefixWord ++ tailWord_2400513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2400515 : List Nat := [1, 1, 1, 3, 2, 3, 4, 2, 2, 3]
def baseStart_2400515 : Nat := 118140960795 + 2400515 * 2 ^ 59
def prefixEnd_2400515 : Nat := 4983230072969 + 3 ^ 40 * 2400515 * 2
def baseEnd_2400515 : Nat := 821745342218520471815159

theorem tailTrace_2400515 : CollatzResearch.WordTrace tailWord_2400515 prefixEnd_2400515 821745342218520471815159 := by
  unfold tailWord_2400515
  simp only [CollatzResearch.WordTrace]
  refine ⟨87553974898351605167306999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58369316598901070111537999 87553974898351605167306999)
  ·
    refine ⟨131330962347527407750960499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87553974898351605167306999 131330962347527407750960499)
    ·
      refine ⟨196996443521291111626440749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131330962347527407750960499 196996443521291111626440749)
      ·
        refine ⟨73873666320484166859915281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 196996443521291111626440749 73873666320484166859915281)
        ·
          refine ⟨55405249740363125144936461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73873666320484166859915281 55405249740363125144936461)
          ·
            refine ⟨20776968652636171929351173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55405249740363125144936461 20776968652636171929351173)
            ·
              refine ⟨3895681622369282236753345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20776968652636171929351173 3895681622369282236753345)
              ·
                refine ⟨2921761216776961677565009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3895681622369282236753345 2921761216776961677565009)
                ·
                  refine ⟨2191320912582721258173757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2921761216776961677565009 2191320912582721258173757)
                  ·
                    refine ⟨821745342218520471815159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2191320912582721258173757 821745342218520471815159)
                    ·
                      rfl

theorem cell22_2400515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 4, 2, 2, 3].length) (baseStart_2400515 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2400515 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2400515 prefixEnd_2400515 := by exact prefixLift 2400515
  have htrace : WordTrace (prefixWord ++ tailWord_2400515) baseStart_2400515 baseEnd_2400515 := by
    simpa [prefixWord, tailWord_2400515, baseEnd_2400515] using wordTrace_append hprefix tailTrace_2400515
  have hstable : (prefixWord ++ tailWord_2400515).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2400515).length < 2 ^ (prefixWord ++ tailWord_2400515).sum := by decide
  have hdescent : baseEnd_2400515 < baseStart_2400515 := by decide
  rcases family_descends (prefixWord ++ tailWord_2400515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2400551 : List Nat := [1, 1, 8, 1, 1, 1, 2, 3, 4]
def baseStart_2400551 : Nat := 118140960795 + 2400551 * 2 ^ 59
def prefixEnd_2400551 : Nat := 4983230072969 + 3 ^ 40 * 2400551 * 2
def baseEnd_2400551 : Nat := 273919221918076125971683

theorem tailTrace_2400551 : CollatzResearch.WordTrace tailWord_2400551 prefixEnd_2400551 273919221918076125971683 := by
  unfold tailWord_2400551
  simp only [CollatzResearch.WordTrace]
  refine ⟨87555287926221183315617507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58370191950814122210411671 87555287926221183315617507)
  ·
    refine ⟨131332931889331774973426261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87555287926221183315617507 131332931889331774973426261)
    ·
      refine ⟨1539057795578106737969839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 131332931889331774973426261 1539057795578106737969839)
      ·
        refine ⟨2308586693367160106954759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1539057795578106737969839 2308586693367160106954759)
        ·
          refine ⟨3462880040050740160432139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2308586693367160106954759 3462880040050740160432139)
          ·
            refine ⟨5194320060076110240648209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3462880040050740160432139 5194320060076110240648209)
            ·
              refine ⟨3895740045057082680486157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5194320060076110240648209 3895740045057082680486157)
              ·
                refine ⟨1460902516896406005182309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3895740045057082680486157 1460902516896406005182309)
                ·
                  refine ⟨273919221918076125971683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1460902516896406005182309 273919221918076125971683)
                  ·
                    rfl

theorem cell22_2400551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 2, 3, 4].length) (baseStart_2400551 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2400551 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2400551 prefixEnd_2400551 := by exact prefixLift 2400551
  have htrace : WordTrace (prefixWord ++ tailWord_2400551) baseStart_2400551 baseEnd_2400551 := by
    simpa [prefixWord, tailWord_2400551, baseEnd_2400551] using wordTrace_append hprefix tailTrace_2400551
  have hstable : (prefixWord ++ tailWord_2400551).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2400551).length < 2 ^ (prefixWord ++ tailWord_2400551).sum := by decide
  have hdescent : baseEnd_2400551 < baseStart_2400551 := by decide
  rcases family_descends (prefixWord ++ tailWord_2400551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2400571 : List Nat := [1, 1, 1, 1, 1, 2, 1, 1, 2, 11]
def baseStart_2400571 : Nat := 118140960795 + 2400571 * 2 ^ 59
def prefixEnd_2400571 : Nat := 4983230072969 + 3 ^ 40 * 2400571 * 2
def baseEnd_2400571 : Nat := 821764512162954992414987

theorem tailTrace_2400571 : CollatzResearch.WordTrace tailWord_2400571 prefixEnd_2400571 821764512162954992414987 := by
  unfold tailWord_2400571
  simp only [CollatzResearch.WordTrace]
  refine ⟨87556017386148726731345567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58370678257432484487563711 87556017386148726731345567)
  ·
    refine ⟨131334026079223090097018351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87556017386148726731345567 131334026079223090097018351)
    ·
      refine ⟨197001039118834635145527527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131334026079223090097018351 197001039118834635145527527)
      ·
        refine ⟨295501558678251952718291291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 197001039118834635145527527 295501558678251952718291291)
        ·
          refine ⟨443252338017377929077436937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 295501558678251952718291291 443252338017377929077436937)
          ·
            refine ⟨332439253513033446808077703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 443252338017377929077436937 332439253513033446808077703)
            ·
              refine ⟨498658880269550170212116555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 332439253513033446808077703 498658880269550170212116555)
              ·
                refine ⟨747988320404325255318174833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 498658880269550170212116555 747988320404325255318174833)
                ·
                  refine ⟨560991240303243941488631125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 747988320404325255318174833 560991240303243941488631125)
                  ·
                    refine ⟨821764512162954992414987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 11 560991240303243941488631125 821764512162954992414987)
                    ·
                      rfl

theorem cell22_2400571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 11].length) (baseStart_2400571 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2400571 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2400571 prefixEnd_2400571 := by exact prefixLift 2400571
  have htrace : WordTrace (prefixWord ++ tailWord_2400571) baseStart_2400571 baseEnd_2400571 := by
    simpa [prefixWord, tailWord_2400571, baseEnd_2400571] using wordTrace_append hprefix tailTrace_2400571
  have hstable : (prefixWord ++ tailWord_2400571).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2400571).length < 2 ^ (prefixWord ++ tailWord_2400571).sum := by decide
  have hdescent : baseEnd_2400571 < baseStart_2400571 := by decide
  rcases family_descends (prefixWord ++ tailWord_2400571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2400588 : List Nat := [2, 2, 1, 3, 2, 1, 1, 3, 2, 5]
def baseStart_2400588 : Nat := 118140960795 + 2400588 * 2 ^ 59
def prefixEnd_2400588 : Nat := 4983230072969 + 3 ^ 40 * 2400588 * 2
def baseEnd_2400588 : Nat := 821770331610372614739935

theorem tailTrace_2400588 : CollatzResearch.WordTrace tailWord_2400588 prefixEnd_2400588 821770331610372614739935 := by
  unfold tailWord_2400588
  simp only [CollatzResearch.WordTrace]
  refine ⟨43778318713543569317357209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58371091618058092423142945 43778318713543569317357209)
  ·
    refine ⟨32833739035157676988017907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43778318713543569317357209 32833739035157676988017907)
    ·
      refine ⟨49250608552736515482026861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32833739035157676988017907 49250608552736515482026861)
      ·
        refine ⟨18468978207276193305760073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49250608552736515482026861 18468978207276193305760073)
        ·
          refine ⟨13851733655457144979320055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18468978207276193305760073 13851733655457144979320055)
          ·
            refine ⟨20777600483185717468980083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13851733655457144979320055 20777600483185717468980083)
            ·
              refine ⟨31166400724778576203470125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20777600483185717468980083 31166400724778576203470125)
              ·
                refine ⟨11687400271791966076301297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31166400724778576203470125 11687400271791966076301297)
                ·
                  refine ⟨8765550203843974557225973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11687400271791966076301297 8765550203843974557225973)
                  ·
                    refine ⟨821770331610372614739935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8765550203843974557225973 821770331610372614739935)
                    ·
                      rfl

theorem cell22_2400588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 3, 2, 5].length) (baseStart_2400588 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2400588 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2400588 prefixEnd_2400588 := by exact prefixLift 2400588
  have htrace : WordTrace (prefixWord ++ tailWord_2400588) baseStart_2400588 baseEnd_2400588 := by
    simpa [prefixWord, tailWord_2400588, baseEnd_2400588] using wordTrace_append hprefix tailTrace_2400588
  have hstable : (prefixWord ++ tailWord_2400588).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2400588).length < 2 ^ (prefixWord ++ tailWord_2400588).sum := by decide
  have hdescent : baseEnd_2400588 < baseStart_2400588 := by decide
  rcases family_descends (prefixWord ++ tailWord_2400588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2400635 : List Nat := [1, 1, 1, 1, 1, 9, 1, 1, 6]
def baseStart_2400635 : Nat := 118140960795 + 2400635 * 2 ^ 59
def prefixEnd_2400635 : Nat := 4983230072969 + 3 ^ 40 * 2400635 * 2
def baseEnd_2400635 : Nat := 273928806890293386271597

theorem tailTrace_2400635 : CollatzResearch.WordTrace tailWord_2400635 prefixEnd_2400635 273928806890293386271597 := by
  unfold tailWord_2400635
  simp only [CollatzResearch.WordTrace]
  refine ⟨87558351657916865661675359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58372234438611243774450239 87558351657916865661675359)
  ·
    refine ⟨131337527486875298492513039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87558351657916865661675359 131337527486875298492513039)
    ·
      refine ⟨197006291230312947738769559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131337527486875298492513039 197006291230312947738769559)
      ·
        refine ⟨295509436845469421608154339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 197006291230312947738769559 295509436845469421608154339)
        ·
          refine ⟨443264155268204132412231509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 295509436845469421608154339 443264155268204132412231509)
          ·
            refine ⟨2597250909774633588352919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 443264155268204132412231509 2597250909774633588352919)
            ·
              refine ⟨3895876364661950382529379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2597250909774633588352919 3895876364661950382529379)
              ·
                refine ⟨5843814546992925573794069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3895876364661950382529379 5843814546992925573794069)
                ·
                  refine ⟨273928806890293386271597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5843814546992925573794069 273928806890293386271597)
                  ·
                    rfl

theorem cell22_2400635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 9, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 9, 1, 1, 6].length) (baseStart_2400635 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2400635 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2400635 prefixEnd_2400635 := by exact prefixLift 2400635
  have htrace : WordTrace (prefixWord ++ tailWord_2400635) baseStart_2400635 baseEnd_2400635 := by
    simpa [prefixWord, tailWord_2400635, baseEnd_2400635] using wordTrace_append hprefix tailTrace_2400635
  have hstable : (prefixWord ++ tailWord_2400635).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2400635).length < 2 ^ (prefixWord ++ tailWord_2400635).sum := by decide
  have hdescent : baseEnd_2400635 < baseStart_2400635 := by decide
  rcases family_descends (prefixWord ++ tailWord_2400635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2400654 : List Nat := [4, 1, 1, 4, 1, 3, 1, 2, 1, 4]
def baseStart_2400654 : Nat := 118140960795 + 2400654 * 2 ^ 59
def prefixEnd_2400654 : Nat := 4983230072969 + 3 ^ 40 * 2400654 * 2
def baseEnd_2400654 : Nat := 821792924759170442589733

theorem tailTrace_2400654 : CollatzResearch.WordTrace tailWord_2400654 prefixEnd_2400654 821792924759170442589733 := by
  unfold tailWord_2400654
  simp only [CollatzResearch.WordTrace]
  refine ⟨10944880580606003988327127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 58372696429898687937744677 10944880580606003988327127)
  ·
    refine ⟨16417320870909005982490691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10944880580606003988327127 16417320870909005982490691)
    ·
      refine ⟨24625981306363508973736037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16417320870909005982490691 24625981306363508973736037)
      ·
        refine ⟨4617371494943157932575507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24625981306363508973736037 4617371494943157932575507)
        ·
          refine ⟨6926057242414736898863261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4617371494943157932575507 6926057242414736898863261)
          ·
            refine ⟨2597271465905526337073723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6926057242414736898863261 2597271465905526337073723)
            ·
              refine ⟨3895907198858289505610585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2597271465905526337073723 3895907198858289505610585)
              ·
                refine ⟨2921930399143717129207939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3895907198858289505610585 2921930399143717129207939)
                ·
                  refine ⟨4382895598715575693811909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2921930399143717129207939 4382895598715575693811909)
                  ·
                    refine ⟨821792924759170442589733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4382895598715575693811909 821792924759170442589733)
                    ·
                      rfl

theorem cell22_2400654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 3, 1, 2, 1, 4].length) (baseStart_2400654 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2400654 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2400654 prefixEnd_2400654 := by exact prefixLift 2400654
  have htrace : WordTrace (prefixWord ++ tailWord_2400654) baseStart_2400654 baseEnd_2400654 := by
    simpa [prefixWord, tailWord_2400654, baseEnd_2400654] using wordTrace_append hprefix tailTrace_2400654
  have hstable : (prefixWord ++ tailWord_2400654).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2400654).length < 2 ^ (prefixWord ++ tailWord_2400654).sum := by decide
  have hdescent : baseEnd_2400654 < baseStart_2400654 := by decide
  rcases family_descends (prefixWord ++ tailWord_2400654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2400663 : List Nat := [1, 1, 3, 3, 1, 1, 4, 8]
def baseStart_2400663 : Nat := 118140960795 + 2400663 * 2 ^ 59
def prefixEnd_2400663 : Nat := 4983230072969 + 3 ^ 40 * 2400663 * 2
def baseEnd_2400663 : Nat := 91310667293677491012745

theorem tailTrace_2400663 : CollatzResearch.WordTrace tailWord_2400663 prefixEnd_2400663 91310667293677491012745 := by
  unfold tailWord_2400663
  simp only [CollatzResearch.WordTrace]
  refine ⟨87559372901815426443694643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58372915267876950962463095 87559372901815426443694643)
  ·
    refine ⟨131339059352723139665541965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87559372901815426443694643 131339059352723139665541965)
    ·
      refine ⟨49252147257271177374578237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 131339059352723139665541965 49252147257271177374578237)
      ·
        refine ⟨18469555221476691515466839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49252147257271177374578237 18469555221476691515466839)
        ·
          refine ⟨27704332832215037273200259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18469555221476691515466839 27704332832215037273200259)
          ·
            refine ⟨41556499248322555909800389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27704332832215037273200259 41556499248322555909800389)
            ·
              refine ⟨7791843609060479233087573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 41556499248322555909800389 7791843609060479233087573)
              ·
                refine ⟨91310667293677491012745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7791843609060479233087573 91310667293677491012745)
                ·
                  rfl

theorem cell22_2400663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 4, 8].length) (baseStart_2400663 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2400663 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2400663 prefixEnd_2400663 := by exact prefixLift 2400663
  have htrace : WordTrace (prefixWord ++ tailWord_2400663) baseStart_2400663 baseEnd_2400663 := by
    simpa [prefixWord, tailWord_2400663, baseEnd_2400663] using wordTrace_append hprefix tailTrace_2400663
  have hstable : (prefixWord ++ tailWord_2400663).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2400663).length < 2 ^ (prefixWord ++ tailWord_2400663).sum := by decide
  have hdescent : baseEnd_2400663 < baseStart_2400663 := by decide
  rcases family_descends (prefixWord ++ tailWord_2400663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2400665 : List Nat := [1, 2, 1, 2, 1, 4, 4, 1, 2, 4]
def baseStart_2400665 : Nat := 118140960795 + 2400665 * 2 ^ 59
def prefixEnd_2400665 : Nat := 4983230072969 + 3 ^ 40 * 2400665 * 2
def baseEnd_2400665 : Nat := 821796690283970080564699

theorem tailTrace_2400665 : CollatzResearch.WordTrace tailWord_2400665 prefixEnd_2400665 821796690283970080564699 := by
  unfold tailWord_2400665
  simp only [CollatzResearch.WordTrace]
  refine ⟨87559445847808180785267449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58372963898538787190178299 87559445847808180785267449)
  ·
    refine ⟨65669584385856135588950587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87559445847808180785267449 65669584385856135588950587)
    ·
      refine ⟨98504376578784203383425881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65669584385856135588950587 98504376578784203383425881)
      ·
        refine ⟨73878282434088152537569411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 98504376578784203383425881 73878282434088152537569411)
        ·
          refine ⟨110817423651132228806354117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73878282434088152537569411 110817423651132228806354117)
          ·
            refine ⟨20778266934587292901191397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 110817423651132228806354117 20778266934587292901191397)
            ·
              refine ⟨3895925050235117418973387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20778266934587292901191397 3895925050235117418973387)
              ·
                refine ⟨5843887575352676128460081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3895925050235117418973387 5843887575352676128460081)
                ·
                  refine ⟨4382915681514507096345061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5843887575352676128460081 4382915681514507096345061)
                  ·
                    refine ⟨821796690283970080564699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4382915681514507096345061 821796690283970080564699)
                    ·
                      rfl

theorem cell22_2400665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 4, 1, 2, 4].length) (baseStart_2400665 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2400665 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2400665 prefixEnd_2400665 := by exact prefixLift 2400665
  have htrace : WordTrace (prefixWord ++ tailWord_2400665) baseStart_2400665 baseEnd_2400665 := by
    simpa [prefixWord, tailWord_2400665, baseEnd_2400665] using wordTrace_append hprefix tailTrace_2400665
  have hstable : (prefixWord ++ tailWord_2400665).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2400665).length < 2 ^ (prefixWord ++ tailWord_2400665).sum := by decide
  have hdescent : baseEnd_2400665 < baseStart_2400665 := by decide
  rcases family_descends (prefixWord ++ tailWord_2400665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2400680 : List Nat := [2, 1, 6, 1, 1, 11]
def baseStart_2400680 : Nat := 118140960795 + 2400680 * 2 ^ 59
def prefixEnd_2400680 : Nat := 4983230072969 + 3 ^ 40 * 2400680 * 2
def baseEnd_2400680 : Nat := 10145701544327346190613

theorem tailTrace_2400680 : CollatzResearch.WordTrace tailWord_2400680 prefixEnd_2400680 10145701544327346190613 := by
  unfold tailWord_2400680
  simp only [CollatzResearch.WordTrace]
  refine ⟨43779996471376919173531747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58373328628502558898042329 43779996471376919173531747)
  ·
    refine ⟨65669994707065378760297621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43779996471376919173531747 65669994707065378760297621)
    ·
      refine ⟨3078281001893689629388951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 65669994707065378760297621 3078281001893689629388951)
      ·
        refine ⟨4617421502840534444083427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3078281001893689629388951 4617421502840534444083427)
        ·
          refine ⟨6926132254260801666125141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4617421502840534444083427 6926132254260801666125141)
          ·
            refine ⟨10145701544327346190613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 6926132254260801666125141 10145701544327346190613)
            ·
              rfl

theorem cell22_2400680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 11].length) (baseStart_2400680 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2400680 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2400680 prefixEnd_2400680 := by exact prefixLift 2400680
  have htrace : WordTrace (prefixWord ++ tailWord_2400680) baseStart_2400680 baseEnd_2400680 := by
    simpa [prefixWord, tailWord_2400680, baseEnd_2400680] using wordTrace_append hprefix tailTrace_2400680
  have hstable : (prefixWord ++ tailWord_2400680).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2400680).length < 2 ^ (prefixWord ++ tailWord_2400680).sum := by decide
  have hdescent : baseEnd_2400680 < baseStart_2400680 := by decide
  rcases family_descends (prefixWord ++ tailWord_2400680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2400712 : List Nat := [2, 1, 3, 1, 3, 3, 1, 2, 3, 3]
def baseStart_2400712 : Nat := 118140960795 + 2400712 * 2 ^ 59
def prefixEnd_2400712 : Nat := 4983230072969 + 3 ^ 40 * 2400712 * 2
def baseEnd_2400712 : Nat := 821812779344477624639555

theorem tailTrace_2400712 : CollatzResearch.WordTrace tailWord_2400712 prefixEnd_2400712 821812779344477624639555 := by
  unfold tailWord_2400712
  simp only [CollatzResearch.WordTrace]
  refine ⟨43780580039318953906114195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58374106719091938541485593 43780580039318953906114195)
  ·
    refine ⟨65670870058978430859171293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43780580039318953906114195 65670870058978430859171293)
    ·
      refine ⟨24626576272116911572189235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65670870058978430859171293 24626576272116911572189235)
      ·
        refine ⟨36939864408175367358283853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24626576272116911572189235 36939864408175367358283853)
        ·
          refine ⟨13852449153065762759356445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36939864408175367358283853 13852449153065762759356445)
          ·
            refine ⟨5194668432399661034758667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13852449153065762759356445 5194668432399661034758667)
            ·
              refine ⟨7792002648599491552138001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5194668432399661034758667 7792002648599491552138001)
              ·
                refine ⟨5844001986449618664103501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7792002648599491552138001 5844001986449618664103501)
                ·
                  refine ⟨2191500744918606999038813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5844001986449618664103501 2191500744918606999038813)
                  ·
                    refine ⟨821812779344477624639555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2191500744918606999038813 821812779344477624639555)
                    ·
                      rfl

theorem cell22_2400712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 1, 2, 3, 3].length) (baseStart_2400712 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2400712 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2400712 prefixEnd_2400712 := by exact prefixLift 2400712
  have htrace : WordTrace (prefixWord ++ tailWord_2400712) baseStart_2400712 baseEnd_2400712 := by
    simpa [prefixWord, tailWord_2400712, baseEnd_2400712] using wordTrace_append hprefix tailTrace_2400712
  have hstable : (prefixWord ++ tailWord_2400712).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2400712).length < 2 ^ (prefixWord ++ tailWord_2400712).sum := by decide
  have hdescent : baseEnd_2400712 < baseStart_2400712 := by decide
  rcases family_descends (prefixWord ++ tailWord_2400712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2400729 : List Nat := [1, 2, 1, 2, 4, 1, 4, 3, 1, 3]
def baseStart_2400729 : Nat := 118140960795 + 2400729 * 2 ^ 59
def prefixEnd_2400729 : Nat := 4983230072969 + 3 ^ 40 * 2400729 * 2
def baseEnd_2400729 : Nat := 821818598791895246964503

theorem tailTrace_2400729 : CollatzResearch.WordTrace tailWord_2400729 prefixEnd_2400729 821818598791895246964503 := by
  unfold tailWord_2400729
  simp only [CollatzResearch.WordTrace]
  refine ⟨87561780119576319715597241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58374520079717546477064827 87561780119576319715597241)
  ·
    refine ⟨65671335089682239786697931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87561780119576319715597241 65671335089682239786697931)
    ·
      refine ⟨98507002634523359680046897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65671335089682239786697931 98507002634523359680046897)
      ·
        refine ⟨73880251975892519760035173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 98507002634523359680046897 73880251975892519760035173)
        ·
          refine ⟨13852547245479847455006595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 73880251975892519760035173 13852547245479847455006595)
          ·
            refine ⟨20778820868219771182509893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13852547245479847455006595 20778820868219771182509893)
            ·
              refine ⟨3896028912791207096720605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20778820868219771182509893 3896028912791207096720605)
              ·
                refine ⟨1461010842296702661270227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3896028912791207096720605 1461010842296702661270227)
                ·
                  refine ⟨2191516263445053991905341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1461010842296702661270227 2191516263445053991905341)
                  ·
                    refine ⟨821818598791895246964503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2191516263445053991905341 821818598791895246964503)
                    ·
                      rfl

theorem cell22_2400729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 4, 3, 1, 3].length) (baseStart_2400729 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2400729 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2400729 prefixEnd_2400729 := by exact prefixLift 2400729
  have htrace : WordTrace (prefixWord ++ tailWord_2400729) baseStart_2400729 baseEnd_2400729 := by
    simpa [prefixWord, tailWord_2400729, baseEnd_2400729] using wordTrace_append hprefix tailTrace_2400729
  have hstable : (prefixWord ++ tailWord_2400729).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2400729).length < 2 ^ (prefixWord ++ tailWord_2400729).sum := by decide
  have hdescent : baseEnd_2400729 < baseStart_2400729 := by decide
  rcases family_descends (prefixWord ++ tailWord_2400729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2400866 : List Nat := [3, 3, 2, 3, 1, 2, 1, 7]
def baseStart_2400866 : Nat := 118140960795 + 2400866 * 2 ^ 59
def prefixEnd_2400866 : Nat := 4983230072969 + 3 ^ 40 * 2400866 * 2
def baseEnd_2400866 : Nat := 91318388521296950698787

theorem tailTrace_2400866 : CollatzResearch.WordTrace tailWord_2400866 prefixEnd_2400866 91318388521296950698787 := by
  unfold tailWord_2400866
  simp only [CollatzResearch.WordTrace]
  refine ⟨21891694230019998028333613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58377851280053328075556301 21891694230019998028333613)
  ·
    refine ⟨8209385336257499260625105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21891694230019998028333613 8209385336257499260625105)
    ·
      refine ⟨6157039002193124445468829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8209385336257499260625105 6157039002193124445468829)
      ·
        refine ⟨2308889625822421667050811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6157039002193124445468829 2308889625822421667050811)
        ·
          refine ⟨3463334438733632500576217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2308889625822421667050811 3463334438733632500576217)
          ·
            refine ⟨2597500829050224375432163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3463334438733632500576217 2597500829050224375432163)
            ·
              refine ⟨3896251243575336563148245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2597500829050224375432163 3896251243575336563148245)
              ·
                refine ⟨91318388521296950698787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3896251243575336563148245 91318388521296950698787)
                ·
                  rfl

theorem cell22_2400866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 2, 1, 7].length) (baseStart_2400866 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2400866 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2400866 prefixEnd_2400866 := by exact prefixLift 2400866
  have htrace : WordTrace (prefixWord ++ tailWord_2400866) baseStart_2400866 baseEnd_2400866 := by
    simpa [prefixWord, tailWord_2400866, baseEnd_2400866] using wordTrace_append hprefix tailTrace_2400866
  have hstable : (prefixWord ++ tailWord_2400866).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2400866).length < 2 ^ (prefixWord ++ tailWord_2400866).sum := by decide
  have hdescent : baseEnd_2400866 < baseStart_2400866 := by decide
  rcases family_descends (prefixWord ++ tailWord_2400866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2400905 : List Nat := [1, 2, 1, 1, 4, 1, 1, 1, 10]
def baseStart_2400905 : Nat := 118140960795 + 2400905 * 2 ^ 59
def prefixEnd_2400905 : Nat := 4983230072969 + 3 ^ 40 * 2400905 * 2
def baseEnd_2400905 : Nat := 273959615729563151521321

theorem tailTrace_2400905 : CollatzResearch.WordTrace tailWord_2400905 prefixEnd_2400905 273959615729563151521321 := by
  unfold tailWord_2400905
  simp only [CollatzResearch.WordTrace]
  refine ⟨87568199366938701774004169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58378799577959134516002779 87568199366938701774004169)
  ·
    refine ⟨65676149525204026330503127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87568199366938701774004169 65676149525204026330503127)
    ·
      refine ⟨98514224287806039495754691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65676149525204026330503127 98514224287806039495754691)
      ·
        refine ⟨147771336431709059243632037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98514224287806039495754691 147771336431709059243632037)
        ·
          refine ⟨27707125580945448608181007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 147771336431709059243632037 27707125580945448608181007)
          ·
            refine ⟨41560688371418172912271511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27707125580945448608181007 41560688371418172912271511)
            ·
              refine ⟨62341032557127259368407267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41560688371418172912271511 62341032557127259368407267)
              ·
                refine ⟨93511548835690889052610901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62341032557127259368407267 93511548835690889052610901)
                ·
                  refine ⟨273959615729563151521321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 93511548835690889052610901 273959615729563151521321)
                  ·
                    rfl

theorem cell22_2400905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 1, 10].length) (baseStart_2400905 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2400905 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2400905 prefixEnd_2400905 := by exact prefixLift 2400905
  have htrace : WordTrace (prefixWord ++ tailWord_2400905) baseStart_2400905 baseEnd_2400905 := by
    simpa [prefixWord, tailWord_2400905, baseEnd_2400905] using wordTrace_append hprefix tailTrace_2400905
  have hstable : (prefixWord ++ tailWord_2400905).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2400905).length < 2 ^ (prefixWord ++ tailWord_2400905).sum := by decide
  have hdescent : baseEnd_2400905 < baseStart_2400905 := by decide
  rcases family_descends (prefixWord ++ tailWord_2400905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2400937 : List Nat := [1, 2, 1, 1, 1, 1, 2, 4, 6, 3]
def baseStart_2400937 : Nat := 118140960795 + 2400937 * 2 ^ 59
def prefixEnd_2400937 : Nat := 4983230072969 + 3 ^ 40 * 2400937 * 2
def baseEnd_2400937 : Nat := 821889801442652037763865

theorem tailTrace_2400937 : CollatzResearch.WordTrace tailWord_2400937 prefixEnd_2400937 821889801442652037763865 := by
  unfold tailWord_2400937
  simp only [CollatzResearch.WordTrace]
  refine ⟨87569366502822771239169065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58379577668548514159446043 87569366502822771239169065)
  ·
    refine ⟨65677024877117078429376799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87569366502822771239169065 65677024877117078429376799)
    ·
      refine ⟨98515537315675617644065199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65677024877117078429376799 98515537315675617644065199)
      ·
        refine ⟨147773305973513426466097799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98515537315675617644065199 147773305973513426466097799)
        ·
          refine ⟨221659958960270139699146699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 147773305973513426466097799 221659958960270139699146699)
          ·
            refine ⟨332489938440405209548720049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 221659958960270139699146699 332489938440405209548720049)
            ·
              refine ⟨249367453830303907161540037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 332489938440405209548720049 249367453830303907161540037)
              ·
                refine ⟨46756397593181982592788757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 249367453830303907161540037 46756397593181982592788757)
                ·
                  refine ⟨2191706137180405434036973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 46756397593181982592788757 2191706137180405434036973)
                  ·
                    refine ⟨821889801442652037763865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2191706137180405434036973 821889801442652037763865)
                    ·
                      rfl

theorem cell22_2400937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 4, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 4, 6, 3].length) (baseStart_2400937 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2400937 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2400937 prefixEnd_2400937 := by exact prefixLift 2400937
  have htrace : WordTrace (prefixWord ++ tailWord_2400937) baseStart_2400937 baseEnd_2400937 := by
    simpa [prefixWord, tailWord_2400937, baseEnd_2400937] using wordTrace_append hprefix tailTrace_2400937
  have hstable : (prefixWord ++ tailWord_2400937).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2400937).length < 2 ^ (prefixWord ++ tailWord_2400937).sum := by decide
  have hdescent : baseEnd_2400937 < baseStart_2400937 := by decide
  rcases family_descends (prefixWord ++ tailWord_2400937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2400941 : List Nat := [1, 5, 2, 1, 1, 3, 2, 2, 1, 4]
def baseStart_2400941 : Nat := 118140960795 + 2400941 * 2 ^ 59
def prefixEnd_2400941 : Nat := 4983230072969 + 3 ^ 40 * 2400941 * 2
def baseEnd_2400941 : Nat := 821891170724397360663853

theorem tailTrace_2400941 : CollatzResearch.WordTrace tailWord_2400941 prefixEnd_2400941 821891170724397360663853 := by
  unfold tailWord_2400941
  simp only [CollatzResearch.WordTrace]
  refine ⟨87569512394808279922314677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58379674929872186614876451 87569512394808279922314677)
  ·
    refine ⟨8209641787013276242717001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 87569512394808279922314677 8209641787013276242717001)
    ·
      refine ⟨6157231340259957182037751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8209641787013276242717001 6157231340259957182037751)
      ·
        refine ⟨9235847010389935773056627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6157231340259957182037751 9235847010389935773056627)
        ·
          refine ⟨13853770515584903659584941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9235847010389935773056627 13853770515584903659584941)
          ·
            refine ⟨5195163943344338872344353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13853770515584903659584941 5195163943344338872344353)
            ·
              refine ⟨3896372957508254154258265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5195163943344338872344353 3896372957508254154258265)
              ·
                refine ⟨2922279718131190615693699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3896372957508254154258265 2922279718131190615693699)
                ·
                  refine ⟨4383419577196785923540549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2922279718131190615693699 4383419577196785923540549)
                  ·
                    refine ⟨821891170724397360663853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4383419577196785923540549 821891170724397360663853)
                    ·
                      rfl

theorem cell22_2400941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 2, 2, 1, 4].length) (baseStart_2400941 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2400941 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2400941 prefixEnd_2400941 := by exact prefixLift 2400941
  have htrace : WordTrace (prefixWord ++ tailWord_2400941) baseStart_2400941 baseEnd_2400941 := by
    simpa [prefixWord, tailWord_2400941, baseEnd_2400941] using wordTrace_append hprefix tailTrace_2400941
  have hstable : (prefixWord ++ tailWord_2400941).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2400941).length < 2 ^ (prefixWord ++ tailWord_2400941).sum := by decide
  have hdescent : baseEnd_2400941 < baseStart_2400941 := by decide
  rcases family_descends (prefixWord ++ tailWord_2400941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2400973 : List Nat := [1, 6, 2, 1, 2, 2, 1, 1, 6]
def baseStart_2400973 : Nat := 118140960795 + 2400973 * 2 ^ 59
def prefixEnd_2400973 : Nat := 4983230072969 + 3 ^ 40 * 2400973 * 2
def baseEnd_2400973 : Nat := 273967374992786647954585

theorem tailTrace_2400973 : CollatzResearch.WordTrace tailWord_2400973 prefixEnd_2400973 273967374992786647954585 := by
  unfold tailWord_2400973
  simp only [CollatzResearch.WordTrace]
  refine ⟨87570679530692349387479573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58380453020461566258319715 87570679530692349387479573)
  ·
    refine ⟨4104875603001203877538105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 87570679530692349387479573 4104875603001203877538105)
    ·
      refine ⟨3078656702250902908153579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4104875603001203877538105 3078656702250902908153579)
      ·
        refine ⟨4617985053376354362230369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3078656702250902908153579 4617985053376354362230369)
        ·
          refine ⟨3463488790032265771672777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4617985053376354362230369 3463488790032265771672777)
          ·
            refine ⟨2597616592524199328754583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3463488790032265771672777 2597616592524199328754583)
            ·
              refine ⟨3896424888786298993131875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2597616592524199328754583 3896424888786298993131875)
              ·
                refine ⟨5844637333179448489697813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3896424888786298993131875 5844637333179448489697813)
                ·
                  refine ⟨273967374992786647954585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5844637333179448489697813 273967374992786647954585)
                  ·
                    rfl

theorem cell22_2400973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 2, 1, 1, 6].length) (baseStart_2400973 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2400973 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2400973 prefixEnd_2400973 := by exact prefixLift 2400973
  have htrace : WordTrace (prefixWord ++ tailWord_2400973) baseStart_2400973 baseEnd_2400973 := by
    simpa [prefixWord, tailWord_2400973, baseEnd_2400973] using wordTrace_append hprefix tailTrace_2400973
  have hstable : (prefixWord ++ tailWord_2400973).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2400973).length < 2 ^ (prefixWord ++ tailWord_2400973).sum := by decide
  have hdescent : baseEnd_2400973 < baseStart_2400973 := by decide
  rcases family_descends (prefixWord ++ tailWord_2400973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2400988 : List Nat := [2, 2, 5, 1, 1, 2, 1, 3, 2, 3]
def baseStart_2400988 : Nat := 118140960795 + 2400988 * 2 ^ 59
def prefixEnd_2400988 : Nat := 4983230072969 + 3 ^ 40 * 2400988 * 2
def baseEnd_2400988 : Nat := 821907259784904904738709

theorem tailTrace_2400988 : CollatzResearch.WordTrace tailWord_2400988 prefixEnd_2400988 821907259784904904738709 := by
  unfold tailWord_2400988
  simp only [CollatzResearch.WordTrace]
  refine ⟨43785613312819003474637809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58380817750425337966183745 43785613312819003474637809)
  ·
    refine ⟨32839209984614252605978357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43785613312819003474637809 32839209984614252605978357)
    ·
      refine ⟨3078675936057586181810471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 32839209984614252605978357 3078675936057586181810471)
      ·
        refine ⟨4618013904086379272715707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3078675936057586181810471 4618013904086379272715707)
        ·
          refine ⟨6927020856129568909073561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4618013904086379272715707 6927020856129568909073561)
          ·
            refine ⟨5195265642097176681805171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6927020856129568909073561 5195265642097176681805171)
            ·
              refine ⟨7792898463145765022707757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5195265642097176681805171 7792898463145765022707757)
              ·
                refine ⟨2922336923679661883515409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7792898463145765022707757 2922336923679661883515409)
                ·
                  refine ⟨2191752692759746412636557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2922336923679661883515409 2191752692759746412636557)
                  ·
                    refine ⟨821907259784904904738709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2191752692759746412636557 821907259784904904738709)
                    ·
                      rfl

theorem cell22_2400988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 1, 3, 2, 3].length) (baseStart_2400988 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2400988 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2400988 prefixEnd_2400988 := by exact prefixLift 2400988
  have htrace : WordTrace (prefixWord ++ tailWord_2400988) baseStart_2400988 baseEnd_2400988 := by
    simpa [prefixWord, tailWord_2400988, baseEnd_2400988] using wordTrace_append hprefix tailTrace_2400988
  have hstable : (prefixWord ++ tailWord_2400988).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2400988).length < 2 ^ (prefixWord ++ tailWord_2400988).sum := by decide
  have hdescent : baseEnd_2400988 < baseStart_2400988 := by decide
  rcases family_descends (prefixWord ++ tailWord_2400988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2401016 : List Nat := [2, 1, 2, 1, 1, 2, 4, 5, 1, 3]
def baseStart_2401016 : Nat := 118140960795 + 2401016 * 2 ^ 59
def prefixEnd_2401016 : Nat := 4983230072969 + 3 ^ 40 * 2401016 * 2
def baseEnd_2401016 : Nat := 821916844757122165038623

theorem tailTrace_2401016 : CollatzResearch.WordTrace tailWord_2401016 prefixEnd_2401016 821916844757122165038623 := by
  unfold tailWord_2401016
  simp only [CollatzResearch.WordTrace]
  refine ⟨43786123934768283865647451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58381498579691045154196601 43786123934768283865647451)
  ·
    refine ⟨65679185902152425798471177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43786123934768283865647451 65679185902152425798471177)
    ·
      refine ⟨49259389426614319348853383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65679185902152425798471177 49259389426614319348853383)
      ·
        refine ⟨73889084139921479023280075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49259389426614319348853383 73889084139921479023280075)
        ·
          refine ⟨110833626209882218534920113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73889084139921479023280075 110833626209882218534920113)
          ·
            refine ⟨83125219657411663901190085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 110833626209882218534920113 83125219657411663901190085)
            ·
              refine ⟨15585978685764686981473141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 83125219657411663901190085 15585978685764686981473141)
              ·
                refine ⟨1461185501790439404513107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15585978685764686981473141 1461185501790439404513107)
                ·
                  refine ⟨2191778252685659106769661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1461185501790439404513107 2191778252685659106769661)
                  ·
                    refine ⟨821916844757122165038623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2191778252685659106769661 821916844757122165038623)
                    ·
                      rfl

theorem cell22_2401016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 4, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 4, 5, 1, 3].length) (baseStart_2401016 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2401016 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2401016 prefixEnd_2401016 := by exact prefixLift 2401016
  have htrace : WordTrace (prefixWord ++ tailWord_2401016) baseStart_2401016 baseEnd_2401016 := by
    simpa [prefixWord, tailWord_2401016, baseEnd_2401016] using wordTrace_append hprefix tailTrace_2401016
  have hstable : (prefixWord ++ tailWord_2401016).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2401016).length < 2 ^ (prefixWord ++ tailWord_2401016).sum := by decide
  have hdescent : baseEnd_2401016 < baseStart_2401016 := by decide
  rcases family_descends (prefixWord ++ tailWord_2401016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2401027 : List Nat := [1, 1, 1, 3, 2, 2, 1, 4, 2, 5]
def baseStart_2401027 : Nat := 118140960795 + 2401027 * 2 ^ 59
def prefixEnd_2401027 : Nat := 4983230072969 + 3 ^ 40 * 2401027 * 2
def baseEnd_2401027 : Nat := 821920610281921803013589

theorem tailTrace_2401027 : CollatzResearch.WordTrace tailWord_2401027 prefixEnd_2401027 821920610281921803013589 := by
  unfold tailWord_2401027
  simp only [CollatzResearch.WordTrace]
  refine ⟨87572649072496716609945335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58381766048331144406630223 87572649072496716609945335)
  ·
    refine ⟨131358973608745074914918003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87572649072496716609945335 131358973608745074914918003)
    ·
      refine ⟨197038460413117612372377005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131358973608745074914918003 197038460413117612372377005)
      ·
        refine ⟨73889422654919104639641377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 197038460413117612372377005 73889422654919104639641377)
        ·
          refine ⟨55417066991189328479731033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73889422654919104639641377 55417066991189328479731033)
          ·
            refine ⟨41562800243391996359798275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55417066991189328479731033 41562800243391996359798275)
            ·
              refine ⟨62344200365087994539697413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41562800243391996359798275 62344200365087994539697413)
              ·
                refine ⟨11689537568453998976193265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 62344200365087994539697413 11689537568453998976193265)
                ·
                  refine ⟨8767153176340499232144949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11689537568453998976193265 8767153176340499232144949)
                  ·
                    refine ⟨821920610281921803013589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8767153176340499232144949 821920610281921803013589)
                    ·
                      rfl

theorem cell22_2401027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 4, 2, 5].length) (baseStart_2401027 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2401027 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2401027 prefixEnd_2401027 := by exact prefixLift 2401027
  have htrace : WordTrace (prefixWord ++ tailWord_2401027) baseStart_2401027 baseEnd_2401027 := by
    simpa [prefixWord, tailWord_2401027, baseEnd_2401027] using wordTrace_append hprefix tailTrace_2401027
  have hstable : (prefixWord ++ tailWord_2401027).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2401027).length < 2 ^ (prefixWord ++ tailWord_2401027).sum := by decide
  have hdescent : baseEnd_2401027 < baseStart_2401027 := by decide
  rcases family_descends (prefixWord ++ tailWord_2401027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2401033 : List Nat := [1, 2, 1, 1, 3, 2, 6, 2, 1, 3]
def baseStart_2401033 : Nat := 118140960795 + 2401033 * 2 ^ 59
def prefixEnd_2401033 : Nat := 4983230072969 + 3 ^ 40 * 2401033 * 2
def baseEnd_2401033 : Nat := 821922664204539787363571

theorem tailTrace_2401033 : CollatzResearch.WordTrace tailWord_2401033 prefixEnd_2401033 821922664204539787363571 := by
  unfold tailWord_2401033
  simp only [CollatzResearch.WordTrace]
  refine ⟨87572867910474979634663753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58381911940316653089775835 87572867910474979634663753)
  ·
    refine ⟨65679650932856234725997815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87572867910474979634663753 65679650932856234725997815)
    ·
      refine ⟨98519476399284352088996723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65679650932856234725997815 98519476399284352088996723)
      ·
        refine ⟨147779214598926528133495085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98519476399284352088996723 147779214598926528133495085)
        ·
          refine ⟨55417205474597448050060657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 147779214598926528133495085 55417205474597448050060657)
          ·
            refine ⟨41562904105948086037545493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55417205474597448050060657 41562904105948086037545493)
            ·
              refine ⟨1948261129966316533009945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 41562904105948086037545493 1948261129966316533009945)
              ·
                refine ⟨1461195847474737399757459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1948261129966316533009945 1461195847474737399757459)
                ·
                  refine ⟨2191793771212106099636189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1461195847474737399757459 2191793771212106099636189)
                  ·
                    refine ⟨821922664204539787363571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2191793771212106099636189 821922664204539787363571)
                    ·
                      rfl

theorem cell22_2401033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 6, 2, 1, 3].length) (baseStart_2401033 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2401033 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2401033 prefixEnd_2401033 := by exact prefixLift 2401033
  have htrace : WordTrace (prefixWord ++ tailWord_2401033) baseStart_2401033 baseEnd_2401033 := by
    simpa [prefixWord, tailWord_2401033, baseEnd_2401033] using wordTrace_append hprefix tailTrace_2401033
  have hstable : (prefixWord ++ tailWord_2401033).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2401033).length < 2 ^ (prefixWord ++ tailWord_2401033).sum := by decide
  have hdescent : baseEnd_2401033 < baseStart_2401033 := by decide
  rcases family_descends (prefixWord ++ tailWord_2401033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2401059 : List Nat := [1, 1, 1, 4, 2, 1, 1, 6, 1, 4]
def baseStart_2401059 : Nat := 118140960795 + 2401059 * 2 ^ 59
def prefixEnd_2401059 : Nat := 4983230072969 + 3 ^ 40 * 2401059 * 2
def baseEnd_2401059 : Nat := 821931564535884386213491

theorem tailTrace_2401059 : CollatzResearch.WordTrace tailWord_2401059 prefixEnd_2401059 821931564535884386213491 := by
  unfold tailWord_2401059
  simp only [CollatzResearch.WordTrace]
  refine ⟨87573816208380786075110231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58382544138920524050073487 87573816208380786075110231)
  ·
    refine ⟨131360724312571179112665347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87573816208380786075110231 131360724312571179112665347)
    ·
      refine ⟨197041086468856768668998021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131360724312571179112665347 197041086468856768668998021)
      ·
        refine ⟨36945203712910644125437129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 197041086468856768668998021 36945203712910644125437129)
        ·
          refine ⟨27708902784682983094077847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36945203712910644125437129 27708902784682983094077847)
          ·
            refine ⟨41563354177024474641116771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27708902784682983094077847 41563354177024474641116771)
            ·
              refine ⟨62345031265536711961675157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41563354177024474641116771 62345031265536711961675157)
              ·
                refine ⟨2922423340572033373203523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 62345031265536711961675157 2922423340572033373203523)
                ·
                  refine ⟨4383635010858050059805285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2922423340572033373203523 4383635010858050059805285)
                  ·
                    refine ⟨821931564535884386213491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4383635010858050059805285 821931564535884386213491)
                    ·
                      rfl

theorem cell22_2401059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 6, 1, 4].length) (baseStart_2401059 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2401059 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2401059 prefixEnd_2401059 := by exact prefixLift 2401059
  have htrace : WordTrace (prefixWord ++ tailWord_2401059) baseStart_2401059 baseEnd_2401059 := by
    simpa [prefixWord, tailWord_2401059, baseEnd_2401059] using wordTrace_append hprefix tailTrace_2401059
  have hstable : (prefixWord ++ tailWord_2401059).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2401059).length < 2 ^ (prefixWord ++ tailWord_2401059).sum := by decide
  have hdescent : baseEnd_2401059 < baseStart_2401059 := by decide
  rcases family_descends (prefixWord ++ tailWord_2401059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2401151 : List Nat := [1, 1, 2, 2, 1, 1, 7, 1, 3, 3]
def baseStart_2401151 : Nat := 118140960795 + 2401151 * 2 ^ 59
def prefixEnd_2401151 : Nat := 4983230072969 + 3 ^ 40 * 2401151 * 2
def baseEnd_2401151 : Nat := 821963058016026812913209

theorem tailTrace_2401151 : CollatzResearch.WordTrace tailWord_2401151 prefixEnd_2401151 821963058016026812913209 := by
  unfold tailWord_2401151
  simp only [CollatzResearch.WordTrace]
  refine ⟨87577171724047485787459307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58384781149364990524972871 87577171724047485787459307)
  ·
    refine ⟨131365757586071228681188961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87577171724047485787459307 131365757586071228681188961)
    ·
      refine ⟨98524318189553421510891721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 131365757586071228681188961 98524318189553421510891721)
      ·
        refine ⟨73893238642165066133168791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 98524318189553421510891721 73893238642165066133168791)
        ·
          refine ⟨110839857963247599199753187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73893238642165066133168791 110839857963247599199753187)
          ·
            refine ⟨166259786944871398799629781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 110839857963247599199753187 166259786944871398799629781)
            ·
              refine ⟨3896713756520423409366323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 166259786944871398799629781 3896713756520423409366323)
              ·
                refine ⟨5845070634780635114049485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3896713756520423409366323 5845070634780635114049485)
                ·
                  refine ⟨2191901488042738167768557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5845070634780635114049485 2191901488042738167768557)
                  ·
                    refine ⟨821963058016026812913209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2191901488042738167768557 821963058016026812913209)
                    ·
                      rfl

theorem cell22_2401151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 7, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 7, 1, 3, 3].length) (baseStart_2401151 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2401151 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2401151 prefixEnd_2401151 := by exact prefixLift 2401151
  have htrace : WordTrace (prefixWord ++ tailWord_2401151) baseStart_2401151 baseEnd_2401151 := by
    simpa [prefixWord, tailWord_2401151, baseEnd_2401151] using wordTrace_append hprefix tailTrace_2401151
  have hstable : (prefixWord ++ tailWord_2401151).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2401151).length < 2 ^ (prefixWord ++ tailWord_2401151).sum := by decide
  have hdescent : baseEnd_2401151 < baseStart_2401151 := by decide
  rcases family_descends (prefixWord ++ tailWord_2401151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2401241 : List Nat := [1, 2, 1, 2, 5, 1, 2, 2, 1, 5]
def baseStart_2401241 : Nat := 118140960795 + 2401241 * 2 ^ 59
def prefixEnd_2401241 : Nat := 4983230072969 + 3 ^ 40 * 2401241 * 2
def baseEnd_2401241 : Nat := 821993866855296578162933

theorem tailTrace_2401241 : CollatzResearch.WordTrace tailWord_2401241 prefixEnd_2401241 821993866855296578162933 := by
  unfold tailWord_2401241
  simp only [CollatzResearch.WordTrace]
  refine ⟨87580454293721431158235577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58386969529147620772157051 87580454293721431158235577)
  ·
    refine ⟨65685340720291073368676683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87580454293721431158235577 65685340720291073368676683)
    ·
      refine ⟨98528011080436610053015025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65685340720291073368676683 98528011080436610053015025)
      ·
        refine ⟨73896008310327457539761269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 98528011080436610053015025 73896008310327457539761269)
        ·
          refine ⟨6927750779093199144352619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 73896008310327457539761269 6927750779093199144352619)
          ·
            refine ⟨10391626168639798716528929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6927750779093199144352619 10391626168639798716528929)
            ·
              refine ⟨7793719626479849037396697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10391626168639798716528929 7793719626479849037396697)
              ·
                refine ⟨5845289719859886778047523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7793719626479849037396697 5845289719859886778047523)
                ·
                  refine ⟨8767934579789830167071285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5845289719859886778047523 8767934579789830167071285)
                  ·
                    refine ⟨821993866855296578162933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8767934579789830167071285 821993866855296578162933)
                    ·
                      rfl

theorem cell22_2401241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 2, 2, 1, 5].length) (baseStart_2401241 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2401241 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2401241 prefixEnd_2401241 := by exact prefixLift 2401241
  have htrace : WordTrace (prefixWord ++ tailWord_2401241) baseStart_2401241 baseEnd_2401241 := by
    simpa [prefixWord, tailWord_2401241, baseEnd_2401241] using wordTrace_append hprefix tailTrace_2401241
  have hstable : (prefixWord ++ tailWord_2401241).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2401241).length < 2 ^ (prefixWord ++ tailWord_2401241).sum := by decide
  have hdescent : baseEnd_2401241 < baseStart_2401241 := by decide
  rcases family_descends (prefixWord ++ tailWord_2401241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2401245 : List Nat := [1, 4, 3, 1, 2, 1, 4, 1, 1, 4]
def baseStart_2401245 : Nat := 118140960795 + 2401245 * 2 ^ 59
def prefixEnd_2401245 : Nat := 4983230072969 + 3 ^ 40 * 2401245 * 2
def baseEnd_2401245 : Nat := 821995236137041901062921

theorem tailTrace_2401245 : CollatzResearch.WordTrace tailWord_2401245 prefixEnd_2401245 821995236137041901062921 := by
  unfold tailWord_2401245
  simp only [CollatzResearch.WordTrace]
  refine ⟨87580600185706939841381189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58387066790471293227587459 87580600185706939841381189)
  ·
    refine ⟨16421362534820051220258973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 87580600185706939841381189 16421362534820051220258973)
    ·
      refine ⟨6158010950557519207597115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16421362534820051220258973 6158010950557519207597115)
      ·
        refine ⟨9237016425836278811395673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6158010950557519207597115 9237016425836278811395673)
        ·
          refine ⟨6927762319377209108546755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9237016425836278811395673 6927762319377209108546755)
          ·
            refine ⟨10391643479065813662820133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6927762319377209108546755 10391643479065813662820133)
            ·
              refine ⟨1948433152324840061778775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10391643479065813662820133 1948433152324840061778775)
              ·
                refine ⟨2922649728487260092668163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1948433152324840061778775 2922649728487260092668163)
                ·
                  refine ⟨4383974592730890139002245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2922649728487260092668163 4383974592730890139002245)
                  ·
                    refine ⟨821995236137041901062921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4383974592730890139002245 821995236137041901062921)
                    ·
                      rfl

theorem cell22_2401245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 4, 1, 1, 4].length) (baseStart_2401245 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2401245 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2401245 prefixEnd_2401245 := by exact prefixLift 2401245
  have htrace : WordTrace (prefixWord ++ tailWord_2401245) baseStart_2401245 baseEnd_2401245 := by
    simpa [prefixWord, tailWord_2401245, baseEnd_2401245] using wordTrace_append hprefix tailTrace_2401245
  have hstable : (prefixWord ++ tailWord_2401245).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2401245).length < 2 ^ (prefixWord ++ tailWord_2401245).sum := by decide
  have hdescent : baseEnd_2401245 < baseStart_2401245 := by decide
  rcases family_descends (prefixWord ++ tailWord_2401245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2401256 : List Nat := [2, 1, 4, 1, 1, 1, 2, 4, 2, 4]
def baseStart_2401256 : Nat := 118140960795 + 2401256 * 2 ^ 59
def prefixEnd_2401256 : Nat := 4983230072969 + 3 ^ 40 * 2401256 * 2
def baseEnd_2401256 : Nat := 821999001661841539037887

theorem tailTrace_2401256 : CollatzResearch.WordTrace tailWord_2401256 prefixEnd_2401256 821999001661841539037887 := by
  unfold tailWord_2401256
  simp only [CollatzResearch.WordTrace]
  refine ⟨43790500694333544360015811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58387334259111392480021081 43790500694333544360015811)
  ·
    refine ⟨65685751041500316540023717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43790500694333544360015811 65685751041500316540023717)
    ·
      refine ⟨12316078320281309351254447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 65685751041500316540023717 12316078320281309351254447)
      ·
        refine ⟨18474117480421964026881671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12316078320281309351254447 18474117480421964026881671)
        ·
          refine ⟨27711176220632946040322507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18474117480421964026881671 27711176220632946040322507)
          ·
            refine ⟨41566764330949419060483761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27711176220632946040322507 41566764330949419060483761)
            ·
              refine ⟨31175073248212064295362821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41566764330949419060483761 31175073248212064295362821)
              ·
                refine ⟨5845326234039762055380529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31175073248212064295362821 5845326234039762055380529)
                ·
                  refine ⟨4383994675529821541535397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5845326234039762055380529 4383994675529821541535397)
                  ·
                    refine ⟨821999001661841539037887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4383994675529821541535397 821999001661841539037887)
                    ·
                      rfl

theorem cell22_2401256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 4, 2, 4].length) (baseStart_2401256 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2401256 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2401256 prefixEnd_2401256 := by exact prefixLift 2401256
  have htrace : WordTrace (prefixWord ++ tailWord_2401256) baseStart_2401256 baseEnd_2401256 := by
    simpa [prefixWord, tailWord_2401256, baseEnd_2401256] using wordTrace_append hprefix tailTrace_2401256
  have hstable : (prefixWord ++ tailWord_2401256).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2401256).length < 2 ^ (prefixWord ++ tailWord_2401256).sum := by decide
  have hdescent : baseEnd_2401256 < baseStart_2401256 := by decide
  rcases family_descends (prefixWord ++ tailWord_2401256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2401258 : List Nat := [3, 1, 3, 1, 2, 3, 1, 1, 4, 3]
def baseStart_2401258 : Nat := 118140960795 + 2401258 * 2 ^ 59
def prefixEnd_2401258 : Nat := 4983230072969 + 3 ^ 40 * 2401258 * 2
def baseEnd_2401258 : Nat := 821999686302714200487881

theorem tailTrace_2401258 : CollatzResearch.WordTrace tailWord_2401258 prefixEnd_2401258 821999686302714200487881 := by
  unfold tailWord_2401258
  simp only [CollatzResearch.WordTrace]
  refine ⟨21895268583664960765401107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58387382889773228707736285 21895268583664960765401107)
  ·
    refine ⟨32842902875497441148101661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21895268583664960765401107 32842902875497441148101661)
    ·
      refine ⟨12316088578311540430538123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32842902875497441148101661 12316088578311540430538123)
      ·
        refine ⟨18474132867467310645807185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12316088578311540430538123 18474132867467310645807185)
        ·
          refine ⟨13855599650600482984355389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18474132867467310645807185 13855599650600482984355389)
          ·
            refine ⟨5195849868975181119133271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13855599650600482984355389 5195849868975181119133271)
            ·
              refine ⟨7793774803462771678699907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5195849868975181119133271 7793774803462771678699907)
              ·
                refine ⟨11690662205194157518049861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7793774803462771678699907 11690662205194157518049861)
                ·
                  refine ⟨2191999163473904534634349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11690662205194157518049861 2191999163473904534634349)
                  ·
                    refine ⟨821999686302714200487881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2191999163473904534634349 821999686302714200487881)
                    ·
                      rfl

theorem cell22_2401258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 1, 1, 4, 3].length) (baseStart_2401258 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2401258 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2401258 prefixEnd_2401258 := by exact prefixLift 2401258
  have htrace : WordTrace (prefixWord ++ tailWord_2401258) baseStart_2401258 baseEnd_2401258 := by
    simpa [prefixWord, tailWord_2401258, baseEnd_2401258] using wordTrace_append hprefix tailTrace_2401258
  have hstable : (prefixWord ++ tailWord_2401258).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2401258).length < 2 ^ (prefixWord ++ tailWord_2401258).sum := by decide
  have hdescent : baseEnd_2401258 < baseStart_2401258 := by decide
  rcases family_descends (prefixWord ++ tailWord_2401258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2401288 : List Nat := [2, 1, 3, 2, 1, 5, 2, 6]
def baseStart_2401288 : Nat := 118140960795 + 2401288 * 2 ^ 59
def prefixEnd_2401288 : Nat := 4983230072969 + 3 ^ 40 * 2401288 * 2
def baseEnd_2401288 : Nat := 91334439546200458026421

theorem tailTrace_2401288 : CollatzResearch.WordTrace tailWord_2401288 prefixEnd_2401288 91334439546200458026421 := by
  unfold tailWord_2401288
  simp only [CollatzResearch.WordTrace]
  refine ⟨43791084262275579092598259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58388112349700772123464345 43791084262275579092598259)
  ·
    refine ⟨65686626393413368638897389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43791084262275579092598259 65686626393413368638897389)
    ·
      refine ⟨24632484897530013239586521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65686626393413368638897389 24632484897530013239586521)
      ·
        refine ⟨18474363673147509929689891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24632484897530013239586521 18474363673147509929689891)
        ·
          refine ⟨27711545509721264894534837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18474363673147509929689891 27711545509721264894534837)
          ·
            refine ⟨2597957391536368583862641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 27711545509721264894534837 2597957391536368583862641)
            ·
              refine ⟨1948468043652276437896981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2597957391536368583862641 1948468043652276437896981)
              ·
                refine ⟨91334439546200458026421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1948468043652276437896981 91334439546200458026421)
                ·
                  rfl

theorem cell22_2401288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 5, 2, 6].length) (baseStart_2401288 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2401288 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2401288 prefixEnd_2401288 := by exact prefixLift 2401288
  have htrace : WordTrace (prefixWord ++ tailWord_2401288) baseStart_2401288 baseEnd_2401288 := by
    simpa [prefixWord, tailWord_2401288, baseEnd_2401288] using wordTrace_append hprefix tailTrace_2401288
  have hstable : (prefixWord ++ tailWord_2401288).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2401288).length < 2 ^ (prefixWord ++ tailWord_2401288).sum := by decide
  have hdescent : baseEnd_2401288 < baseStart_2401288 := by decide
  rcases family_descends (prefixWord ++ tailWord_2401288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2401376 : List Nat := [2, 1, 1, 3, 2, 2, 1, 2, 3, 5]
def baseStart_2401376 : Nat := 118140960795 + 2401376 * 2 ^ 59
def prefixEnd_2401376 : Nat := 4983230072969 + 3 ^ 40 * 2401376 * 2
def baseEnd_2401376 : Nat := 822040080114201226037519

theorem tailTrace_2401376 : CollatzResearch.WordTrace tailWord_2401376 prefixEnd_2401376 822040080114201226037519 := by
  unfold tailWord_2401376
  simp only [CollatzResearch.WordTrace]
  refine ⟨43792689074116174607199991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58390252098821566142933321 43792689074116174607199991)
  ·
    refine ⟨65689033611174261910799987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43792689074116174607199991 65689033611174261910799987)
    ·
      refine ⟨98533550416761392866199981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65689033611174261910799987 98533550416761392866199981)
      ·
        refine ⟨36950081406285522324824993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 98533550416761392866199981 36950081406285522324824993)
        ·
          refine ⟨27712561054714141743618745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36950081406285522324824993 27712561054714141743618745)
          ·
            refine ⟨20784420791035606307714059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27712561054714141743618745 20784420791035606307714059)
            ·
              refine ⟨31176631186553409461571089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20784420791035606307714059 31176631186553409461571089)
              ·
                refine ⟨23382473389915057096178317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31176631186553409461571089 23382473389915057096178317)
                ·
                  refine ⟨8768427521218146411066869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23382473389915057096178317 8768427521218146411066869)
                  ·
                    refine ⟨822040080114201226037519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8768427521218146411066869 822040080114201226037519)
                    ·
                      rfl

theorem cell22_2401376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 2, 3, 5].length) (baseStart_2401376 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2401376 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2401376 prefixEnd_2401376 := by exact prefixLift 2401376
  have htrace : WordTrace (prefixWord ++ tailWord_2401376) baseStart_2401376 baseEnd_2401376 := by
    simpa [prefixWord, tailWord_2401376, baseEnd_2401376] using wordTrace_append hprefix tailTrace_2401376
  have hstable : (prefixWord ++ tailWord_2401376).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2401376).length < 2 ^ (prefixWord ++ tailWord_2401376).sum := by decide
  have hdescent : baseEnd_2401376 < baseStart_2401376 := by decide
  rcases family_descends (prefixWord ++ tailWord_2401376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2401391 : List Nat := [1, 1, 2, 1, 3, 3, 2, 2, 1, 6]
def baseStart_2401391 : Nat := 118140960795 + 2401391 * 2 ^ 59
def prefixEnd_2401391 : Nat := 4983230072969 + 3 ^ 40 * 2401391 * 2
def baseEnd_2401391 : Nat := 822045214920746186912473

theorem tailTrace_2401391 : CollatzResearch.WordTrace tailWord_2401391 prefixEnd_2401391 822045214920746186912473 := by
  unfold tailWord_2401391
  simp only [CollatzResearch.WordTrace]
  refine ⟨87585925243178006776196027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58390616828785337850797351 87585925243178006776196027)
  ·
    refine ⟨131378887864767010164294041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87585925243178006776196027 131378887864767010164294041)
    ·
      refine ⟨98534165898575257623220531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 131378887864767010164294041 98534165898575257623220531)
      ·
        refine ⟨147801248847862886434830797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98534165898575257623220531 147801248847862886434830797)
        ·
          refine ⟨55425468317948582413061549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 147801248847862886434830797 55425468317948582413061549)
          ·
            refine ⟨20784550619230718404898081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55425468317948582413061549 20784550619230718404898081)
            ·
              refine ⟨15588412964423038803673561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20784550619230718404898081 15588412964423038803673561)
              ·
                refine ⟨11691309723317279102755171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15588412964423038803673561 11691309723317279102755171)
                ·
                  refine ⟨17536964584975918654132757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11691309723317279102755171 17536964584975918654132757)
                  ·
                    refine ⟨822045214920746186912473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17536964584975918654132757 822045214920746186912473)
                    ·
                      rfl

theorem cell22_2401391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 2, 2, 1, 6].length) (baseStart_2401391 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2401391 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2401391 prefixEnd_2401391 := by exact prefixLift 2401391
  have htrace : WordTrace (prefixWord ++ tailWord_2401391) baseStart_2401391 baseEnd_2401391 := by
    simpa [prefixWord, tailWord_2401391, baseEnd_2401391] using wordTrace_append hprefix tailTrace_2401391
  have hstable : (prefixWord ++ tailWord_2401391).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2401391).length < 2 ^ (prefixWord ++ tailWord_2401391).sum := by decide
  have hdescent : baseEnd_2401391 < baseStart_2401391 := by decide
  rcases family_descends (prefixWord ++ tailWord_2401391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2401408 : List Nat := [2, 1, 1, 2, 1, 3, 5, 1, 2, 4]
def baseStart_2401408 : Nat := 118140960795 + 2401408 * 2 ^ 59
def prefixEnd_2401408 : Nat := 4983230072969 + 3 ^ 40 * 2401408 * 2
def baseEnd_2401408 : Nat := 822051034368163809237421

theorem tailTrace_2401408 : CollatzResearch.WordTrace tailWord_2401408 prefixEnd_2401408 822051034368163809237421 := by
  unfold tailWord_2401408
  simp only [CollatzResearch.WordTrace]
  refine ⟨43793272642058209339782439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58391030189410945786376585 43793272642058209339782439)
  ·
    refine ⟨65689908963087314009673659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43793272642058209339782439 65689908963087314009673659)
    ·
      refine ⟨98534863444630971014510489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65689908963087314009673659 98534863444630971014510489)
      ·
        refine ⟨73901147583473228260882867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 98534863444630971014510489 73901147583473228260882867)
        ·
          refine ⟨110851721375209842391324301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73901147583473228260882867 110851721375209842391324301)
          ·
            refine ⟨41569395515703690896746613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 110851721375209842391324301 41569395515703690896746613)
            ·
              refine ⟨3897130829597221021569995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 41569395515703690896746613 3897130829597221021569995)
              ·
                refine ⟨5845696244395831532354993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3897130829597221021569995 5845696244395831532354993)
                ·
                  refine ⟨4384272183296873649266245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5845696244395831532354993 4384272183296873649266245)
                  ·
                    refine ⟨822051034368163809237421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4384272183296873649266245 822051034368163809237421)
                    ·
                      rfl

theorem cell22_2401408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 5, 1, 2, 4].length) (baseStart_2401408 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2401408 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2401408 prefixEnd_2401408 := by exact prefixLift 2401408
  have htrace : WordTrace (prefixWord ++ tailWord_2401408) baseStart_2401408 baseEnd_2401408 := by
    simpa [prefixWord, tailWord_2401408, baseEnd_2401408] using wordTrace_append hprefix tailTrace_2401408
  have hstable : (prefixWord ++ tailWord_2401408).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2401408).length < 2 ^ (prefixWord ++ tailWord_2401408).sum := by decide
  have hdescent : baseEnd_2401408 < baseStart_2401408 := by decide
  rcases family_descends (prefixWord ++ tailWord_2401408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2401468 : List Nat := [2, 2, 2, 3, 2, 1, 1, 2, 7]
def baseStart_2401468 : Nat := 118140960795 + 2401468 * 2 ^ 59
def prefixEnd_2401468 : Nat := 4983230072969 + 3 ^ 40 * 2401468 * 2
def baseEnd_2401468 : Nat := 274023857864781217579079

theorem tailTrace_2401468 : CollatzResearch.WordTrace tailWord_2401468 prefixEnd_2401468 274023857864781217579079 := by
  unfold tailWord_2401468
  simp only [CollatzResearch.WordTrace]
  refine ⟨43794366831949524463374529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58392489109266032617832705 43794366831949524463374529)
  ·
    refine ⟨32845775123962143347530897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43794366831949524463374529 32845775123962143347530897)
    ·
      refine ⟨24634331342971607510648173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32845775123962143347530897 24634331342971607510648173)
      ·
        refine ⟨9237874253614352816493065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24634331342971607510648173 9237874253614352816493065)
        ·
          refine ⟨6928405690210764612369799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9237874253614352816493065 6928405690210764612369799)
          ·
            refine ⟨10392608535316146918554699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6928405690210764612369799 10392608535316146918554699)
            ·
              refine ⟨15588912802974220377832049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10392608535316146918554699 15588912802974220377832049)
              ·
                refine ⟨11691684602230665283374037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15588912802974220377832049 11691684602230665283374037)
                ·
                  refine ⟨274023857864781217579079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11691684602230665283374037 274023857864781217579079)
                  ·
                    rfl

theorem cell22_2401468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 1, 2, 7].length) (baseStart_2401468 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2401468 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2401468 prefixEnd_2401468 := by exact prefixLift 2401468
  have htrace : WordTrace (prefixWord ++ tailWord_2401468) baseStart_2401468 baseEnd_2401468 := by
    simpa [prefixWord, tailWord_2401468, baseEnd_2401468] using wordTrace_append hprefix tailTrace_2401468
  have hstable : (prefixWord ++ tailWord_2401468).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2401468).length < 2 ^ (prefixWord ++ tailWord_2401468).sum := by decide
  have hdescent : baseEnd_2401468 < baseStart_2401468 := by decide
  rcases family_descends (prefixWord ++ tailWord_2401468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2401474 : List Nat := [3, 5, 1, 1, 3, 1, 8]
def baseStart_2401474 : Nat := 118140960795 + 2401474 * 2 ^ 59
def prefixEnd_2401474 : Nat := 4983230072969 + 3 ^ 40 * 2401474 * 2
def baseEnd_2401474 : Nat := 30447171389517097669897

theorem tailTrace_2401474 : CollatzResearch.WordTrace tailWord_2401474 prefixEnd_2401474 30447171389517097669897 := by
  unfold tailWord_2401474
  simp only [CollatzResearch.WordTrace]
  refine ⟨21897238125469327987866869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58392635001251541300978317 21897238125469327987866869)
  ·
    refine ⟨2052866074262749498862519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 21897238125469327987866869 2052866074262749498862519)
    ·
      refine ⟨3079299111394124248293779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2052866074262749498862519 3079299111394124248293779)
      ·
        refine ⟨4618948667091186372440669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3079299111394124248293779 4618948667091186372440669)
        ·
          refine ⟨1732105750159194889665251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4618948667091186372440669 1732105750159194889665251)
          ·
            refine ⟨2598158625238792334497877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1732105750159194889665251 2598158625238792334497877)
            ·
              refine ⟨30447171389517097669897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2598158625238792334497877 30447171389517097669897)
              ·
                rfl

theorem cell22_2401474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 3, 1, 8].length) (baseStart_2401474 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2401474 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2401474 prefixEnd_2401474 := by exact prefixLift 2401474
  have htrace : WordTrace (prefixWord ++ tailWord_2401474) baseStart_2401474 baseEnd_2401474 := by
    simpa [prefixWord, tailWord_2401474, baseEnd_2401474] using wordTrace_append hprefix tailTrace_2401474
  have hstable : (prefixWord ++ tailWord_2401474).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2401474).length < 2 ^ (prefixWord ++ tailWord_2401474).sum := by decide
  have hdescent : baseEnd_2401474 < baseStart_2401474 := by decide
  rcases family_descends (prefixWord ++ tailWord_2401474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2401481 : List Nat := [1, 2, 1, 1, 2, 1, 1, 2, 1, 10]
def baseStart_2401481 : Nat := 118140960795 + 2401481 * 2 ^ 59
def prefixEnd_2401481 : Nat := 4983230072969 + 3 ^ 40 * 2401481 * 2
def baseEnd_2401481 : Nat := 822076023760015952162197

theorem tailTrace_2401481 : CollatzResearch.WordTrace tailWord_2401481 prefixEnd_2401481 822076023760015952162197 := by
  unfold tailWord_2401481
  simp only [CollatzResearch.WordTrace]
  refine ⟨87589207812851952146972297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58392805208567968097981531 87589207812851952146972297)
  ·
    refine ⟨65691905859638964110229223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87589207812851952146972297 65691905859638964110229223)
    ·
      refine ⟨98537858789458446165343835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65691905859638964110229223 98537858789458446165343835)
      ·
        refine ⟨147806788184187669248015753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98537858789458446165343835 147806788184187669248015753)
        ·
          refine ⟨110855091138140751936011815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 147806788184187669248015753 110855091138140751936011815)
          ·
            refine ⟨166282636707211127904017723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 110855091138140751936011815 166282636707211127904017723)
            ·
              refine ⟨249423955060816691856026585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 166282636707211127904017723 249423955060816691856026585)
              ·
                refine ⟨187067966295612518892019939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 249423955060816691856026585 187067966295612518892019939)
                ·
                  refine ⟨280601949443418778338029909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 187067966295612518892019939 280601949443418778338029909)
                  ·
                    refine ⟨822076023760015952162197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 280601949443418778338029909 822076023760015952162197)
                    ·
                      rfl

theorem cell22_2401481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 2, 1, 10].length) (baseStart_2401481 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2401481 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2401481 prefixEnd_2401481 := by exact prefixLift 2401481
  have htrace : WordTrace (prefixWord ++ tailWord_2401481) baseStart_2401481 baseEnd_2401481 := by
    simpa [prefixWord, tailWord_2401481, baseEnd_2401481] using wordTrace_append hprefix tailTrace_2401481
  have hstable : (prefixWord ++ tailWord_2401481).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2401481).length < 2 ^ (prefixWord ++ tailWord_2401481).sum := by decide
  have hdescent : baseEnd_2401481 < baseStart_2401481 := by decide
  rcases family_descends (prefixWord ++ tailWord_2401481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2401498 : List Nat := [3, 1, 1, 2, 2, 1, 1, 4, 3, 4]
def baseStart_2401498 : Nat := 118140960795 + 2401498 * 2 ^ 59
def prefixEnd_2401498 : Nat := 4983230072969 + 3 ^ 40 * 2401498 * 2
def baseEnd_2401498 : Nat := 822081843207433574487145

theorem tailTrace_2401498 : CollatzResearch.WordTrace tailWord_2401498 prefixEnd_2401498 822081843207433574487145 := by
  unfold tailWord_2401498
  simp only [CollatzResearch.WordTrace]
  refine ⟨21897456963447591012585287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58393218569193576033560765 21897456963447591012585287)
  ·
    refine ⟨32846185445171386518877931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21897456963447591012585287 32846185445171386518877931)
    ·
      refine ⟨49269278167757079778316897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32846185445171386518877931 49269278167757079778316897)
      ·
        refine ⟨36951958625817809833737673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49269278167757079778316897 36951958625817809833737673)
        ·
          refine ⟨27713968969363357375303255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36951958625817809833737673 27713968969363357375303255)
          ·
            refine ⟨41570953454045036062954883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27713968969363357375303255 41570953454045036062954883)
            ·
              refine ⟨62356430181067554094432325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41570953454045036062954883 62356430181067554094432325)
              ·
                refine ⟨11691830658950166392706061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 62356430181067554094432325 11691830658950166392706061)
                ·
                  refine ⟨4384436497106312397264773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11691830658950166392706061 4384436497106312397264773)
                  ·
                    refine ⟨822081843207433574487145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4384436497106312397264773 822081843207433574487145)
                    ·
                      rfl

theorem cell22_2401498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 4, 3, 4].length) (baseStart_2401498 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2401498 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2401498 prefixEnd_2401498 := by exact prefixLift 2401498
  have htrace : WordTrace (prefixWord ++ tailWord_2401498) baseStart_2401498 baseEnd_2401498 := by
    simpa [prefixWord, tailWord_2401498, baseEnd_2401498] using wordTrace_append hprefix tailTrace_2401498
  have hstable : (prefixWord ++ tailWord_2401498).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2401498).length < 2 ^ (prefixWord ++ tailWord_2401498).sum := by decide
  have hdescent : baseEnd_2401498 < baseStart_2401498 := by decide
  rcases family_descends (prefixWord ++ tailWord_2401498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2401515 : List Nat := [1, 1, 1, 1, 2, 6, 3, 2, 1, 4]
def baseStart_2401515 : Nat := 118140960795 + 2401515 * 2 ^ 59
def prefixEnd_2401515 : Nat := 4983230072969 + 3 ^ 40 * 2401515 * 2
def baseEnd_2401515 : Nat := 822087662654851196812093

theorem tailTrace_2401515 : CollatzResearch.WordTrace tailWord_2401515 prefixEnd_2401515 822087662654851196812093 := by
  unfold tailWord_2401515
  simp only [CollatzResearch.WordTrace]
  refine ⟨87590447894728775953709999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58393631929819183969139999 87590447894728775953709999)
  ·
    refine ⟨131385671842093163930564999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87590447894728775953709999 131385671842093163930564999)
    ·
      refine ⟨197078507763139745895847499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131385671842093163930564999 197078507763139745895847499)
      ·
        refine ⟨295617761644709618843771249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 197078507763139745895847499 295617761644709618843771249)
        ·
          refine ⟨221713321233532214132828437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 295617761644709618843771249 221713321233532214132828437)
          ·
            refine ⟨10392811932821822537476333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 221713321233532214132828437 10392811932821822537476333)
            ·
              refine ⟨3897304474808183451553625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10392811932821822537476333 3897304474808183451553625)
              ·
                refine ⟨2922978356106137588665219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3897304474808183451553625 2922978356106137588665219)
                ·
                  refine ⟨4384467534159206382997829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2922978356106137588665219 4384467534159206382997829)
                  ·
                    refine ⟨822087662654851196812093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4384467534159206382997829 822087662654851196812093)
                    ·
                      rfl

theorem cell22_2401515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 3, 2, 1, 4].length) (baseStart_2401515 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2401515 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2401515 prefixEnd_2401515 := by exact prefixLift 2401515
  have htrace : WordTrace (prefixWord ++ tailWord_2401515) baseStart_2401515 baseEnd_2401515 := by
    simpa [prefixWord, tailWord_2401515, baseEnd_2401515] using wordTrace_append hprefix tailTrace_2401515
  have hstable : (prefixWord ++ tailWord_2401515).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2401515).length < 2 ^ (prefixWord ++ tailWord_2401515).sum := by decide
  have hdescent : baseEnd_2401515 < baseStart_2401515 := by decide
  rcases family_descends (prefixWord ++ tailWord_2401515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2401530 : List Nat := [3, 1, 1, 1, 1, 4, 2, 5, 4]
def baseStart_2401530 : Nat := 118140960795 + 2401530 * 2 ^ 59
def prefixEnd_2401530 : Nat := 4983230072969 + 3 ^ 40 * 2401530 * 2
def baseEnd_2401530 : Nat := 274030932487132052562349

theorem tailTrace_2401530 : CollatzResearch.WordTrace tailWord_2401530 prefixEnd_2401530 274030932487132052562349 := by
  unfold tailWord_2401530
  simp only [CollatzResearch.WordTrace]
  refine ⟨21897748747418608378876511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58393996659782955677004029 21897748747418608378876511)
  ·
    refine ⟨32846623121127912568314767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21897748747418608378876511 32846623121127912568314767)
    ·
      refine ⟨49269934681691868852472151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32846623121127912568314767 49269934681691868852472151)
      ·
        refine ⟨73904902022537803278708227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49269934681691868852472151 73904902022537803278708227)
        ·
          refine ⟨110857353033806704918062341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73904902022537803278708227 110857353033806704918062341)
          ·
            refine ⟨20785753693838757172136689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 110857353033806704918062341 20785753693838757172136689)
            ·
              refine ⟨15589315270379067879102517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20785753693838757172136689 15589315270379067879102517)
              ·
                refine ⟨1461498306598037613665861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15589315270379067879102517 1461498306598037613665861)
                ·
                  refine ⟨274030932487132052562349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1461498306598037613665861 274030932487132052562349)
                  ·
                    rfl

theorem cell22_2401530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 2, 5, 4].length) (baseStart_2401530 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2401530 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2401530 prefixEnd_2401530 := by exact prefixLift 2401530
  have htrace : WordTrace (prefixWord ++ tailWord_2401530) baseStart_2401530 baseEnd_2401530 := by
    simpa [prefixWord, tailWord_2401530, baseEnd_2401530] using wordTrace_append hprefix tailTrace_2401530
  have hstable : (prefixWord ++ tailWord_2401530).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2401530).length < 2 ^ (prefixWord ++ tailWord_2401530).sum := by decide
  have hdescent : baseEnd_2401530 < baseStart_2401530 := by decide
  rcases family_descends (prefixWord ++ tailWord_2401530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2401547 : List Nat := [1, 1, 1, 1, 5, 3, 4, 2, 4]
def baseStart_2401547 : Nat := 118140960795 + 2401547 * 2 ^ 59
def prefixEnd_2401547 : Nat := 4983230072969 + 3 ^ 40 * 2401547 * 2
def baseEnd_2401547 : Nat := 274032872302937926670665

theorem tailTrace_2401547 : CollatzResearch.WordTrace tailWord_2401547 prefixEnd_2401547 274032872302937926670665 := by
  unfold tailWord_2401547
  simp only [CollatzResearch.WordTrace]
  refine ⟨87591615030612845418874895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58394410020408563612583263 87591615030612845418874895)
  ·
    refine ⟨131387422545919268128312343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87591615030612845418874895 131387422545919268128312343)
    ·
      refine ⟨197081133818878902192468515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131387422545919268128312343 197081133818878902192468515)
      ·
        refine ⟨295621700728318353288702773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 197081133818878902192468515 295621700728318353288702773)
        ·
          refine ⟨27714534443279845620815885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 295621700728318353288702773 27714534443279845620815885)
          ·
            refine ⟨10392950416229942107805957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27714534443279845620815885 10392950416229942107805957)
            ·
              refine ⟨1948678203043114145213617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10392950416229942107805957 1948678203043114145213617)
              ·
                refine ⟨1461508652282335608910213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1948678203043114145213617 1461508652282335608910213)
                ·
                  refine ⟨274032872302937926670665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1461508652282335608910213 274032872302937926670665)
                  ·
                    rfl

theorem cell22_2401547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 4, 2, 4].length) (baseStart_2401547 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2401547 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2401547 prefixEnd_2401547 := by exact prefixLift 2401547
  have htrace : WordTrace (prefixWord ++ tailWord_2401547) baseStart_2401547 baseEnd_2401547 := by
    simpa [prefixWord, tailWord_2401547, baseEnd_2401547] using wordTrace_append hprefix tailTrace_2401547
  have hstable : (prefixWord ++ tailWord_2401547).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2401547).length < 2 ^ (prefixWord ++ tailWord_2401547).sum := by decide
  have hdescent : baseEnd_2401547 < baseStart_2401547 := by decide
  rcases family_descends (prefixWord ++ tailWord_2401547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2401562 : List Nat := [3, 1, 1, 3, 3, 1, 2, 3, 2, 3]
def baseStart_2401562 : Nat := 118140960795 + 2401562 * 2 ^ 59
def prefixEnd_2401562 : Nat := 4983230072969 + 3 ^ 40 * 2401562 * 2
def baseEnd_2401562 : Nat := 822103751715358740886949

theorem tailTrace_2401562 : CollatzResearch.WordTrace tailWord_2401562 prefixEnd_2401562 822103751715358740886949 := by
  unfold tailWord_2401562
  simp only [CollatzResearch.WordTrace]
  refine ⟨21898040531389625745167735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58394774750372335320447293 21898040531389625745167735)
  ·
    refine ⟨32847060797084438617751603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21898040531389625745167735 32847060797084438617751603)
    ·
      refine ⟨49270591195626657926627405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32847060797084438617751603 49270591195626657926627405)
      ·
        refine ⟨18476471698359996722485277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49270591195626657926627405 18476471698359996722485277)
        ·
          refine ⟨6928676886884998770931979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18476471698359996722485277 6928676886884998770931979)
          ·
            refine ⟨10393015330327498156397969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6928676886884998770931979 10393015330327498156397969)
            ·
              refine ⟨7794761497745623617298477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10393015330327498156397969 7794761497745623617298477)
              ·
                refine ⟨2923035561654608856486929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7794761497745623617298477 2923035561654608856486929)
                ·
                  refine ⟨2192276671240956642365197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2923035561654608856486929 2192276671240956642365197)
                  ·
                    refine ⟨822103751715358740886949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2192276671240956642365197 822103751715358740886949)
                    ·
                      rfl

theorem cell22_2401562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 2, 3, 2, 3].length) (baseStart_2401562 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2401562 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2401562 prefixEnd_2401562 := by exact prefixLift 2401562
  have htrace : WordTrace (prefixWord ++ tailWord_2401562) baseStart_2401562 baseEnd_2401562 := by
    simpa [prefixWord, tailWord_2401562, baseEnd_2401562] using wordTrace_append hprefix tailTrace_2401562
  have hstable : (prefixWord ++ tailWord_2401562).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2401562).length < 2 ^ (prefixWord ++ tailWord_2401562).sum := by decide
  have hdescent : baseEnd_2401562 < baseStart_2401562 := by decide
  rcases family_descends (prefixWord ++ tailWord_2401562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2401607 : List Nat := [1, 1, 4, 1, 2, 4, 2, 1, 3, 3]
def baseStart_2401607 : Nat := 118140960795 + 2401607 * 2 ^ 59
def prefixEnd_2401607 : Nat := 4983230072969 + 3 ^ 40 * 2401607 * 2
def baseEnd_2401607 : Nat := 822119156134993623511811

theorem tailTrace_2401607 : CollatzResearch.WordTrace tailWord_2401607 prefixEnd_2401607 822119156134993623511811 := by
  unfold tailWord_2401607
  simp only [CollatzResearch.WordTrace]
  refine ⟨87593803410395475666059075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58395868940263650444039383 87593803410395475666059075)
  ·
    refine ⟨131390705115593213499088613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87593803410395475666059075 131390705115593213499088613)
    ·
      refine ⟨24635757209173727531079115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 131390705115593213499088613 24635757209173727531079115)
      ·
        refine ⟨36953635813760591296618673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24635757209173727531079115 36953635813760591296618673)
        ·
          refine ⟨27715226860320443472464005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36953635813760591296618673 27715226860320443472464005)
          ·
            refine ⟨5196605036310083151087001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27715226860320443472464005 5196605036310083151087001)
            ·
              refine ⟨3897453777232562363315251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5196605036310083151087001 3897453777232562363315251)
              ·
                refine ⟨5846180665848843544972877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3897453777232562363315251 5846180665848843544972877)
                ·
                  refine ⟨2192317749693316329364829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5846180665848843544972877 2192317749693316329364829)
                  ·
                    refine ⟨822119156134993623511811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2192317749693316329364829 822119156134993623511811)
                    ·
                      rfl

theorem cell22_2401607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 2, 1, 3, 3].length) (baseStart_2401607 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2401607 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2401607 prefixEnd_2401607 := by exact prefixLift 2401607
  have htrace : WordTrace (prefixWord ++ tailWord_2401607) baseStart_2401607 baseEnd_2401607 := by
    simpa [prefixWord, tailWord_2401607, baseEnd_2401607] using wordTrace_append hprefix tailTrace_2401607
  have hstable : (prefixWord ++ tailWord_2401607).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2401607).length < 2 ^ (prefixWord ++ tailWord_2401607).sum := by decide
  have hdescent : baseEnd_2401607 < baseStart_2401607 := by decide
  rcases family_descends (prefixWord ++ tailWord_2401607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2401613 : List Nat := [1, 6, 1, 3, 1, 1, 3, 1, 2, 3]
def baseStart_2401613 : Nat := 118140960795 + 2401613 * 2 ^ 59
def prefixEnd_2401613 : Nat := 4983230072969 + 3 ^ 40 * 2401613 * 2
def baseEnd_2401613 : Nat := 822121210057611607861793

theorem tailTrace_2401613 : CollatzResearch.WordTrace tailWord_2401613 prefixEnd_2401613 822121210057611607861793 := by
  unfold tailWord_2401613
  simp only [CollatzResearch.WordTrace]
  refine ⟨87594022248373738690777493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58396014832249159127184995 87594022248373738690777493)
  ·
    refine ⟨4105969792892519001130195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 87594022248373738690777493 4105969792892519001130195)
    ·
      refine ⟨6158954689338778501695293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4105969792892519001130195 6158954689338778501695293)
      ·
        refine ⟨2309608008502041938135735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6158954689338778501695293 2309608008502041938135735)
        ·
          refine ⟨3464412012753062907203603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2309608008502041938135735 3464412012753062907203603)
          ·
            refine ⟨5196618019129594360805405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3464412012753062907203603 5196618019129594360805405)
            ·
              refine ⟨1948731757173597885302027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5196618019129594360805405 1948731757173597885302027)
              ·
                refine ⟨2923097635760396827953041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1948731757173597885302027 2923097635760396827953041)
                ·
                  refine ⟨2192323226820297620964781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2923097635760396827953041 2192323226820297620964781)
                  ·
                    refine ⟨822121210057611607861793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2192323226820297620964781 822121210057611607861793)
                    ·
                      rfl

theorem cell22_2401613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 3, 1, 2, 3].length) (baseStart_2401613 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2401613 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2401613 prefixEnd_2401613 := by exact prefixLift 2401613
  have htrace : WordTrace (prefixWord ++ tailWord_2401613) baseStart_2401613 baseEnd_2401613 := by
    simpa [prefixWord, tailWord_2401613, baseEnd_2401613] using wordTrace_append hprefix tailTrace_2401613
  have hstable : (prefixWord ++ tailWord_2401613).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2401613).length < 2 ^ (prefixWord ++ tailWord_2401613).sum := by decide
  have hdescent : baseEnd_2401613 < baseStart_2401613 := by decide
  rcases family_descends (prefixWord ++ tailWord_2401613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2401633 : List Nat := [1, 2, 3, 1, 1, 1, 1, 2, 2, 8]
def baseStart_2401633 : Nat := 118140960795 + 2401633 * 2 ^ 59
def prefixEnd_2401633 : Nat := 4983230072969 + 3 ^ 40 * 2401633 * 2
def baseEnd_2401633 : Nat := 822128056466338222361731

theorem tailTrace_2401633 : CollatzResearch.WordTrace tailWord_2401633 prefixEnd_2401633 822128056466338222361731 := by
  unfold tailWord_2401633
  simp only [CollatzResearch.WordTrace]
  refine ⟨87594751708301282106505553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58396501138867521404337035 87594751708301282106505553)
  ·
    refine ⟨65696063781225961579879165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87594751708301282106505553 65696063781225961579879165)
    ·
      refine ⟨24636023917959735592454687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65696063781225961579879165 24636023917959735592454687)
      ·
        refine ⟨36954035876939603388682031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24636023917959735592454687 36954035876939603388682031)
        ·
          refine ⟨55431053815409405083023047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36954035876939603388682031 55431053815409405083023047)
          ·
            refine ⟨83146580723114107624534571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55431053815409405083023047 83146580723114107624534571)
            ·
              refine ⟨124719871084671161436801857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83146580723114107624534571 124719871084671161436801857)
              ·
                refine ⟨93539903313503371077601393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 124719871084671161436801857 93539903313503371077601393)
                ·
                  refine ⟨70154927485127528308201045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 93539903313503371077601393 70154927485127528308201045)
                  ·
                    refine ⟨822128056466338222361731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 70154927485127528308201045 822128056466338222361731)
                    ·
                      rfl

theorem cell22_2401633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 2, 2, 8].length) (baseStart_2401633 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2401633 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2401633 prefixEnd_2401633 := by exact prefixLift 2401633
  have htrace : WordTrace (prefixWord ++ tailWord_2401633) baseStart_2401633 baseEnd_2401633 := by
    simpa [prefixWord, tailWord_2401633, baseEnd_2401633] using wordTrace_append hprefix tailTrace_2401633
  have hstable : (prefixWord ++ tailWord_2401633).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2401633).length < 2 ^ (prefixWord ++ tailWord_2401633).sum := by decide
  have hdescent : baseEnd_2401633 < baseStart_2401633 := by decide
  rcases family_descends (prefixWord ++ tailWord_2401633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2401663 : List Nat := [1, 1, 2, 2, 1, 1, 2, 1, 2, 9]
def baseStart_2401663 : Nat := 118140960795 + 2401663 * 2 ^ 59
def prefixEnd_2401663 : Nat := 4983230072969 + 3 ^ 40 * 2401663 * 2
def baseEnd_2401663 : Nat := 822138326079428144111639

theorem tailTrace_2401663 : CollatzResearch.WordTrace tailWord_2401663 prefixEnd_2401663 822138326079428144111639 := by
  unfold tailWord_2401663
  simp only [CollatzResearch.WordTrace]
  refine ⟨87595845898192597230097643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58397230598795064820065095 87595845898192597230097643)
  ·
    refine ⟨131393768847288895845146465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87595845898192597230097643 131393768847288895845146465)
    ·
      refine ⟨98545326635466671883859849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 131393768847288895845146465 98545326635466671883859849)
      ·
        refine ⟨73908994976600003912894887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 98545326635466671883859849 73908994976600003912894887)
        ·
          refine ⟨110863492464900005869342331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73908994976600003912894887 110863492464900005869342331)
          ·
            refine ⟨166295238697350008804013497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 110863492464900005869342331 166295238697350008804013497)
            ·
              refine ⟨124721429023012506603010123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 166295238697350008804013497 124721429023012506603010123)
              ·
                refine ⟨187082143534518759904515185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 124721429023012506603010123 187082143534518759904515185)
                ·
                  refine ⟨140311607650889069928386389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 187082143534518759904515185 140311607650889069928386389)
                  ·
                    refine ⟨822138326079428144111639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 140311607650889069928386389 822138326079428144111639)
                    ·
                      rfl

theorem cell22_2401663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 1, 2, 9].length) (baseStart_2401663 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2401663 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2401663 prefixEnd_2401663 := by exact prefixLift 2401663
  have htrace : WordTrace (prefixWord ++ tailWord_2401663) baseStart_2401663 baseEnd_2401663 := by
    simpa [prefixWord, tailWord_2401663, baseEnd_2401663] using wordTrace_append hprefix tailTrace_2401663
  have hstable : (prefixWord ++ tailWord_2401663).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2401663).length < 2 ^ (prefixWord ++ tailWord_2401663).sum := by decide
  have hdescent : baseEnd_2401663 < baseStart_2401663 := by decide
  rcases family_descends (prefixWord ++ tailWord_2401663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2401684 : List Nat := [2, 4, 2, 1, 2, 1, 3, 2, 1, 4]
def baseStart_2401684 : Nat := 118140960795 + 2401684 * 2 ^ 59
def prefixEnd_2401684 : Nat := 4983230072969 + 3 ^ 40 * 2401684 * 2
def baseEnd_2401684 : Nat := 822145514808591089336575

theorem tailTrace_2401684 : CollatzResearch.WordTrace tailWord_2401684 prefixEnd_2401684 822145514808591089336575 := by
  unfold tailWord_2401684
  simp only [CollatzResearch.WordTrace]
  refine ⟨43798305915558258908306053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58397741220744345211074737 43798305915558258908306053)
  ·
    refine ⟨8212182359167173545307385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 43798305915558258908306053 8212182359167173545307385)
    ·
      refine ⟨6159136769375380158980539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8212182359167173545307385 6159136769375380158980539)
      ·
        refine ⟨9238705154063070238470809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6159136769375380158980539 9238705154063070238470809)
        ·
          refine ⟨6929028865547302678853107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9238705154063070238470809 6929028865547302678853107)
          ·
            refine ⟨10393543298320954018279661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6929028865547302678853107 10393543298320954018279661)
            ·
              refine ⟨3897578736870357756854873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10393543298320954018279661 3897578736870357756854873)
              ·
                refine ⟨2923184052652768317641155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3897578736870357756854873 2923184052652768317641155)
                ·
                  refine ⟨4384776078979152476461733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2923184052652768317641155 4384776078979152476461733)
                  ·
                    refine ⟨822145514808591089336575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4384776078979152476461733 822145514808591089336575)
                    ·
                      rfl

theorem cell22_2401684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 3, 2, 1, 4].length) (baseStart_2401684 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2401684 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2401684 prefixEnd_2401684 := by exact prefixLift 2401684
  have htrace : WordTrace (prefixWord ++ tailWord_2401684) baseStart_2401684 baseEnd_2401684 := by
    simpa [prefixWord, tailWord_2401684, baseEnd_2401684] using wordTrace_append hprefix tailTrace_2401684
  have hstable : (prefixWord ++ tailWord_2401684).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2401684).length < 2 ^ (prefixWord ++ tailWord_2401684).sum := by decide
  have hdescent : baseEnd_2401684 < baseStart_2401684 := by decide
  rcases family_descends (prefixWord ++ tailWord_2401684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2401742 : List Nat := [4, 1, 1, 1, 2, 1, 3, 1, 5, 3]
def baseStart_2401742 : Nat := 118140960795 + 2401742 * 2 ^ 59
def prefixEnd_2401742 : Nat := 4983230072969 + 3 ^ 40 * 2401742 * 2
def baseEnd_2401742 : Nat := 822165369393898271386397

theorem tailTrace_2401742 : CollatzResearch.WordTrace tailWord_2401742 prefixEnd_2401742 822165369393898271386397 := by
  unfold tailWord_2401742
  simp only [CollatzResearch.WordTrace]
  refine ⟨10949840908113299215277935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 58399151509937595814815653 10949840908113299215277935)
  ·
    refine ⟨16424761362169948822916903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10949840908113299215277935 16424761362169948822916903)
    ·
      refine ⟨24637142043254923234375355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16424761362169948822916903 24637142043254923234375355)
      ·
        refine ⟨36955713064882384851563033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24637142043254923234375355 36955713064882384851563033)
        ·
          refine ⟨27716784798661788638672275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36955713064882384851563033 27716784798661788638672275)
          ·
            refine ⟨41575177197992682958008413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27716784798661788638672275 41575177197992682958008413)
            ·
              refine ⟨15590691449247256109253155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41575177197992682958008413 15590691449247256109253155)
              ·
                refine ⟨23386037173870884163879733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15590691449247256109253155 23386037173870884163879733)
                ·
                  refine ⟨2192440985050395390363725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 23386037173870884163879733 2192440985050395390363725)
                  ·
                    refine ⟨822165369393898271386397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2192440985050395390363725 822165369393898271386397)
                    ·
                      rfl

theorem cell22_2401742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 3, 1, 5, 3].length) (baseStart_2401742 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2401742 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2401742 prefixEnd_2401742 := by exact prefixLift 2401742
  have htrace : WordTrace (prefixWord ++ tailWord_2401742) baseStart_2401742 baseEnd_2401742 := by
    simpa [prefixWord, tailWord_2401742, baseEnd_2401742] using wordTrace_append hprefix tailTrace_2401742
  have hstable : (prefixWord ++ tailWord_2401742).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2401742).length < 2 ^ (prefixWord ++ tailWord_2401742).sum := by decide
  have hdescent : baseEnd_2401742 < baseStart_2401742 := by decide
  rcases family_descends (prefixWord ++ tailWord_2401742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2401789 : List Nat := [1, 4, 1, 1, 1, 5, 3, 1, 5]
def baseStart_2401789 : Nat := 118140960795 + 2401789 * 2 ^ 59
def prefixEnd_2401789 : Nat := 4983230072969 + 3 ^ 40 * 2401789 * 2
def baseEnd_2401789 : Nat := 274060486151468605153751

theorem tailTrace_2401789 : CollatzResearch.WordTrace tailWord_2401789 prefixEnd_2401789 274060486151468605153751 := by
  unfold tailWord_2401789
  simp only [CollatzResearch.WordTrace]
  refine ⟨87600441495736120749184421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58400294330490747166122947 87600441495736120749184421)
  ·
    refine ⟨16425082780450522640472079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 87600441495736120749184421 16425082780450522640472079)
    ·
      refine ⟨24637624170675783960708119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16425082780450522640472079 24637624170675783960708119)
      ·
        refine ⟨36956436256013675941062179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24637624170675783960708119 36956436256013675941062179)
        ·
          refine ⟨55434654384020513911593269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36956436256013675941062179 55434654384020513911593269)
          ·
            refine ⟨5196998848501923179211869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 55434654384020513911593269 5196998848501923179211869)
            ·
              refine ⟨1948874568188221192204451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5196998848501923179211869 1948874568188221192204451)
              ·
                refine ⟨2923311852282331788306677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1948874568188221192204451 2923311852282331788306677)
                ·
                  refine ⟨274060486151468605153751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2923311852282331788306677 274060486151468605153751)
                  ·
                    rfl

theorem cell22_2401789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 3, 1, 5].length) (baseStart_2401789 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2401789 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2401789 prefixEnd_2401789 := by exact prefixLift 2401789
  have htrace : WordTrace (prefixWord ++ tailWord_2401789) baseStart_2401789 baseEnd_2401789 := by
    simpa [prefixWord, tailWord_2401789, baseEnd_2401789] using wordTrace_append hprefix tailTrace_2401789
  have hstable : (prefixWord ++ tailWord_2401789).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2401789).length < 2 ^ (prefixWord ++ tailWord_2401789).sum := by decide
  have hdescent : baseEnd_2401789 < baseStart_2401789 := by decide
  rcases family_descends (prefixWord ++ tailWord_2401789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2401853 : List Nat := [1, 4, 1, 3, 4, 1, 1, 2, 1, 4]
def baseStart_2401853 : Nat := 118140960795 + 2401853 * 2 ^ 59
def prefixEnd_2401853 : Nat := 4983230072969 + 3 ^ 40 * 2401853 * 2
def baseEnd_2401853 : Nat := 822203366962330981861057

theorem tailTrace_2401853 : CollatzResearch.WordTrace tailWord_2401853 prefixEnd_2401853 822203366962330981861057 := by
  unfold tailWord_2401853
  simp only [CollatzResearch.WordTrace]
  refine ⟨87602775767504259679514213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58401850511669506453009475 87602775767504259679514213)
  ·
    refine ⟨16425520456407048689908915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 87602775767504259679514213 16425520456407048689908915)
    ·
      refine ⟨24638280684610573034863373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16425520456407048689908915 24638280684610573034863373)
      ·
        refine ⟨9239355256728964888073765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24638280684610573034863373 9239355256728964888073765)
        ·
          refine ⟨1732379110636680916513831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9239355256728964888073765 1732379110636680916513831)
          ·
            refine ⟨2598568665955021374770747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1732379110636680916513831 2598568665955021374770747)
            ·
              refine ⟨3897852998932532062156121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2598568665955021374770747 3897852998932532062156121)
              ·
                refine ⟨2923389749199399046617091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3897852998932532062156121 2923389749199399046617091)
                ·
                  refine ⟨4385084623799098569925637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2923389749199399046617091 4385084623799098569925637)
                  ·
                    refine ⟨822203366962330981861057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4385084623799098569925637 822203366962330981861057)
                    ·
                      rfl

theorem cell22_2401853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 4, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 4, 1, 1, 2, 1, 4].length) (baseStart_2401853 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2401853 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2401853 prefixEnd_2401853 := by exact prefixLift 2401853
  have htrace : WordTrace (prefixWord ++ tailWord_2401853) baseStart_2401853 baseEnd_2401853 := by
    simpa [prefixWord, tailWord_2401853, baseEnd_2401853] using wordTrace_append hprefix tailTrace_2401853
  have hstable : (prefixWord ++ tailWord_2401853).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2401853).length < 2 ^ (prefixWord ++ tailWord_2401853).sum := by decide
  have hdescent : baseEnd_2401853 < baseStart_2401853 := by decide
  rcases family_descends (prefixWord ++ tailWord_2401853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2401892 : List Nat := [2, 3, 1, 1, 2, 3, 1, 1, 2, 6]
def baseStart_2401892 : Nat := 118140960795 + 2401892 * 2 ^ 59
def prefixEnd_2401892 : Nat := 4983230072969 + 3 ^ 40 * 2401892 * 2
def baseEnd_2401892 : Nat := 822216717459347880135937

theorem tailTrace_2401892 : CollatzResearch.WordTrace tailWord_2401892 prefixEnd_2401892 822216717459347880135937 := by
  unfold tailWord_2401892
  simp only [CollatzResearch.WordTrace]
  refine ⟨43802099107181484670091965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58402798809575312893455953 43802099107181484670091965)
  ·
    refine ⟨16425787165193056751284487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43802099107181484670091965 16425787165193056751284487)
    ·
      refine ⟨24638680747789585126926731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16425787165193056751284487 24638680747789585126926731)
      ·
        refine ⟨36958021121684377690390097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24638680747789585126926731 36958021121684377690390097)
        ·
          refine ⟨27718515841263283267792573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36958021121684377690390097 27718515841263283267792573)
          ·
            refine ⟨10394443440473731225422215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27718515841263283267792573 10394443440473731225422215)
            ·
              refine ⟨15591665160710596838133323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10394443440473731225422215 15591665160710596838133323)
              ·
                refine ⟨23387497741065895257199985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15591665160710596838133323 23387497741065895257199985)
                ·
                  refine ⟨17540623305799421442899989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23387497741065895257199985 17540623305799421442899989)
                  ·
                    refine ⟨822216717459347880135937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17540623305799421442899989 822216717459347880135937)
                    ·
                      rfl

theorem cell22_2401892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 1, 1, 2, 6].length) (baseStart_2401892 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2401892 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2401892 prefixEnd_2401892 := by exact prefixLift 2401892
  have htrace : WordTrace (prefixWord ++ tailWord_2401892) baseStart_2401892 baseEnd_2401892 := by
    simpa [prefixWord, tailWord_2401892, baseEnd_2401892] using wordTrace_append hprefix tailTrace_2401892
  have hstable : (prefixWord ++ tailWord_2401892).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2401892).length < 2 ^ (prefixWord ++ tailWord_2401892).sum := by decide
  have hdescent : baseEnd_2401892 < baseStart_2401892 := by decide
  rcases family_descends (prefixWord ++ tailWord_2401892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2401937 : List Nat := [1, 2, 2, 1, 1, 1, 1, 4, 5, 4]
def baseStart_2401937 : Nat := 118140960795 + 2401937 * 2 ^ 59
def prefixEnd_2401937 : Nat := 4983230072969 + 3 ^ 40 * 2401937 * 2
def baseEnd_2401937 : Nat := 822232121878982762760799

theorem tailTrace_2401937 : CollatzResearch.WordTrace tailWord_2401937 prefixEnd_2401937 822232121878982762760799 := by
  unfold tailWord_2401937
  simp only [CollatzResearch.WordTrace]
  refine ⟨87605839499199942025572065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58403892999466628017048043 87605839499199942025572065)
  ·
    refine ⟨65704379624399956519179049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87605839499199942025572065 65704379624399956519179049)
    ·
      refine ⟨49278284718299967389384287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65704379624399956519179049 49278284718299967389384287)
      ·
        refine ⟨73917427077449951084076431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49278284718299967389384287 73917427077449951084076431)
        ·
          refine ⟨110876140616174926626114647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73917427077449951084076431 110876140616174926626114647)
          ·
            refine ⟨166314210924262389939171971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 110876140616174926626114647 166314210924262389939171971)
            ·
              refine ⟨249471316386393584908757957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 166314210924262389939171971 249471316386393584908757957)
              ·
                refine ⟨46775871822448797170392117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 249471316386393584908757957 46775871822448797170392117)
                ·
                  refine ⟨4385237983354574734724261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 46775871822448797170392117 4385237983354574734724261)
                  ·
                    refine ⟨822232121878982762760799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4385237983354574734724261 822232121878982762760799)
                    ·
                      rfl

theorem cell22_2401937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 4].length) (baseStart_2401937 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2401937 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2401937 prefixEnd_2401937 := by exact prefixLift 2401937
  have htrace : WordTrace (prefixWord ++ tailWord_2401937) baseStart_2401937 baseEnd_2401937 := by
    simpa [prefixWord, tailWord_2401937, baseEnd_2401937] using wordTrace_append hprefix tailTrace_2401937
  have hstable : (prefixWord ++ tailWord_2401937).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2401937).length < 2 ^ (prefixWord ++ tailWord_2401937).sum := by decide
  have hdescent : baseEnd_2401937 < baseStart_2401937 := by decide
  rcases family_descends (prefixWord ++ tailWord_2401937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2401984 : List Nat := [2, 1, 1, 2, 4, 1, 1, 1, 6, 3]
def baseStart_2401984 : Nat := 118140960795 + 2401984 * 2 ^ 59
def prefixEnd_2401984 : Nat := 4983230072969 + 3 ^ 40 * 2401984 * 2
def baseEnd_2401984 : Nat := 822248210939490306835655

theorem tailTrace_2401984 : CollatzResearch.WordTrace tailWord_2401984 prefixEnd_2401984 822248210939490306835655 := by
  unfold tailWord_2401984
  simp only [CollatzResearch.WordTrace]
  refine ⟨43803776865014834526266503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58405035820019779368355337 43803776865014834526266503)
  ·
    refine ⟨65705665297522251789399755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43803776865014834526266503 65705665297522251789399755)
    ·
      refine ⟨98558497946283377684099633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65705665297522251789399755 98558497946283377684099633)
      ·
        refine ⟨73918873459712533263074725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 98558497946283377684099633 73918873459712533263074725)
        ·
          refine ⟨13859788773696099986826511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 73918873459712533263074725 13859788773696099986826511)
          ·
            refine ⟨20789683160544149980239767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13859788773696099986826511 20789683160544149980239767)
            ·
              refine ⟨31184524740816224970359651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20789683160544149980239767 31184524740816224970359651)
              ·
                refine ⟨46776787111224337455539477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31184524740816224970359651 46776787111224337455539477)
                ·
                  refine ⟨2192661895838640818228413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 46776787111224337455539477 2192661895838640818228413)
                  ·
                    refine ⟨822248210939490306835655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2192661895838640818228413 822248210939490306835655)
                    ·
                      rfl

theorem cell22_2401984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 1, 6, 3].length) (baseStart_2401984 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2401984 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2401984 prefixEnd_2401984 := by exact prefixLift 2401984
  have htrace : WordTrace (prefixWord ++ tailWord_2401984) baseStart_2401984 baseEnd_2401984 := by
    simpa [prefixWord, tailWord_2401984, baseEnd_2401984] using wordTrace_append hprefix tailTrace_2401984
  have hstable : (prefixWord ++ tailWord_2401984).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2401984).length < 2 ^ (prefixWord ++ tailWord_2401984).sum := by decide
  have hdescent : baseEnd_2401984 < baseStart_2401984 := by decide
  rcases family_descends (prefixWord ++ tailWord_2401984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2402059 : List Nat := [1, 1, 1, 1, 5, 1, 3, 4, 5]
def baseStart_2402059 : Nat := 118140960795 + 2402059 * 2 ^ 59
def prefixEnd_2402059 : Nat := 4983230072969 + 3 ^ 40 * 2402059 * 2
def baseEnd_2402059 : Nat := 274091294990738370403475

theorem tailTrace_2402059 : CollatzResearch.WordTrace tailWord_2402059 prefixEnd_2402059 274091294990738370403475 := by
  unfold tailWord_2402059
  simp only [CollatzResearch.WordTrace]
  refine ⟨87610289204757956861513231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58406859469838637907675487 87610289204757956861513231)
  ·
    refine ⟨131415433807136935292269847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87610289204757956861513231 131415433807136935292269847)
    ·
      refine ⟨197123150710705402938404771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131415433807136935292269847 197123150710705402938404771)
      ·
        refine ⟨295684726066058104407607157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 197123150710705402938404771 295684726066058104407607157)
        ·
          refine ⟨27720443068692947288213171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 295684726066058104407607157 27720443068692947288213171)
          ·
            refine ⟨41580664603039420932319757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27720443068692947288213171 41580664603039420932319757)
            ·
              refine ⟨15592749226139782849619909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41580664603039420932319757 15592749226139782849619909)
              ·
                refine ⟨2923640479901209284303733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15592749226139782849619909 2923640479901209284303733)
                ·
                  refine ⟨274091294990738370403475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2923640479901209284303733 274091294990738370403475)
                  ·
                    rfl

theorem cell22_2402059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 3, 4, 5].length) (baseStart_2402059 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2402059 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2402059 prefixEnd_2402059 := by exact prefixLift 2402059
  have htrace : WordTrace (prefixWord ++ tailWord_2402059) baseStart_2402059 baseEnd_2402059 := by
    simpa [prefixWord, tailWord_2402059, baseEnd_2402059] using wordTrace_append hprefix tailTrace_2402059
  have hstable : (prefixWord ++ tailWord_2402059).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2402059).length < 2 ^ (prefixWord ++ tailWord_2402059).sum := by decide
  have hdescent : baseEnd_2402059 < baseStart_2402059 := by decide
  rcases family_descends (prefixWord ++ tailWord_2402059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2402074 : List Nat := [3, 1, 1, 3, 2, 2, 1, 1, 1, 7]
def baseStart_2402074 : Nat := 118140960795 + 2402074 * 2 ^ 59
def prefixEnd_2402074 : Nat := 4983230072969 + 3 ^ 40 * 2402074 * 2
def baseEnd_2402074 : Nat := 822279019778760072085379

theorem tailTrace_2402074 : CollatzResearch.WordTrace tailWord_2402074 prefixEnd_2402074 822279019778760072085379 := by
  unfold tailWord_2402074
  simp only [CollatzResearch.WordTrace]
  refine ⟨21902709074925903605827319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58407224199802409615539517 21902709074925903605827319)
  ·
    refine ⟨32854063612388855408740979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21902709074925903605827319 32854063612388855408740979)
    ·
      refine ⟨49281095418583283113111469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32854063612388855408740979 49281095418583283113111469)
      ·
        refine ⟨18480410781968731167416801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49281095418583283113111469 18480410781968731167416801)
        ·
          refine ⟨13860308086476548375562601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18480410781968731167416801 13860308086476548375562601)
          ·
            refine ⟨10395231064857411281671951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13860308086476548375562601 10395231064857411281671951)
            ·
              refine ⟨15592846597286116922507927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10395231064857411281671951 15592846597286116922507927)
              ·
                refine ⟨23389269895929175383761891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15592846597286116922507927 23389269895929175383761891)
                ·
                  refine ⟨35083904843893763075642837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23389269895929175383761891 35083904843893763075642837)
                  ·
                    refine ⟨822279019778760072085379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 35083904843893763075642837 822279019778760072085379)
                    ·
                      rfl

theorem cell22_2402074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 1, 1, 1, 7].length) (baseStart_2402074 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2402074 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2402074 prefixEnd_2402074 := by exact prefixLift 2402074
  have htrace : WordTrace (prefixWord ++ tailWord_2402074) baseStart_2402074 baseEnd_2402074 := by
    simpa [prefixWord, tailWord_2402074, baseEnd_2402074] using wordTrace_append hprefix tailTrace_2402074
  have hstable : (prefixWord ++ tailWord_2402074).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2402074).length < 2 ^ (prefixWord ++ tailWord_2402074).sum := by decide
  have hdescent : baseEnd_2402074 < baseStart_2402074 := by decide
  rcases family_descends (prefixWord ++ tailWord_2402074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2402119 : List Nat := [1, 1, 4, 1, 2, 1, 2, 2, 3, 5]
def baseStart_2402119 : Nat := 118140960795 + 2402119 * 2 ^ 59
def prefixEnd_2402119 : Nat := 4983230072969 + 3 ^ 40 * 2402119 * 2
def baseEnd_2402119 : Nat := 822294424198394954710241

theorem tailTrace_2402119 : CollatzResearch.WordTrace tailWord_2402119 prefixEnd_2402119 822294424198394954710241 := by
  unfold tailWord_2402119
  simp only [CollatzResearch.WordTrace]
  refine ⟨87612477584540587108697411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58408318389693724739131607 87612477584540587108697411)
  ·
    refine ⟨131418716376810880663046117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87612477584540587108697411 131418716376810880663046117)
    ·
      refine ⟨24641009320652040124321147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 131418716376810880663046117 24641009320652040124321147)
      ·
        refine ⟨36961513980978060186481721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24641009320652040124321147 36961513980978060186481721)
        ·
          refine ⟨27721135485733545139861291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36961513980978060186481721 27721135485733545139861291)
          ·
            refine ⟨41581703228600317709791937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27721135485733545139861291 41581703228600317709791937)
            ·
              refine ⟨31186277421450238282343953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41581703228600317709791937 31186277421450238282343953)
              ·
                refine ⟨23389708066087678711757965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31186277421450238282343953 23389708066087678711757965)
                ·
                  refine ⟨8771140524782879516909237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23389708066087678711757965 8771140524782879516909237)
                  ·
                    refine ⟨822294424198394954710241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8771140524782879516909237 822294424198394954710241)
                    ·
                      rfl

theorem cell22_2402119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 2, 3, 5].length) (baseStart_2402119 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2402119 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2402119 prefixEnd_2402119 := by exact prefixLift 2402119
  have htrace : WordTrace (prefixWord ++ tailWord_2402119) baseStart_2402119 baseEnd_2402119 := by
    simpa [prefixWord, tailWord_2402119, baseEnd_2402119] using wordTrace_append hprefix tailTrace_2402119
  have hstable : (prefixWord ++ tailWord_2402119).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2402119).length < 2 ^ (prefixWord ++ tailWord_2402119).sum := by decide
  have hdescent : baseEnd_2402119 < baseStart_2402119 := by decide
  rcases family_descends (prefixWord ++ tailWord_2402119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2402121 : List Nat := [1, 2, 1, 1, 2, 4, 1, 6, 4]
def baseStart_2402121 : Nat := 118140960795 + 2402121 * 2 ^ 59
def prefixEnd_2402121 : Nat := 4983230072969 + 3 ^ 40 * 2402121 * 2
def baseEnd_2402121 : Nat := 274098369613089205386745

theorem tailTrace_2402121 : CollatzResearch.WordTrace tailWord_2402121 prefixEnd_2402121 274098369613089205386745 := by
  unfold tailWord_2402121
  simp only [CollatzResearch.WordTrace]
  refine ⟨87612550530533341450270217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58408367020355560966846811 87612550530533341450270217)
  ·
    refine ⟨65709412897900006087702663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87612550530533341450270217 65709412897900006087702663)
    ·
      refine ⟨98564119346850009131553995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65709412897900006087702663 98564119346850009131553995)
      ·
        refine ⟨147846179020275013697330993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98564119346850009131553995 147846179020275013697330993)
        ·
          refine ⟨110884634265206260272998245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 147846179020275013697330993 110884634265206260272998245)
          ·
            refine ⟨20790868924726173801187171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 110884634265206260272998245 20790868924726173801187171)
            ·
              refine ⟨31186303387089260701780757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20790868924726173801187171 31186303387089260701780757)
              ·
                refine ⟨1461857971269809095395973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 31186303387089260701780757 1461857971269809095395973)
                ·
                  refine ⟨274098369613089205386745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1461857971269809095395973 274098369613089205386745)
                  ·
                    rfl

theorem cell22_2402121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 6, 4].length) (baseStart_2402121 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2402121 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2402121 prefixEnd_2402121 := by exact prefixLift 2402121
  have htrace : WordTrace (prefixWord ++ tailWord_2402121) baseStart_2402121 baseEnd_2402121 := by
    simpa [prefixWord, tailWord_2402121, baseEnd_2402121] using wordTrace_append hprefix tailTrace_2402121
  have hstable : (prefixWord ++ tailWord_2402121).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2402121).length < 2 ^ (prefixWord ++ tailWord_2402121).sum := by decide
  have hdescent : baseEnd_2402121 < baseStart_2402121 := by decide
  rcases family_descends (prefixWord ++ tailWord_2402121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2402140 : List Nat := [2, 2, 4, 2, 2, 1, 2, 2, 1, 4]
def baseStart_2402140 : Nat := 118140960795 + 2402140 * 2 ^ 59
def prefixEnd_2402140 : Nat := 4983230072969 + 3 ^ 40 * 2402140 * 2
def baseEnd_2402140 : Nat := 822301612927557899935177

theorem tailTrace_2402140 : CollatzResearch.WordTrace tailWord_2402140 prefixEnd_2402140 822301612927557899935177 := by
  unfold tailWord_2402140
  simp only [CollatzResearch.WordTrace]
  refine ⟨43806621758732253847605937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58408829011643005130141249 43806621758732253847605937)
  ·
    refine ⟨32854966319049190385704453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43806621758732253847605937 32854966319049190385704453)
    ·
      refine ⟨6160306184821723197319585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32854966319049190385704453 6160306184821723197319585)
      ·
        refine ⟨4620229638616292397989689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6160306184821723197319585 4620229638616292397989689)
        ·
          refine ⟨3465172228962219298492267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4620229638616292397989689 3465172228962219298492267)
          ·
            refine ⟨5197758343443328947738401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3465172228962219298492267 5197758343443328947738401)
            ·
              refine ⟨3898318757582496710803801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5197758343443328947738401 3898318757582496710803801)
              ·
                refine ⟨2923739068186872533102851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3898318757582496710803801 2923739068186872533102851)
                ·
                  refine ⟨4385608602280308799654277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2923739068186872533102851 4385608602280308799654277)
                  ·
                    refine ⟨822301612927557899935177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4385608602280308799654277 822301612927557899935177)
                    ·
                      rfl

theorem cell22_2402140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 2, 2, 1, 4].length) (baseStart_2402140 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2402140 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2402140 prefixEnd_2402140 := by exact prefixLift 2402140
  have htrace : WordTrace (prefixWord ++ tailWord_2402140) baseStart_2402140 baseEnd_2402140 := by
    simpa [prefixWord, tailWord_2402140, baseEnd_2402140] using wordTrace_append hprefix tailTrace_2402140
  have hstable : (prefixWord ++ tailWord_2402140).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2402140).length < 2 ^ (prefixWord ++ tailWord_2402140).sum := by decide
  have hdescent : baseEnd_2402140 < baseStart_2402140 := by decide
  rcases family_descends (prefixWord ++ tailWord_2402140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2402151 : List Nat := [1, 1, 5, 1, 2, 1, 2, 3, 2, 4]
def baseStart_2402151 : Nat := 118140960795 + 2402151 * 2 ^ 59
def prefixEnd_2402151 : Nat := 4983230072969 + 3 ^ 40 * 2402151 * 2
def baseEnd_2402151 : Nat := 822305378452357537910143

theorem tailTrace_2402151 : CollatzResearch.WordTrace tailWord_2402151 prefixEnd_2402151 822305378452357537910143 := by
  unfold tailWord_2402151
  simp only [CollatzResearch.WordTrace]
  refine ⟨87613644720424656573862307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58409096480283104382574871 87613644720424656573862307)
  ·
    refine ⟨131420467080636984860793461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87613644720424656573862307 131420467080636984860793461)
    ·
      refine ⟨12320668788809717330699387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 131420467080636984860793461 12320668788809717330699387)
      ·
        refine ⟨18481003183214575996049081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12320668788809717330699387 18481003183214575996049081)
        ·
          refine ⟨13860752387410931997036811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18481003183214575996049081 13860752387410931997036811)
          ·
            refine ⟨20791128581116397995555217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13860752387410931997036811 20791128581116397995555217)
            ·
              refine ⟨15593346435837298496666413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20791128581116397995555217 15593346435837298496666413)
              ·
                refine ⟨5847504913438986936249905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15593346435837298496666413 5847504913438986936249905)
                ·
                  refine ⟨4385628685079240202187429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5847504913438986936249905 4385628685079240202187429)
                  ·
                    refine ⟨822305378452357537910143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4385628685079240202187429 822305378452357537910143)
                    ·
                      rfl

theorem cell22_2402151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 2, 3, 2, 4].length) (baseStart_2402151 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2402151 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2402151 prefixEnd_2402151 := by exact prefixLift 2402151
  have htrace : WordTrace (prefixWord ++ tailWord_2402151) baseStart_2402151 baseEnd_2402151 := by
    simpa [prefixWord, tailWord_2402151, baseEnd_2402151] using wordTrace_append hprefix tailTrace_2402151
  have hstable : (prefixWord ++ tailWord_2402151).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2402151).length < 2 ^ (prefixWord ++ tailWord_2402151).sum := by decide
  have hdescent : baseEnd_2402151 < baseStart_2402151 := by decide
  rcases family_descends (prefixWord ++ tailWord_2402151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2402273 : List Nat := [1, 2, 3, 1, 2, 1, 3, 5, 4]
def baseStart_2402273 : Nat := 118140960795 + 2402273 * 2 ^ 59
def prefixEnd_2402273 : Nat := 4983230072969 + 3 ^ 40 * 2402273 * 2
def baseEnd_2402273 : Nat := 274115713848529962119923

theorem tailTrace_2402273 : CollatzResearch.WordTrace tailWord_2402273 prefixEnd_2402273 274115713848529962119923 := by
  unfold tailWord_2402273
  simp only [CollatzResearch.WordTrace]
  refine ⟨87618094425982671409803473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58412062950655114273202315 87618094425982671409803473)
  ·
    refine ⟨65713570819487003557352605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87618094425982671409803473 65713570819487003557352605)
    ·
      refine ⟨24642589057307626334007227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65713570819487003557352605 24642589057307626334007227)
      ·
        refine ⟨36963883585961439501010841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24642589057307626334007227 36963883585961439501010841)
        ·
          refine ⟨27722912689471079625758131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36963883585961439501010841 27722912689471079625758131)
          ·
            refine ⟨41584369034206619438637197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27722912689471079625758131 41584369034206619438637197)
            ·
              refine ⟨15594138387827482289488949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41584369034206619438637197 15594138387827482289488949)
              ·
                refine ⟨1461950473858826464639589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15594138387827482289488949 1461950473858826464639589)
                ·
                  refine ⟨274115713848529962119923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1461950473858826464639589 274115713848529962119923)
                  ·
                    rfl

theorem cell22_2402273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 3, 5, 4].length) (baseStart_2402273 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2402273 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2402273 prefixEnd_2402273 := by exact prefixLift 2402273
  have htrace : WordTrace (prefixWord ++ tailWord_2402273) baseStart_2402273 baseEnd_2402273 := by
    simpa [prefixWord, tailWord_2402273, baseEnd_2402273] using wordTrace_append hprefix tailTrace_2402273
  have hstable : (prefixWord ++ tailWord_2402273).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2402273).length < 2 ^ (prefixWord ++ tailWord_2402273).sum := by decide
  have hdescent : baseEnd_2402273 < baseStart_2402273 := by decide
  rcases family_descends (prefixWord ++ tailWord_2402273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2402275 : List Nat := [1, 1, 1, 6, 1, 2, 4, 1, 1, 4]
def baseStart_2402275 : Nat := 118140960795 + 2402275 * 2 ^ 59
def prefixEnd_2402275 : Nat := 4983230072969 + 3 ^ 40 * 2402275 * 2
def baseEnd_2402275 : Nat := 822347826186462547809763

theorem tailTrace_2402275 : CollatzResearch.WordTrace tailWord_2402275 prefixEnd_2402275 822347826186462547809763 := by
  unfold tailWord_2402275
  simp only [CollatzResearch.WordTrace]
  refine ⟨87618167371975425751376279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58412111581316950500917519 87618167371975425751376279)
  ·
    refine ⟨131427251057963138627064419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87618167371975425751376279 131427251057963138627064419)
    ·
      refine ⟨197140876586944707940596629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131427251057963138627064419 197140876586944707940596629)
      ·
        refine ⟨9240978590013033184715467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 197140876586944707940596629 9240978590013033184715467)
        ·
          refine ⟨13861467885019549777073201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9240978590013033184715467 13861467885019549777073201)
          ·
            refine ⟨10396100913764662332804901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13861467885019549777073201 10396100913764662332804901)
            ·
              refine ⟨1949268921330874187400919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10396100913764662332804901 1949268921330874187400919)
              ·
                refine ⟨2923903381996311281101379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1949268921330874187400919 2923903381996311281101379)
                ·
                  refine ⟨4385855072994466921652069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2923903381996311281101379 4385855072994466921652069)
                  ·
                    refine ⟨822347826186462547809763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4385855072994466921652069 822347826186462547809763)
                    ·
                      rfl

theorem cell22_2402275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 4, 1, 1, 4].length) (baseStart_2402275 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2402275 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2402275 prefixEnd_2402275 := by exact prefixLift 2402275
  have htrace : WordTrace (prefixWord ++ tailWord_2402275) baseStart_2402275 baseEnd_2402275 := by
    simpa [prefixWord, tailWord_2402275, baseEnd_2402275] using wordTrace_append hprefix tailTrace_2402275
  have hstable : (prefixWord ++ tailWord_2402275).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2402275).length < 2 ^ (prefixWord ++ tailWord_2402275).sum := by decide
  have hdescent : baseEnd_2402275 < baseStart_2402275 := by decide
  rcases family_descends (prefixWord ++ tailWord_2402275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2402316 : List Nat := [2, 2, 1, 2, 3, 1, 1, 1, 2, 7]
def baseStart_2402316 : Nat := 118140960795 + 2402316 * 2 ^ 59
def prefixEnd_2402316 : Nat := 4983230072969 + 3 ^ 40 * 2402316 * 2
def baseEnd_2402316 : Nat := 822361861324352107534637

theorem tailTrace_2402316 : CollatzResearch.WordTrace tailWord_2402316 prefixEnd_2402316 822361861324352107534637 := by
  unfold tailWord_2402316
  simp only [CollatzResearch.WordTrace]
  refine ⟨43809831382413444876809401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58413108509884593169079201 43809831382413444876809401)
  ·
    refine ⟨32857373536810083657607051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43809831382413444876809401 32857373536810083657607051)
    ·
      refine ⟨49286060305215125486410577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32857373536810083657607051 49286060305215125486410577)
      ·
        refine ⟨36964545228911344114807933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49286060305215125486410577 36964545228911344114807933)
        ·
          refine ⟨13861704460841754043052975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36964545228911344114807933 13861704460841754043052975)
          ·
            refine ⟨20792556691262631064579463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13861704460841754043052975 20792556691262631064579463)
            ·
              refine ⟨31188835036893946596869195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20792556691262631064579463 31188835036893946596869195)
              ·
                refine ⟨46783252555340919895303793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31188835036893946596869195 46783252555340919895303793)
                ·
                  refine ⟨35087439416505689921477845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 46783252555340919895303793 35087439416505689921477845)
                  ·
                    refine ⟨822361861324352107534637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 35087439416505689921477845 822361861324352107534637)
                    ·
                      rfl

theorem cell22_2402316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 1, 2, 7].length) (baseStart_2402316 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2402316 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2402316 prefixEnd_2402316 := by exact prefixLift 2402316
  have htrace : WordTrace (prefixWord ++ tailWord_2402316) baseStart_2402316 baseEnd_2402316 := by
    simpa [prefixWord, tailWord_2402316, baseEnd_2402316] using wordTrace_append hprefix tailTrace_2402316
  have hstable : (prefixWord ++ tailWord_2402316).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2402316).length < 2 ^ (prefixWord ++ tailWord_2402316).sum := by decide
  have hdescent : baseEnd_2402316 < baseStart_2402316 := by decide
  rcases family_descends (prefixWord ++ tailWord_2402316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2402356 : List Nat := [2, 5, 1, 2, 2, 2, 2, 1, 2, 3]
def baseStart_2402356 : Nat := 118140960795 + 2402356 * 2 ^ 59
def prefixEnd_2402356 : Nat := 4983230072969 + 3 ^ 40 * 2402356 * 2
def baseEnd_2402356 : Nat := 822375554141805336534515

theorem tailTrace_2402356 : CollatzResearch.WordTrace tailWord_2402356 prefixEnd_2402356 822375554141805336534515 := by
  unfold tailWord_2402356
  simp only [CollatzResearch.WordTrace]
  refine ⟨43810560842340988292537461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58414081123121317723383281 43810560842340988292537461)
  ·
    refine ⟨4107240078969467652425387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 43810560842340988292537461 4107240078969467652425387)
    ·
      refine ⟨6160860118454201478638081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4107240078969467652425387 6160860118454201478638081)
      ·
        refine ⟨4620645088840651108978561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6160860118454201478638081 4620645088840651108978561)
        ·
          refine ⟨3465483816630488331733921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4620645088840651108978561 3465483816630488331733921)
          ·
            refine ⟨2599112862472866248800441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3465483816630488331733921 2599112862472866248800441)
            ·
              refine ⟨1949334646854649686600331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2599112862472866248800441 1949334646854649686600331)
              ·
                refine ⟨2924001970281974529900497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1949334646854649686600331 2924001970281974529900497)
                ·
                  refine ⟨2193001477711480897425373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2924001970281974529900497 2193001477711480897425373)
                  ·
                    refine ⟨822375554141805336534515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2193001477711480897425373 822375554141805336534515)
                    ·
                      rfl

theorem cell22_2402356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 2, 2, 1, 2, 3].length) (baseStart_2402356 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2402356 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2402356 prefixEnd_2402356 := by exact prefixLift 2402356
  have htrace : WordTrace (prefixWord ++ tailWord_2402356) baseStart_2402356 baseEnd_2402356 := by
    simpa [prefixWord, tailWord_2402356, baseEnd_2402356] using wordTrace_append hprefix tailTrace_2402356
  have hstable : (prefixWord ++ tailWord_2402356).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2402356).length < 2 ^ (prefixWord ++ tailWord_2402356).sum := by decide
  have hdescent : baseEnd_2402356 < baseStart_2402356 := by decide
  rcases family_descends (prefixWord ++ tailWord_2402356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2402397 : List Nat := [1, 4, 4, 1, 1, 2, 2, 2, 5]
def baseStart_2402397 : Nat := 118140960795 + 2402397 * 2 ^ 59
def prefixEnd_2402397 : Nat := 4983230072969 + 3 ^ 40 * 2402397 * 2
def baseEnd_2402397 : Nat := 274129863093231632086463

theorem tailTrace_2402397 : CollatzResearch.WordTrace tailWord_2402397 prefixEnd_2402397 274129863093231632086463 := by
  unfold tailWord_2402397
  simp only [CollatzResearch.WordTrace]
  refine ⟨87622617077533440587317445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58415078051688960391544963 87622617077533440587317445)
  ·
    refine ⟨16429240702037520110122021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 87622617077533440587317445 16429240702037520110122021)
    ·
      refine ⟨3080482631632035020647879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16429240702037520110122021 3080482631632035020647879)
      ·
        refine ⟨4620723947448052530971819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3080482631632035020647879 4620723947448052530971819)
        ·
          refine ⟨6931085921172078796457729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4620723947448052530971819 6931085921172078796457729)
          ·
            refine ⟨5198314440879059097343297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6931085921172078796457729 5198314440879059097343297)
            ·
              refine ⟨3898735830659294323007473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5198314440879059097343297 3898735830659294323007473)
              ·
                refine ⟨2924051872994470742255605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3898735830659294323007473 2924051872994470742255605)
                ·
                  refine ⟨274129863093231632086463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2924051872994470742255605 274129863093231632086463)
                  ·
                    rfl

theorem cell22_2402397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 2, 2, 5].length) (baseStart_2402397 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2402397 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2402397 prefixEnd_2402397 := by exact prefixLift 2402397
  have htrace : WordTrace (prefixWord ++ tailWord_2402397) baseStart_2402397 baseEnd_2402397 := by
    simpa [prefixWord, tailWord_2402397, baseEnd_2402397] using wordTrace_append hprefix tailTrace_2402397
  have hstable : (prefixWord ++ tailWord_2402397).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2402397).length < 2 ^ (prefixWord ++ tailWord_2402397).sum := by decide
  have hdescent : baseEnd_2402397 < baseStart_2402397 := by decide
  rcases family_descends (prefixWord ++ tailWord_2402397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2402423 : List Nat := [1, 1, 3, 1, 1, 5, 1, 3, 1, 5]
def baseStart_2402423 : Nat := 118140960795 + 2402423 * 2 ^ 59
def prefixEnd_2402423 : Nat := 4983230072969 + 3 ^ 40 * 2402423 * 2
def baseEnd_2402423 : Nat := 822398489611039495109309

theorem tailTrace_2402423 : CollatzResearch.WordTrace tailWord_2402423 prefixEnd_2402423 822398489611039495109309 := by
  unfold tailWord_2402423
  simp only [CollatzResearch.WordTrace]
  refine ⟨87623565375439247027763923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58415710250292831351842615 87623565375439247027763923)
  ·
    refine ⟨131435348063158870541645885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87623565375439247027763923 131435348063158870541645885)
    ·
      refine ⟨49288255523684576453117207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 131435348063158870541645885 49288255523684576453117207)
      ·
        refine ⟨73932383285526864679675811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49288255523684576453117207 73932383285526864679675811)
        ·
          refine ⟨110898574928290297019513717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73932383285526864679675811 110898574928290297019513717)
          ·
            refine ⟨10396741399527215345579411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 110898574928290297019513717 10396741399527215345579411)
            ·
              refine ⟨15595112099290823018369117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10396741399527215345579411 15595112099290823018369117)
              ·
                refine ⟨5848167037234058631888419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15595112099290823018369117 5848167037234058631888419)
                ·
                  refine ⟨8772250555851087947832629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5848167037234058631888419 8772250555851087947832629)
                  ·
                    refine ⟨822398489611039495109309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8772250555851087947832629 822398489611039495109309)
                    ·
                      rfl

theorem cell22_2402423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 1, 3, 1, 5].length) (baseStart_2402423 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2402423 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2402423 prefixEnd_2402423 := by exact prefixLift 2402423
  have htrace : WordTrace (prefixWord ++ tailWord_2402423) baseStart_2402423 baseEnd_2402423 := by
    simpa [prefixWord, tailWord_2402423, baseEnd_2402423] using wordTrace_append hprefix tailTrace_2402423
  have hstable : (prefixWord ++ tailWord_2402423).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2402423).length < 2 ^ (prefixWord ++ tailWord_2402423).sum := by decide
  have hdescent : baseEnd_2402423 < baseStart_2402423 := by decide
  rcases family_descends (prefixWord ++ tailWord_2402423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2402440 : List Nat := [2, 1, 3, 4, 1, 1, 2, 2, 1, 5]
def baseStart_2402440 : Nat := 118140960795 + 2402440 * 2 ^ 59
def prefixEnd_2402440 : Nat := 4983230072969 + 3 ^ 40 * 2402440 * 2
def baseEnd_2402440 : Nat := 822404309058457117434257

theorem tailTrace_2402440 : CollatzResearch.WordTrace tailWord_2402440 prefixEnd_2402440 822404309058457117434257 := by
  unfold tailWord_2402440
  simp only [CollatzResearch.WordTrace]
  refine ⟨43812092708188829465566387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58416123610918439287421849 43812092708188829465566387)
  ·
    refine ⟨65718139062283244198349581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43812092708188829465566387 65718139062283244198349581)
    ·
      refine ⟨24644302148356216574381093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65718139062283244198349581 24644302148356216574381093)
      ·
        refine ⟨4620806652816790607696455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24644302148356216574381093 4620806652816790607696455)
        ·
          refine ⟨6931209979225185911544683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4620806652816790607696455 6931209979225185911544683)
          ·
            refine ⟨10396814968837778867317025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6931209979225185911544683 10396814968837778867317025)
            ·
              refine ⟨7797611226628334150487769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10396814968837778867317025 7797611226628334150487769)
              ·
                refine ⟨5848208419971250612865827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7797611226628334150487769 5848208419971250612865827)
                ·
                  refine ⟨8772312629956875919298741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5848208419971250612865827 8772312629956875919298741)
                  ·
                    refine ⟨822404309058457117434257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8772312629956875919298741 822404309058457117434257)
                    ·
                      rfl

theorem cell22_2402440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 2, 2, 1, 5].length) (baseStart_2402440 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2402440 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2402440 prefixEnd_2402440 := by exact prefixLift 2402440
  have htrace : WordTrace (prefixWord ++ tailWord_2402440) baseStart_2402440 baseEnd_2402440 := by
    simpa [prefixWord, tailWord_2402440, baseEnd_2402440] using wordTrace_append hprefix tailTrace_2402440
  have hstable : (prefixWord ++ tailWord_2402440).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2402440).length < 2 ^ (prefixWord ++ tailWord_2402440).sum := by decide
  have hdescent : baseEnd_2402440 < baseStart_2402440 := by decide
  rcases family_descends (prefixWord ++ tailWord_2402440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2402442 : List Nat := [3, 1, 2, 3, 1, 3, 2, 3, 4]
def baseStart_2402442 : Nat := 118140960795 + 2402442 * 2 ^ 59
def prefixEnd_2402442 : Nat := 4983230072969 + 3 ^ 40 * 2402442 * 2
def baseEnd_2402442 : Nat := 274134997899776592961417

theorem tailTrace_2402442 : CollatzResearch.WordTrace tailWord_2402442 prefixEnd_2402442 274134997899776592961417 := by
  unfold tailWord_2402442
  simp only [CollatzResearch.WordTrace]
  refine ⟨21906064590592603318176395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58416172241580275515137053 21906064590592603318176395)
  ·
    refine ⟨32859096885888904977264593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21906064590592603318176395 32859096885888904977264593)
    ·
      refine ⟨24644322664416678732948445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32859096885888904977264593 24644322664416678732948445)
      ·
        refine ⟨9241620999156254524855667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24644322664416678732948445 9241620999156254524855667)
        ·
          refine ⟨13862431498734381787283501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9241620999156254524855667 13862431498734381787283501)
          ·
            refine ⟨5198411812025393170231313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13862431498734381787283501 5198411812025393170231313)
            ·
              refine ⟨3898808859019044877673485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5198411812025393170231313 3898808859019044877673485)
              ·
                refine ⟨1462053322132141829127557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3898808859019044877673485 1462053322132141829127557)
                ·
                  refine ⟨274134997899776592961417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1462053322132141829127557 274134997899776592961417)
                  ·
                    rfl

theorem cell22_2402442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 2, 3, 4].length) (baseStart_2402442 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2402442 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2402442 prefixEnd_2402442 := by exact prefixLift 2402442
  have htrace : WordTrace (prefixWord ++ tailWord_2402442) baseStart_2402442 baseEnd_2402442 := by
    simpa [prefixWord, tailWord_2402442, baseEnd_2402442] using wordTrace_append hprefix tailTrace_2402442
  have hstable : (prefixWord ++ tailWord_2402442).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2402442).length < 2 ^ (prefixWord ++ tailWord_2402442).sum := by decide
  have hdescent : baseEnd_2402442 < baseStart_2402442 := by decide
  rcases family_descends (prefixWord ++ tailWord_2402442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2402474 : List Nat := [3, 1, 5, 1, 2, 2, 1, 1, 1, 5]
def baseStart_2402474 : Nat := 118140960795 + 2402474 * 2 ^ 59
def prefixEnd_2402474 : Nat := 4983230072969 + 3 ^ 40 * 2402474 * 2
def baseEnd_2402474 : Nat := 822415947953292362084153

theorem tailTrace_2402474 : CollatzResearch.WordTrace tailWord_2402474 prefixEnd_2402474 822415947953292362084153 := by
  unfold tailWord_2402474
  simp only [CollatzResearch.WordTrace]
  refine ⟨21906356374563620684467619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58416950332169655158580317 21906356374563620684467619)
  ·
    refine ⟨32859534561845431026701429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21906356374563620684467619 32859534561845431026701429)
    ·
      refine ⟨3080581365173009158753259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 32859534561845431026701429 3080581365173009158753259)
      ·
        refine ⟨4620872047759513738129889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3080581365173009158753259 4620872047759513738129889)
        ·
          refine ⟨3465654035819635303597417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4620872047759513738129889 3465654035819635303597417)
          ·
            refine ⟨2599240526864726477698063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3465654035819635303597417 2599240526864726477698063)
            ·
              refine ⟨3898860790297089716547095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2599240526864726477698063 3898860790297089716547095)
              ·
                refine ⟨5848291185445634574820643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3898860790297089716547095 5848291185445634574820643)
                ·
                  refine ⟨8772436778168451862230965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5848291185445634574820643 8772436778168451862230965)
                  ·
                    refine ⟨822415947953292362084153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8772436778168451862230965 822415947953292362084153)
                    ·
                      rfl

theorem cell22_2402474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 2, 1, 1, 1, 5].length) (baseStart_2402474 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2402474 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2402474 prefixEnd_2402474 := by exact prefixLift 2402474
  have htrace : WordTrace (prefixWord ++ tailWord_2402474) baseStart_2402474 baseEnd_2402474 := by
    simpa [prefixWord, tailWord_2402474, baseEnd_2402474] using wordTrace_append hprefix tailTrace_2402474
  have hstable : (prefixWord ++ tailWord_2402474).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2402474).length < 2 ^ (prefixWord ++ tailWord_2402474).sum := by decide
  have hdescent : baseEnd_2402474 < baseStart_2402474 := by decide
  rcases family_descends (prefixWord ++ tailWord_2402474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2402513 : List Nat := [1, 2, 2, 1, 2, 2, 2, 1, 4, 5]
def baseStart_2402513 : Nat := 118140960795 + 2402513 * 2 ^ 59
def prefixEnd_2402513 : Nat := 4983230072969 + 3 ^ 40 * 2402513 * 2
def baseEnd_2402513 : Nat := 822429298450309260359033

theorem tailTrace_2402513 : CollatzResearch.WordTrace tailWord_2402513 prefixEnd_2402513 822429298450309260359033 := by
  unfold tailWord_2402513
  simp only [CollatzResearch.WordTrace]
  refine ⟨87626847945113192398540193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58417898630075461599026795 87626847945113192398540193)
  ·
    refine ⟨65720135958834894298905145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87626847945113192398540193 65720135958834894298905145)
    ·
      refine ⟨49290101969126170724178859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65720135958834894298905145 49290101969126170724178859)
      ·
        refine ⟨73935152953689256086268289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49290101969126170724178859 73935152953689256086268289)
        ·
          refine ⟨55451364715266942064701217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73935152953689256086268289 55451364715266942064701217)
          ·
            refine ⟨41588523536450206548525913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55451364715266942064701217 41588523536450206548525913)
            ·
              refine ⟨31191392652337654911394435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41588523536450206548525913 31191392652337654911394435)
              ·
                refine ⟨46787088978506482367091653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31191392652337654911394435 46787088978506482367091653)
                ·
                  refine ⟨8772579183469965443829685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 46787088978506482367091653 8772579183469965443829685)
                  ·
                    refine ⟨822429298450309260359033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8772579183469965443829685 822429298450309260359033)
                    ·
                      rfl

theorem cell22_2402513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 1, 4, 5].length) (baseStart_2402513 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2402513 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2402513 prefixEnd_2402513 := by exact prefixLift 2402513
  have htrace : WordTrace (prefixWord ++ tailWord_2402513) baseStart_2402513 baseEnd_2402513 := by
    simpa [prefixWord, tailWord_2402513, baseEnd_2402513] using wordTrace_append hprefix tailTrace_2402513
  have hstable : (prefixWord ++ tailWord_2402513).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2402513).length < 2 ^ (prefixWord ++ tailWord_2402513).sum := by decide
  have hdescent : baseEnd_2402513 < baseStart_2402513 := by decide
  rcases family_descends (prefixWord ++ tailWord_2402513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2402575 : List Nat := [1, 1, 2, 1, 1, 1, 3, 5, 4, 3]
def baseStart_2402575 : Nat := 118140960795 + 2402575 * 2 ^ 59
def prefixEnd_2402575 : Nat := 4983230072969 + 3 ^ 40 * 2402575 * 2
def baseEnd_2402575 : Nat := 822450522317361765308843

theorem tailTrace_2402575 : CollatzResearch.WordTrace tailWord_2402575 prefixEnd_2402575 822450522317361765308843 := by
  unfold tailWord_2402575
  simp only [CollatzResearch.WordTrace]
  refine ⟨87629109270888576987297179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58419406180592384658198119 87629109270888576987297179)
  ·
    refine ⟨131443663906332865480945769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87629109270888576987297179 131443663906332865480945769)
    ·
      refine ⟨98582747929749649110709327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 131443663906332865480945769 98582747929749649110709327)
      ·
        refine ⟨147874121894624473666063991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98582747929749649110709327 147874121894624473666063991)
        ·
          refine ⟨221811182841936710499095987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 147874121894624473666063991 221811182841936710499095987)
          ·
            refine ⟨332716774262905065748643981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 221811182841936710499095987 332716774262905065748643981)
            ·
              refine ⟨124768790348589399655741493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 332716774262905065748643981 124768790348589399655741493)
              ·
                refine ⟨11697074095180256217725765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 124768790348589399655741493 11697074095180256217725765)
                ·
                  refine ⟨2193201392846298040823581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11697074095180256217725765 2193201392846298040823581)
                  ·
                    refine ⟨822450522317361765308843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2193201392846298040823581 822450522317361765308843)
                    ·
                      rfl

theorem cell22_2402575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 5, 4, 3].length) (baseStart_2402575 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2402575 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2402575 prefixEnd_2402575 := by exact prefixLift 2402575
  have htrace : WordTrace (prefixWord ++ tailWord_2402575) baseStart_2402575 baseEnd_2402575 := by
    simpa [prefixWord, tailWord_2402575, baseEnd_2402575] using wordTrace_append hprefix tailTrace_2402575
  have hstable : (prefixWord ++ tailWord_2402575).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2402575).length < 2 ^ (prefixWord ++ tailWord_2402575).sum := by decide
  have hdescent : baseEnd_2402575 < baseStart_2402575 := by decide
  rcases family_descends (prefixWord ++ tailWord_2402575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2402577 : List Nat := [1, 2, 2, 1, 1, 6, 1, 4, 4]
def baseStart_2402577 : Nat := 118140960795 + 2402577 * 2 ^ 59
def prefixEnd_2402577 : Nat := 4983230072969 + 3 ^ 40 * 2402577 * 2
def baseEnd_2402577 : Nat := 274150402319411475586279

theorem tailTrace_2402577 : CollatzResearch.WordTrace tailWord_2402577 prefixEnd_2402577 274150402319411475586279 := by
  unfold tailWord_2402577
  simp only [CollatzResearch.WordTrace]
  refine ⟨87629182216881331328869985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58419454811254220885913323 87629182216881331328869985)
  ·
    refine ⟨65721886662660998496652489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87629182216881331328869985 65721886662660998496652489)
    ·
      refine ⟨49291414996995748872489367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65721886662660998496652489 49291414996995748872489367)
      ·
        refine ⟨73937122495493623308734051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49291414996995748872489367 73937122495493623308734051)
        ·
          refine ⟨110905683743240434963101077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73937122495493623308734051 110905683743240434963101077)
          ·
            refine ⟨5198703925464395388895363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 110905683743240434963101077 5198703925464395388895363)
            ·
              refine ⟨7798055888196593083343045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5198703925464395388895363 7798055888196593083343045)
              ·
                refine ⟨1462135479036861203126821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7798055888196593083343045 1462135479036861203126821)
                ·
                  refine ⟨274150402319411475586279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1462135479036861203126821 274150402319411475586279)
                  ·
                    rfl

theorem cell22_2402577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 1, 4, 4].length) (baseStart_2402577 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2402577 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2402577 prefixEnd_2402577 := by exact prefixLift 2402577
  have htrace : WordTrace (prefixWord ++ tailWord_2402577) baseStart_2402577 baseEnd_2402577 := by
    simpa [prefixWord, tailWord_2402577, baseEnd_2402577] using wordTrace_append hprefix tailTrace_2402577
  have hstable : (prefixWord ++ tailWord_2402577).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2402577).length < 2 ^ (prefixWord ++ tailWord_2402577).sum := by decide
  have hdescent : baseEnd_2402577 < baseStart_2402577 := by decide
  rcases family_descends (prefixWord ++ tailWord_2402577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2402592 : List Nat := [2, 1, 1, 5, 2, 2, 2, 1, 1, 5]
def baseStart_2402592 : Nat := 118140960795 + 2402592 * 2 ^ 59
def prefixEnd_2402592 : Nat := 4983230072969 + 3 ^ 40 * 2402592 * 2
def baseEnd_2402592 : Nat := 822456341764779387633791

theorem tailTrace_2402592 : CollatzResearch.WordTrace tailWord_2402592 prefixEnd_2402592 822456341764779387633791 := by
  unfold tailWord_2402592
  simp only [CollatzResearch.WordTrace]
  refine ⟨43814864655913494445333015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58419819541217992593777353 43814864655913494445333015)
  ·
    refine ⟨65722296983870241667999523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43814864655913494445333015 65722296983870241667999523)
    ·
      refine ⟨98583445475805362501999285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65722296983870241667999523 98583445475805362501999285)
      ·
        refine ⟨9242198013356752734562433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 98583445475805362501999285 9242198013356752734562433)
        ·
          refine ⟨6931648510017564550921825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9242198013356752734562433 6931648510017564550921825)
          ·
            refine ⟨5198736382513173413191369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6931648510017564550921825 5198736382513173413191369)
            ·
              refine ⟨3899052286884880059893527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5198736382513173413191369 3899052286884880059893527)
              ·
                refine ⟨5848578430327320089840291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3899052286884880059893527 5848578430327320089840291)
                ·
                  refine ⟨8772867645490980134760437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5848578430327320089840291 8772867645490980134760437)
                  ·
                    refine ⟨822456341764779387633791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8772867645490980134760437 822456341764779387633791)
                    ·
                      rfl

theorem cell22_2402592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 2, 1, 1, 5].length) (baseStart_2402592 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2402592 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2402592 prefixEnd_2402592 := by exact prefixLift 2402592
  have htrace : WordTrace (prefixWord ++ tailWord_2402592) baseStart_2402592 baseEnd_2402592 := by
    simpa [prefixWord, tailWord_2402592, baseEnd_2402592] using wordTrace_append hprefix tailTrace_2402592
  have hstable : (prefixWord ++ tailWord_2402592).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2402592).length < 2 ^ (prefixWord ++ tailWord_2402592).sum := by decide
  have hdescent : baseEnd_2402592 < baseStart_2402592 := by decide
  rcases family_descends (prefixWord ++ tailWord_2402592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2402714 : List Nat := [3, 1, 1, 4, 1, 2, 3, 2, 1, 4]
def baseStart_2402714 : Nat := 118140960795 + 2402714 * 2 ^ 59
def prefixEnd_2402714 : Nat := 4983230072969 + 3 ^ 40 * 2402714 * 2
def baseEnd_2402714 : Nat := 822498104858011736083417

theorem tailTrace_2402714 : CollatzResearch.WordTrace tailWord_2402714 prefixEnd_2402714 822498104858011736083417 := by
  unfold tailWord_2402714
  simp only [CollatzResearch.WordTrace]
  refine ⟨21908544754346250931651799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58422786011590002484404797 21908544754346250931651799)
  ·
    refine ⟨32862817131519376397477699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21908544754346250931651799 32862817131519376397477699)
    ·
      refine ⟨49294225697279064596216549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32862817131519376397477699 49294225697279064596216549)
      ·
        refine ⟨9242667318239824611790603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 49294225697279064596216549 9242667318239824611790603)
        ·
          refine ⟨13864000977359736917685905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9242667318239824611790603 13864000977359736917685905)
          ·
            refine ⟨10398000733019802688264429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13864000977359736917685905 10398000733019802688264429)
            ·
              refine ⟨3899250274882426008099161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10398000733019802688264429 3899250274882426008099161)
              ·
                refine ⟨2924437706161819506074371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3899250274882426008099161 2924437706161819506074371)
                ·
                  refine ⟨4386656559242729259111557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2924437706161819506074371 4386656559242729259111557)
                  ·
                    refine ⟨822498104858011736083417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4386656559242729259111557 822498104858011736083417)
                    ·
                      rfl

theorem cell22_2402714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 3, 2, 1, 4].length) (baseStart_2402714 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2402714 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2402714 prefixEnd_2402714 := by exact prefixLift 2402714
  have htrace : WordTrace (prefixWord ++ tailWord_2402714) baseStart_2402714 baseEnd_2402714 := by
    simpa [prefixWord, tailWord_2402714, baseEnd_2402714] using wordTrace_append hprefix tailTrace_2402714
  have hstable : (prefixWord ++ tailWord_2402714).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2402714).length < 2 ^ (prefixWord ++ tailWord_2402714).sum := by decide
  have hdescent : baseEnd_2402714 < baseStart_2402714 := by decide
  rcases family_descends (prefixWord ++ tailWord_2402714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2402727 : List Nat := [1, 1, 6, 1, 1, 2, 1, 1, 3, 5]
def baseStart_2402727 : Nat := 118140960795 + 2402727 * 2 ^ 59
def prefixEnd_2402727 : Nat := 4983230072969 + 3 ^ 40 * 2402727 * 2
def baseEnd_2402727 : Nat := 822502555023684035508377

theorem tailTrace_2402727 : CollatzResearch.WordTrace tailWord_2402727 prefixEnd_2402727 822502555023684035508377 := by
  unfold tailWord_2402727
  simp only [CollatzResearch.WordTrace]
  refine ⟨87634653166337906946830435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58423102110891937964553623 87634653166337906946830435)
  ·
    refine ⟨131451979749506860420245653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87634653166337906946830435 131451979749506860420245653)
    ·
      refine ⟨6161811550758134082199015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 131451979749506860420245653 6161811550758134082199015)
      ·
        refine ⟨9242717326137201123298523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6161811550758134082199015 9242717326137201123298523)
        ·
          refine ⟨13864075989205801684947785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9242717326137201123298523 13864075989205801684947785)
          ·
            refine ⟨10398056991904351263710839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13864075989205801684947785 10398056991904351263710839)
            ·
              refine ⟨15597085487856526895566259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10398056991904351263710839 15597085487856526895566259)
              ·
                refine ⟨23395628231784790343349389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15597085487856526895566259 23395628231784790343349389)
                ·
                  refine ⟨8773360586919296378756021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23395628231784790343349389 8773360586919296378756021)
                  ·
                    refine ⟨822502555023684035508377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8773360586919296378756021 822502555023684035508377)
                    ·
                      rfl

theorem cell22_2402727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 1, 1, 3, 5].length) (baseStart_2402727 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2402727 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2402727 prefixEnd_2402727 := by exact prefixLift 2402727
  have htrace : WordTrace (prefixWord ++ tailWord_2402727) baseStart_2402727 baseEnd_2402727 := by
    simpa [prefixWord, tailWord_2402727, baseEnd_2402727] using wordTrace_append hprefix tailTrace_2402727
  have hstable : (prefixWord ++ tailWord_2402727).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2402727).length < 2 ^ (prefixWord ++ tailWord_2402727).sum := by decide
  have hdescent : baseEnd_2402727 < baseStart_2402727 := by decide
  rcases family_descends (prefixWord ++ tailWord_2402727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2402755 : List Nat := [1, 1, 1, 3, 1, 1, 3, 2, 2, 7]
def baseStart_2402755 : Nat := 118140960795 + 2402755 * 2 ^ 59
def prefixEnd_2402755 : Nat := 4983230072969 + 3 ^ 40 * 2402755 * 2
def baseEnd_2402755 : Nat := 822512139995901295808291

theorem tailTrace_2402755 : CollatzResearch.WordTrace tailWord_2402755 prefixEnd_2402755 822512139995901295808291 := by
  unfold tailWord_2402755
  simp only [CollatzResearch.WordTrace]
  refine ⟨87635674410236467728849719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58423782940157645152566479 87635674410236467728849719)
  ·
    refine ⟨131453511615354701593274579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87635674410236467728849719 131453511615354701593274579)
    ·
      refine ⟨197180267423032052389911869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131453511615354701593274579 197180267423032052389911869)
      ·
        refine ⟨73942600283637019646216951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 197180267423032052389911869 73942600283637019646216951)
        ·
          refine ⟨110913900425455529469325427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73942600283637019646216951 110913900425455529469325427)
          ·
            refine ⟨166370850638183294203988141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 110913900425455529469325427 166370850638183294203988141)
            ·
              refine ⟨62389068989318735326495553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 166370850638183294203988141 62389068989318735326495553)
              ·
                refine ⟨46791801741989051494871665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 62389068989318735326495553 46791801741989051494871665)
                ·
                  refine ⟨35093851306491788621153749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 46791801741989051494871665 35093851306491788621153749)
                  ·
                    refine ⟨822512139995901295808291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 35093851306491788621153749 822512139995901295808291)
                    ·
                      rfl

theorem cell22_2402755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 2, 2, 7].length) (baseStart_2402755 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2402755 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2402755 prefixEnd_2402755 := by exact prefixLift 2402755
  have htrace : WordTrace (prefixWord ++ tailWord_2402755) baseStart_2402755 baseEnd_2402755 := by
    simpa [prefixWord, tailWord_2402755, baseEnd_2402755] using wordTrace_append hprefix tailTrace_2402755
  have hstable : (prefixWord ++ tailWord_2402755).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2402755).length < 2 ^ (prefixWord ++ tailWord_2402755).sum := by decide
  have hdescent : baseEnd_2402755 < baseStart_2402755 := by decide
  rcases family_descends (prefixWord ++ tailWord_2402755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2402806 : List Nat := [5, 1, 1, 1, 2, 1, 4, 1, 3, 3]
def baseStart_2402806 : Nat := 118140960795 + 2402806 * 2 ^ 59
def prefixEnd_2402806 : Nat := 4983230072969 + 3 ^ 40 * 2402806 * 2
def baseEnd_2402806 : Nat := 822529598338154162783135

theorem tailTrace_2402806 : CollatzResearch.WordTrace tailWord_2402806 prefixEnd_2402806 822529598338154162783135 := by
  unfold tailWord_2402806
  simp only [CollatzResearch.WordTrace]
  refine ⟨5477345908315731464934767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 58425023022034468959304181 5477345908315731464934767)
  ·
    refine ⟨8216018862473597197402151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5477345908315731464934767 8216018862473597197402151)
    ·
      refine ⟨12324028293710395796103227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8216018862473597197402151 12324028293710395796103227)
      ·
        refine ⟨18486042440565593694154841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12324028293710395796103227 18486042440565593694154841)
        ·
          refine ⟨13864531830424195270616131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18486042440565593694154841 13864531830424195270616131)
          ·
            refine ⟨20796797745636292905924197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13864531830424195270616131 20796797745636292905924197)
            ·
              refine ⟨3899399577306804919860787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20796797745636292905924197 3899399577306804919860787)
              ·
                refine ⟨5849099365960207379791181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3899399577306804919860787 5849099365960207379791181)
                ·
                  refine ⟨2193412262235077767421693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5849099365960207379791181 2193412262235077767421693)
                  ·
                    refine ⟨822529598338154162783135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2193412262235077767421693 822529598338154162783135)
                    ·
                      rfl

theorem cell22_2402806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 4, 1, 3, 3].length) (baseStart_2402806 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2402806 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2402806 prefixEnd_2402806 := by exact prefixLift 2402806
  have htrace : WordTrace (prefixWord ++ tailWord_2402806) baseStart_2402806 baseEnd_2402806 := by
    simpa [prefixWord, tailWord_2402806, baseEnd_2402806] using wordTrace_append hprefix tailTrace_2402806
  have hstable : (prefixWord ++ tailWord_2402806).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2402806).length < 2 ^ (prefixWord ++ tailWord_2402806).sum := by decide
  have hdescent : baseEnd_2402806 < baseStart_2402806 := by decide
  rcases family_descends (prefixWord ++ tailWord_2402806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2402819 : List Nat := [1, 1, 1, 3, 2, 1, 7, 1, 5]
def baseStart_2402819 : Nat := 118140960795 + 2402819 * 2 ^ 59
def prefixEnd_2402819 : Nat := 4983230072969 + 3 ^ 40 * 2402819 * 2
def baseEnd_2402819 : Nat := 274178016167942154069365

theorem tailTrace_2402819 : CollatzResearch.WordTrace tailWord_2402819 prefixEnd_2402819 274178016167942154069365 := by
  unfold tailWord_2402819
  simp only [CollatzResearch.WordTrace]
  refine ⟨87638008682004606659179511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58425339121336404439453007 87638008682004606659179511)
  ·
    refine ⟨131457013023006909988769267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87638008682004606659179511 131457013023006909988769267)
    ·
      refine ⟨197185519534510364983153901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131457013023006909988769267 197185519534510364983153901)
      ·
        refine ⟨73944569825441386868682713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 197185519534510364983153901 73944569825441386868682713)
        ·
          refine ⟨55458427369081040151512035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73944569825441386868682713 55458427369081040151512035)
          ·
            refine ⟨83187641053621560227268053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55458427369081040151512035 83187641053621560227268053)
            ·
              refine ⟨1949710337194255317826595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 83187641053621560227268053 1949710337194255317826595)
              ·
                refine ⟨2924565505791382976739893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1949710337194255317826595 2924565505791382976739893)
                ·
                  refine ⟨274178016167942154069365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2924565505791382976739893 274178016167942154069365)
                  ·
                    rfl

theorem cell22_2402819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 7, 1, 5].length) (baseStart_2402819 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2402819 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2402819 prefixEnd_2402819 := by exact prefixLift 2402819
  have htrace : WordTrace (prefixWord ++ tailWord_2402819) baseStart_2402819 baseEnd_2402819 := by
    simpa [prefixWord, tailWord_2402819, baseEnd_2402819] using wordTrace_append hprefix tailTrace_2402819
  have hstable : (prefixWord ++ tailWord_2402819).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2402819).length < 2 ^ (prefixWord ++ tailWord_2402819).sum := by decide
  have hdescent : baseEnd_2402819 < baseStart_2402819 := by decide
  rcases family_descends (prefixWord ++ tailWord_2402819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2402849 : List Nat := [1, 2, 3, 2, 2, 1, 1, 5, 1, 4]
def baseStart_2402849 : Nat := 118140960795 + 2402849 * 2 ^ 59
def prefixEnd_2402849 : Nat := 4983230072969 + 3 ^ 40 * 2402849 * 2
def baseEnd_2402849 : Nat := 822544318116916383958003

theorem tailTrace_2402849 : CollatzResearch.WordTrace tailWord_2402849 prefixEnd_2402849 822544318116916383958003 := by
  unfold tailWord_2402849
  simp only [CollatzResearch.WordTrace]
  refine ⟨87639102871895921782771601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58426068581263947855181067 87639102871895921782771601)
  ·
    refine ⟨65729327153921941337078701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87639102871895921782771601 65729327153921941337078701)
    ·
      refine ⟨24648497682720728001404513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65729327153921941337078701 24648497682720728001404513)
      ·
        refine ⟨18486373262040546001053385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24648497682720728001404513 18486373262040546001053385)
        ·
          refine ⟨13864779946530409500790039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18486373262040546001053385 13864779946530409500790039)
          ·
            refine ⟨20797169919795614251185059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13864779946530409500790039 20797169919795614251185059)
            ·
              refine ⟨31195754879693421376777589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20797169919795614251185059 31195754879693421376777589)
              ·
                refine ⟨2924602019971258254072899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 31195754879693421376777589 2924602019971258254072899)
                ·
                  refine ⟨4386903029956887381109349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2924602019971258254072899 4386903029956887381109349)
                  ·
                    refine ⟨822544318116916383958003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4386903029956887381109349 822544318116916383958003)
                    ·
                      rfl

theorem cell22_2402849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 5, 1, 4].length) (baseStart_2402849 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2402849 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2402849 prefixEnd_2402849 := by exact prefixLift 2402849
  have htrace : WordTrace (prefixWord ++ tailWord_2402849) baseStart_2402849 baseEnd_2402849 := by
    simpa [prefixWord, tailWord_2402849, baseEnd_2402849] using wordTrace_append hprefix tailTrace_2402849
  have hstable : (prefixWord ++ tailWord_2402849).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2402849).length < 2 ^ (prefixWord ++ tailWord_2402849).sum := by decide
  have hdescent : baseEnd_2402849 < baseStart_2402849 := by decide
  rcases family_descends (prefixWord ++ tailWord_2402849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2402864 : List Nat := [2, 1, 1, 1, 2, 3, 2, 6, 4]
def baseStart_2402864 : Nat := 118140960795 + 2402864 * 2 ^ 59
def prefixEnd_2402864 : Nat := 4983230072969 + 3 ^ 40 * 2402864 * 2
def baseEnd_2402864 : Nat := 274183150974487114944319

theorem tailTrace_2402864 : CollatzResearch.WordTrace tailWord_2402864 prefixEnd_2402864 274183150974487114944319 := by
  unfold tailWord_2402864
  simp only [CollatzResearch.WordTrace]
  refine ⟨43819824983420789672283823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58426433311227719563045097 43819824983420789672283823)
  ·
    refine ⟨65729737475131184508425735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43819824983420789672283823 65729737475131184508425735)
    ·
      refine ⟨98594606212696776762638603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65729737475131184508425735 98594606212696776762638603)
      ·
        refine ⟨147891909319045165143957905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98594606212696776762638603 147891909319045165143957905)
        ·
          refine ⟨110918931989283873857968429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 147891909319045165143957905 110918931989283873857968429)
          ·
            refine ⟨41594599495981452696738161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 110918931989283873857968429 41594599495981452696738161)
            ·
              refine ⟨31195949621986089522553621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41594599495981452696738161 31195949621986089522553621)
              ·
                refine ⟨1462310138530597946369701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 31195949621986089522553621 1462310138530597946369701)
                ·
                  refine ⟨274183150974487114944319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1462310138530597946369701 274183150974487114944319)
                  ·
                    rfl

theorem cell22_2402864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 6, 4].length) (baseStart_2402864 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2402864 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2402864 prefixEnd_2402864 := by exact prefixLift 2402864
  have htrace : WordTrace (prefixWord ++ tailWord_2402864) baseStart_2402864 baseEnd_2402864 := by
    simpa [prefixWord, tailWord_2402864, baseEnd_2402864] using wordTrace_append hprefix tailTrace_2402864
  have hstable : (prefixWord ++ tailWord_2402864).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2402864).length < 2 ^ (prefixWord ++ tailWord_2402864).sum := by decide
  have hdescent : baseEnd_2402864 < baseStart_2402864 := by decide
  rcases family_descends (prefixWord ++ tailWord_2402864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2402892 : List Nat := [2, 2, 1, 3, 1, 2, 1, 10]
def baseStart_2402892 : Nat := 118140960795 + 2402892 * 2 ^ 59
def prefixEnd_2402892 : Nat := 4983230072969 + 3 ^ 40 * 2402892 * 2
def baseEnd_2402892 : Nat := 91395448655075400570319

theorem tailTrace_2402892 : CollatzResearch.WordTrace tailWord_2402892 prefixEnd_2402892 91395448655075400570319 := by
  unfold tailWord_2402892
  simp only [CollatzResearch.WordTrace]
  refine ⟨43820335605370070063293465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58427114140493426751057953 43820335605370070063293465)
  ·
    refine ⟨32865251704027552547470099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43820335605370070063293465 32865251704027552547470099)
    ·
      refine ⟨49297877556041328821205149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32865251704027552547470099 49297877556041328821205149)
      ·
        refine ⟨18486704083515498307951931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49297877556041328821205149 18486704083515498307951931)
        ·
          refine ⟨27730056125273247461927897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18486704083515498307951931 27730056125273247461927897)
          ·
            refine ⟨20797542093954935596445923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27730056125273247461927897 20797542093954935596445923)
            ·
              refine ⟨31196313140932403394668885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20797542093954935596445923 31196313140932403394668885)
              ·
                refine ⟨91395448655075400570319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 31196313140932403394668885 91395448655075400570319)
                ·
                  rfl

theorem cell22_2402892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 10].length) (baseStart_2402892 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2402892 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2402892 prefixEnd_2402892 := by exact prefixLift 2402892
  have htrace : WordTrace (prefixWord ++ tailWord_2402892) baseStart_2402892 baseEnd_2402892 := by
    simpa [prefixWord, tailWord_2402892, baseEnd_2402892] using wordTrace_append hprefix tailTrace_2402892
  have hstable : (prefixWord ++ tailWord_2402892).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2402892).length < 2 ^ (prefixWord ++ tailWord_2402892).sum := by decide
  have hdescent : baseEnd_2402892 < baseStart_2402892 := by decide
  rcases family_descends (prefixWord ++ tailWord_2402892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2402894 : List Nat := [4, 1, 1, 1, 1, 2, 3, 3, 2, 4]
def baseStart_2402894 : Nat := 118140960795 + 2402894 * 2 ^ 59
def prefixEnd_2402894 : Nat := 4983230072969 + 3 ^ 40 * 2402894 * 2
def baseEnd_2402894 : Nat := 822559722536551266582865

theorem tailTrace_2402894 : CollatzResearch.WordTrace tailWord_2402894 prefixEnd_2402894 822559722536551266582865 := by
  unfold tailWord_2402894
  simp only [CollatzResearch.WordTrace]
  refine ⟨10955093019591611808519967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 58427162771155262978773157 10955093019591611808519967)
  ·
    refine ⟨16432639529387417712779951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10955093019591611808519967 16432639529387417712779951)
    ·
      refine ⟨24648959294081126569169927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16432639529387417712779951 24648959294081126569169927)
      ·
        refine ⟨36973438941121689853754891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24648959294081126569169927 36973438941121689853754891)
        ·
          refine ⟨55460158411682534780632337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36973438941121689853754891 55460158411682534780632337)
          ·
            refine ⟨41595118808761901085474253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55460158411682534780632337 41595118808761901085474253)
            ·
              refine ⟨15598169553285712907052845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41595118808761901085474253 15598169553285712907052845)
              ·
                refine ⟨5849313582482142340144817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15598169553285712907052845 5849313582482142340144817)
                ·
                  refine ⟨4386985186861606755108613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5849313582482142340144817 4386985186861606755108613)
                  ·
                    refine ⟨822559722536551266582865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4386985186861606755108613 822559722536551266582865)
                    ·
                      rfl

theorem cell22_2402894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 3, 3, 2, 4].length) (baseStart_2402894 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2402894 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2402894 prefixEnd_2402894 := by exact prefixLift 2402894
  have htrace : WordTrace (prefixWord ++ tailWord_2402894) baseStart_2402894 baseEnd_2402894 := by
    simpa [prefixWord, tailWord_2402894, baseEnd_2402894] using wordTrace_append hprefix tailTrace_2402894
  have hstable : (prefixWord ++ tailWord_2402894).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2402894).length < 2 ^ (prefixWord ++ tailWord_2402894).sum := by decide
  have hdescent : baseEnd_2402894 < baseStart_2402894 := by decide
  rcases family_descends (prefixWord ++ tailWord_2402894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2402926 : List Nat := [4, 1, 2, 2, 2, 3, 1, 7]
def baseStart_2402926 : Nat := 118140960795 + 2402926 * 2 ^ 59
def prefixEnd_2402926 : Nat := 4983230072969 + 3 ^ 40 * 2402926 * 2
def baseEnd_2402926 : Nat := 91396741865612649975863

theorem tailTrace_2402926 : CollatzResearch.WordTrace tailWord_2402926 prefixEnd_2402926 91396741865612649975863 := by
  unfold tailWord_2402926
  simp only [CollatzResearch.WordTrace]
  refine ⟨10955238911577120491665579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 58427940861744642622216421 10955238911577120491665579)
  ·
    refine ⟨16432858367365680737498369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10955238911577120491665579 16432858367365680737498369)
    ·
      refine ⟨12324643775524260553123777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16432858367365680737498369 12324643775524260553123777)
      ·
        refine ⟨9243482831643195414842833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12324643775524260553123777 9243482831643195414842833)
        ·
          refine ⟨6932612123732396561132125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9243482831643195414842833 6932612123732396561132125)
          ·
            refine ⟨2599729546399648710424547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6932612123732396561132125 2599729546399648710424547)
            ·
              refine ⟨3899594319599473065636821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2599729546399648710424547 3899594319599473065636821)
              ·
                refine ⟨91396741865612649975863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3899594319599473065636821 91396741865612649975863)
                ·
                  rfl

theorem cell22_2402926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 3, 1, 7].length) (baseStart_2402926 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2402926 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2402926 prefixEnd_2402926 := by exact prefixLift 2402926
  have htrace : WordTrace (prefixWord ++ tailWord_2402926) baseStart_2402926 baseEnd_2402926 := by
    simpa [prefixWord, tailWord_2402926, baseEnd_2402926] using wordTrace_append hprefix tailTrace_2402926
  have hstable : (prefixWord ++ tailWord_2402926).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2402926).length < 2 ^ (prefixWord ++ tailWord_2402926).sum := by decide
  have hdescent : baseEnd_2402926 < baseStart_2402926 := by decide
  rcases family_descends (prefixWord ++ tailWord_2402926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2403009 : List Nat := [1, 2, 6, 2, 1, 2, 1, 3, 1, 3]
def baseStart_2403009 : Nat := 118140960795 + 2403009 * 2 ^ 59
def prefixEnd_2403009 : Nat := 4983230072969 + 3 ^ 40 * 2403009 * 2
def baseEnd_2403009 : Nat := 822599089386729299957513

theorem tailTrace_2403009 : CollatzResearch.WordTrace tailWord_2403009 prefixEnd_2403009 822599089386729299957513 := by
  unfold tailWord_2403009
  simp only [CollatzResearch.WordTrace]
  refine ⟨87644938551316269108596081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58429959034210846072397387 87644938551316269108596081)
  ·
    refine ⟨65733703913487201831447061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87644938551316269108596081 65733703913487201831447061)
    ·
      refine ⟨3081267370944712585849081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 65733703913487201831447061 3081267370944712585849081)
      ·
        refine ⟨2310950528208534439386811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3081267370944712585849081 2310950528208534439386811)
        ·
          refine ⟨3466425792312801659080217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2310950528208534439386811 3466425792312801659080217)
          ·
            refine ⟨2599819344234601244310163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3466425792312801659080217 2599819344234601244310163)
            ·
              refine ⟨3899729016351901866465245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2599819344234601244310163 3899729016351901866465245)
              ·
                refine ⟨1462398381131963199924467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3899729016351901866465245 1462398381131963199924467)
                ·
                  refine ⟨2193597571697944799886701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1462398381131963199924467 2193597571697944799886701)
                  ·
                    refine ⟨822599089386729299957513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2193597571697944799886701 822599089386729299957513)
                    ·
                      rfl

theorem cell22_2403009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 2, 1, 3, 1, 3].length) (baseStart_2403009 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2403009 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2403009 prefixEnd_2403009 := by exact prefixLift 2403009
  have htrace : WordTrace (prefixWord ++ tailWord_2403009) baseStart_2403009 baseEnd_2403009 := by
    simpa [prefixWord, tailWord_2403009, baseEnd_2403009] using wordTrace_append hprefix tailTrace_2403009
  have hstable : (prefixWord ++ tailWord_2403009).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2403009).length < 2 ^ (prefixWord ++ tailWord_2403009).sum := by decide
  have hdescent : baseEnd_2403009 < baseStart_2403009 := by decide
  rcases family_descends (prefixWord ++ tailWord_2403009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2403031 : List Nat := [1, 1, 3, 2, 1, 4, 2, 1, 4, 3]
def baseStart_2403031 : Nat := 118140960795 + 2403031 * 2 ^ 59
def prefixEnd_2403031 : Nat := 4983230072969 + 3 ^ 40 * 2403031 * 2
def baseEnd_2403031 : Nat := 822606620436328575907445

theorem tailTrace_2403031 : CollatzResearch.WordTrace tailWord_2403031 prefixEnd_2403031 822606620436328575907445 := by
  unfold tailWord_2403031
  simp only [CollatzResearch.WordTrace]
  refine ⟨87645740957236566865896947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58430493971491044577264631 87645740957236566865896947)
  ·
    refine ⟨131468611435854850298845421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87645740957236566865896947 131468611435854850298845421)
    ·
      refine ⟨49300729288445568862067033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 131468611435854850298845421 49300729288445568862067033)
      ·
        refine ⟨36975546966334176646550275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49300729288445568862067033 36975546966334176646550275)
        ·
          refine ⟨55463320449501264969825413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36975546966334176646550275 55463320449501264969825413)
          ·
            refine ⟨10399372584281487181842265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 55463320449501264969825413 10399372584281487181842265)
            ·
              refine ⟨7799529438211115386381699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10399372584281487181842265 7799529438211115386381699)
              ·
                refine ⟨11699294157316673079572549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7799529438211115386381699 11699294157316673079572549)
                ·
                  refine ⟨2193617654496876202419853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11699294157316673079572549 2193617654496876202419853)
                  ·
                    refine ⟨822606620436328575907445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2193617654496876202419853 822606620436328575907445)
                    ·
                      rfl

theorem cell22_2403031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 2, 1, 4, 3].length) (baseStart_2403031 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2403031 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2403031 prefixEnd_2403031 := by exact prefixLift 2403031
  have htrace : WordTrace (prefixWord ++ tailWord_2403031) baseStart_2403031 baseEnd_2403031 := by
    simpa [prefixWord, tailWord_2403031, baseEnd_2403031] using wordTrace_append hprefix tailTrace_2403031
  have hstable : (prefixWord ++ tailWord_2403031).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2403031).length < 2 ^ (prefixWord ++ tailWord_2403031).sum := by decide
  have hdescent : baseEnd_2403031 < baseStart_2403031 := by decide
  rcases family_descends (prefixWord ++ tailWord_2403031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2403033 : List Nat := [1, 2, 1, 2, 3, 2, 5, 2, 4]
def baseStart_2403033 : Nat := 118140960795 + 2403033 * 2 ^ 59
def prefixEnd_2403033 : Nat := 4983230072969 + 3 ^ 40 * 2403033 * 2
def baseEnd_2403033 : Nat := 274202435025733745785813

theorem tailTrace_2403033 : CollatzResearch.WordTrace tailWord_2403033 prefixEnd_2403033 274202435025733745785813 := by
  unfold tailWord_2403033
  simp only [CollatzResearch.WordTrace]
  refine ⟨87645813903229321207469753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58430542602152880804979835 87645813903229321207469753)
  ·
    refine ⟨65734360427421990905602315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87645813903229321207469753 65734360427421990905602315)
    ·
      refine ⟨98601540641132986358403473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65734360427421990905602315 98601540641132986358403473)
      ·
        refine ⟨73951155480849739768802605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 98601540641132986358403473 73951155480849739768802605)
        ·
          refine ⟨27731683305318652413300977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 73951155480849739768802605 27731683305318652413300977)
          ·
            refine ⟨20798762478988989309975733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27731683305318652413300977 20798762478988989309975733)
            ·
              refine ⟨1949883982405217747810225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 20798762478988989309975733 1949883982405217747810225)
              ·
                refine ⟨1462412986803913310857669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1949883982405217747810225 1462412986803913310857669)
                ·
                  refine ⟨274202435025733745785813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1462412986803913310857669 274202435025733745785813)
                  ·
                    rfl

theorem cell22_2403033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 5, 2, 4].length) (baseStart_2403033 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2403033 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2403033 prefixEnd_2403033 := by exact prefixLift 2403033
  have htrace : WordTrace (prefixWord ++ tailWord_2403033) baseStart_2403033 baseEnd_2403033 := by
    simpa [prefixWord, tailWord_2403033, baseEnd_2403033] using wordTrace_append hprefix tailTrace_2403033
  have hstable : (prefixWord ++ tailWord_2403033).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2403033).length < 2 ^ (prefixWord ++ tailWord_2403033).sum := by decide
  have hdescent : baseEnd_2403033 < baseStart_2403033 := by decide
  rcases family_descends (prefixWord ++ tailWord_2403033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2403044 : List Nat := [2, 3, 1, 1, 1, 4, 1, 9]
def baseStart_2403044 : Nat := 118140960795 + 2403044 * 2 ^ 59
def prefixEnd_2403044 : Nat := 4983230072969 + 3 ^ 40 * 2403044 * 2
def baseEnd_2403044 : Nat := 91401230066888986148045

theorem tailTrace_2403044 : CollatzResearch.WordTrace tailWord_2403044 prefixEnd_2403044 91401230066888986148045 := by
  unfold tailWord_2403044
  simp only [CollatzResearch.WordTrace]
  refine ⟨43823107553094735043060093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58430810070792980057413457 43823107553094735043060093)
  ·
    refine ⟨16433665332410525641147535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43823107553094735043060093 16433665332410525641147535)
    ·
      refine ⟨24650497998615788461721303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16433665332410525641147535 24650497998615788461721303)
      ·
        refine ⟨36975746997923682692581955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24650497998615788461721303 36975746997923682692581955)
        ·
          refine ⟨55463620496885524038872933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36975746997923682692581955 55463620496885524038872933)
          ·
            refine ⟨10399428843166035757288675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 55463620496885524038872933 10399428843166035757288675)
            ·
              refine ⟨15599143264749053635933013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10399428843166035757288675 15599143264749053635933013)
              ·
                refine ⟨91401230066888986148045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 15599143264749053635933013 91401230066888986148045)
                ·
                  rfl

theorem cell22_2403044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 1, 9].length) (baseStart_2403044 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2403044 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2403044 prefixEnd_2403044 := by exact prefixLift 2403044
  have htrace : WordTrace (prefixWord ++ tailWord_2403044) baseStart_2403044 baseEnd_2403044 := by
    simpa [prefixWord, tailWord_2403044, baseEnd_2403044] using wordTrace_append hprefix tailTrace_2403044
  have hstable : (prefixWord ++ tailWord_2403044).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2403044).length < 2 ^ (prefixWord ++ tailWord_2403044).sum := by decide
  have hdescent : baseEnd_2403044 < baseStart_2403044 := by decide
  rcases family_descends (prefixWord ++ tailWord_2403044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2403089 : List Nat := [1, 2, 2, 1, 1, 3, 2, 3, 7]
def baseStart_2403089 : Nat := 118140960795 + 2403089 * 2 ^ 59
def prefixEnd_2403089 : Nat := 4983230072969 + 3 ^ 40 * 2403089 * 2
def baseEnd_2403089 : Nat := 274208825007211919319089

theorem tailTrace_2403089 : CollatzResearch.WordTrace tailWord_2403089 prefixEnd_2403089 274208825007211919319089 := by
  unfold tailWord_2403089
  simp only [CollatzResearch.WordTrace]
  refine ⟨87647856391026442771508321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58431904260684295181005547 87647856391026442771508321)
  ·
    refine ⟨65735892293269832078631241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87647856391026442771508321 65735892293269832078631241)
    ·
      refine ⟨49301919219952374058973431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65735892293269832078631241 49301919219952374058973431)
      ·
        refine ⟨73952878829928561088460147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49301919219952374058973431 73952878829928561088460147)
        ·
          refine ⟨110929318244892841632690221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73952878829928561088460147 110929318244892841632690221)
          ·
            refine ⟨41598494341834815612258833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 110929318244892841632690221 41598494341834815612258833)
            ·
              refine ⟨31198870756376111709194125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41598494341834815612258833 31198870756376111709194125)
              ·
                refine ⟨11699576533641041890947797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31198870756376111709194125 11699576533641041890947797)
                ·
                  refine ⟨274208825007211919319089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11699576533641041890947797 274208825007211919319089)
                  ·
                    rfl

theorem cell22_2403089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 3, 7].length) (baseStart_2403089 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2403089 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2403089 prefixEnd_2403089 := by exact prefixLift 2403089
  have htrace : WordTrace (prefixWord ++ tailWord_2403089) baseStart_2403089 baseEnd_2403089 := by
    simpa [prefixWord, tailWord_2403089, baseEnd_2403089] using wordTrace_append hprefix tailTrace_2403089
  have hstable : (prefixWord ++ tailWord_2403089).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2403089).length < 2 ^ (prefixWord ++ tailWord_2403089).sum := by decide
  have hdescent : baseEnd_2403089 < baseStart_2403089 := by decide
  rcases family_descends (prefixWord ++ tailWord_2403089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2403140 : List Nat := [2, 3, 4, 2, 1, 1, 1, 1, 7]
def baseStart_2403140 : Nat := 118140960795 + 2403140 * 2 ^ 59
def prefixEnd_2403140 : Nat := 4983230072969 + 3 ^ 40 * 2403140 * 2
def baseEnd_2403140 : Nat := 274214644454629541644037

theorem tailTrace_2403140 : CollatzResearch.WordTrace tailWord_2403140 prefixEnd_2403140 274214644454629541644037 := by
  unfold tailWord_2403140
  simp only [CollatzResearch.WordTrace]
  refine ⟨43824858256920839240807437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58433144342561118987743249 43824858256920839240807437)
  ·
    refine ⟨16434321846345314715302789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43824858256920839240807437 16434321846345314715302789)
    ·
      refine ⟨3081435346189746509119273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16434321846345314715302789 3081435346189746509119273)
      ·
        refine ⟨2311076509642309881839455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3081435346189746509119273 2311076509642309881839455)
        ·
          refine ⟨3466614764463464822759183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2311076509642309881839455 3466614764463464822759183)
          ·
            refine ⟨5199922146695197234138775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3466614764463464822759183 5199922146695197234138775)
            ·
              refine ⟨7799883220042795851208163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5199922146695197234138775 7799883220042795851208163)
              ·
                refine ⟨11699824830064193776812245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7799883220042795851208163 11699824830064193776812245)
                ·
                  refine ⟨274214644454629541644037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11699824830064193776812245 274214644454629541644037)
                  ·
                    rfl

theorem cell22_2403140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 1, 1, 7].length) (baseStart_2403140 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2403140 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2403140 prefixEnd_2403140 := by exact prefixLift 2403140
  have htrace : WordTrace (prefixWord ++ tailWord_2403140) baseStart_2403140 baseEnd_2403140 := by
    simpa [prefixWord, tailWord_2403140, baseEnd_2403140] using wordTrace_append hprefix tailTrace_2403140
  have hstable : (prefixWord ++ tailWord_2403140).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2403140).length < 2 ^ (prefixWord ++ tailWord_2403140).sum := by decide
  have hdescent : baseEnd_2403140 < baseStart_2403140 := by decide
  rcases family_descends (prefixWord ++ tailWord_2403140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2403185 : List Nat := [1, 2, 2, 2, 1, 6, 1, 3, 4]
def baseStart_2403185 : Nat := 118140960795 + 2403185 * 2 ^ 59
def prefixEnd_2403185 : Nat := 4983230072969 + 3 ^ 40 * 2403185 * 2
def baseEnd_2403185 : Nat := 274219779261174502518991

theorem tailTrace_2403185 : CollatzResearch.WordTrace tailWord_2403185 prefixEnd_2403185 274219779261174502518991 := by
  unfold tailWord_2403185
  simp only [CollatzResearch.WordTrace]
  refine ⟨87651357798678651167003009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58434238532452434111335339 87651357798678651167003009)
  ·
    refine ⟨65738518349008988375252257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87651357798678651167003009 65738518349008988375252257)
    ·
      refine ⟨49303888761756741281439193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65738518349008988375252257 49303888761756741281439193)
      ·
        refine ⟨36977916571317555961079395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49303888761756741281439193 36977916571317555961079395)
        ·
          refine ⟨55466874856976333941619093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36977916571317555961079395 55466874856976333941619093)
          ·
            refine ⟨2600009758920765653513395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 55466874856976333941619093 2600009758920765653513395)
            ·
              refine ⟨3900014638381148480270093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2600009758920765653513395 3900014638381148480270093)
              ·
                refine ⟨1462505489392930680101285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3900014638381148480270093 1462505489392930680101285)
                ·
                  refine ⟨274219779261174502518991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1462505489392930680101285 274219779261174502518991)
                  ·
                    rfl

theorem cell22_2403185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 6, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 6, 1, 3, 4].length) (baseStart_2403185 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2403185 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2403185 prefixEnd_2403185 := by exact prefixLift 2403185
  have htrace : WordTrace (prefixWord ++ tailWord_2403185) baseStart_2403185 baseEnd_2403185 := by
    simpa [prefixWord, tailWord_2403185, baseEnd_2403185] using wordTrace_append hprefix tailTrace_2403185
  have hstable : (prefixWord ++ tailWord_2403185).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2403185).length < 2 ^ (prefixWord ++ tailWord_2403185).sum := by decide
  have hdescent : baseEnd_2403185 < baseStart_2403185 := by decide
  rcases family_descends (prefixWord ++ tailWord_2403185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2403258 : List Nat := [3, 1, 1, 1, 2, 1, 6, 2, 5]
def baseStart_2403258 : Nat := 118140960795 + 2403258 * 2 ^ 59
def prefixEnd_2403258 : Nat := 4983230072969 + 3 ^ 40 * 2403258 * 2
def baseEnd_2403258 : Nat := 274228109058458550160583

theorem tailTrace_2403258 : CollatzResearch.WordTrace tailWord_2403258 prefixEnd_2403258 274228109058458550160583 := by
  unfold tailWord_2403258
  simp only [CollatzResearch.WordTrace]
  refine ⟨21913505081853546158602607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58436013551609456422940285 21913505081853546158602607)
  ·
    refine ⟨32870257622780319237903911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21913505081853546158602607 32870257622780319237903911)
    ·
      refine ⟨49305386434170478856855867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32870257622780319237903911 49305386434170478856855867)
      ·
        refine ⟨73958079651255718285283801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49305386434170478856855867 73958079651255718285283801)
        ·
          refine ⟨55468559738441788713962851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73958079651255718285283801 55468559738441788713962851)
          ·
            refine ⟨83202839607662683070944277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55468559738441788713962851 83202839607662683070944277)
            ·
              refine ⟨3900133106609188268950513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 83202839607662683070944277 3900133106609188268950513)
              ·
                refine ⟨2925099829956891201712885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3900133106609188268950513 2925099829956891201712885)
                ·
                  refine ⟨274228109058458550160583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2925099829956891201712885 274228109058458550160583)
                  ·
                    rfl

theorem cell22_2403258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 6, 2, 5].length) (baseStart_2403258 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2403258 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2403258 prefixEnd_2403258 := by exact prefixLift 2403258
  have htrace : WordTrace (prefixWord ++ tailWord_2403258) baseStart_2403258 baseEnd_2403258 := by
    simpa [prefixWord, tailWord_2403258, baseEnd_2403258] using wordTrace_append hprefix tailTrace_2403258
  have hstable : (prefixWord ++ tailWord_2403258).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2403258).length < 2 ^ (prefixWord ++ tailWord_2403258).sum := by decide
  have hdescent : baseEnd_2403258 < baseStart_2403258 := by decide
  rcases family_descends (prefixWord ++ tailWord_2403258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2403262 : List Nat := [4, 2, 1, 1, 1, 2, 3, 4, 1, 3]
def baseStart_2403262 : Nat := 118140960795 + 2403262 * 2 ^ 59
def prefixEnd_2403262 : Nat := 4983230072969 + 3 ^ 40 * 2403262 * 2
def baseEnd_2403262 : Nat := 822685696457120973381737

theorem tailTrace_2403262 : CollatzResearch.WordTrace tailWord_2403262 prefixEnd_2403262 822685696457120973381737 := by
  unfold tailWord_2403262
  simp only [CollatzResearch.WordTrace]
  refine ⟨10956770777424961664694505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 58436110812933128878370693 10956770777424961664694505)
  ·
    refine ⟨8217578083068721248520879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10956770777424961664694505 8217578083068721248520879)
    ·
      refine ⟨12326367124603081872781319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8217578083068721248520879 12326367124603081872781319)
      ·
        refine ⟨18489550686904622809171979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12326367124603081872781319 18489550686904622809171979)
        ·
          refine ⟨27734326030356934213757969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18489550686904622809171979 27734326030356934213757969)
          ·
            refine ⟨20800744522767700660318477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27734326030356934213757969 20800744522767700660318477)
            ·
              refine ⟨7800279196037887747619429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20800744522767700660318477 7800279196037887747619429)
              ·
                refine ⟨1462552349257103952678643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7800279196037887747619429 1462552349257103952678643)
                ·
                  refine ⟨2193828523885655929017965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1462552349257103952678643 2193828523885655929017965)
                  ·
                    refine ⟨822685696457120973381737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2193828523885655929017965 822685696457120973381737)
                    ·
                      rfl

theorem cell22_2403262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 3, 4, 1, 3].length) (baseStart_2403262 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2403262 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2403262 prefixEnd_2403262 := by exact prefixLift 2403262
  have htrace : WordTrace (prefixWord ++ tailWord_2403262) baseStart_2403262 baseEnd_2403262 := by
    simpa [prefixWord, tailWord_2403262, baseEnd_2403262] using wordTrace_append hprefix tailTrace_2403262
  have hstable : (prefixWord ++ tailWord_2403262).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2403262).length < 2 ^ (prefixWord ++ tailWord_2403262).sum := by decide
  have hdescent : baseEnd_2403262 < baseStart_2403262 := by decide
  rcases family_descends (prefixWord ++ tailWord_2403262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2403288 : List Nat := [2, 1, 2, 2, 2, 3, 2, 1, 3, 4]
def baseStart_2403288 : Nat := 118140960795 + 2403288 * 2 ^ 59
def prefixEnd_2403288 : Nat := 4983230072969 + 3 ^ 40 * 2403288 * 2
def baseEnd_2403288 : Nat := 822694596788465572231657

theorem tailTrace_2403288 : CollatzResearch.WordTrace tailWord_2403288 prefixEnd_2403288 822694596788465572231657 := by
  unfold tailWord_2403288
  simp only [CollatzResearch.WordTrace]
  refine ⟨43827557258652749879001259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58436743011536999838668345 43827557258652749879001259)
  ·
    refine ⟨65741335887979124818501889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43827557258652749879001259 65741335887979124818501889)
    ·
      refine ⟨49306001915984343613876417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65741335887979124818501889 49306001915984343613876417)
      ·
        refine ⟨36979501436988257710407313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49306001915984343613876417 36979501436988257710407313)
        ·
          refine ⟨27734626077741193282805485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36979501436988257710407313 27734626077741193282805485)
          ·
            refine ⟨10400484779152947481052057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27734626077741193282805485 10400484779152947481052057)
            ·
              refine ⟨7800363584364710610789043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10400484779152947481052057 7800363584364710610789043)
              ·
                refine ⟨11700545376547065916183565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7800363584364710610789043 11700545376547065916183565)
                ·
                  refine ⟨4387704516205149718568837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11700545376547065916183565 4387704516205149718568837)
                  ·
                    refine ⟨822694596788465572231657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4387704516205149718568837 822694596788465572231657)
                    ·
                      rfl

theorem cell22_2403288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 2, 1, 3, 4].length) (baseStart_2403288 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2403288 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2403288 prefixEnd_2403288 := by exact prefixLift 2403288
  have htrace : WordTrace (prefixWord ++ tailWord_2403288) baseStart_2403288 baseEnd_2403288 := by
    simpa [prefixWord, tailWord_2403288, baseEnd_2403288] using wordTrace_append hprefix tailTrace_2403288
  have hstable : (prefixWord ++ tailWord_2403288).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2403288).length < 2 ^ (prefixWord ++ tailWord_2403288).sum := by decide
  have hdescent : baseEnd_2403288 < baseStart_2403288 := by decide
  rcases family_descends (prefixWord ++ tailWord_2403288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2403367 : List Nat := [1, 1, 7, 1, 1, 2, 1, 2, 2, 4]
def baseStart_2403367 : Nat := 118140960795 + 2403367 * 2 ^ 59
def prefixEnd_2403367 : Nat := 4983230072969 + 3 ^ 40 * 2403367 * 2
def baseEnd_2403367 : Nat := 822721640102935699506415

theorem tailTrace_2403367 : CollatzResearch.WordTrace tailWord_2403367 prefixEnd_2403367 822721640102935699506415 := by
  unfold tailWord_2403367
  simp only [CollatzResearch.WordTrace]
  refine ⟨87657995884019296250128355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58438663922679530833418903 87657995884019296250128355)
  ·
    refine ⟨131486993826028944375192533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87657995884019296250128355 131486993826028944375192533)
    ·
      refine ⟨3081726417797553383793575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 131486993826028944375192533 3081726417797553383793575)
      ·
        refine ⟨4622589626696330075690363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3081726417797553383793575 4622589626696330075690363)
        ·
          refine ⟨6933884440044495113535545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4622589626696330075690363 6933884440044495113535545)
          ·
            refine ⟨5200413330033371335151659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6933884440044495113535545 5200413330033371335151659)
            ·
              refine ⟨7800619995050057002727489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5200413330033371335151659 7800619995050057002727489)
              ·
                refine ⟨5850464996287542752045617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7800619995050057002727489 5850464996287542752045617)
                ·
                  refine ⟨4387848747215657064034213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5850464996287542752045617 4387848747215657064034213)
                  ·
                    refine ⟨822721640102935699506415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4387848747215657064034213 822721640102935699506415)
                    ·
                      rfl

theorem cell22_2403367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 1, 2, 2, 4].length) (baseStart_2403367 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2403367 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2403367 prefixEnd_2403367 := by exact prefixLift 2403367
  have htrace : WordTrace (prefixWord ++ tailWord_2403367) baseStart_2403367 baseEnd_2403367 := by
    simpa [prefixWord, tailWord_2403367, baseEnd_2403367] using wordTrace_append hprefix tailTrace_2403367
  have hstable : (prefixWord ++ tailWord_2403367).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2403367).length < 2 ^ (prefixWord ++ tailWord_2403367).sum := by decide
  have hdescent : baseEnd_2403367 < baseStart_2403367 := by decide
  rcases family_descends (prefixWord ++ tailWord_2403367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2403378 : List Nat := [3, 2, 1, 1, 2, 2, 2, 1, 2, 6]
def baseStart_2403378 : Nat := 118140960795 + 2403378 * 2 ^ 59
def prefixEnd_2403378 : Nat := 4983230072969 + 3 ^ 40 * 2403378 * 2
def baseEnd_2403378 : Nat := 822725405627735337481381

theorem tailTrace_2403378 : CollatzResearch.WordTrace tailWord_2403378 prefixEnd_2403378 822725405627735337481381 := by
  unfold tailWord_2403378
  simp only [CollatzResearch.WordTrace]
  refine ⟨21914599271744861282194697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58438931391319630085852525 21914599271744861282194697)
  ·
    refine ⟨16435949453808645961646023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21914599271744861282194697 16435949453808645961646023)
    ·
      refine ⟨24653924180712968942469035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16435949453808645961646023 24653924180712968942469035)
      ·
        refine ⟨36980886271069453413703553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24653924180712968942469035 36980886271069453413703553)
        ·
          refine ⟨27735664703302090060277665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36980886271069453413703553 27735664703302090060277665)
          ·
            refine ⟨20801748527476567545208249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27735664703302090060277665 20801748527476567545208249)
            ·
              refine ⟨15601311395607425658906187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20801748527476567545208249 15601311395607425658906187)
              ·
                refine ⟨23401967093411138488359281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15601311395607425658906187 23401967093411138488359281)
                ·
                  refine ⟨17551475320058353866269461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23401967093411138488359281 17551475320058353866269461)
                  ·
                    refine ⟨822725405627735337481381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17551475320058353866269461 822725405627735337481381)
                    ·
                      rfl

theorem cell22_2403378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 2, 1, 2, 6].length) (baseStart_2403378 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2403378 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2403378 prefixEnd_2403378 := by exact prefixLift 2403378
  have htrace : WordTrace (prefixWord ++ tailWord_2403378) baseStart_2403378 baseEnd_2403378 := by
    simpa [prefixWord, tailWord_2403378, baseEnd_2403378] using wordTrace_append hprefix tailTrace_2403378
  have hstable : (prefixWord ++ tailWord_2403378).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2403378).length < 2 ^ (prefixWord ++ tailWord_2403378).sum := by decide
  have hdescent : baseEnd_2403378 < baseStart_2403378 := by decide
  rcases family_descends (prefixWord ++ tailWord_2403378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2403431 : List Nat := [1, 1, 5, 1, 1, 5, 2, 2, 1, 3]
def baseStart_2403431 : Nat := 118140960795 + 2403431 * 2 ^ 59
def prefixEnd_2403431 : Nat := 4983230072969 + 3 ^ 40 * 2403431 * 2
def baseEnd_2403431 : Nat := 822743548610860865906219

theorem tailTrace_2403431 : CollatzResearch.WordTrace tailWord_2403431 prefixEnd_2403431 822743548610860865906219 := by
  unfold tailWord_2403431
  simp only [CollatzResearch.WordTrace]
  refine ⟨87660330155787435180458147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58440220103858290120305431 87660330155787435180458147)
  ·
    refine ⟨131490495233681152770687221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87660330155787435180458147 131490495233681152770687221)
    ·
      refine ⟨12327233928157608072251927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 131490495233681152770687221 12327233928157608072251927)
      ·
        refine ⟨18490850892236412108377891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12327233928157608072251927 18490850892236412108377891)
        ·
          refine ⟨27736276338354618162566837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18490850892236412108377891 27736276338354618162566837)
          ·
            refine ⟨2600275906720745452740641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 27736276338354618162566837 2600275906720745452740641)
            ·
              refine ⟨1950206930040559089555481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2600275906720745452740641 1950206930040559089555481)
              ·
                refine ⟨1462655197530419317166611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1950206930040559089555481 1462655197530419317166611)
                ·
                  refine ⟨2193982796295628975749917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1462655197530419317166611 2193982796295628975749917)
                  ·
                    refine ⟨822743548610860865906219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2193982796295628975749917 822743548610860865906219)
                    ·
                      rfl

theorem cell22_2403431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 5, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 5, 2, 2, 1, 3].length) (baseStart_2403431 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2403431 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2403431 prefixEnd_2403431 := by exact prefixLift 2403431
  have htrace : WordTrace (prefixWord ++ tailWord_2403431) baseStart_2403431 baseEnd_2403431 := by
    simpa [prefixWord, tailWord_2403431, baseEnd_2403431] using wordTrace_append hprefix tailTrace_2403431
  have hstable : (prefixWord ++ tailWord_2403431).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2403431).length < 2 ^ (prefixWord ++ tailWord_2403431).sum := by decide
  have hdescent : baseEnd_2403431 < baseStart_2403431 := by decide
  rcases family_descends (prefixWord ++ tailWord_2403431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2403474 : List Nat := [3, 2, 3, 1, 1, 2, 4, 1, 1, 4]
def baseStart_2403474 : Nat := 118140960795 + 2403474 * 2 ^ 59
def prefixEnd_2403474 : Nat := 4983230072969 + 3 ^ 40 * 2403474 * 2
def baseEnd_2403474 : Nat := 822758268389623087081087

theorem tailTrace_2403474 : CollatzResearch.WordTrace tailWord_2403474 prefixEnd_2403474 822758268389623087081087 := by
  unfold tailWord_2403474
  simp only [CollatzResearch.WordTrace]
  refine ⟨21915474623657913381068369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58441265663087769016182317 21915474623657913381068369)
  ·
    refine ⟨16436605967743435035801277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21915474623657913381068369 16436605967743435035801277)
    ·
      refine ⟨6163727237903788138425479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16436605967743435035801277 6163727237903788138425479)
      ·
        refine ⟨9245590856855682207638219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6163727237903788138425479 9245590856855682207638219)
        ·
          refine ⟨13868386285283523311457329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9245590856855682207638219 13868386285283523311457329)
          ·
            refine ⟨10401289713962642483592997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13868386285283523311457329 10401289713962642483592997)
            ·
              refine ⟨1950241821367995465673687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10401289713962642483592997 1950241821367995465673687)
              ·
                refine ⟨2925362732051993198510531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1950241821367995465673687 2925362732051993198510531)
                ·
                  refine ⟨4388044098077989797765797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2925362732051993198510531 4388044098077989797765797)
                  ·
                    refine ⟨822758268389623087081087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4388044098077989797765797 822758268389623087081087)
                    ·
                      rfl

theorem cell22_2403474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 4, 1, 1, 4].length) (baseStart_2403474 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2403474 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2403474 prefixEnd_2403474 := by exact prefixLift 2403474
  have htrace : WordTrace (prefixWord ++ tailWord_2403474) baseStart_2403474 baseEnd_2403474 := by
    simpa [prefixWord, tailWord_2403474, baseEnd_2403474] using wordTrace_append hprefix tailTrace_2403474
  have hstable : (prefixWord ++ tailWord_2403474).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2403474).length < 2 ^ (prefixWord ++ tailWord_2403474).sum := by decide
  have hdescent : baseEnd_2403474 < baseStart_2403474 := by decide
  rcases family_descends (prefixWord ++ tailWord_2403474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2403485 : List Nat := [1, 4, 2, 1, 1, 2, 2, 1, 4, 4]
def baseStart_2403485 : Nat := 118140960795 + 2403485 * 2 ^ 59
def prefixEnd_2403485 : Nat := 4983230072969 + 3 ^ 40 * 2403485 * 2
def baseEnd_2403485 : Nat := 822762033914422725056053

theorem tailTrace_2403485 : CollatzResearch.WordTrace tailWord_2403485 prefixEnd_2403485 822762033914422725056053 := by
  unfold tailWord_2403485
  simp only [CollatzResearch.WordTrace]
  refine ⟨87662299697591802402923909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58441533131727868268615939 87662299697591802402923909)
  ·
    refine ⟨16436681193298462950548233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 87662299697591802402923909 16436681193298462950548233)
    ·
      refine ⟨12327510894973847212911175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16436681193298462950548233 12327510894973847212911175)
      ·
        refine ⟨18491266342460770819366763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12327510894973847212911175 18491266342460770819366763)
        ·
          refine ⟨27736899513691156229050145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18491266342460770819366763 27736899513691156229050145)
          ·
            refine ⟨20802674635268367171787609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27736899513691156229050145 20802674635268367171787609)
            ·
              refine ⟨15602005976451275378840707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20802674635268367171787609 15602005976451275378840707)
              ·
                refine ⟨23403008964676913068261061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15602005976451275378840707 23403008964676913068261061)
                ·
                  refine ⟨4388064180876921200298949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23403008964676913068261061 4388064180876921200298949)
                  ·
                    refine ⟨822762033914422725056053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4388064180876921200298949 822762033914422725056053)
                    ·
                      rfl

theorem cell22_2403485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 2, 1, 4, 4].length) (baseStart_2403485 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2403485 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2403485 prefixEnd_2403485 := by exact prefixLift 2403485
  have htrace : WordTrace (prefixWord ++ tailWord_2403485) baseStart_2403485 baseEnd_2403485 := by
    simpa [prefixWord, tailWord_2403485, baseEnd_2403485] using wordTrace_append hprefix tailTrace_2403485
  have hstable : (prefixWord ++ tailWord_2403485).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2403485).length < 2 ^ (prefixWord ++ tailWord_2403485).sum := by decide
  have hdescent : baseEnd_2403485 < baseStart_2403485 := by decide
  rcases family_descends (prefixWord ++ tailWord_2403485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2403515 : List Nat := [1, 1, 1, 1, 1, 2, 4, 3, 5, 3]
def baseStart_2403515 : Nat := 118140960795 + 2403515 * 2 ^ 59
def prefixEnd_2403515 : Nat := 4983230072969 + 3 ^ 40 * 2403515 * 2
def baseEnd_2403515 : Nat := 822772303527512646805961

theorem tailTrace_2403515 : CollatzResearch.WordTrace tailWord_2403515 prefixEnd_2403515 822772303527512646805961 := by
  unfold tailWord_2403515
  simp only [CollatzResearch.WordTrace]
  refine ⟨87663393887483117526515999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58442262591655411684343999 87663393887483117526515999)
  ·
    refine ⟨131495090831224676289773999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87663393887483117526515999 131495090831224676289773999)
    ·
      refine ⟨197242636246837014434660999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131495090831224676289773999 197242636246837014434660999)
      ·
        refine ⟨295863954370255521651991499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 197242636246837014434660999 295863954370255521651991499)
        ·
          refine ⟨443795931555383282477987249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 295863954370255521651991499 443795931555383282477987249)
          ·
            refine ⟨332846948666537461858490437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 443795931555383282477987249 332846948666537461858490437)
            ·
              refine ⟨62408802874975774098466957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 332846948666537461858490437 62408802874975774098466957)
              ·
                refine ⟨23403301078115915286925109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 62408802874975774098466957 23403301078115915286925109)
                ·
                  refine ⟨2194059476073367058149229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 23403301078115915286925109 2194059476073367058149229)
                  ·
                    refine ⟨822772303527512646805961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2194059476073367058149229 822772303527512646805961)
                    ·
                      rfl

theorem cell22_2403515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 3, 5, 3].length) (baseStart_2403515 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2403515 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2403515 prefixEnd_2403515 := by exact prefixLift 2403515
  have htrace : WordTrace (prefixWord ++ tailWord_2403515) baseStart_2403515 baseEnd_2403515 := by
    simpa [prefixWord, tailWord_2403515, baseEnd_2403515] using wordTrace_append hprefix tailTrace_2403515
  have hstable : (prefixWord ++ tailWord_2403515).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2403515).length < 2 ^ (prefixWord ++ tailWord_2403515).sum := by decide
  have hdescent : baseEnd_2403515 < baseStart_2403515 := by decide
  rcases family_descends (prefixWord ++ tailWord_2403515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2403545 : List Nat := [1, 2, 1, 2, 3, 1, 1, 6, 5]
def baseStart_2403545 : Nat := 118140960795 + 2403545 * 2 ^ 59
def prefixEnd_2403545 : Nat := 4983230072969 + 3 ^ 40 * 2403545 * 2
def baseEnd_2403545 : Nat := 274260857713534189518623

theorem tailTrace_2403545 : CollatzResearch.WordTrace tailWord_2403545 prefixEnd_2403545 274260857713534189518623 := by
  unfold tailWord_2403545
  simp only [CollatzResearch.WordTrace]
  refine ⟨87664488077374432650108089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58442992051582955100072059 87664488077374432650108089)
  ·
    refine ⟨65748366058030824487581067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87664488077374432650108089 65748366058030824487581067)
    ·
      refine ⟨98622549087046236731371601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65748366058030824487581067 98622549087046236731371601)
      ·
        refine ⟨73966911815284677548528701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 98622549087046236731371601 73966911815284677548528701)
        ·
          refine ⟨27737591930731754080698263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 73966911815284677548528701 27737591930731754080698263)
          ·
            refine ⟨41606387896097631121047395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27737591930731754080698263 41606387896097631121047395)
            ·
              refine ⟨62409581844146446681571093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41606387896097631121047395 62409581844146446681571093)
              ·
                refine ⟨2925449148944364688198645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 62409581844146446681571093 2925449148944364688198645)
                ·
                  refine ⟨274260857713534189518623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2925449148944364688198645 274260857713534189518623)
                  ·
                    rfl

theorem cell22_2403545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 6, 5].length) (baseStart_2403545 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2403545 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2403545 prefixEnd_2403545 := by exact prefixLift 2403545
  have htrace : WordTrace (prefixWord ++ tailWord_2403545) baseStart_2403545 baseEnd_2403545 := by
    simpa [prefixWord, tailWord_2403545, baseEnd_2403545] using wordTrace_append hprefix tailTrace_2403545
  have hstable : (prefixWord ++ tailWord_2403545).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2403545).length < 2 ^ (prefixWord ++ tailWord_2403545).sum := by decide
  have hdescent : baseEnd_2403545 < baseStart_2403545 := by decide
  rcases family_descends (prefixWord ++ tailWord_2403545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2403560 : List Nat := [2, 1, 4, 1, 2, 1, 2, 1, 1, 7]
def baseStart_2403560 : Nat := 118140960795 + 2403560 * 2 ^ 59
def prefixEnd_2403560 : Nat := 4983230072969 + 3 ^ 40 * 2403560 * 2
def baseEnd_2403560 : Nat := 822787707947147529430823

theorem tailTrace_2403560 : CollatzResearch.WordTrace tailWord_2403560 prefixEnd_2403560 822787707947147529430823 := by
  unfold tailWord_2403560
  simp only [CollatzResearch.WordTrace]
  refine ⟨43832517586160045105952067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58443356781546726807936089 43832517586160045105952067)
  ·
    refine ⟨65748776379240067658928101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43832517586160045105952067 65748776379240067658928101)
    ·
      refine ⟨12327895571107512686049019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 65748776379240067658928101 12327895571107512686049019)
      ·
        refine ⟨18491843356661269029073529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12327895571107512686049019 18491843356661269029073529)
        ·
          refine ⟨13868882517495951771805147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18491843356661269029073529 13868882517495951771805147)
          ·
            refine ⟨20803323776243927657707721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13868882517495951771805147 20803323776243927657707721)
            ·
              refine ⟨15602492832182945743280791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20803323776243927657707721 15602492832182945743280791)
              ·
                refine ⟨23403739248274418614921187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15602492832182945743280791 23403739248274418614921187)
                ·
                  refine ⟨35105608872411627922381781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23403739248274418614921187 35105608872411627922381781)
                  ·
                    refine ⟨822787707947147529430823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 35105608872411627922381781 822787707947147529430823)
                    ·
                      rfl

theorem cell22_2403560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 2, 1, 1, 7].length) (baseStart_2403560 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2403560 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2403560 prefixEnd_2403560 := by exact prefixLift 2403560
  have htrace : WordTrace (prefixWord ++ tailWord_2403560) baseStart_2403560 baseEnd_2403560 := by
    simpa [prefixWord, tailWord_2403560, baseEnd_2403560] using wordTrace_append hprefix tailTrace_2403560
  have hstable : (prefixWord ++ tailWord_2403560).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2403560).length < 2 ^ (prefixWord ++ tailWord_2403560).sum := by decide
  have hdescent : baseEnd_2403560 < baseStart_2403560 := by decide
  rcases family_descends (prefixWord ++ tailWord_2403560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2403562 : List Nat := [3, 1, 3, 1, 1, 4, 1, 3, 5]
def baseStart_2403562 : Nat := 118140960795 + 2403562 * 2 ^ 59
def prefixEnd_2403562 : Nat := 4983230072969 + 3 ^ 40 * 2403562 * 2
def baseEnd_2403562 : Nat := 274262797529340063626939

theorem tailTrace_2403562 : CollatzResearch.WordTrace tailWord_2403562 prefixEnd_2403562 274262797529340063626939 := by
  unfold tailWord_2403562
  simp only [CollatzResearch.WordTrace]
  refine ⟨21916277029578211138369235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58443405412208563035651293 21916277029578211138369235)
  ·
    refine ⟨32874415544367316707553853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21916277029578211138369235 32874415544367316707553853)
    ·
      refine ⟨12327905829137743765332695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32874415544367316707553853 12327905829137743765332695)
      ·
        refine ⟨18491858743706615647999043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12327905829137743765332695 18491858743706615647999043)
        ·
          refine ⟨27737788115559923471998565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18491858743706615647999043 27737788115559923471998565)
          ·
            refine ⟨5200835271667485650999731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27737788115559923471998565 5200835271667485650999731)
            ·
              refine ⟨7801252907501228476499597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5200835271667485650999731 7801252907501228476499597)
              ·
                refine ⟨2925469840312960678687349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7801252907501228476499597 2925469840312960678687349)
                ·
                  refine ⟨274262797529340063626939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2925469840312960678687349 274262797529340063626939)
                  ·
                    rfl

theorem cell22_2403562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 1, 3, 5].length) (baseStart_2403562 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2403562 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2403562 prefixEnd_2403562 := by exact prefixLift 2403562
  have htrace : WordTrace (prefixWord ++ tailWord_2403562) baseStart_2403562 baseEnd_2403562 := by
    simpa [prefixWord, tailWord_2403562, baseEnd_2403562] using wordTrace_append hprefix tailTrace_2403562
  have hstable : (prefixWord ++ tailWord_2403562).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2403562).length < 2 ^ (prefixWord ++ tailWord_2403562).sum := by decide
  have hdescent : baseEnd_2403562 < baseStart_2403562 := by decide
  rcases family_descends (prefixWord ++ tailWord_2403562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2403575 : List Nat := [1, 1, 3, 1, 1, 1, 2, 5, 3, 4]
def baseStart_2403575 : Nat := 118140960795 + 2403575 * 2 ^ 59
def prefixEnd_2403575 : Nat := 4983230072969 + 3 ^ 40 * 2403575 * 2
def baseEnd_2403575 : Nat := 822792842753692490305777

theorem tailTrace_2403575 : CollatzResearch.WordTrace tailWord_2403575 prefixEnd_2403575 822792842753692490305777 := by
  unfold tailWord_2403575
  simp only [CollatzResearch.WordTrace]
  refine ⟨87665582267265747773700179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58443721511510498515800119 87665582267265747773700179)
  ·
    refine ⟨131498373400898621660550269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87665582267265747773700179 131498373400898621660550269)
    ·
      refine ⟨49311890025336983122706351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 131498373400898621660550269 49311890025336983122706351)
      ·
        refine ⟨73967835038005474684059527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49311890025336983122706351 73967835038005474684059527)
        ·
          refine ⟨110951752557008212026089291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73967835038005474684059527 110951752557008212026089291)
          ·
            refine ⟨166427628835512318039133937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 110951752557008212026089291 166427628835512318039133937)
            ·
              refine ⟨124820721626634238529350453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 166427628835512318039133937 124820721626634238529350453)
              ·
                refine ⟨11701942652496959862126605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 124820721626634238529350453 11701942652496959862126605)
                ·
                  refine ⟨4388228494686359948297477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11701942652496959862126605 4388228494686359948297477)
                  ·
                    refine ⟨822792842753692490305777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4388228494686359948297477 822792842753692490305777)
                    ·
                      rfl

theorem cell22_2403575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 5, 3, 4].length) (baseStart_2403575 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2403575 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2403575 prefixEnd_2403575 := by exact prefixLift 2403575
  have htrace : WordTrace (prefixWord ++ tailWord_2403575) baseStart_2403575 baseEnd_2403575 := by
    simpa [prefixWord, tailWord_2403575, baseEnd_2403575] using wordTrace_append hprefix tailTrace_2403575
  have hstable : (prefixWord ++ tailWord_2403575).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2403575).length < 2 ^ (prefixWord ++ tailWord_2403575).sum := by decide
  have hdescent : baseEnd_2403575 < baseStart_2403575 := by decide
  rcases family_descends (prefixWord ++ tailWord_2403575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2403605 : List Nat := [1, 3, 2, 1, 2, 1, 1, 1, 5, 5]
def baseStart_2403605 : Nat := 118140960795 + 2403605 * 2 ^ 59
def prefixEnd_2403605 : Nat := 4983230072969 + 3 ^ 40 * 2403605 * 2
def baseEnd_2403605 : Nat := 822803112366782412055685

theorem tailTrace_2403605 : CollatzResearch.WordTrace tailWord_2403605 prefixEnd_2403605 822803112366782412055685 := by
  unfold tailWord_2403605
  simp only [CollatzResearch.WordTrace]
  refine ⟨87666676457157062897292269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58444450971438041931528179 87666676457157062897292269)
  ·
    refine ⟨32875003671433898586484601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 87666676457157062897292269 32875003671433898586484601)
    ·
      refine ⟨24656252753575423939863451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32875003671433898586484601 24656252753575423939863451)
      ·
        refine ⟨36984379130363135909795177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24656252753575423939863451 36984379130363135909795177)
        ·
          refine ⟨27738284347772351932346383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36984379130363135909795177 27738284347772351932346383)
          ·
            refine ⟨41607426521658527898519575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27738284347772351932346383 41607426521658527898519575)
            ·
              refine ⟨62411139782487791847779363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41607426521658527898519575 62411139782487791847779363)
              ·
                refine ⟨93616709673731687771669045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62411139782487791847779363 93616709673731687771669045)
                ·
                  refine ⟨8776566531912345728593973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 93616709673731687771669045 8776566531912345728593973)
                  ·
                    refine ⟨822803112366782412055685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8776566531912345728593973 822803112366782412055685)
                    ·
                      rfl

theorem cell22_2403605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 1, 5, 5].length) (baseStart_2403605 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2403605 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2403605 prefixEnd_2403605 := by exact prefixLift 2403605
  have htrace : WordTrace (prefixWord ++ tailWord_2403605) baseStart_2403605 baseEnd_2403605 := by
    simpa [prefixWord, tailWord_2403605, baseEnd_2403605] using wordTrace_append hprefix tailTrace_2403605
  have hstable : (prefixWord ++ tailWord_2403605).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2403605).length < 2 ^ (prefixWord ++ tailWord_2403605).sum := by decide
  have hdescent : baseEnd_2403605 < baseStart_2403605 := by decide
  rcases family_descends (prefixWord ++ tailWord_2403605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2403637 : List Nat := [1, 3, 3, 1, 2, 3, 1, 1, 1, 6]
def baseStart_2403637 : Nat := 118140960795 + 2403637 * 2 ^ 59
def prefixEnd_2403637 : Nat := 4983230072969 + 3 ^ 40 * 2403637 * 2
def baseEnd_2403637 : Nat := 822814066620744995255587

theorem tailTrace_2403637 : CollatzResearch.WordTrace tailWord_2403637 prefixEnd_2403637 822814066620744995255587 := by
  unfold tailWord_2403637
  simp only [CollatzResearch.WordTrace]
  refine ⟨87667843593041132362457165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58445229062027421574971443 87667843593041132362457165)
  ·
    refine ⟨32875441347390424635921437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 87667843593041132362457165 32875441347390424635921437)
    ·
      refine ⟨12328290505271409238470539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32875441347390424635921437 12328290505271409238470539)
      ·
        refine ⟨18492435757907113857705809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12328290505271409238470539 18492435757907113857705809)
        ·
          refine ⟨13869326818430335393279357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18492435757907113857705809 13869326818430335393279357)
          ·
            refine ⟨5200997556911375772479759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13869326818430335393279357 5200997556911375772479759)
            ·
              refine ⟨7801496335367063658719639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5200997556911375772479759 7801496335367063658719639)
              ·
                refine ⟨11702244503050595488079459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7801496335367063658719639 11702244503050595488079459)
                ·
                  refine ⟨17553366754575893232119189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11702244503050595488079459 17553366754575893232119189)
                  ·
                    refine ⟨822814066620744995255587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17553366754575893232119189 822814066620744995255587)
                    ·
                      rfl

theorem cell22_2403637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 1, 1, 1, 6].length) (baseStart_2403637 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2403637 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2403637 prefixEnd_2403637 := by exact prefixLift 2403637
  have htrace : WordTrace (prefixWord ++ tailWord_2403637) baseStart_2403637 baseEnd_2403637 := by
    simpa [prefixWord, tailWord_2403637, baseEnd_2403637] using wordTrace_append hprefix tailTrace_2403637
  have hstable : (prefixWord ++ tailWord_2403637).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2403637).length < 2 ^ (prefixWord ++ tailWord_2403637).sum := by decide
  have hdescent : baseEnd_2403637 < baseStart_2403637 := by decide
  rcases family_descends (prefixWord ++ tailWord_2403637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2403641 : List Nat := [1, 2, 1, 6, 2, 1, 2, 3, 4]
def baseStart_2403641 : Nat := 118140960795 + 2403641 * 2 ^ 59
def prefixEnd_2403641 : Nat := 4983230072969 + 3 ^ 40 * 2403641 * 2
def baseEnd_2403641 : Nat := 274271811967496772718525

theorem tailTrace_2403641 : CollatzResearch.WordTrace tailWord_2403641 prefixEnd_2403641 274271811967496772718525 := by
  unfold tailWord_2403641
  simp only [CollatzResearch.WordTrace]
  refine ⟨87667989485026641045602777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58445326323351094030401851 87667989485026641045602777)
  ·
    refine ⟨65750992113769980784202083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87667989485026641045602777 65750992113769980784202083)
    ·
      refine ⟨98626488170654971176303125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65750992113769980784202083 98626488170654971176303125)
      ·
        refine ⟨4623116632999451773889209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 98626488170654971176303125 4623116632999451773889209)
        ·
          refine ⟨3467337474749588830416907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4623116632999451773889209 3467337474749588830416907)
          ·
            refine ⟨5201006212124383245625361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3467337474749588830416907 5201006212124383245625361)
            ·
              refine ⟨3900754659093287434219021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5201006212124383245625361 3900754659093287434219021)
              ·
                refine ⟨1462782997159982787832133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3900754659093287434219021 1462782997159982787832133)
                ·
                  refine ⟨274271811967496772718525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1462782997159982787832133 274271811967496772718525)
                  ·
                    rfl

theorem cell22_2403641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 2, 3, 4].length) (baseStart_2403641 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2403641 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2403641 prefixEnd_2403641 := by exact prefixLift 2403641
  have htrace : WordTrace (prefixWord ++ tailWord_2403641) baseStart_2403641 baseEnd_2403641 := by
    simpa [prefixWord, tailWord_2403641, baseEnd_2403641] using wordTrace_append hprefix tailTrace_2403641
  have hstable : (prefixWord ++ tailWord_2403641).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2403641).length < 2 ^ (prefixWord ++ tailWord_2403641).sum := by decide
  have hdescent : baseEnd_2403641 < baseStart_2403641 := by decide
  rcases family_descends (prefixWord ++ tailWord_2403641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2403684 : List Nat := [2, 3, 1, 1, 3, 2, 2, 2, 3, 3]
def baseStart_2403684 : Nat := 118140960795 + 2403684 * 2 ^ 59
def prefixEnd_2403684 : Nat := 4983230072969 + 3 ^ 40 * 2403684 * 2
def baseEnd_2403684 : Nat := 822830155681252539330443

theorem tailTrace_2403684 : CollatzResearch.WordTrace tailWord_2403684 prefixEnd_2403684 822830155681252539330443 := by
  unfold tailWord_2403684
  simp only [CollatzResearch.WordTrace]
  refine ⟨43834778911935429694709053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58446371882580572926278737 43834778911935429694709053)
  ·
    refine ⟨16438042091975786135515895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43834778911935429694709053 16438042091975786135515895)
    ·
      refine ⟨24657063137963679203273843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16438042091975786135515895 24657063137963679203273843)
      ·
        refine ⟨36985594706945518804910765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24657063137963679203273843 36985594706945518804910765)
        ·
          refine ⟨13869598015104569551841537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36985594706945518804910765 13869598015104569551841537)
          ·
            refine ⟨10402198511328427163881153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13869598015104569551841537 10402198511328427163881153)
            ·
              refine ⟨7801648883496320372910865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10402198511328427163881153 7801648883496320372910865)
              ·
                refine ⟨5851236662622240279683149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7801648883496320372910865 5851236662622240279683149)
                ·
                  refine ⟨2194213748483340104881181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5851236662622240279683149 2194213748483340104881181)
                  ·
                    refine ⟨822830155681252539330443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2194213748483340104881181 822830155681252539330443)
                    ·
                      rfl

theorem cell22_2403684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 2, 2, 3, 3].length) (baseStart_2403684 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2403684 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2403684 prefixEnd_2403684 := by exact prefixLift 2403684
  have htrace : WordTrace (prefixWord ++ tailWord_2403684) baseStart_2403684 baseEnd_2403684 := by
    simpa [prefixWord, tailWord_2403684, baseEnd_2403684] using wordTrace_append hprefix tailTrace_2403684
  have hstable : (prefixWord ++ tailWord_2403684).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2403684).length < 2 ^ (prefixWord ++ tailWord_2403684).sum := by decide
  have hdescent : baseEnd_2403684 < baseStart_2403684 := by decide
  rcases family_descends (prefixWord ++ tailWord_2403684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2403761 : List Nat := [1, 2, 2, 4, 1, 1, 5, 1, 1, 4]
def baseStart_2403761 : Nat := 118140960795 + 2403761 * 2 ^ 59
def prefixEnd_2403761 : Nat := 4983230072969 + 3 ^ 40 * 2403761 * 2
def baseEnd_2403761 : Nat := 822856514354850005155207

theorem tailTrace_2403761 : CollatzResearch.WordTrace tailWord_2403761 prefixEnd_2403761 822856514354850005155207 := by
  unfold tailWord_2403761
  simp only [CollatzResearch.WordTrace]
  refine ⟨87672366244591901539971137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58448244163061267693314091 87672366244591901539971137)
  ·
    refine ⟨65754274683443926154978353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87672366244591901539971137 65754274683443926154978353)
    ·
      refine ⟨49315706012582944616233765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65754274683443926154978353 49315706012582944616233765)
      ·
        refine ⟨9246694877359302115543831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 49315706012582944616233765 9246694877359302115543831)
        ·
          refine ⟨13870042316038953173315747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9246694877359302115543831 13870042316038953173315747)
          ·
            refine ⟨20805063474058429759973621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13870042316038953173315747 20805063474058429759973621)
            ·
              refine ⟨1950474700692977789997527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 20805063474058429759973621 1950474700692977789997527)
              ·
                refine ⟨2925712051039466684996291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1950474700692977789997527 2925712051039466684996291)
                ·
                  refine ⟨4388568076559200027494437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2925712051039466684996291 4388568076559200027494437)
                  ·
                    refine ⟨822856514354850005155207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4388568076559200027494437 822856514354850005155207)
                    ·
                      rfl

theorem cell22_2403761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 5, 1, 1, 4].length) (baseStart_2403761 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2403761 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2403761 prefixEnd_2403761 := by exact prefixLift 2403761
  have htrace : WordTrace (prefixWord ++ tailWord_2403761) baseStart_2403761 baseEnd_2403761 := by
    simpa [prefixWord, tailWord_2403761, baseEnd_2403761] using wordTrace_append hprefix tailTrace_2403761
  have hstable : (prefixWord ++ tailWord_2403761).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2403761).length < 2 ^ (prefixWord ++ tailWord_2403761).sum := by decide
  have hdescent : baseEnd_2403761 < baseStart_2403761 := by decide
  rcases family_descends (prefixWord ++ tailWord_2403761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2403776 : List Nat := [2, 1, 1, 2, 3, 1, 6, 2, 4]
def baseStart_2403776 : Nat := 118140960795 + 2403776 * 2 ^ 59
def prefixEnd_2403776 : Nat := 4983230072969 + 3 ^ 40 * 2403776 * 2
def baseEnd_2403776 : Nat := 274287216387131655343387

theorem tailTrace_2403776 : CollatzResearch.WordTrace tailWord_2403776 prefixEnd_2403776 274287216387131655343387 := by
  unfold tailWord_2403776
  simp only [CollatzResearch.WordTrace]
  refine ⟨43836456669768779550883591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58448608893025039401178121 43836456669768779550883591)
  ·
    refine ⟨65754685004653169326325387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43836456669768779550883591 65754685004653169326325387)
    ·
      refine ⟨98632027506979753989488081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65754685004653169326325387 98632027506979753989488081)
      ·
        refine ⟨73974020630234815492116061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 98632027506979753989488081 73974020630234815492116061)
        ·
          refine ⟨27740257736338055809543523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 73974020630234815492116061 27740257736338055809543523)
          ·
            refine ⟨41610386604507083714315285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27740257736338055809543523 41610386604507083714315285)
            ·
              refine ⟨1950486872086269549108529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 41610386604507083714315285 1950486872086269549108529)
              ·
                refine ⟨1462865154064702161831397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1950486872086269549108529 1462865154064702161831397)
                ·
                  refine ⟨274287216387131655343387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1462865154064702161831397 274287216387131655343387)
                  ·
                    rfl

theorem cell22_2403776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 6, 2, 4].length) (baseStart_2403776 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2403776 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2403776 prefixEnd_2403776 := by exact prefixLift 2403776
  have htrace : WordTrace (prefixWord ++ tailWord_2403776) baseStart_2403776 baseEnd_2403776 := by
    simpa [prefixWord, tailWord_2403776, baseEnd_2403776] using wordTrace_append hprefix tailTrace_2403776
  have hstable : (prefixWord ++ tailWord_2403776).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2403776).length < 2 ^ (prefixWord ++ tailWord_2403776).sum := by decide
  have hdescent : baseEnd_2403776 < baseStart_2403776 := by decide
  rcases family_descends (prefixWord ++ tailWord_2403776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2403787 : List Nat := [1, 1, 1, 1, 3, 3, 5, 7]
def baseStart_2403787 : Nat := 118140960795 + 2403787 * 2 ^ 59
def prefixEnd_2403787 : Nat := 4983230072969 + 3 ^ 40 * 2403787 * 2
def baseEnd_2403787 : Nat := 91429490520688289333903

theorem tailTrace_2403787 : CollatzResearch.WordTrace tailWord_2403787 prefixEnd_2403787 91429490520688289333903 := by
  unfold tailWord_2403787
  simp only [CollatzResearch.WordTrace]
  refine ⟨87673314542497707980417615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58448876361665138653611743 87673314542497707980417615)
  ·
    refine ⟨131509971813746561970626423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87673314542497707980417615 131509971813746561970626423)
    ·
      refine ⟨197264957720619842955939635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131509971813746561970626423 197264957720619842955939635)
      ·
        refine ⟨295897436580929764433909453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 197264957720619842955939635 295897436580929764433909453)
        ·
          refine ⟨110961538717848661662716045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 295897436580929764433909453 110961538717848661662716045)
          ·
            refine ⟨41610577019193248123518517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 110961538717848661662716045 41610577019193248123518517)
            ·
              refine ⟨3900991595549367011579861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 41610577019193248123518517 3900991595549367011579861)
              ·
                refine ⟨91429490520688289333903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3900991595549367011579861 91429490520688289333903)
                ·
                  rfl

theorem cell22_2403787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 5, 7].length) (baseStart_2403787 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2403787 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2403787 prefixEnd_2403787 := by exact prefixLift 2403787
  have htrace : WordTrace (prefixWord ++ tailWord_2403787) baseStart_2403787 baseEnd_2403787 := by
    simpa [prefixWord, tailWord_2403787, baseEnd_2403787] using wordTrace_append hprefix tailTrace_2403787
  have hstable : (prefixWord ++ tailWord_2403787).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2403787).length < 2 ^ (prefixWord ++ tailWord_2403787).sum := by decide
  have hdescent : baseEnd_2403787 < baseStart_2403787 := by decide
  rcases family_descends (prefixWord ++ tailWord_2403787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2403900 : List Nat := [2, 2, 2, 2, 5, 1, 2, 1, 5]
def baseStart_2403900 : Nat := 118140960795 + 2403900 * 2 ^ 59
def prefixEnd_2403900 : Nat := 4983230072969 + 3 ^ 40 * 2403900 * 2
def baseEnd_2403900 : Nat := 274301365631833325309927

theorem tailTrace_2403900 : CollatzResearch.WordTrace tailWord_2403900 prefixEnd_2403900 274301365631833325309927 := by
  unfold tailWord_2403900
  simp only [CollatzResearch.WordTrace]
  refine ⟨43838717995544164139640577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58451623994058885519520769 43838717995544164139640577)
  ·
    refine ⟨32879038496658123104730433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43838717995544164139640577 32879038496658123104730433)
    ·
      refine ⟨24659278872493592328547825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32879038496658123104730433 24659278872493592328547825)
      ·
        refine ⟨18494459154370194246410869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24659278872493592328547825 18494459154370194246410869)
        ·
          refine ⟨1733855545722205710601019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 18494459154370194246410869 1733855545722205710601019)
          ·
            refine ⟨2600783318583308565901529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1733855545722205710601019 2600783318583308565901529)
            ·
              refine ⟨1950587488937481424426147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2600783318583308565901529 1950587488937481424426147)
              ·
                refine ⟨2925881233406222136639221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1950587488937481424426147 2925881233406222136639221)
                ·
                  refine ⟨274301365631833325309927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2925881233406222136639221 274301365631833325309927)
                  ·
                    rfl

theorem cell22_2403900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 5, 1, 2, 1, 5].length) (baseStart_2403900 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2403900 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2403900 prefixEnd_2403900 := by exact prefixLift 2403900
  have htrace : WordTrace (prefixWord ++ tailWord_2403900) baseStart_2403900 baseEnd_2403900 := by
    simpa [prefixWord, tailWord_2403900, baseEnd_2403900] using wordTrace_append hprefix tailTrace_2403900
  have hstable : (prefixWord ++ tailWord_2403900).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2403900).length < 2 ^ (prefixWord ++ tailWord_2403900).sum := by decide
  have hdescent : baseEnd_2403900 < baseStart_2403900 := by decide
  rcases family_descends (prefixWord ++ tailWord_2403900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2403909 : List Nat := [1, 3, 1, 1, 1, 4, 2, 3, 1, 5]
def baseStart_2403909 : Nat := 118140960795 + 2403909 * 2 ^ 59
def prefixEnd_2403909 : Nat := 4983230072969 + 3 ^ 40 * 2403909 * 2
def baseEnd_2403909 : Nat := 822907177779426952454753

theorem tailTrace_2403909 : CollatzResearch.WordTrace tailWord_2403909 prefixEnd_2403909 822907177779426952454753 := by
  unfold tailWord_2403909
  simp only [CollatzResearch.WordTrace]
  refine ⟨87677764248055722816358781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58451842832037148544239187 87677764248055722816358781)
  ·
    refine ⟨32879161593020896056134543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 87677764248055722816358781 32879161593020896056134543)
    ·
      refine ⟨49318742389531344084201815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32879161593020896056134543 49318742389531344084201815)
      ·
        refine ⟨73978113584297016126302723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49318742389531344084201815 73978113584297016126302723)
        ·
          refine ⟨110967170376445524189454085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73978113584297016126302723 110967170376445524189454085)
          ·
            refine ⟨20806344445583535785522641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 110967170376445524189454085 20806344445583535785522641)
            ·
              refine ⟨15604758334187651839141981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20806344445583535785522641 15604758334187651839141981)
              ·
                refine ⟨5851784375320369439678243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15604758334187651839141981 5851784375320369439678243)
                ·
                  refine ⟨8777676562980554159517365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5851784375320369439678243 8777676562980554159517365)
                  ·
                    refine ⟨822907177779426952454753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8777676562980554159517365 822907177779426952454753)
                    ·
                      rfl

theorem cell22_2403909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 2, 3, 1, 5].length) (baseStart_2403909 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2403909 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2403909 prefixEnd_2403909 := by exact prefixLift 2403909
  have htrace : WordTrace (prefixWord ++ tailWord_2403909) baseStart_2403909 baseEnd_2403909 := by
    simpa [prefixWord, tailWord_2403909, baseEnd_2403909] using wordTrace_append hprefix tailTrace_2403909
  have hstable : (prefixWord ++ tailWord_2403909).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2403909).length < 2 ^ (prefixWord ++ tailWord_2403909).sum := by decide
  have hdescent : baseEnd_2403909 < baseStart_2403909 := by decide
  rcases family_descends (prefixWord ++ tailWord_2403909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2403941 : List Nat := [1, 3, 1, 3, 3, 1, 2, 2, 2, 4]
def baseStart_2403941 : Nat := 118140960795 + 2403941 * 2 ^ 59
def prefixEnd_2403941 : Nat := 4983230072969 + 3 ^ 40 * 2403941 * 2
def baseEnd_2403941 : Nat := 822918132033389535654655

theorem tailTrace_2403941 : CollatzResearch.WordTrace tailWord_2403941 prefixEnd_2403941 822918132033389535654655 := by
  unfold tailWord_2403941
  simp only [CollatzResearch.WordTrace]
  refine ⟨87678931383939792281523677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58452620922626528187682451 87678931383939792281523677)
  ·
    refine ⟨32879599268977422105571379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 87678931383939792281523677 32879599268977422105571379)
    ·
      refine ⟨49319398903466133158357069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32879599268977422105571379 49319398903466133158357069)
      ·
        refine ⟨18494774588799799934383901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49319398903466133158357069 18494774588799799934383901)
        ·
          refine ⟨6935540470799924975393963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18494774588799799934383901 6935540470799924975393963)
          ·
            refine ⟨10403310706199887463090945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6935540470799924975393963 10403310706199887463090945)
            ·
              refine ⟨7802483029649915597318209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10403310706199887463090945 7802483029649915597318209)
              ·
                refine ⟨5851862272237436697988657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7802483029649915597318209 5851862272237436697988657)
                ·
                  refine ⟨4388896704178077523491493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5851862272237436697988657 4388896704178077523491493)
                  ·
                    refine ⟨822918132033389535654655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4388896704178077523491493 822918132033389535654655)
                    ·
                      rfl

theorem cell22_2403941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 2, 2, 2, 4].length) (baseStart_2403941 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2403941 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2403941 prefixEnd_2403941 := by exact prefixLift 2403941
  have htrace : WordTrace (prefixWord ++ tailWord_2403941) baseStart_2403941 baseEnd_2403941 := by
    simpa [prefixWord, tailWord_2403941, baseEnd_2403941] using wordTrace_append hprefix tailTrace_2403941
  have hstable : (prefixWord ++ tailWord_2403941).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2403941).length < 2 ^ (prefixWord ++ tailWord_2403941).sum := by decide
  have hdescent : baseEnd_2403941 < baseStart_2403941 := by decide
  rcases family_descends (prefixWord ++ tailWord_2403941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2404001 : List Nat := [1, 2, 3, 3, 2, 2, 1, 1, 7]
def baseStart_2404001 : Nat := 118140960795 + 2404001 * 2 ^ 59
def prefixEnd_2404001 : Nat := 4983230072969 + 3 ^ 40 * 2404001 * 2
def baseEnd_2404001 : Nat := 274312890419856459718157

theorem tailTrace_2404001 : CollatzResearch.WordTrace tailWord_2404001 prefixEnd_2404001 274312890419856459718157 := by
  unfold tailWord_2404001
  simp only [CollatzResearch.WordTrace]
  refine ⟨87681119763722422528707857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58454079842481615019138571 87681119763722422528707857)
  ·
    refine ⟨65760839822791816896530893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87681119763722422528707857 65760839822791816896530893)
    ·
      refine ⟨24660314933546931336199085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65760839822791816896530893 24660314933546931336199085)
      ·
        refine ⟨9247618100080099251074657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24660314933546931336199085 9247618100080099251074657)
        ·
          refine ⟨6935713575060074438305993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9247618100080099251074657 6935713575060074438305993)
          ·
            refine ⟨5201785181295055828729495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6935713575060074438305993 5201785181295055828729495)
            ·
              refine ⟨7802677771942583743094243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5201785181295055828729495 7802677771942583743094243)
              ·
                refine ⟨11704016657913875614641365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7802677771942583743094243 11704016657913875614641365)
                ·
                  refine ⟨274312890419856459718157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11704016657913875614641365 274312890419856459718157)
                  ·
                    rfl

theorem cell22_2404001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 1, 1, 7].length) (baseStart_2404001 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2404001 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2404001 prefixEnd_2404001 := by exact prefixLift 2404001
  have htrace : WordTrace (prefixWord ++ tailWord_2404001) baseStart_2404001 baseEnd_2404001 := by
    simpa [prefixWord, tailWord_2404001, baseEnd_2404001] using wordTrace_append hprefix tailTrace_2404001
  have hstable : (prefixWord ++ tailWord_2404001).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2404001).length < 2 ^ (prefixWord ++ tailWord_2404001).sum := by decide
  have hdescent : baseEnd_2404001 < baseStart_2404001 := by decide
  rcases family_descends (prefixWord ++ tailWord_2404001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2404114 : List Nat := [3, 2, 4, 1, 1, 3, 2, 2, 4]
def baseStart_2404114 : Nat := 118140960795 + 2404114 * 2 ^ 59
def prefixEnd_2404114 : Nat := 4983230072969 + 3 ^ 40 * 2404114 * 2
def baseEnd_2404114 : Nat := 274325784489624917026375

theorem tailTrace_2404114 : CollatzResearch.WordTrace tailWord_2404114 prefixEnd_2404114 274325784489624917026375 := by
  unfold tailWord_2404114
  simp only [CollatzResearch.WordTrace]
  refine ⟨21921310303078260706892849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58456827474875361885047597 21921310303078260706892849)
  ·
    refine ⟨16440982727308695530169637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21921310303078260706892849 16440982727308695530169637)
    ·
      refine ⟨3082684261370380411906807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16440982727308695530169637 3082684261370380411906807)
      ·
        refine ⟨4624026392055570617860211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3082684261370380411906807 4624026392055570617860211)
        ·
          refine ⟨6936039588083355926790317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4624026392055570617860211 6936039588083355926790317)
          ·
            refine ⟨2601014845531258472546369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6936039588083355926790317 2601014845531258472546369)
            ·
              refine ⟨1950761134148443854409777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2601014845531258472546369 1950761134148443854409777)
              ·
                refine ⟨1463070850611332890807333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1950761134148443854409777 1463070850611332890807333)
                ·
                  refine ⟨274325784489624917026375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1463070850611332890807333 274325784489624917026375)
                  ·
                    rfl

theorem cell22_2404114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 3, 2, 2, 4].length) (baseStart_2404114 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2404114 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2404114 prefixEnd_2404114 := by exact prefixLift 2404114
  have htrace : WordTrace (prefixWord ++ tailWord_2404114) baseStart_2404114 baseEnd_2404114 := by
    simpa [prefixWord, tailWord_2404114, baseEnd_2404114] using wordTrace_append hprefix tailTrace_2404114
  have hstable : (prefixWord ++ tailWord_2404114).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2404114).length < 2 ^ (prefixWord ++ tailWord_2404114).sum := by decide
  have hdescent : baseEnd_2404114 < baseStart_2404114 := by decide
  rcases family_descends (prefixWord ++ tailWord_2404114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2404157 : List Nat := [1, 4, 1, 4, 1, 1, 1, 5, 1, 3]
def baseStart_2404157 : Nat := 118140960795 + 2404157 * 2 ^ 59
def prefixEnd_2404157 : Nat := 4983230072969 + 3 ^ 40 * 2404157 * 2
def baseEnd_2404157 : Nat := 822992073247636972253993

theorem tailTrace_2404157 : CollatzResearch.WordTrace tailWord_2404157 prefixEnd_2404157 822992073247636972253993 := by
  unfold tailWord_2404157
  simp only [CollatzResearch.WordTrace]
  refine ⟨87686809551157261171386725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58457873034104840780924483 87686809551157261171386725)
  ·
    refine ⟨16441276790841986469635011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 87686809551157261171386725 16441276790841986469635011)
    ·
      refine ⟨24661915186262979704452517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16441276790841986469635011 24661915186262979704452517)
      ·
        refine ⟨4624109097424308694584847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24661915186262979704452517 4624109097424308694584847)
        ·
          refine ⟨6936163646136463041877271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4624109097424308694584847 6936163646136463041877271)
          ·
            refine ⟨10404245469204694562815907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6936163646136463041877271 10404245469204694562815907)
            ·
              refine ⟨15606368203807041844223861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10404245469204694562815907 15606368203807041844223861)
              ·
                refine ⟨1463097019106910172895987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15606368203807041844223861 1463097019106910172895987)
                ·
                  refine ⟨2194645528660365259343981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1463097019106910172895987 2194645528660365259343981)
                  ·
                    refine ⟨822992073247636972253993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2194645528660365259343981 822992073247636972253993)
                    ·
                      rfl

theorem cell22_2404157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 1, 5, 1, 3].length) (baseStart_2404157 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2404157 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2404157 prefixEnd_2404157 := by exact prefixLift 2404157
  have htrace : WordTrace (prefixWord ++ tailWord_2404157) baseStart_2404157 baseEnd_2404157 := by
    simpa [prefixWord, tailWord_2404157, baseEnd_2404157] using wordTrace_append hprefix tailTrace_2404157
  have hstable : (prefixWord ++ tailWord_2404157).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2404157).length < 2 ^ (prefixWord ++ tailWord_2404157).sum := by decide
  have hdescent : baseEnd_2404157 < baseStart_2404157 := by decide
  rcases family_descends (prefixWord ++ tailWord_2404157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2404200 : List Nat := [2, 1, 4, 2, 1, 1, 4, 2, 1, 4]
def baseStart_2404200 : Nat := 118140960795 + 2404200 * 2 ^ 59
def prefixEnd_2404200 : Nat := 4983230072969 + 3 ^ 40 * 2404200 * 2
def baseEnd_2404200 : Nat := 823006793026399193428861

theorem tailTrace_2404200 : CollatzResearch.WordTrace tailWord_2404200 prefixEnd_2404200 823006793026399193428861 := by
  unfold tailWord_2404200
  simp only [CollatzResearch.WordTrace]
  refine ⟨43844188945000739757601027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58458918593334319676801369 43844188945000739757601027)
  ·
    refine ⟨65766283417501109636401541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43844188945000739757601027 65766283417501109636401541)
    ·
      refine ⟨12331178140781458056825289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 65766283417501109636401541 12331178140781458056825289)
      ·
        refine ⟨9248383605586093542618967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12331178140781458056825289 9248383605586093542618967)
        ·
          refine ⟨13872575408379140313928451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9248383605586093542618967 13872575408379140313928451)
          ·
            refine ⟨20808863112568710470892677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13872575408379140313928451 20808863112568710470892677)
            ·
              refine ⟨3901661833606633213292377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20808863112568710470892677 3901661833606633213292377)
              ·
                refine ⟨2926246375204974909969283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3901661833606633213292377 2926246375204974909969283)
                ·
                  refine ⟨4389369562807462364953925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2926246375204974909969283 4389369562807462364953925)
                  ·
                    refine ⟨823006793026399193428861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4389369562807462364953925 823006793026399193428861)
                    ·
                      rfl

theorem cell22_2404200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 4, 2, 1, 4].length) (baseStart_2404200 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2404200 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2404200 prefixEnd_2404200 := by exact prefixLift 2404200
  have htrace : WordTrace (prefixWord ++ tailWord_2404200) baseStart_2404200 baseEnd_2404200 := by
    simpa [prefixWord, tailWord_2404200, baseEnd_2404200] using wordTrace_append hprefix tailTrace_2404200
  have hstable : (prefixWord ++ tailWord_2404200).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2404200).length < 2 ^ (prefixWord ++ tailWord_2404200).sum := by decide
  have hdescent : baseEnd_2404200 < baseStart_2404200 := by decide
  rcases family_descends (prefixWord ++ tailWord_2404200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2404213 : List Nat := [1, 3, 4, 1, 1, 1, 2, 1, 3, 5]
def baseStart_2404213 : Nat := 118140960795 + 2404213 * 2 ^ 59
def prefixEnd_2404213 : Nat := 4983230072969 + 3 ^ 40 * 2404213 * 2
def baseEnd_2404213 : Nat := 823011243192071492853821

theorem tailTrace_2404213 : CollatzResearch.WordTrace tailWord_2404213 prefixEnd_2404213 823011243192071492853821 := by
  unfold tailWord_2404213
  simp only [CollatzResearch.WordTrace]
  refine ⟨87688852038954382735425293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58459234692636255156950195 87688852038954382735425293)
  ·
    refine ⟨32883319514607893525784485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 87688852038954382735425293 32883319514607893525784485)
    ·
      refine ⟨6165622408988980036084591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32883319514607893525784485 6165622408988980036084591)
      ·
        refine ⟨9248433613483470054126887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6165622408988980036084591 9248433613483470054126887)
        ·
          refine ⟨13872650420225205081190331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9248433613483470054126887 13872650420225205081190331)
          ·
            refine ⟨20808975630337807621785497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13872650420225205081190331 20808975630337807621785497)
            ·
              refine ⟨15606731722753355716339123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20808975630337807621785497 15606731722753355716339123)
              ·
                refine ⟨23410097584130033574508685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15606731722753355716339123 23410097584130033574508685)
                ·
                  refine ⟨8778786594048762590440757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23410097584130033574508685 8778786594048762590440757)
                  ·
                    refine ⟨823011243192071492853821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8778786594048762590440757 823011243192071492853821)
                    ·
                      rfl

theorem cell22_2404213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 2, 1, 3, 5].length) (baseStart_2404213 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2404213 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2404213 prefixEnd_2404213 := by exact prefixLift 2404213
  have htrace : WordTrace (prefixWord ++ tailWord_2404213) baseStart_2404213 baseEnd_2404213 := by
    simpa [prefixWord, tailWord_2404213, baseEnd_2404213] using wordTrace_append hprefix tailTrace_2404213
  have hstable : (prefixWord ++ tailWord_2404213).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2404213).length < 2 ^ (prefixWord ++ tailWord_2404213).sum := by decide
  have hdescent : baseEnd_2404213 < baseStart_2404213 := by decide
  rcases family_descends (prefixWord ++ tailWord_2404213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2404228 : List Nat := [2, 3, 2, 1, 1, 1, 3, 1, 4, 4]
def baseStart_2404228 : Nat := 118140960795 + 2404228 * 2 ^ 59
def prefixEnd_2404228 : Nat := 4983230072969 + 3 ^ 40 * 2404228 * 2
def baseEnd_2404228 : Nat := 823016377998616453728775

theorem tailTrace_2404228 : CollatzResearch.WordTrace tailWord_2404228 prefixEnd_2404228 823016377998616453728775 := by
  unfold tailWord_2404228
  simp only [CollatzResearch.WordTrace]
  refine ⟨43844699566950020148610669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58459599422600026864814225 43844699566950020148610669)
  ·
    refine ⟨16441762337606257555729001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43844699566950020148610669 16441762337606257555729001)
    ·
      refine ⟨12331321753204693166796751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16441762337606257555729001 12331321753204693166796751)
      ·
        refine ⟨18496982629807039750195127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12331321753204693166796751 18496982629807039750195127)
        ·
          refine ⟨27745473944710559625292691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18496982629807039750195127 27745473944710559625292691)
          ·
            refine ⟨41618210917065839437939037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27745473944710559625292691 41618210917065839437939037)
            ·
              refine ⟨15606829093899689789227139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41618210917065839437939037 15606829093899689789227139)
              ·
                refine ⟨23410243640849534683840709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15606829093899689789227139 23410243640849534683840709)
                ·
                  refine ⟨4389420682659287753220133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23410243640849534683840709 4389420682659287753220133)
                  ·
                    refine ⟨823016377998616453728775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4389420682659287753220133 823016377998616453728775)
                    ·
                      rfl

theorem cell22_2404228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 3, 1, 4, 4].length) (baseStart_2404228 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2404228 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2404228 prefixEnd_2404228 := by exact prefixLift 2404228
  have htrace : WordTrace (prefixWord ++ tailWord_2404228) baseStart_2404228 baseEnd_2404228 := by
    simpa [prefixWord, tailWord_2404228, baseEnd_2404228] using wordTrace_append hprefix tailTrace_2404228
  have hstable : (prefixWord ++ tailWord_2404228).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2404228).length < 2 ^ (prefixWord ++ tailWord_2404228).sum := by decide
  have hdescent : baseEnd_2404228 < baseStart_2404228 := by decide
  rcases family_descends (prefixWord ++ tailWord_2404228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2404232 : List Nat := [2, 1, 3, 3, 4, 1, 1, 1, 6]
def baseStart_2404232 : Nat := 118140960795 + 2404232 * 2 ^ 59
def prefixEnd_2404232 : Nat := 4983230072969 + 3 ^ 40 * 2404232 * 2
def baseEnd_2404232 : Nat := 274339249093453925542921

theorem tailTrace_2404232 : CollatzResearch.WordTrace tailWord_2404232 prefixEnd_2404232 274339249093453925542921 := by
  unfold tailWord_2404232
  simp only [CollatzResearch.WordTrace]
  refine ⟨43844772512942774490183475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58459696683923699320244633 43844772512942774490183475)
  ·
    refine ⟨65767158769414161735275213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43844772512942774490183475 65767158769414161735275213)
    ·
      refine ⟨24662684538530310650728205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65767158769414161735275213 24662684538530310650728205)
      ·
        refine ⟨9248506701948866494023077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24662684538530310650728205 9248506701948866494023077)
        ·
          refine ⟨1734095006615412467629327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9248506701948866494023077 1734095006615412467629327)
          ·
            refine ⟨2601142509923118701443991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1734095006615412467629327 2601142509923118701443991)
            ·
              refine ⟨3901713764884678052165987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2601142509923118701443991 3901713764884678052165987)
              ·
                refine ⟨5852570647327017078248981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3901713764884678052165987 5852570647327017078248981)
                ·
                  refine ⟨274339249093453925542921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5852570647327017078248981 274339249093453925542921)
                  ·
                    rfl

theorem cell22_2404232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 4, 1, 1, 1, 6].length) (baseStart_2404232 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2404232 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2404232 prefixEnd_2404232 := by exact prefixLift 2404232
  have htrace : WordTrace (prefixWord ++ tailWord_2404232) baseStart_2404232 baseEnd_2404232 := by
    simpa [prefixWord, tailWord_2404232, baseEnd_2404232] using wordTrace_append hprefix tailTrace_2404232
  have hstable : (prefixWord ++ tailWord_2404232).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2404232).length < 2 ^ (prefixWord ++ tailWord_2404232).sum := by decide
  have hdescent : baseEnd_2404232 < baseStart_2404232 := by decide
  rcases family_descends (prefixWord ++ tailWord_2404232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2404247 : List Nat := [1, 1, 3, 3, 1, 3, 4, 1, 2, 3]
def baseStart_2404247 : Nat := 118140960795 + 2404247 * 2 ^ 59
def prefixEnd_2404247 : Nat := 4983230072969 + 3 ^ 40 * 2404247 * 2
def baseEnd_2404247 : Nat := 823022882086906737503717

theorem tailTrace_2404247 : CollatzResearch.WordTrace tailWord_2404247 prefixEnd_2404247 823022882086906737503717 := by
  unfold tailWord_2404247
  simp only [CollatzResearch.WordTrace]
  refine ⟨87690092120831206542162995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58460061413887471028108663 87690092120831206542162995)
  ·
    refine ⟨131535138181246809813244493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87690092120831206542162995 131535138181246809813244493)
    ·
      refine ⟨49325676817967553679966685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 131535138181246809813244493 49325676817967553679966685)
      ·
        refine ⟨18497128806737832629987507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49325676817967553679966685 18497128806737832629987507)
        ·
          refine ⟨27745693210106748944981261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18497128806737832629987507 27745693210106748944981261)
          ·
            refine ⟨10404634953790030854367973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27745693210106748944981261 10404634953790030854367973)
            ·
              refine ⟨1950869053835630785193995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10404634953790030854367973 1950869053835630785193995)
              ·
                refine ⟨2926303580753446177790993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1950869053835630785193995 2926303580753446177790993)
                ·
                  refine ⟨2194727685565084633343245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2926303580753446177790993 2194727685565084633343245)
                  ·
                    refine ⟨823022882086906737503717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2194727685565084633343245 823022882086906737503717)
                    ·
                      rfl

theorem cell22_2404247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 4, 1, 2, 3].length) (baseStart_2404247 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2404247 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2404247 prefixEnd_2404247 := by exact prefixLift 2404247
  have htrace : WordTrace (prefixWord ++ tailWord_2404247) baseStart_2404247 baseEnd_2404247 := by
    simpa [prefixWord, tailWord_2404247, baseEnd_2404247] using wordTrace_append hprefix tailTrace_2404247
  have hstable : (prefixWord ++ tailWord_2404247).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2404247).length < 2 ^ (prefixWord ++ tailWord_2404247).sum := by decide
  have hdescent : baseEnd_2404247 < baseStart_2404247 := by decide
  rcases family_descends (prefixWord ++ tailWord_2404247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2404303 : List Nat := [1, 1, 2, 1, 1, 5, 3, 1, 2, 5]
def baseStart_2404303 : Nat := 118140960795 + 2404303 * 2 ^ 59
def prefixEnd_2404303 : Nat := 4983230072969 + 3 ^ 40 * 2404303 * 2
def baseEnd_2404303 : Nat := 823042052031341258103545

theorem tailTrace_2404303 : CollatzResearch.WordTrace tailWord_2404303 prefixEnd_2404303 823042052031341258103545 := by
  unfold tailWord_2404303
  simp only [CollatzResearch.WordTrace]
  refine ⟨87692134608628328106201563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58461423072418885404134375 87692134608628328106201563)
  ·
    refine ⟨131538201912942492159302345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87692134608628328106201563 131538201912942492159302345)
    ·
      refine ⟨98653651434706869119476759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 131538201912942492159302345 98653651434706869119476759)
      ·
        refine ⟨147980477152060303679215139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98653651434706869119476759 147980477152060303679215139)
        ·
          refine ⟨221970715728090455518822709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 147980477152060303679215139 221970715728090455518822709)
          ·
            refine ⟨20809754599508480204889629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 221970715728090455518822709 20809754599508480204889629)
            ·
              refine ⟨7803657974815680076833611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20809754599508480204889629 7803657974815680076833611)
              ·
                refine ⟨11705486962223520115250417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7803657974815680076833611 11705486962223520115250417)
                ·
                  refine ⟨8779115221667640086437813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11705486962223520115250417 8779115221667640086437813)
                  ·
                    refine ⟨823042052031341258103545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8779115221667640086437813 823042052031341258103545)
                    ·
                      rfl

theorem cell22_2404303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 3, 1, 2, 5].length) (baseStart_2404303 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2404303 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2404303 prefixEnd_2404303 := by exact prefixLift 2404303
  have htrace : WordTrace (prefixWord ++ tailWord_2404303) baseStart_2404303 baseEnd_2404303 := by
    simpa [prefixWord, tailWord_2404303, baseEnd_2404303] using wordTrace_append hprefix tailTrace_2404303
  have hstable : (prefixWord ++ tailWord_2404303).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2404303).length < 2 ^ (prefixWord ++ tailWord_2404303).sum := by decide
  have hdescent : baseEnd_2404303 < baseStart_2404303 := by decide
  rcases family_descends (prefixWord ++ tailWord_2404303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2404335 : List Nat := [1, 1, 2, 1, 4, 2, 3, 3, 1, 4]
def baseStart_2404335 : Nat := 118140960795 + 2404335 * 2 ^ 59
def prefixEnd_2404335 : Nat := 4983230072969 + 3 ^ 40 * 2404335 * 2
def baseEnd_2404335 : Nat := 823053006285303841303447

theorem tailTrace_2404335 : CollatzResearch.WordTrace tailWord_2404335 prefixEnd_2404335 823053006285303841303447 := by
  unfold tailWord_2404335
  simp only [CollatzResearch.WordTrace]
  refine ⟨87693301744512397571366459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58462201163008265047577639 87693301744512397571366459)
  ·
    refine ⟨131539952616768596357049689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87693301744512397571366459 131539952616768596357049689)
    ·
      refine ⟨98654964462576447267787267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 131539952616768596357049689 98654964462576447267787267)
      ·
        refine ⟨147982446693864670901680901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98654964462576447267787267 147982446693864670901680901)
        ·
          refine ⟨27746708755099625794065169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 147982446693864670901680901 27746708755099625794065169)
          ·
            refine ⟨20810031566324719345548877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27746708755099625794065169 20810031566324719345548877)
            ·
              refine ⟨7803761837371769754580829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20810031566324719345548877 7803761837371769754580829)
              ·
                refine ⟨2926410689014413657967811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7803761837371769754580829 2926410689014413657967811)
                ·
                  refine ⟨4389616033521620486951717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2926410689014413657967811 4389616033521620486951717)
                  ·
                    refine ⟨823053006285303841303447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4389616033521620486951717 823053006285303841303447)
                    ·
                      rfl

theorem cell22_2404335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 3, 3, 1, 4].length) (baseStart_2404335 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2404335 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2404335 prefixEnd_2404335 := by exact prefixLift 2404335
  have htrace : WordTrace (prefixWord ++ tailWord_2404335) baseStart_2404335 baseEnd_2404335 := by
    simpa [prefixWord, tailWord_2404335, baseEnd_2404335] using wordTrace_append hprefix tailTrace_2404335
  have hstable : (prefixWord ++ tailWord_2404335).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2404335).length < 2 ^ (prefixWord ++ tailWord_2404335).sum := by decide
  have hdescent : baseEnd_2404335 < baseStart_2404335 := by decide
  rcases family_descends (prefixWord ++ tailWord_2404335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2404363 : List Nat := [1, 1, 1, 1, 6, 1, 1, 1, 3, 6]
def baseStart_2404363 : Nat := 118140960795 + 2404363 * 2 ^ 59
def prefixEnd_2404363 : Nat := 4983230072969 + 3 ^ 40 * 2404363 * 2
def baseEnd_2404363 : Nat := 823062591257521101603361

theorem tailTrace_2404363 : CollatzResearch.WordTrace tailWord_2404363 prefixEnd_2404363 823062591257521101603361 := by
  unfold tailWord_2404363
  simp only [CollatzResearch.WordTrace]
  refine ⟨87694322988410958353385743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58462881992273972235590495 87694322988410958353385743)
  ·
    refine ⟨131541484482616437530078615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87694322988410958353385743 131541484482616437530078615)
    ·
      refine ⟨197312226723924656295117923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131541484482616437530078615 197312226723924656295117923)
      ·
        refine ⟨295968340085886984442676885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 197312226723924656295117923 295968340085886984442676885)
        ·
          refine ⟨13873515941525952395750479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 295968340085886984442676885 13873515941525952395750479)
          ·
            refine ⟨20810273912288928593625719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13873515941525952395750479 20810273912288928593625719)
            ·
              refine ⟨31215410868433392890438579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20810273912288928593625719 31215410868433392890438579)
              ·
                refine ⟨46823116302650089335657869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31215410868433392890438579 46823116302650089335657869)
                ·
                  refine ⟨17558668613493783500871701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 46823116302650089335657869 17558668613493783500871701)
                  ·
                    refine ⟨823062591257521101603361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17558668613493783500871701 823062591257521101603361)
                    ·
                      rfl

theorem cell22_2404363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 1, 3, 6].length) (baseStart_2404363 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2404363 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2404363 prefixEnd_2404363 := by exact prefixLift 2404363
  have htrace : WordTrace (prefixWord ++ tailWord_2404363) baseStart_2404363 baseEnd_2404363 := by
    simpa [prefixWord, tailWord_2404363, baseEnd_2404363] using wordTrace_append hprefix tailTrace_2404363
  have hstable : (prefixWord ++ tailWord_2404363).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2404363).length < 2 ^ (prefixWord ++ tailWord_2404363).sum := by decide
  have hdescent : baseEnd_2404363 < baseStart_2404363 := by decide
  rcases family_descends (prefixWord ++ tailWord_2404363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2404380 : List Nat := [2, 2, 3, 1, 3, 1, 2, 1, 1, 6]
def baseStart_2404380 : Nat := 118140960795 + 2404380 * 2 ^ 59
def prefixEnd_2404380 : Nat := 4983230072969 + 3 ^ 40 * 2404380 * 2
def baseEnd_2404380 : Nat := 823068410704938723928309

theorem tailTrace_2404380 : CollatzResearch.WordTrace tailWord_2404380 prefixEnd_2404380 823068410704938723928309 := by
  unfold tailWord_2404380
  simp only [CollatzResearch.WordTrace]
  refine ⟨43847471514674685128377297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58463295352899580171169729 43847471514674685128377297)
  ·
    refine ⟨32885603636006013846282973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43847471514674685128377297 32885603636006013846282973)
    ·
      refine ⟨12332101363502255192356115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32885603636006013846282973 12332101363502255192356115)
      ·
        refine ⟨18498152045253382788534173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12332101363502255192356115 18498152045253382788534173)
        ·
          refine ⟨6936807016970018545700315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18498152045253382788534173 6936807016970018545700315)
          ·
            refine ⟨10405210525455027818550473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6936807016970018545700315 10405210525455027818550473)
            ·
              refine ⟨7803907894091270863912855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10405210525455027818550473 7803907894091270863912855)
              ·
                refine ⟨11705861841136906295869283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7803907894091270863912855 11705861841136906295869283)
                ·
                  refine ⟨17558792761705359443803925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11705861841136906295869283 17558792761705359443803925)
                  ·
                    refine ⟨823068410704938723928309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17558792761705359443803925 823068410704938723928309)
                    ·
                      rfl

theorem cell22_2404380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 2, 1, 1, 6].length) (baseStart_2404380 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2404380 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2404380 prefixEnd_2404380 := by exact prefixLift 2404380
  have htrace : WordTrace (prefixWord ++ tailWord_2404380) baseStart_2404380 baseEnd_2404380 := by
    simpa [prefixWord, tailWord_2404380, baseEnd_2404380] using wordTrace_append hprefix tailTrace_2404380
  have hstable : (prefixWord ++ tailWord_2404380).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2404380).length < 2 ^ (prefixWord ++ tailWord_2404380).sum := by decide
  have hdescent : baseEnd_2404380 < baseStart_2404380 := by decide
  rcases family_descends (prefixWord ++ tailWord_2404380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2404455 : List Nat := [1, 1, 5, 1, 1, 2, 2, 2, 2, 5]
def baseStart_2404455 : Nat := 118140960795 + 2404455 * 2 ^ 59
def prefixEnd_2404455 : Nat := 4983230072969 + 3 ^ 40 * 2404455 * 2
def baseEnd_2404455 : Nat := 823094084737663528303079

theorem tailTrace_2404455 : CollatzResearch.WordTrace tailWord_2404455 prefixEnd_2404455 823094084737663528303079 := by
  unfold tailWord_2404455
  simp only [CollatzResearch.WordTrace]
  refine ⟨87697678504077658065734819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58465119002718438710489879 87697678504077658065734819)
  ·
    refine ⟨131546517756116487098602229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87697678504077658065734819 131546517756116487098602229)
    ·
      refine ⟨12332486039635920665493959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 131546517756116487098602229 12332486039635920665493959)
      ·
        refine ⟨18498729059453880998240939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12332486039635920665493959 18498729059453880998240939)
        ·
          refine ⟨27748093589180821497361409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18498729059453880998240939 27748093589180821497361409)
          ·
            refine ⟨20811070191885616123021057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27748093589180821497361409 20811070191885616123021057)
            ·
              refine ⟨15608302643914212092265793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20811070191885616123021057 15608302643914212092265793)
              ·
                refine ⟨11706226982935659069199345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15608302643914212092265793 11706226982935659069199345)
                ·
                  refine ⟨8779670237201744301899509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11706226982935659069199345 8779670237201744301899509)
                  ·
                    refine ⟨823094084737663528303079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8779670237201744301899509 823094084737663528303079)
                    ·
                      rfl

theorem cell22_2404455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 2, 2, 2, 5].length) (baseStart_2404455 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2404455 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2404455 prefixEnd_2404455 := by exact prefixLift 2404455
  have htrace : WordTrace (prefixWord ++ tailWord_2404455) baseStart_2404455 baseEnd_2404455 := by
    simpa [prefixWord, tailWord_2404455, baseEnd_2404455] using wordTrace_append hprefix tailTrace_2404455
  have hstable : (prefixWord ++ tailWord_2404455).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2404455).length < 2 ^ (prefixWord ++ tailWord_2404455).sum := by decide
  have hdescent : baseEnd_2404455 < baseStart_2404455 := by decide
  rcases family_descends (prefixWord ++ tailWord_2404455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2404485 : List Nat := [1, 3, 1, 1, 5, 1, 1, 1, 8]
def baseStart_2404485 : Nat := 118140960795 + 2404485 * 2 ^ 59
def prefixEnd_2404485 : Nat := 4983230072969 + 3 ^ 40 * 2404485 * 2
def baseEnd_2404485 : Nat := 274368118116917816684329

theorem tailTrace_2404485 : CollatzResearch.WordTrace tailWord_2404485 prefixEnd_2404485 274368118116917816684329 := by
  unfold tailWord_2404485
  simp only [CollatzResearch.WordTrace]
  refine ⟨87698772693968973189326909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58465848462645982126217939 87698772693968973189326909)
  ·
    refine ⟨32887039760238364945997591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 87698772693968973189326909 32887039760238364945997591)
    ·
      refine ⟨49330559640357547418996387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32887039760238364945997591 49330559640357547418996387)
      ·
        refine ⟨73995839460536321128494581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49330559640357547418996387 73995839460536321128494581)
        ·
          refine ⟨6937109949425280105796367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 73995839460536321128494581 6937109949425280105796367)
          ·
            refine ⟨10405664924137920158694551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6937109949425280105796367 10405664924137920158694551)
            ·
              refine ⟨15608497386206880238041827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10405664924137920158694551 15608497386206880238041827)
              ·
                refine ⟨23412746079310320357062741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15608497386206880238041827 23412746079310320357062741)
                ·
                  refine ⟨274368118116917816684329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 23412746079310320357062741 274368118116917816684329)
                  ·
                    rfl

theorem cell22_2404485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 1, 1, 8].length) (baseStart_2404485 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2404485 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2404485 prefixEnd_2404485 := by exact prefixLift 2404485
  have htrace : WordTrace (prefixWord ++ tailWord_2404485) baseStart_2404485 baseEnd_2404485 := by
    simpa [prefixWord, tailWord_2404485, baseEnd_2404485] using wordTrace_append hprefix tailTrace_2404485
  have hstable : (prefixWord ++ tailWord_2404485).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2404485).length < 2 ^ (prefixWord ++ tailWord_2404485).sum := by decide
  have hdescent : baseEnd_2404485 < baseStart_2404485 := by decide
  rcases family_descends (prefixWord ++ tailWord_2404485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2404504 : List Nat := [2, 1, 2, 4, 3, 1, 1, 3, 1, 4]
def baseStart_2404504 : Nat := 118140960795 + 2404504 * 2 ^ 59
def prefixEnd_2404504 : Nat := 4983230072969 + 3 ^ 40 * 2404504 * 2
def baseEnd_2404504 : Nat := 823110858439043733827929

theorem tailTrace_2404504 : CollatzResearch.WordTrace tailWord_2404504 prefixEnd_2404504 823110858439043733827929 := by
  unfold tailWord_2404504
  simp only [CollatzResearch.WordTrace]
  refine ⟨43849732840450069717134283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58466310453933426289512377 43849732840450069717134283)
  ·
    refine ⟨65774599260675104575701425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43849732840450069717134283 65774599260675104575701425)
    ·
      refine ⟨49330949445506328431776069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65774599260675104575701425 49330949445506328431776069)
      ·
        refine ⟨9249553021032436580958013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 49330949445506328431776069 9249553021032436580958013)
        ·
          refine ⟨3468582382887163717859255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9249553021032436580958013 3468582382887163717859255)
          ·
            refine ⟨5202873574330745576788883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3468582382887163717859255 5202873574330745576788883)
            ·
              refine ⟨7804310361496118365183325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5202873574330745576788883 7804310361496118365183325)
              ·
                refine ⟨2926616385561044386943747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7804310361496118365183325 2926616385561044386943747)
                ·
                  refine ⟨4389924578341566580415621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2926616385561044386943747 4389924578341566580415621)
                  ·
                    refine ⟨823110858439043733827929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4389924578341566580415621 823110858439043733827929)
                    ·
                      rfl

theorem cell22_2404504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 1, 3, 1, 4].length) (baseStart_2404504 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2404504 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2404504 prefixEnd_2404504 := by exact prefixLift 2404504
  have htrace : WordTrace (prefixWord ++ tailWord_2404504) baseStart_2404504 baseEnd_2404504 := by
    simpa [prefixWord, tailWord_2404504, baseEnd_2404504] using wordTrace_append hprefix tailTrace_2404504
  have hstable : (prefixWord ++ tailWord_2404504).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2404504).length < 2 ^ (prefixWord ++ tailWord_2404504).sum := by decide
  have hdescent : baseEnd_2404504 < baseStart_2404504 := by decide
  rcases family_descends (prefixWord ++ tailWord_2404504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2404517 : List Nat := [1, 3, 1, 2, 1, 3, 3, 1, 4, 3]
def baseStart_2404517 : Nat := 118140960795 + 2404517 * 2 ^ 59
def prefixEnd_2404517 : Nat := 4983230072969 + 3 ^ 40 * 2404517 * 2
def baseEnd_2404517 : Nat := 823115308604716033252889

theorem tailTrace_2404517 : CollatzResearch.WordTrace tailWord_2404517 prefixEnd_2404517 823115308604716033252889 := by
  unfold tailWord_2404517
  simp only [CollatzResearch.WordTrace]
  refine ⟨87699939829853042654491805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58466626553235361769661203 87699939829853042654491805)
  ·
    refine ⟨32887477436194890995434427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 87699939829853042654491805 32887477436194890995434427)
    ·
      refine ⟨49331216154292336493151641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32887477436194890995434427 49331216154292336493151641)
      ·
        refine ⟨36998412115719252369863731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49331216154292336493151641 36998412115719252369863731)
        ·
          refine ⟨55497618173578878554795597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36998412115719252369863731 55497618173578878554795597)
          ·
            refine ⟨20811606815092079458048349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55497618173578878554795597 20811606815092079458048349)
            ·
              refine ⟨7804352555659529796768131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20811606815092079458048349 7804352555659529796768131)
              ·
                refine ⟨11706528833489294695152197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7804352555659529796768131 11706528833489294695152197)
                ·
                  refine ⟨2194974156279242755341037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11706528833489294695152197 2194974156279242755341037)
                  ·
                    refine ⟨823115308604716033252889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2194974156279242755341037 823115308604716033252889)
                    ·
                      rfl

theorem cell22_2404517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 3, 1, 4, 3].length) (baseStart_2404517 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2404517 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2404517 prefixEnd_2404517 := by exact prefixLift 2404517
  have htrace : WordTrace (prefixWord ++ tailWord_2404517) baseStart_2404517 baseEnd_2404517 := by
    simpa [prefixWord, tailWord_2404517, baseEnd_2404517] using wordTrace_append hprefix tailTrace_2404517
  have hstable : (prefixWord ++ tailWord_2404517).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2404517).length < 2 ^ (prefixWord ++ tailWord_2404517).sum := by decide
  have hdescent : baseEnd_2404517 < baseStart_2404517 := by decide
  rcases family_descends (prefixWord ++ tailWord_2404517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2404519 : List Nat := [1, 1, 6, 2, 2, 1, 2, 1, 6]
def baseStart_2404519 : Nat := 118140960795 + 2404519 * 2 ^ 59
def prefixEnd_2404519 : Nat := 4983230072969 + 3 ^ 40 * 2404519 * 2
def baseEnd_2404519 : Nat := 274371997748529564900961

theorem tailTrace_2404519 : CollatzResearch.WordTrace tailWord_2404519 prefixEnd_2404519 274371997748529564900961 := by
  unfold tailWord_2404519
  simp only [CollatzResearch.WordTrace]
  refine ⟨87700012775845796996064611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58466675183897197997376407 87700012775845796996064611)
  ·
    refine ⟨131550019163768695494096917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87700012775845796996064611 131550019163768695494096917)
    ·
      refine ⟨6166407148301657601285793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 131550019163768695494096917 6166407148301657601285793)
      ·
        refine ⟨4624805361226243200964345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6166407148301657601285793 4624805361226243200964345)
        ·
          refine ⟨3468604020919682400723259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4624805361226243200964345 3468604020919682400723259)
          ·
            refine ⟨5202906031379523601084889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3468604020919682400723259 5202906031379523601084889)
            ·
              refine ⟨3902179523534642700813667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5202906031379523601084889 3902179523534642700813667)
              ·
                refine ⟨5853269285301964051220501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3902179523534642700813667 5853269285301964051220501)
                ·
                  refine ⟨274371997748529564900961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5853269285301964051220501 274371997748529564900961)
                  ·
                    rfl

theorem cell22_2404519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 2, 1, 6].length) (baseStart_2404519 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2404519 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2404519 prefixEnd_2404519 := by exact prefixLift 2404519
  have htrace : WordTrace (prefixWord ++ tailWord_2404519) baseStart_2404519 baseEnd_2404519 := by
    simpa [prefixWord, tailWord_2404519, baseEnd_2404519] using wordTrace_append hprefix tailTrace_2404519
  have hstable : (prefixWord ++ tailWord_2404519).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2404519).length < 2 ^ (prefixWord ++ tailWord_2404519).sum := by decide
  have hdescent : baseEnd_2404519 < baseStart_2404519 := by decide
  rcases family_descends (prefixWord ++ tailWord_2404519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2404530 : List Nat := [3, 2, 1, 1, 1, 3, 2, 9]
def baseStart_2404530 : Nat := 118140960795 + 2404530 * 2 ^ 59
def prefixEnd_2404530 : Nat := 4983230072969 + 3 ^ 40 * 2404530 * 2
def baseEnd_2404530 : Nat := 91457750974487592519761

theorem tailTrace_2404530 : CollatzResearch.WordTrace tailWord_2404530 prefixEnd_2404530 91457750974487592519761 := by
  unfold tailWord_2404530
  simp only [CollatzResearch.WordTrace]
  refine ⟨21925103494701486468678761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58466942652537297249810029 21925103494701486468678761)
  ·
    refine ⟨16443827621026114851509071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21925103494701486468678761 16443827621026114851509071)
    ·
      refine ⟨24665741431539172277263607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16443827621026114851509071 24665741431539172277263607)
      ·
        refine ⟨36998612147308758415895411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24665741431539172277263607 36998612147308758415895411)
        ·
          refine ⟨55497918220963137623843117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36998612147308758415895411 55497918220963137623843117)
          ·
            refine ⟨20811719332861176608941169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55497918220963137623843117 20811719332861176608941169)
            ·
              refine ⟨15608789499645882456705877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20811719332861176608941169 15608789499645882456705877)
              ·
                refine ⟨91457750974487592519761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 15608789499645882456705877 91457750974487592519761)
                ·
                  rfl

theorem cell22_2404530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 2, 9].length) (baseStart_2404530 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2404530 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2404530 prefixEnd_2404530 := by exact prefixLift 2404530
  have htrace : WordTrace (prefixWord ++ tailWord_2404530) baseStart_2404530 baseEnd_2404530 := by
    simpa [prefixWord, tailWord_2404530, baseEnd_2404530] using wordTrace_append hprefix tailTrace_2404530
  have hstable : (prefixWord ++ tailWord_2404530).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2404530).length < 2 ^ (prefixWord ++ tailWord_2404530).sum := by decide
  have hdescent : baseEnd_2404530 < baseStart_2404530 := by decide
  rcases family_descends (prefixWord ++ tailWord_2404530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2404566 : List Nat := [5, 2, 1, 2, 1, 2, 1, 2, 2, 4]
def baseStart_2404566 : Nat := 118140960795 + 2404566 * 2 ^ 59
def prefixEnd_2404566 : Nat := 4983230072969 + 3 ^ 40 * 2404566 * 2
def baseEnd_2404566 : Nat := 823132082306096238777739

theorem tailTrace_2404566 : CollatzResearch.WordTrace tailWord_2404566 prefixEnd_2404566 823132082306096238777739 := by
  unfold tailWord_2404566
  simp only [CollatzResearch.WordTrace]
  refine ⟨5481357937917220251439097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 58467818004450349348683701 5481357937917220251439097)
  ·
    refine ⟨4111018453437915188579323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5481357937917220251439097 4111018453437915188579323)
    ·
      refine ⟨6166527680156872782868985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4111018453437915188579323 6166527680156872782868985)
      ·
        refine ⟨4624895760117654587151739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6166527680156872782868985 4624895760117654587151739)
        ·
          refine ⟨6937343640176481880727609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4624895760117654587151739 6937343640176481880727609)
          ·
            refine ⟨5203007730132361410545707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6937343640176481880727609 5203007730132361410545707)
            ·
              refine ⟨7804511595198542115818561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5203007730132361410545707 7804511595198542115818561)
              ·
                refine ⟨5853383696398906586863921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7804511595198542115818561 5853383696398906586863921)
                ·
                  refine ⟨4390037772299179940147941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5853383696398906586863921 4390037772299179940147941)
                  ·
                    refine ⟨823132082306096238777739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4390037772299179940147941 823132082306096238777739)
                    ·
                      rfl

theorem cell22_2404566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 1, 2, 2, 4].length) (baseStart_2404566 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2404566 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2404566 prefixEnd_2404566 := by exact prefixLift 2404566
  have htrace : WordTrace (prefixWord ++ tailWord_2404566) baseStart_2404566 baseEnd_2404566 := by
    simpa [prefixWord, tailWord_2404566, baseEnd_2404566] using wordTrace_append hprefix tailTrace_2404566
  have hstable : (prefixWord ++ tailWord_2404566).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2404566).length < 2 ^ (prefixWord ++ tailWord_2404566).sum := by decide
  have hdescent : baseEnd_2404566 < baseStart_2404566 := by decide
  rcases family_descends (prefixWord ++ tailWord_2404566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2404652 : List Nat := [2, 2, 1, 1, 1, 3, 3, 3, 1, 5]
def baseStart_2404652 : Nat := 118140960795 + 2404652 * 2 ^ 59
def prefixEnd_2404652 : Nat := 4983230072969 + 3 ^ 40 * 2404652 * 2
def baseEnd_2404652 : Nat := 823161521863620681127475

theorem tailTrace_2404652 : CollatzResearch.WordTrace tailWord_2404652 prefixEnd_2404652 823161521863620681127475 := by
  unfold tailWord_2404652
  simp only [CollatzResearch.WordTrace]
  refine ⟨43852431842181980355328105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58469909122909307140437473 43852431842181980355328105)
  ·
    refine ⟨32889323881636485266496079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43852431842181980355328105 32889323881636485266496079)
    ·
      refine ⟨49333985822454727899744119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32889323881636485266496079 49333985822454727899744119)
      ·
        refine ⟨74000978733682091849616179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49333985822454727899744119 74000978733682091849616179)
        ·
          refine ⟨111001468100523137774424269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74000978733682091849616179 111001468100523137774424269)
          ·
            refine ⟨41625550537696176665409101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 111001468100523137774424269 41625550537696176665409101)
            ·
              refine ⟨15609581451636066249528413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41625550537696176665409101 15609581451636066249528413)
              ·
                refine ⟨5853593044363524843573155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15609581451636066249528413 5853593044363524843573155)
                ·
                  refine ⟨8780389566545287265359733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5853593044363524843573155 8780389566545287265359733)
                  ·
                    refine ⟨823161521863620681127475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8780389566545287265359733 823161521863620681127475)
                    ·
                      rfl

theorem cell22_2404652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 5].length) (baseStart_2404652 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2404652 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2404652 prefixEnd_2404652 := by exact prefixLift 2404652
  have htrace : WordTrace (prefixWord ++ tailWord_2404652) baseStart_2404652 baseEnd_2404652 := by
    simpa [prefixWord, tailWord_2404652, baseEnd_2404652] using wordTrace_append hprefix tailTrace_2404652
  have hstable : (prefixWord ++ tailWord_2404652).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2404652).length < 2 ^ (prefixWord ++ tailWord_2404652).sum := by decide
  have hdescent : baseEnd_2404652 < baseStart_2404652 := by decide
  rcases family_descends (prefixWord ++ tailWord_2404652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2404716 : List Nat := [2, 2, 1, 1, 6, 2, 2, 6]
def baseStart_2404716 : Nat := 118140960795 + 2404716 * 2 ^ 59
def prefixEnd_2404716 : Nat := 4983230072969 + 3 ^ 40 * 2404716 * 2
def baseEnd_2404716 : Nat := 91464825596838427503031

theorem tailTrace_2404716 : CollatzResearch.WordTrace tailWord_2404716 prefixEnd_2404716 91464825596838427503031 := by
  unfold tailWord_2404716
  simp only [CollatzResearch.WordTrace]
  refine ⟨43853598978066049820493001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58471465304088066427324001 43853598978066049820493001)
  ·
    refine ⟨32890199233549537365369751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43853598978066049820493001 32890199233549537365369751)
    ·
      refine ⟨49335298850324306048054627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32890199233549537365369751 49335298850324306048054627)
      ·
        refine ⟨74002948275486459072081941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49335298850324306048054627 74002948275486459072081941)
        ·
          refine ⟨3468888200413427769003841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 74002948275486459072081941 3468888200413427769003841)
          ·
            refine ⟨2601666150310070826752881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3468888200413427769003841 2601666150310070826752881)
            ·
              refine ⟨1951249612732553120064661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2601666150310070826752881 1951249612732553120064661)
              ·
                refine ⟨91464825596838427503031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1951249612732553120064661 91464825596838427503031)
                ·
                  rfl

theorem cell22_2404716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 2, 2, 6].length) (baseStart_2404716 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2404716 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2404716 prefixEnd_2404716 := by exact prefixLift 2404716
  have htrace : WordTrace (prefixWord ++ tailWord_2404716) baseStart_2404716 baseEnd_2404716 := by
    simpa [prefixWord, tailWord_2404716, baseEnd_2404716] using wordTrace_append hprefix tailTrace_2404716
  have hstable : (prefixWord ++ tailWord_2404716).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2404716).length < 2 ^ (prefixWord ++ tailWord_2404716).sum := by decide
  have hdescent : baseEnd_2404716 < baseStart_2404716 := by decide
  rcases family_descends (prefixWord ++ tailWord_2404716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2404744 : List Nat := [2, 1, 3, 3, 1, 1, 2, 4, 5]
def baseStart_2404744 : Nat := 118140960795 + 2404744 * 2 ^ 59
def prefixEnd_2404744 : Nat := 4983230072969 + 3 ^ 40 * 2404744 * 2
def baseEnd_2404744 : Nat := 274397671781254369275731

theorem tailTrace_2404744 : CollatzResearch.WordTrace tailWord_2404744 prefixEnd_2404744 274397671781254369275731 := by
  unfold tailWord_2404744
  simp only [CollatzResearch.WordTrace]
  refine ⟨43854109600015330211502643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58472146133353773615336857 43854109600015330211502643)
  ·
    refine ⟨65781164400022995317253965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43854109600015330211502643 65781164400022995317253965)
    ·
      refine ⟨24667936650008623243970237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65781164400022995317253965 24667936650008623243970237)
      ·
        refine ⟨9250476243753233716488839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24667936650008623243970237 9250476243753233716488839)
        ·
          refine ⟨13875714365629850574733259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9250476243753233716488839 13875714365629850574733259)
          ·
            refine ⟨20813571548444775862099889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13875714365629850574733259 20813571548444775862099889)
            ·
              refine ⟨15610178661333581896574917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20813571548444775862099889 15610178661333581896574917)
              ·
                refine ⟨2926908499000046605607797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15610178661333581896574917 2926908499000046605607797)
                ·
                  refine ⟨274397671781254369275731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2926908499000046605607797 274397671781254369275731)
                  ·
                    rfl

theorem cell22_2404744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 2, 4, 5].length) (baseStart_2404744 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2404744 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2404744 prefixEnd_2404744 := by exact prefixLift 2404744
  have htrace : WordTrace (prefixWord ++ tailWord_2404744) baseStart_2404744 baseEnd_2404744 := by
    simpa [prefixWord, tailWord_2404744, baseEnd_2404744] using wordTrace_append hprefix tailTrace_2404744
  have hstable : (prefixWord ++ tailWord_2404744).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2404744).length < 2 ^ (prefixWord ++ tailWord_2404744).sum := by decide
  have hdescent : baseEnd_2404744 < baseStart_2404744 := by decide
  rcases family_descends (prefixWord ++ tailWord_2404744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2404757 : List Nat := [1, 3, 2, 1, 1, 2, 1, 1, 2, 8]
def baseStart_2404757 : Nat := 118140960795 + 2404757 * 2 ^ 59
def prefixEnd_2404757 : Nat := 4983230072969 + 3 ^ 40 * 2404757 * 2
def baseEnd_2404757 : Nat := 823197465509435407252153

theorem tailTrace_2404757 : CollatzResearch.WordTrace tailWord_2404757 prefixEnd_2404757 823197465509435407252153 := by
  unfold tailWord_2404757
  simp only [CollatzResearch.WordTrace]
  refine ⟨87708693348983563643228525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58472462232655709095485683 87708693348983563643228525)
  ·
    refine ⟨32890760005868836366210697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 87708693348983563643228525 32890760005868836366210697)
    ·
      refine ⟨24668070004401627274658023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32890760005868836366210697 24668070004401627274658023)
      ·
        refine ⟨37002105006602440911987035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24668070004401627274658023 37002105006602440911987035)
        ·
          refine ⟨55503157509903661367980553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37002105006602440911987035 55503157509903661367980553)
          ·
            refine ⟨41627368132427746025985415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55503157509903661367980553 41627368132427746025985415)
            ·
              refine ⟨62441052198641619038978123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41627368132427746025985415 62441052198641619038978123)
              ·
                refine ⟨93661578297962428558467185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62441052198641619038978123 93661578297962428558467185)
                ·
                  refine ⟨70246183723471821418850389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 93661578297962428558467185 70246183723471821418850389)
                  ·
                    refine ⟨823197465509435407252153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 70246183723471821418850389 823197465509435407252153)
                    ·
                      rfl

theorem cell22_2404757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 1, 2, 8].length) (baseStart_2404757 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2404757 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2404757 prefixEnd_2404757 := by exact prefixLift 2404757
  have htrace : WordTrace (prefixWord ++ tailWord_2404757) baseStart_2404757 baseEnd_2404757 := by
    simpa [prefixWord, tailWord_2404757, baseEnd_2404757] using wordTrace_append hprefix tailTrace_2404757
  have hstable : (prefixWord ++ tailWord_2404757).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2404757).length < 2 ^ (prefixWord ++ tailWord_2404757).sum := by decide
  have hdescent : baseEnd_2404757 < baseStart_2404757 := by decide
  rcases family_descends (prefixWord ++ tailWord_2404757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2404821 : List Nat := [1, 3, 2, 3, 1, 3, 2, 1, 1, 5]
def baseStart_2404821 : Nat := 118140960795 + 2404821 * 2 ^ 59
def prefixEnd_2404821 : Nat := 4983230072969 + 3 ^ 40 * 2404821 * 2
def baseEnd_2404821 : Nat := 823219374017360573651957

theorem tailTrace_2404821 : CollatzResearch.WordTrace tailWord_2404821 prefixEnd_2404821 823219374017360573651957 := by
  unfold tailWord_2404821
  simp only [CollatzResearch.WordTrace]
  refine ⟨87711027620751702573558317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58474018413834468382372211 87711027620751702573558317)
  ·
    refine ⟨32891635357781888465084369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 87711027620751702573558317 32891635357781888465084369)
    ·
      refine ⟨24668726518336416348813277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32891635357781888465084369 24668726518336416348813277)
      ·
        refine ⟨9250772444376156130804979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24668726518336416348813277 9250772444376156130804979)
        ·
          refine ⟨13876158666564234196207469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9250772444376156130804979 13876158666564234196207469)
          ·
            refine ⟨5203559499961587823577801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13876158666564234196207469 5203559499961587823577801)
            ·
              refine ⟨3902669624971190867683351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5203559499961587823577801 3902669624971190867683351)
              ·
                refine ⟨5854004437456786301525027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3902669624971190867683351 5854004437456786301525027)
                ·
                  refine ⟨8781006656185179452287541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5854004437456786301525027 8781006656185179452287541)
                  ·
                    refine ⟨823219374017360573651957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8781006656185179452287541 823219374017360573651957)
                    ·
                      rfl

theorem cell22_2404821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 2, 1, 1, 5].length) (baseStart_2404821 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2404821 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2404821 prefixEnd_2404821 := by exact prefixLift 2404821
  have htrace : WordTrace (prefixWord ++ tailWord_2404821) baseStart_2404821 baseEnd_2404821 := by
    simpa [prefixWord, tailWord_2404821, baseEnd_2404821] using wordTrace_append hprefix tailTrace_2404821
  have hstable : (prefixWord ++ tailWord_2404821).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2404821).length < 2 ^ (prefixWord ++ tailWord_2404821).sum := by decide
  have hdescent : baseEnd_2404821 < baseStart_2404821 := by decide
  rcases family_descends (prefixWord ++ tailWord_2404821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2404870 : List Nat := [6, 2, 1, 1, 1, 1, 1, 2, 1, 6]
def baseStart_2404870 : Nat := 118140960795 + 2404870 * 2 ^ 59
def prefixEnd_2404870 : Nat := 4983230072969 + 3 ^ 40 * 2404870 * 2
def baseEnd_2404870 : Nat := 823236147718740779176807

theorem tailTrace_2404870 : CollatzResearch.WordTrace tailWord_2404870 prefixEnd_2404870 823236147718740779176807 := by
  unfold tailWord_2404870
  simp only [CollatzResearch.WordTrace]
  refine ⟨2741025462424193248190377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 58475209865049455961394709 2741025462424193248190377)
  ·
    refine ⟨2055769096818144936142783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2741025462424193248190377 2055769096818144936142783)
    ·
      refine ⟨3083653645227217404214175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2055769096818144936142783 3083653645227217404214175)
      ·
        refine ⟨4625480467840826106321263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3083653645227217404214175 4625480467840826106321263)
        ·
          refine ⟨6938220701761239159481895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4625480467840826106321263 6938220701761239159481895)
          ·
            refine ⟨10407331052641858739222843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6938220701761239159481895 10407331052641858739222843)
            ·
              refine ⟨15610996578962788108834265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10407331052641858739222843 15610996578962788108834265)
              ·
                refine ⟨11708247434222091081625699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15610996578962788108834265 11708247434222091081625699)
                ·
                  refine ⟨17562371151333136622438549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11708247434222091081625699 17562371151333136622438549)
                  ·
                    refine ⟨823236147718740779176807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17562371151333136622438549 823236147718740779176807)
                    ·
                      rfl

theorem cell22_2404870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 1, 2, 1, 6].length) (baseStart_2404870 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2404870 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2404870 prefixEnd_2404870 := by exact prefixLift 2404870
  have htrace : WordTrace (prefixWord ++ tailWord_2404870) baseStart_2404870 baseEnd_2404870 := by
    simpa [prefixWord, tailWord_2404870, baseEnd_2404870] using wordTrace_append hprefix tailTrace_2404870
  have hstable : (prefixWord ++ tailWord_2404870).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2404870).length < 2 ^ (prefixWord ++ tailWord_2404870).sum := by decide
  have hdescent : baseEnd_2404870 < baseStart_2404870 := by decide
  rcases family_descends (prefixWord ++ tailWord_2404870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2405093 : List Nat := [1, 3, 1, 4, 1, 2, 3, 1, 6]
def baseStart_2405093 : Nat := 118140960795 + 2405093 * 2 ^ 59
def prefixEnd_2405093 : Nat := 4983230072969 + 3 ^ 40 * 2405093 * 2
def baseEnd_2405093 : Nat := 274437495058680843617041

theorem tailTrace_2405093 : CollatzResearch.WordTrace tailWord_2405093 prefixEnd_2405093 274437495058680843617041 := by
  unfold tailWord_2405093
  simp only [CollatzResearch.WordTrace]
  refine ⟨87720948275766293027459933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58480632183844195351639955 87720948275766293027459933)
  ·
    refine ⟨32895355603412359885297475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 87720948275766293027459933 32895355603412359885297475)
    ·
      refine ⟨49343033405118539827946213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32895355603412359885297475 49343033405118539827946213)
      ·
        refine ⟨9251818763459726217739915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 49343033405118539827946213 9251818763459726217739915)
        ·
          refine ⟨13877728145189589326609873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9251818763459726217739915 13877728145189589326609873)
          ·
            refine ⟨10408296108892191994957405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13877728145189589326609873 10408296108892191994957405)
            ·
              refine ⟨3903111040834571998109027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10408296108892191994957405 3903111040834571998109027)
              ·
                refine ⟨5854666561251857997163541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3903111040834571998109027 5854666561251857997163541)
                ·
                  refine ⟨274437495058680843617041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5854666561251857997163541 274437495058680843617041)
                  ·
                    rfl

theorem cell22_2405093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 3, 1, 6].length) (baseStart_2405093 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2405093 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2405093 prefixEnd_2405093 := by exact prefixLift 2405093
  have htrace : WordTrace (prefixWord ++ tailWord_2405093) baseStart_2405093 baseEnd_2405093 := by
    simpa [prefixWord, tailWord_2405093, baseEnd_2405093] using wordTrace_append hprefix tailTrace_2405093
  have hstable : (prefixWord ++ tailWord_2405093).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2405093).length < 2 ^ (prefixWord ++ tailWord_2405093).sum := by decide
  have hdescent : baseEnd_2405093 < baseStart_2405093 := by decide
  rcases family_descends (prefixWord ++ tailWord_2405093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2405138 : List Nat := [3, 2, 4, 1, 12]
def baseStart_2405138 : Nat := 118140960795 + 2405138 * 2 ^ 59
def prefixEnd_2405138 : Nat := 4983230072969 + 3 ^ 40 * 2405138 * 2
def baseEnd_2405138 : Nat := 3388180615620071660395

theorem tailTrace_2405138 : CollatzResearch.WordTrace tailWord_2405138 prefixEnd_2405138 3388180615620071660395 := by
  unfold tailWord_2405138
  simp only [CollatzResearch.WordTrace]
  refine ⟨21930647390150816428212017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58481726373735510475232045 21930647390150816428212017)
  ·
    refine ⟨16447985542613112321159013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21930647390150816428212017 16447985542613112321159013)
    ·
      refine ⟨3083997289239958560217315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16447985542613112321159013 3083997289239958560217315)
      ·
        refine ⟨4625995933859937840325973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3083997289239958560217315 4625995933859937840325973)
        ·
          refine ⟨3388180615620071660395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 4625995933859937840325973 3388180615620071660395)
          ·
            rfl

theorem cell22_2405138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 12].length) (baseStart_2405138 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2405138 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2405138 prefixEnd_2405138 := by exact prefixLift 2405138
  have htrace : WordTrace (prefixWord ++ tailWord_2405138) baseStart_2405138 baseEnd_2405138 := by
    simpa [prefixWord, tailWord_2405138, baseEnd_2405138] using wordTrace_append hprefix tailTrace_2405138
  have hstable : (prefixWord ++ tailWord_2405138).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2405138).length < 2 ^ (prefixWord ++ tailWord_2405138).sum := by decide
  have hdescent : baseEnd_2405138 < baseStart_2405138 := by decide
  rcases family_descends (prefixWord ++ tailWord_2405138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2405170 : List Nat := [3, 2, 1, 1, 3, 1, 3, 2, 3, 3]
def baseStart_2405170 : Nat := 118140960795 + 2405170 * 2 ^ 59
def prefixEnd_2405170 : Nat := 4983230072969 + 3 ^ 40 * 2405170 * 2
def baseEnd_2405170 : Nat := 823338843849639996675887

theorem tailTrace_2405170 : CollatzResearch.WordTrace tailWord_2405170 prefixEnd_2405170 823338843849639996675887 := by
  unfold tailWord_2405170
  simp only [CollatzResearch.WordTrace]
  refine ⟨21930939174121833794503241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58482504464324890118675309 21930939174121833794503241)
  ·
    refine ⟨16448204380591375345877431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21930939174121833794503241 16448204380591375345877431)
    ·
      refine ⟨24672306570887063018816147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16448204380591375345877431 24672306570887063018816147)
      ·
        refine ⟨37008459856330594528224221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24672306570887063018816147 37008459856330594528224221)
        ·
          refine ⟨13878172446123972948084083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37008459856330594528224221 13878172446123972948084083)
          ·
            refine ⟨20817258669185959422126125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13878172446123972948084083 20817258669185959422126125)
            ·
              refine ⟨7806472000944734783297297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20817258669185959422126125 7806472000944734783297297)
              ·
                refine ⟨5854854000708551087472973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7806472000944734783297297 5854854000708551087472973)
                ·
                  refine ⟨2195570250265706657802365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5854854000708551087472973 2195570250265706657802365)
                  ·
                    refine ⟨823338843849639996675887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2195570250265706657802365 823338843849639996675887)
                    ·
                      rfl

theorem cell22_2405170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 3, 2, 3, 3].length) (baseStart_2405170 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2405170 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2405170 prefixEnd_2405170 := by exact prefixLift 2405170
  have htrace : WordTrace (prefixWord ++ tailWord_2405170) baseStart_2405170 baseEnd_2405170 := by
    simpa [prefixWord, tailWord_2405170, baseEnd_2405170] using wordTrace_append hprefix tailTrace_2405170
  have hstable : (prefixWord ++ tailWord_2405170).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2405170).length < 2 ^ (prefixWord ++ tailWord_2405170).sum := by decide
  have hdescent : baseEnd_2405170 < baseStart_2405170 := by decide
  rcases family_descends (prefixWord ++ tailWord_2405170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2405172 : List Nat := [2, 5, 1, 1, 3, 1, 3, 6]
def baseStart_2405172 : Nat := 118140960795 + 2405172 * 2 ^ 59
def prefixEnd_2405172 : Nat := 4983230072969 + 3 ^ 40 * 2405172 * 2
def baseEnd_2405172 : Nat := 91482169832279184236209

theorem tailTrace_2405172 : CollatzResearch.WordTrace tailWord_2405172 prefixEnd_2405172 91482169832279184236209 := by
  unfold tailWord_2405172
  simp only [CollatzResearch.WordTrace]
  refine ⟨43861914821240044759792885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58482553094986726346390513 43861914821240044759792885)
  ·
    refine ⟨4112054514491254196230583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 43861914821240044759792885 4112054514491254196230583)
    ·
      refine ⟨6168081771736881294345875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4112054514491254196230583 6168081771736881294345875)
      ·
        refine ⟨9252122657605321941518813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6168081771736881294345875 9252122657605321941518813)
        ·
          refine ⟨3469545996601995728069555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9252122657605321941518813 3469545996601995728069555)
          ·
            refine ⟨5204318994902993592104333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3469545996601995728069555 5204318994902993592104333)
            ·
              refine ⟨1951619623088622597039125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5204318994902993592104333 1951619623088622597039125)
              ·
                refine ⟨91482169832279184236209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1951619623088622597039125 91482169832279184236209)
                ·
                  rfl

theorem cell22_2405172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 3, 6].length) (baseStart_2405172 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2405172 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2405172 prefixEnd_2405172 := by exact prefixLift 2405172
  have htrace : WordTrace (prefixWord ++ tailWord_2405172) baseStart_2405172 baseEnd_2405172 := by
    simpa [prefixWord, tailWord_2405172, baseEnd_2405172] using wordTrace_append hprefix tailTrace_2405172
  have hstable : (prefixWord ++ tailWord_2405172).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2405172).length < 2 ^ (prefixWord ++ tailWord_2405172).sum := by decide
  have hdescent : baseEnd_2405172 < baseStart_2405172 := by decide
  rcases family_descends (prefixWord ++ tailWord_2405172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2405174 : List Nat := [5, 1, 2, 2, 2, 2, 1, 1, 2, 4]
def baseStart_2405174 : Nat := 118140960795 + 2405174 * 2 ^ 59
def prefixEnd_2405174 : Nat := 4983230072969 + 3 ^ 40 * 2405174 * 2
def baseEnd_2405174 : Nat := 823340213131385319575875

theorem tailTrace_2405174 : CollatzResearch.WordTrace tailWord_2405174 prefixEnd_2405174 823340213131385319575875 := by
  unfold tailWord_2405174
  simp only [CollatzResearch.WordTrace]
  refine ⟨5482743911779552741322411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 58482601725648562574105717 5482743911779552741322411)
  ·
    refine ⟨8224115867669329111983617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5482743911779552741322411 8224115867669329111983617)
    ·
      refine ⟨6168086900751996833987713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8224115867669329111983617 6168086900751996833987713)
      ·
        refine ⟨4626065175563997625490785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6168086900751996833987713 4626065175563997625490785)
        ·
          refine ⟨3469548881672998219118089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4626065175563997625490785 3469548881672998219118089)
          ·
            refine ⟨2602161661254748664338567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3469548881672998219118089 2602161661254748664338567)
            ·
              refine ⟨3903242491882122996507851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2602161661254748664338567 3903242491882122996507851)
              ·
                refine ⟨5854863737823184494761777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3903242491882122996507851 5854863737823184494761777)
                ·
                  refine ⟨4391147803367388371071333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5854863737823184494761777 4391147803367388371071333)
                  ·
                    refine ⟨823340213131385319575875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4391147803367388371071333 823340213131385319575875)
                    ·
                      rfl

theorem cell22_2405174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 2, 1, 1, 2, 4].length) (baseStart_2405174 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2405174 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2405174 prefixEnd_2405174 := by exact prefixLift 2405174
  have htrace : WordTrace (prefixWord ++ tailWord_2405174) baseStart_2405174 baseEnd_2405174 := by
    simpa [prefixWord, tailWord_2405174, baseEnd_2405174] using wordTrace_append hprefix tailTrace_2405174
  have hstable : (prefixWord ++ tailWord_2405174).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2405174).length < 2 ^ (prefixWord ++ tailWord_2405174).sum := by decide
  have hdescent : baseEnd_2405174 < baseStart_2405174 := by decide
  rcases family_descends (prefixWord ++ tailWord_2405174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2405187 : List Nat := [1, 1, 1, 3, 1, 4, 4, 3, 1, 3]
def baseStart_2405187 : Nat := 118140960795 + 2405187 * 2 ^ 59
def prefixEnd_2405187 : Nat := 4983230072969 + 3 ^ 40 * 2405187 * 2
def baseEnd_2405187 : Nat := 823344663297057619000835

theorem tailTrace_2405187 : CollatzResearch.WordTrace tailWord_2405187 prefixEnd_2405187 823344663297057619000835 := by
  unfold tailWord_2405187
  simp only [CollatzResearch.WordTrace]
  refine ⟨87724376737425747081381815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58482917824950498054254543 87724376737425747081381815)
  ·
    refine ⟨131586565106138620622072723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87724376737425747081381815 131586565106138620622072723)
    ·
      refine ⟨197379847659207930933109085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131586565106138620622072723 197379847659207930933109085)
      ·
        refine ⟨74017442872202974099915907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 197379847659207930933109085 74017442872202974099915907)
        ·
          refine ⟨111026164308304461149873861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74017442872202974099915907 111026164308304461149873861)
          ·
            refine ⟨20817405807807086465601349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 111026164308304461149873861 20817405807807086465601349)
            ·
              refine ⟨3903263588963828712300253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20817405807807086465601349 3903263588963828712300253)
              ·
                refine ⟨1463723845861435767112595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3903263588963828712300253 1463723845861435767112595)
                ·
                  refine ⟨2195585768792153650668893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1463723845861435767112595 2195585768792153650668893)
                  ·
                    refine ⟨823344663297057619000835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2195585768792153650668893 823344663297057619000835)
                    ·
                      rfl

theorem cell22_2405187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 4, 3, 1, 3].length) (baseStart_2405187 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2405187 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2405187 prefixEnd_2405187 := by exact prefixLift 2405187
  have htrace : WordTrace (prefixWord ++ tailWord_2405187) baseStart_2405187 baseEnd_2405187 := by
    simpa [prefixWord, tailWord_2405187, baseEnd_2405187] using wordTrace_append hprefix tailTrace_2405187
  have hstable : (prefixWord ++ tailWord_2405187).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2405187).length < 2 ^ (prefixWord ++ tailWord_2405187).sum := by decide
  have hdescent : baseEnd_2405187 < baseStart_2405187 := by decide
  rcases family_descends (prefixWord ++ tailWord_2405187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2405228 : List Nat := [2, 2, 1, 1, 4, 1, 1, 4, 6]
def baseStart_2405228 : Nat := 118140960795 + 2405228 * 2 ^ 59
def prefixEnd_2405228 : Nat := 4983230072969 + 3 ^ 40 * 2405228 * 2
def baseEnd_2405228 : Nat := 274452899478315726241903

theorem tailTrace_2405228 : CollatzResearch.WordTrace tailWord_2405228 prefixEnd_2405228 274452899478315726241903 := by
  unfold tailWord_2405228
  simp only [CollatzResearch.WordTrace]
  refine ⟨43862936065138605541812169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58483914753518140722416225 43862936065138605541812169)
  ·
    refine ⟨32897202048853954156359127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43862936065138605541812169 32897202048853954156359127)
    ·
      refine ⟨49345803073280931234538691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32897202048853954156359127 49345803073280931234538691)
      ·
        refine ⟨74018704609921396851808037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49345803073280931234538691 74018704609921396851808037)
        ·
          refine ⟨13878507114360261909714007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 74018704609921396851808037 13878507114360261909714007)
          ·
            refine ⟨20817760671540392864571011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13878507114360261909714007 20817760671540392864571011)
            ·
              refine ⟨31226641007310589296856517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20817760671540392864571011 31226641007310589296856517)
              ·
                refine ⟨5854995188870735493160597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31226641007310589296856517 5854995188870735493160597)
                ·
                  refine ⟨274452899478315726241903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5854995188870735493160597 274452899478315726241903)
                  ·
                    rfl

theorem cell22_2405228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 6].length) (baseStart_2405228 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2405228 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2405228 prefixEnd_2405228 := by exact prefixLift 2405228
  have htrace : WordTrace (prefixWord ++ tailWord_2405228) baseStart_2405228 baseEnd_2405228 := by
    simpa [prefixWord, tailWord_2405228, baseEnd_2405228] using wordTrace_append hprefix tailTrace_2405228
  have hstable : (prefixWord ++ tailWord_2405228).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2405228).length < 2 ^ (prefixWord ++ tailWord_2405228).sum := by decide
  have hdescent : baseEnd_2405228 < baseStart_2405228 := by decide
  rcases family_descends (prefixWord ++ tailWord_2405228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2405243 : List Nat := [1, 1, 1, 1, 1, 5, 2, 4, 1, 5]
def baseStart_2405243 : Nat := 118140960795 + 2405243 * 2 ^ 59
def prefixEnd_2405243 : Nat := 4983230072969 + 3 ^ 40 * 2405243 * 2
def baseEnd_2405243 : Nat := 823363833241492139600663

theorem tailTrace_2405243 : CollatzResearch.WordTrace tailWord_2405243 prefixEnd_2405243 823363833241492139600663 := by
  unfold tailWord_2405243
  simp only [CollatzResearch.WordTrace]
  refine ⟨87726419225222868645420383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58484279483481912430280255 87726419225222868645420383)
  ·
    refine ⟨131589628837834302968130575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87726419225222868645420383 131589628837834302968130575)
    ·
      refine ⟨197384443256751454452195863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131589628837834302968130575 197384443256751454452195863)
      ·
        refine ⟨296076664885127181678293795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 197384443256751454452195863 296076664885127181678293795)
        ·
          refine ⟨444114997327690772517440693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 296076664885127181678293795 444114997327690772517440693)
          ·
            refine ⟨41635780999471009923510065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 444114997327690772517440693 41635780999471009923510065)
            ·
              refine ⟨31226835749603257442632549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41635780999471009923510065 31226835749603257442632549)
              ·
                refine ⟨5855031703050610770493603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31226835749603257442632549 5855031703050610770493603)
                ·
                  refine ⟨8782547554575916155740405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5855031703050610770493603 8782547554575916155740405)
                  ·
                    refine ⟨823363833241492139600663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8782547554575916155740405 823363833241492139600663)
                    ·
                      rfl

theorem cell22_2405243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 4, 1, 5].length) (baseStart_2405243 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2405243 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2405243 prefixEnd_2405243 := by exact prefixLift 2405243
  have htrace : WordTrace (prefixWord ++ tailWord_2405243) baseStart_2405243 baseEnd_2405243 := by
    simpa [prefixWord, tailWord_2405243, baseEnd_2405243] using wordTrace_append hprefix tailTrace_2405243
  have hstable : (prefixWord ++ tailWord_2405243).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2405243).length < 2 ^ (prefixWord ++ tailWord_2405243).sum := by decide
  have hdescent : baseEnd_2405243 < baseStart_2405243 := by decide
  rcases family_descends (prefixWord ++ tailWord_2405243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2405260 : List Nat := [2, 2, 1, 2, 1, 2, 4, 1, 4, 3]
def baseStart_2405260 : Nat := 118140960795 + 2405260 * 2 ^ 59
def prefixEnd_2405260 : Nat := 4983230072969 + 3 ^ 40 * 2405260 * 2
def baseEnd_2405260 : Nat := 823369652688909761925611

theorem tailTrace_2405260 : CollatzResearch.WordTrace tailWord_2405260 prefixEnd_2405260 823369652688909761925611 := by
  unfold tailWord_2405260
  simp only [CollatzResearch.WordTrace]
  refine ⟨43863519633080640274394617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58484692844107520365859489 43863519633080640274394617)
  ·
    refine ⟨32897639724810480205795963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43863519633080640274394617 32897639724810480205795963)
    ·
      refine ⟨49346459587215720308693945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32897639724810480205795963 49346459587215720308693945)
      ·
        refine ⟨37009844690411790231520459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49346459587215720308693945 37009844690411790231520459)
        ·
          refine ⟨55514767035617685347280689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37009844690411790231520459 55514767035617685347280689)
          ·
            refine ⟨41636075276713264010460517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55514767035617685347280689 41636075276713264010460517)
            ·
              refine ⟨7806764114383737001961347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 41636075276713264010460517 7806764114383737001961347)
              ·
                refine ⟨11710146171575605502942021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7806764114383737001961347 11710146171575605502942021)
                ·
                  refine ⟨2195652407170426031801629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11710146171575605502942021 2195652407170426031801629)
                  ·
                    refine ⟨823369652688909761925611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2195652407170426031801629 823369652688909761925611)
                    ·
                      rfl

theorem cell22_2405260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 4, 1, 4, 3].length) (baseStart_2405260 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2405260 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2405260 prefixEnd_2405260 := by exact prefixLift 2405260
  have htrace : WordTrace (prefixWord ++ tailWord_2405260) baseStart_2405260 baseEnd_2405260 := by
    simpa [prefixWord, tailWord_2405260, baseEnd_2405260] using wordTrace_append hprefix tailTrace_2405260
  have hstable : (prefixWord ++ tailWord_2405260).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2405260).length < 2 ^ (prefixWord ++ tailWord_2405260).sum := by decide
  have hdescent : baseEnd_2405260 < baseStart_2405260 := by decide
  rcases family_descends (prefixWord ++ tailWord_2405260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2405277 : List Nat := [1, 4, 2, 1, 2, 1, 3, 3, 2, 3]
def baseStart_2405277 : Nat := 118140960795 + 2405277 * 2 ^ 59
def prefixEnd_2405277 : Nat := 4983230072969 + 3 ^ 40 * 2405277 * 2
def baseEnd_2405277 : Nat := 823375472136327384250559

theorem tailTrace_2405277 : CollatzResearch.WordTrace tailWord_2405277 prefixEnd_2405277 823375472136327384250559 := by
  unfold tailWord_2405277
  simp only [CollatzResearch.WordTrace]
  refine ⟨87727659307099692452158085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58485106204733128301438723 87727659307099692452158085)
  ·
    refine ⟨16448936120081192334779641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 87727659307099692452158085 16448936120081192334779641)
    ·
      refine ⟨12336702090060894251084731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16448936120081192334779641 12336702090060894251084731)
      ·
        refine ⟨18505053135091341376627097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12336702090060894251084731 18505053135091341376627097)
        ·
          refine ⟨13878789851318506032470323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18505053135091341376627097 13878789851318506032470323)
          ·
            refine ⟨20818184776977759048705485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13878789851318506032470323 20818184776977759048705485)
            ·
              refine ⟨7806819291366659643264557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20818184776977759048705485 7806819291366659643264557)
              ·
                refine ⟨2927557234262497366224209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7806819291366659643264557 2927557234262497366224209)
                ·
                  refine ⟨2195667925696873024668157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2927557234262497366224209 2195667925696873024668157)
                  ·
                    refine ⟨823375472136327384250559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2195667925696873024668157 823375472136327384250559)
                    ·
                      rfl

theorem cell22_2405277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 3, 3, 2, 3].length) (baseStart_2405277 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2405277 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2405277 prefixEnd_2405277 := by exact prefixLift 2405277
  have htrace : WordTrace (prefixWord ++ tailWord_2405277) baseStart_2405277 baseEnd_2405277 := by
    simpa [prefixWord, tailWord_2405277, baseEnd_2405277] using wordTrace_append hprefix tailTrace_2405277
  have hstable : (prefixWord ++ tailWord_2405277).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2405277).length < 2 ^ (prefixWord ++ tailWord_2405277).sum := by decide
  have hdescent : baseEnd_2405277 < baseStart_2405277 := by decide
  rcases family_descends (prefixWord ++ tailWord_2405277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2405399 : List Nat := [1, 1, 3, 5, 1, 2, 2, 2, 1, 4]
def baseStart_2405399 : Nat := 118140960795 + 2405399 * 2 ^ 59
def prefixEnd_2405399 : Nat := 4983230072969 + 3 ^ 40 * 2405399 * 2
def baseEnd_2405399 : Nat := 823417235229559732700185

theorem tailTrace_2405399 : CollatzResearch.WordTrace tailWord_2405399 prefixEnd_2405399 823417235229559732700185 := by
  unfold tailWord_2405399
  simp only [CollatzResearch.WordTrace]
  refine ⟨87732109012657707288099251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58488072675105138192066167 87732109012657707288099251)
  ·
    refine ⟨131598163518986560932148877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87732109012657707288099251 131598163518986560932148877)
    ·
      refine ⟨49349311319619960349555829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 131598163518986560932148877 49349311319619960349555829)
      ·
        refine ⟨4626497936214371282770859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 49349311319619960349555829 4626497936214371282770859)
        ·
          refine ⟨6939746904321556924156289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4626497936214371282770859 6939746904321556924156289)
          ·
            refine ⟨5204810178241167693117217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6939746904321556924156289 5204810178241167693117217)
            ·
              refine ⟨3903607633680875769837913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5204810178241167693117217 3903607633680875769837913)
              ·
                refine ⟨2927705725260656827378435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3903607633680875769837913 2927705725260656827378435)
                ·
                  refine ⟨4391558587890985241067653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2927705725260656827378435 4391558587890985241067653)
                  ·
                    refine ⟨823417235229559732700185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4391558587890985241067653 823417235229559732700185)
                    ·
                      rfl

theorem cell22_2405399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 2, 2, 1, 4].length) (baseStart_2405399 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2405399 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2405399 prefixEnd_2405399 := by exact prefixLift 2405399
  have htrace : WordTrace (prefixWord ++ tailWord_2405399) baseStart_2405399 baseEnd_2405399 := by
    simpa [prefixWord, tailWord_2405399, baseEnd_2405399] using wordTrace_append hprefix tailTrace_2405399
  have hstable : (prefixWord ++ tailWord_2405399).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2405399).length < 2 ^ (prefixWord ++ tailWord_2405399).sum := by decide
  have hdescent : baseEnd_2405399 < baseStart_2405399 := by decide
  rcases family_descends (prefixWord ++ tailWord_2405399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2405457 : List Nat := [1, 2, 2, 1, 3, 1, 2, 4, 3, 3]
def baseStart_2405457 : Nat := 118140960795 + 2405457 * 2 ^ 59
def prefixEnd_2405457 : Nat := 4983230072969 + 3 ^ 40 * 2405457 * 2
def baseEnd_2405457 : Nat := 823437089814866914750007

theorem tailTrace_2405457 : CollatzResearch.WordTrace tailWord_2405457 prefixEnd_2405457 823437089814866914750007 := by
  unfold tailWord_2405457
  simp only [CollatzResearch.WordTrace]
  refine ⟨87734224446447583193710625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58489482964298388795807083 87734224446447583193710625)
  ·
    refine ⟨65800668334835687395282969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87734224446447583193710625 65800668334835687395282969)
    ·
      refine ⟨49350501251126765546462227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65800668334835687395282969 49350501251126765546462227)
      ·
        refine ⟨74025751876690148319693341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49350501251126765546462227 74025751876690148319693341)
        ·
          refine ⟨27759656953758805619885003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 74025751876690148319693341 27759656953758805619885003)
          ·
            refine ⟨41639485430638208429827505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27759656953758805619885003 41639485430638208429827505)
            ·
              refine ⟨31229614072978656322370629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41639485430638208429827505 31229614072978656322370629)
              ·
                refine ⟨5855552638683498060444493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31229614072978656322370629 5855552638683498060444493)
                ·
                  refine ⟨2195832239506311772666685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5855552638683498060444493 2195832239506311772666685)
                  ·
                    refine ⟨823437089814866914750007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2195832239506311772666685 823437089814866914750007)
                    ·
                      rfl

theorem cell22_2405457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 4, 3, 3].length) (baseStart_2405457 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2405457 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2405457 prefixEnd_2405457 := by exact prefixLift 2405457
  have htrace : WordTrace (prefixWord ++ tailWord_2405457) baseStart_2405457 baseEnd_2405457 := by
    simpa [prefixWord, tailWord_2405457, baseEnd_2405457] using wordTrace_append hprefix tailTrace_2405457
  have hstable : (prefixWord ++ tailWord_2405457).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2405457).length < 2 ^ (prefixWord ++ tailWord_2405457).sum := by decide
  have hdescent : baseEnd_2405457 < baseStart_2405457 := by decide
  rcases family_descends (prefixWord ++ tailWord_2405457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2405487 : List Nat := [1, 1, 2, 1, 3, 3, 4, 2, 5]
def baseStart_2405487 : Nat := 118140960795 + 2405487 * 2 ^ 59
def prefixEnd_2405487 : Nat := 4983230072969 + 3 ^ 40 * 2405487 * 2
def baseEnd_2405487 : Nat := 274482453142652278833305

theorem tailTrace_2405487 : CollatzResearch.WordTrace tailWord_2405487 prefixEnd_2405487 274482453142652278833305 := by
  unfold tailWord_2405487
  simp only [CollatzResearch.WordTrace]
  refine ⟨87735318636338898317302715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58490212424225932211535143 87735318636338898317302715)
  ·
    refine ⟨131602977954508347475954073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87735318636338898317302715 131602977954508347475954073)
    ·
      refine ⟨98702233465881260606965555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 131602977954508347475954073 98702233465881260606965555)
      ·
        refine ⟨148053350198821890910448333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98702233465881260606965555 148053350198821890910448333)
        ·
          refine ⟨55520006324558209091418125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 148053350198821890910448333 55520006324558209091418125)
          ·
            refine ⟨20820002371709328409281797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55520006324558209091418125 20820002371709328409281797)
            ·
              refine ⟨3903750444695499076740337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20820002371709328409281797 3903750444695499076740337)
              ·
                refine ⟨2927812833521624307555253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3903750444695499076740337 2927812833521624307555253)
                ·
                  refine ⟨274482453142652278833305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2927812833521624307555253 274482453142652278833305)
                  ·
                    rfl

theorem cell22_2405487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 4, 2, 5].length) (baseStart_2405487 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2405487 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2405487 prefixEnd_2405487 := by exact prefixLift 2405487
  have htrace : WordTrace (prefixWord ++ tailWord_2405487) baseStart_2405487 baseEnd_2405487 := by
    simpa [prefixWord, tailWord_2405487, baseEnd_2405487] using wordTrace_append hprefix tailTrace_2405487
  have hstable : (prefixWord ++ tailWord_2405487).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2405487).length < 2 ^ (prefixWord ++ tailWord_2405487).sum := by decide
  have hdescent : baseEnd_2405487 < baseStart_2405487 := by decide
  rcases family_descends (prefixWord ++ tailWord_2405487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2405538 : List Nat := [3, 3, 1, 3, 3, 1, 1, 2, 5]
def baseStart_2405538 : Nat := 118140960795 + 2405538 * 2 ^ 59
def prefixEnd_2405538 : Nat := 4983230072969 + 3 ^ 40 * 2405538 * 2
def baseEnd_2405538 : Nat := 274488272590069901158253

theorem tailTrace_2405538 : CollatzResearch.WordTrace tailWord_2405538 prefixEnd_2405538 274488272590069901158253 := by
  unfold tailWord_2405538
  simp only [CollatzResearch.WordTrace]
  refine ⟨21934294689788533506852317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58491452506102756018272845 21934294689788533506852317)
  ·
    refine ⟨8225360508670700065069619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21934294689788533506852317 8225360508670700065069619)
    ·
      refine ⟨12338040763006050097604429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8225360508670700065069619 12338040763006050097604429)
      ·
        refine ⟨4626765286127268786601661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12338040763006050097604429 4626765286127268786601661)
        ·
          refine ⟨1735036982297725794975623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4626765286127268786601661 1735036982297725794975623)
          ·
            refine ⟨2602555473446588692463435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1735036982297725794975623 2602555473446588692463435)
            ·
              refine ⟨3903833210169883038695153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2602555473446588692463435 3903833210169883038695153)
              ·
                refine ⟨2927874907627412279021365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3903833210169883038695153 2927874907627412279021365)
                ·
                  refine ⟨274488272590069901158253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2927874907627412279021365 274488272590069901158253)
                  ·
                    rfl

theorem cell22_2405538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 3, 1, 1, 2, 5].length) (baseStart_2405538 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2405538 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2405538 prefixEnd_2405538 := by exact prefixLift 2405538
  have htrace : WordTrace (prefixWord ++ tailWord_2405538) baseStart_2405538 baseEnd_2405538 := by
    simpa [prefixWord, tailWord_2405538, baseEnd_2405538] using wordTrace_append hprefix tailTrace_2405538
  have hstable : (prefixWord ++ tailWord_2405538).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2405538).length < 2 ^ (prefixWord ++ tailWord_2405538).sum := by decide
  have hdescent : baseEnd_2405538 < baseStart_2405538 := by decide
  rcases family_descends (prefixWord ++ tailWord_2405538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2405545 : List Nat := [1, 2, 1, 1, 1, 1, 2, 1, 2, 10]
def baseStart_2405545 : Nat := 118140960795 + 2405545 * 2 ^ 59
def prefixEnd_2405545 : Nat := 4983230072969 + 3 ^ 40 * 2405545 * 2
def baseEnd_2405545 : Nat := 823467214013264018549737

theorem tailTrace_2405545 : CollatzResearch.WordTrace tailWord_2405545 prefixEnd_2405545 823467214013264018549737 := by
  unfold tailWord_2405545
  simp only [CollatzResearch.WordTrace]
  refine ⟨87737434070128774222914089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58491622713419182815276059 87737434070128774222914089)
  ·
    refine ⟨65803075552596580667185567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87737434070128774222914089 65803075552596580667185567)
    ·
      refine ⟨98704613328894871000778351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65803075552596580667185567 98704613328894871000778351)
      ·
        refine ⟨148056919993342306501167527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98704613328894871000778351 148056919993342306501167527)
        ·
          refine ⟨222085379990013459751751291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 148056919993342306501167527 222085379990013459751751291)
          ·
            refine ⟨333128069985020189627626937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 222085379990013459751751291 333128069985020189627626937)
            ·
              refine ⟨249846052488765142220720203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 333128069985020189627626937 249846052488765142220720203)
              ·
                refine ⟨374769078733147713331080305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 249846052488765142220720203 374769078733147713331080305)
                ·
                  refine ⟨281076809049860784998310229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 374769078733147713331080305 281076809049860784998310229)
                  ·
                    refine ⟨823467214013264018549737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 281076809049860784998310229 823467214013264018549737)
                    ·
                      rfl

theorem cell22_2405545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 1, 2, 10].length) (baseStart_2405545 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2405545 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2405545 prefixEnd_2405545 := by exact prefixLift 2405545
  have htrace : WordTrace (prefixWord ++ tailWord_2405545) baseStart_2405545 baseEnd_2405545 := by
    simpa [prefixWord, tailWord_2405545, baseEnd_2405545] using wordTrace_append hprefix tailTrace_2405545
  have hstable : (prefixWord ++ tailWord_2405545).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2405545).length < 2 ^ (prefixWord ++ tailWord_2405545).sum := by decide
  have hdescent : baseEnd_2405545 < baseStart_2405545 := by decide
  rcases family_descends (prefixWord ++ tailWord_2405545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2405564 : List Nat := [2, 2, 2, 3, 2, 1, 3, 1, 1, 5]
def baseStart_2405564 : Nat := 118140960795 + 2405564 * 2 ^ 59
def prefixEnd_2405564 : Nat := 4983230072969 + 3 ^ 40 * 2405564 * 2
def baseEnd_2405564 : Nat := 823473718101554302324679

theorem tailTrace_2405564 : CollatzResearch.WordTrace tailWord_2405564 prefixEnd_2405564 823473718101554302324679 := by
  unfold tailWord_2405564
  simp only [CollatzResearch.WordTrace]
  refine ⟨43869063528529970233927873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58492084704706626978570497 43869063528529970233927873)
  ·
    refine ⟨32901797646397477675445905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43869063528529970233927873 32901797646397477675445905)
    ·
      refine ⟨24676348234798108256584429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32901797646397477675445905 24676348234798108256584429)
      ·
        refine ⟨9253630588049290596219161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24676348234798108256584429 9253630588049290596219161)
        ·
          refine ⟨6940222941036967947164371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9253630588049290596219161 6940222941036967947164371)
          ·
            refine ⟨10410334411555451920746557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6940222941036967947164371 10410334411555451920746557)
            ·
              refine ⟨3903875404333294470279959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10410334411555451920746557 3903875404333294470279959)
              ·
                refine ⟨5855813106499941705419939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3903875404333294470279959 5855813106499941705419939)
                ·
                  refine ⟨8783719659749912558129909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5855813106499941705419939 8783719659749912558129909)
                  ·
                    refine ⟨823473718101554302324679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8783719659749912558129909 823473718101554302324679)
                    ·
                      rfl

theorem cell22_2405564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 3, 1, 1, 5].length) (baseStart_2405564 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2405564 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2405564 prefixEnd_2405564 := by exact prefixLift 2405564
  have htrace : WordTrace (prefixWord ++ tailWord_2405564) baseStart_2405564 baseEnd_2405564 := by
    simpa [prefixWord, tailWord_2405564, baseEnd_2405564] using wordTrace_append hprefix tailTrace_2405564
  have hstable : (prefixWord ++ tailWord_2405564).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2405564).length < 2 ^ (prefixWord ++ tailWord_2405564).sum := by decide
  have hdescent : baseEnd_2405564 < baseStart_2405564 := by decide
  rcases family_descends (prefixWord ++ tailWord_2405564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2405615 : List Nat := [1, 1, 2, 1, 8, 1, 2, 1, 2, 3]
def baseStart_2405615 : Nat := 118140960795 + 2405615 * 2 ^ 59
def prefixEnd_2405615 : Nat := 4983230072969 + 3 ^ 40 * 2405615 * 2
def baseEnd_2405615 : Nat := 823491176443807169299523

theorem tailTrace_2405615 : CollatzResearch.WordTrace tailWord_2405615 prefixEnd_2405615 823491176443807169299523 := by
  unfold tailWord_2405615
  simp only [CollatzResearch.WordTrace]
  refine ⟨87739987179875176177962299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58493324786583450785308199 87739987179875176177962299)
  ·
    refine ⟨131609980769812764266943449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87739987179875176177962299 131609980769812764266943449)
    ·
      refine ⟨98707485577359573200207587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 131609980769812764266943449 98707485577359573200207587)
      ·
        refine ⟨148061228366039359800311381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98707485577359573200207587 148061228366039359800311381)
        ·
          refine ⟨1735092519914523747659899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 148061228366039359800311381 1735092519914523747659899)
          ·
            refine ⟨2602638779871785621489849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1735092519914523747659899 2602638779871785621489849)
            ·
              refine ⟨1951979084903839216117387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2602638779871785621489849 1951979084903839216117387)
              ·
                refine ⟨2927968627355758824176081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1951979084903839216117387 2927968627355758824176081)
                ·
                  refine ⟨2195976470516819118132061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2927968627355758824176081 2195976470516819118132061)
                  ·
                    refine ⟨823491176443807169299523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2195976470516819118132061 823491176443807169299523)
                    ·
                      rfl

theorem cell22_2405615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 8, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 8, 1, 2, 1, 2, 3].length) (baseStart_2405615 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2405615 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2405615 prefixEnd_2405615 := by exact prefixLift 2405615
  have htrace : WordTrace (prefixWord ++ tailWord_2405615) baseStart_2405615 baseEnd_2405615 := by
    simpa [prefixWord, tailWord_2405615, baseEnd_2405615] using wordTrace_append hprefix tailTrace_2405615
  have hstable : (prefixWord ++ tailWord_2405615).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2405615).length < 2 ^ (prefixWord ++ tailWord_2405615).sum := by decide
  have hdescent : baseEnd_2405615 < baseStart_2405615 := by decide
  rcases family_descends (prefixWord ++ tailWord_2405615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2405669 : List Nat := [1, 3, 1, 2, 4, 1, 1, 2, 3, 4]
def baseStart_2405669 : Nat := 118140960795 + 2405669 * 2 ^ 59
def prefixEnd_2405669 : Nat := 4983230072969 + 3 ^ 40 * 2405669 * 2
def baseEnd_2405669 : Nat := 823509661747369028449357

theorem tailTrace_2405669 : CollatzResearch.WordTrace tailWord_2405669 prefixEnd_2405669 823509661747369028449357 := by
  unfold tailWord_2405669
  simp only [CollatzResearch.WordTrace]
  refine ⟨87741956721679543400428061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58494637814453028933618707 87741956721679543400428061)
  ·
    refine ⟨32903233770629828775160523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 87741956721679543400428061 32903233770629828775160523)
    ·
      refine ⟨49354850655944743162740785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32903233770629828775160523 49354850655944743162740785)
      ·
        refine ⟨37016137991958557372055589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49354850655944743162740785 37016137991958557372055589)
        ·
          refine ⟨6940525873492229507260423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 37016137991958557372055589 6940525873492229507260423)
          ·
            refine ⟨10410788810238344260890635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6940525873492229507260423 10410788810238344260890635)
            ·
              refine ⟨15616183215357516391335953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10410788810238344260890635 15616183215357516391335953)
              ·
                refine ⟨11712137411518137293501965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15616183215357516391335953 11712137411518137293501965)
                ·
                  refine ⟨4392051529319301485063237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11712137411518137293501965 4392051529319301485063237)
                  ·
                    refine ⟨823509661747369028449357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4392051529319301485063237 823509661747369028449357)
                    ·
                      rfl

theorem cell22_2405669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 1, 2, 3, 4].length) (baseStart_2405669 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2405669 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2405669 prefixEnd_2405669 := by exact prefixLift 2405669
  have htrace : WordTrace (prefixWord ++ tailWord_2405669) baseStart_2405669 baseEnd_2405669 := by
    simpa [prefixWord, tailWord_2405669, baseEnd_2405669] using wordTrace_append hprefix tailTrace_2405669
  have hstable : (prefixWord ++ tailWord_2405669).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2405669).length < 2 ^ (prefixWord ++ tailWord_2405669).sum := by decide
  have hdescent : baseEnd_2405669 < baseStart_2405669 := by decide
  rcases family_descends (prefixWord ++ tailWord_2405669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2405699 : List Nat := [1, 1, 1, 3, 1, 3, 1, 4, 4, 3]
def baseStart_2405699 : Nat := 118140960795 + 2405699 * 2 ^ 59
def prefixEnd_2405699 : Nat := 4983230072969 + 3 ^ 40 * 2405699 * 2
def baseEnd_2405699 : Nat := 823519931360458950199265

theorem tailTrace_2405699 : CollatzResearch.WordTrace tailWord_2405699 prefixEnd_2405699 823519931360458950199265 := by
  unfold tailWord_2405699
  simp only [CollatzResearch.WordTrace]
  refine ⟨87743050911570858524020151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58495367274380572349346767 87743050911570858524020151)
  ·
    refine ⟨131614576367356287786030227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87743050911570858524020151 131614576367356287786030227)
    ·
      refine ⟨197421864551034431679045341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131614576367356287786030227 197421864551034431679045341)
      ·
        refine ⟨74033199206637911879642003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 197421864551034431679045341 74033199206637911879642003)
        ·
          refine ⟨111049798809956867819463005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74033199206637911879642003 111049798809956867819463005)
          ·
            refine ⟨41643674553733825432298627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 111049798809956867819463005 41643674553733825432298627)
            ·
              refine ⟨62465511830600738148447941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41643674553733825432298627 62465511830600738148447941)
              ·
                refine ⟨11712283468237638402833989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 62465511830600738148447941 11712283468237638402833989)
                ·
                  refine ⟨2196053150294557200531373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11712283468237638402833989 2196053150294557200531373)
                  ·
                    refine ⟨823519931360458950199265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2196053150294557200531373 823519931360458950199265)
                    ·
                      rfl

theorem cell22_2405699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 4, 4, 3].length) (baseStart_2405699 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2405699 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2405699 prefixEnd_2405699 := by exact prefixLift 2405699
  have htrace : WordTrace (prefixWord ++ tailWord_2405699) baseStart_2405699 baseEnd_2405699 := by
    simpa [prefixWord, tailWord_2405699, baseEnd_2405699] using wordTrace_append hprefix tailTrace_2405699
  have hstable : (prefixWord ++ tailWord_2405699).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2405699).length < 2 ^ (prefixWord ++ tailWord_2405699).sum := by decide
  have hdescent : baseEnd_2405699 < baseStart_2405699 := by decide
  rcases family_descends (prefixWord ++ tailWord_2405699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2405703 : List Nat := [1, 1, 4, 1, 2, 5, 2, 1, 1, 4]
def baseStart_2405703 : Nat := 118140960795 + 2405703 * 2 ^ 59
def prefixEnd_2405703 : Nat := 4983230072969 + 3 ^ 40 * 2405703 * 2
def baseEnd_2405703 : Nat := 823521300642204273099253

theorem tailTrace_2405703 : CollatzResearch.WordTrace tailWord_2405703 prefixEnd_2405703 823521300642204273099253 := by
  unfold tailWord_2405703
  simp only [CollatzResearch.WordTrace]
  refine ⟨87743196803556367207165763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58495464535704244804777175 87743196803556367207165763)
  ·
    refine ⟨131614795205334550810748645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87743196803556367207165763 131614795205334550810748645)
    ·
      refine ⟨24677774101000228277015371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 131614795205334550810748645 24677774101000228277015371)
      ·
        refine ⟨37016661151500342415523057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24677774101000228277015371 37016661151500342415523057)
        ·
          refine ⟨27762495863625256811642293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37016661151500342415523057 27762495863625256811642293)
          ·
            refine ⟨2602733987214867826091465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 27762495863625256811642293 2602733987214867826091465)
            ·
              refine ⟨1952050490411150869568599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2602733987214867826091465 1952050490411150869568599)
              ·
                refine ⟨2928075735616726304352899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1952050490411150869568599 2928075735616726304352899)
                ·
                  refine ⟨4392113603425089456529349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2928075735616726304352899 4392113603425089456529349)
                  ·
                    refine ⟨823521300642204273099253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4392113603425089456529349 823521300642204273099253)
                    ·
                      rfl

theorem cell22_2405703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 5, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 5, 2, 1, 1, 4].length) (baseStart_2405703 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2405703 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2405703 prefixEnd_2405703 := by exact prefixLift 2405703
  have htrace : WordTrace (prefixWord ++ tailWord_2405703) baseStart_2405703 baseEnd_2405703 := by
    simpa [prefixWord, tailWord_2405703, baseEnd_2405703] using wordTrace_append hprefix tailTrace_2405703
  have hstable : (prefixWord ++ tailWord_2405703).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2405703).length < 2 ^ (prefixWord ++ tailWord_2405703).sum := by decide
  have hdescent : baseEnd_2405703 < baseStart_2405703 := by decide
  rcases family_descends (prefixWord ++ tailWord_2405703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2405712 : List Nat := [2, 1, 1, 1, 1, 5, 11]
def baseStart_2405712 : Nat := 118140960795 + 2405712 * 2 ^ 59
def prefixEnd_2405712 : Nat := 4983230072969 + 3 ^ 40 * 2405712 * 2
def baseEnd_2405712 : Nat := 30500903019486342578675

theorem tailTrace_2405712 : CollatzResearch.WordTrace tailWord_2405712 prefixEnd_2405712 30500903019486342578675 := by
  unfold tailWord_2405712
  simp only [CollatzResearch.WordTrace]
  refine ⟨43871762530261880872121695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58495683373682507829495593 43871762530261880872121695)
  ·
    refine ⟨65807643795392821308182543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43871762530261880872121695 65807643795392821308182543)
    ·
      refine ⟨98711465693089231962273815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65807643795392821308182543 98711465693089231962273815)
      ·
        refine ⟨148067198539633847943410723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98711465693089231962273815 148067198539633847943410723)
        ·
          refine ⟨222100797809450771915116085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 148067198539633847943410723 222100797809450771915116085)
          ·
            refine ⟨20821949794636009867042133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 222100797809450771915116085 20821949794636009867042133)
            ·
              refine ⟨30500903019486342578675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 20821949794636009867042133 30500903019486342578675)
              ·
                rfl

theorem cell22_2405712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 11].length) (baseStart_2405712 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2405712 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2405712 prefixEnd_2405712 := by exact prefixLift 2405712
  have htrace : WordTrace (prefixWord ++ tailWord_2405712) baseStart_2405712 baseEnd_2405712 := by
    simpa [prefixWord, tailWord_2405712, baseEnd_2405712] using wordTrace_append hprefix tailTrace_2405712
  have hstable : (prefixWord ++ tailWord_2405712).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2405712).length < 2 ^ (prefixWord ++ tailWord_2405712).sum := by decide
  have hdescent : baseEnd_2405712 < baseStart_2405712 := by decide
  rcases family_descends (prefixWord ++ tailWord_2405712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2405714 : List Nat := [3, 2, 2, 1, 1, 1, 1, 3, 4, 4]
def baseStart_2405714 : Nat := 118140960795 + 2405714 * 2 ^ 59
def prefixEnd_2405714 : Nat := 4983230072969 + 3 ^ 40 * 2405714 * 2
def baseEnd_2405714 : Nat := 823525066167003911074219

theorem tailTrace_2405714 : CollatzResearch.WordTrace tailWord_2405714 prefixEnd_2405714 823525066167003911074219 := by
  unfold tailWord_2405714
  simp only [CollatzResearch.WordTrace]
  refine ⟨21935899501629129021454049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58495732004344344057210797 21935899501629129021454049)
  ·
    refine ⟨16451924626221846766090537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21935899501629129021454049 16451924626221846766090537)
    ·
      refine ⟨12338943469666385074567903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16451924626221846766090537 12338943469666385074567903)
      ·
        refine ⟨18508415204499577611851855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12338943469666385074567903 18508415204499577611851855)
        ·
          refine ⟨27762622806749366417777783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18508415204499577611851855 27762622806749366417777783)
          ·
            refine ⟨41643934210124049626666675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27762622806749366417777783 41643934210124049626666675)
            ·
              refine ⟨62465901315186074440000013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41643934210124049626666675 62465901315186074440000013)
              ·
                refine ⟨23424712993194777915000005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 62465901315186074440000013 23424712993194777915000005)
                ·
                  refine ⟨4392133686224020859062501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23424712993194777915000005 4392133686224020859062501)
                  ·
                    refine ⟨823525066167003911074219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4392133686224020859062501 823525066167003911074219)
                    ·
                      rfl

theorem cell22_2405714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 3, 4, 4].length) (baseStart_2405714 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2405714 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2405714 prefixEnd_2405714 := by exact prefixLift 2405714
  have htrace : WordTrace (prefixWord ++ tailWord_2405714) baseStart_2405714 baseEnd_2405714 := by
    simpa [prefixWord, tailWord_2405714, baseEnd_2405714] using wordTrace_append hprefix tailTrace_2405714
  have hstable : (prefixWord ++ tailWord_2405714).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2405714).length < 2 ^ (prefixWord ++ tailWord_2405714).sum := by decide
  have hdescent : baseEnd_2405714 < baseStart_2405714 := by decide
  rcases family_descends (prefixWord ++ tailWord_2405714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2405716 : List Nat := [2, 4, 1, 1, 2, 1, 3, 1, 4, 3]
def baseStart_2405716 : Nat := 118140960795 + 2405716 * 2 ^ 59
def prefixEnd_2405716 : Nat := 4983230072969 + 3 ^ 40 * 2405716 * 2
def baseEnd_2405716 : Nat := 823525750807876572524213

theorem tailTrace_2405716 : CollatzResearch.WordTrace tailWord_2405716 prefixEnd_2405716 823525750807876572524213 := by
  unfold tailWord_2405716
  simp only [CollatzResearch.WordTrace]
  refine ⟨43871835476254635213694501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58495780635006180284926001 43871835476254635213694501)
  ·
    refine ⟨8225969151797744102567719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 43871835476254635213694501 8225969151797744102567719)
    ·
      refine ⟨12338953727696616153851579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8225969151797744102567719 12338953727696616153851579)
      ·
        refine ⟨18508430591544924230777369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12338953727696616153851579 18508430591544924230777369)
        ·
          refine ⟨13881322943658693173083027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18508430591544924230777369 13881322943658693173083027)
          ·
            refine ⟨20821984415488039759624541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13881322943658693173083027 20821984415488039759624541)
            ·
              refine ⟨7808244155808014909859203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20821984415488039759624541 7808244155808014909859203)
              ·
                refine ⟨11712366233712022364788805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7808244155808014909859203 11712366233712022364788805)
                ·
                  refine ⟨2196068668821004193397901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11712366233712022364788805 2196068668821004193397901)
                  ·
                    refine ⟨823525750807876572524213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2196068668821004193397901 823525750807876572524213)
                    ·
                      rfl

theorem cell22_2405716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 3, 1, 4, 3].length) (baseStart_2405716 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2405716 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2405716 prefixEnd_2405716 := by exact prefixLift 2405716
  have htrace : WordTrace (prefixWord ++ tailWord_2405716) baseStart_2405716 baseEnd_2405716 := by
    simpa [prefixWord, tailWord_2405716, baseEnd_2405716] using wordTrace_append hprefix tailTrace_2405716
  have hstable : (prefixWord ++ tailWord_2405716).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2405716).length < 2 ^ (prefixWord ++ tailWord_2405716).sum := by decide
  have hdescent : baseEnd_2405716 < baseStart_2405716 := by decide
  rcases family_descends (prefixWord ++ tailWord_2405716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2405733 : List Nat := [1, 3, 1, 3, 1, 2, 5, 1, 2, 3]
def baseStart_2405733 : Nat := 118140960795 + 2405733 * 2 ^ 59
def prefixEnd_2405733 : Nat := 4983230072969 + 3 ^ 40 * 2405733 * 2
def baseEnd_2405733 : Nat := 823531570255294194849161

theorem tailTrace_2405733 : CollatzResearch.WordTrace tailWord_2405733 prefixEnd_2405733 823531570255294194849161 := by
  unfold tailWord_2405733
  simp only [CollatzResearch.WordTrace]
  refine ⟨87744290993447682330757853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58496193995631788220505235 87744290993447682330757853)
  ·
    refine ⟨32904109122542880874034195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 87744290993447682330757853 32904109122542880874034195)
    ·
      refine ⟨49356163683814321311051293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32904109122542880874034195 49356163683814321311051293)
      ·
        refine ⟨18508561381430370491644235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49356163683814321311051293 18508561381430370491644235)
        ·
          refine ⟨27762842072145555737466353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18508561381430370491644235 27762842072145555737466353)
          ·
            refine ⟨20822131554109166803099765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27762842072145555737466353 20822131554109166803099765)
            ·
              refine ⟨1952074833197734387790603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 20822131554109166803099765 1952074833197734387790603)
              ·
                refine ⟨2928112249796601581685905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1952074833197734387790603 2928112249796601581685905)
                ·
                  refine ⟨2196084187347451186264429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2928112249796601581685905 2196084187347451186264429)
                  ·
                    refine ⟨823531570255294194849161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2196084187347451186264429 823531570255294194849161)
                    ·
                      rfl

theorem cell22_2405733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 5, 1, 2, 3].length) (baseStart_2405733 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2405733 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2405733 prefixEnd_2405733 := by exact prefixLift 2405733
  have htrace : WordTrace (prefixWord ++ tailWord_2405733) baseStart_2405733 baseEnd_2405733 := by
    simpa [prefixWord, tailWord_2405733, baseEnd_2405733] using wordTrace_append hprefix tailTrace_2405733
  have hstable : (prefixWord ++ tailWord_2405733).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2405733).length < 2 ^ (prefixWord ++ tailWord_2405733).sum := by decide
  have hdescent : baseEnd_2405733 < baseStart_2405733 := by decide
  rcases family_descends (prefixWord ++ tailWord_2405733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2405791 : List Nat := [1, 1, 2, 5, 1, 3, 1, 3, 5]
def baseStart_2405791 : Nat := 118140960795 + 2405791 * 2 ^ 59
def prefixEnd_2405791 : Nat := 4983230072969 + 3 ^ 40 * 2405791 * 2
def baseEnd_2405791 : Nat := 274517141613533792299661

theorem tailTrace_2405791 : CollatzResearch.WordTrace tailWord_2405791 prefixEnd_2405791 274517141613533792299661 := by
  unfold tailWord_2405791
  simp only [CollatzResearch.WordTrace]
  refine ⟨87746406427237558236369227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58497604284825038824246151 87746406427237558236369227)
  ·
    refine ⟨131619609640856337354553841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87746406427237558236369227 131619609640856337354553841)
    ·
      refine ⟨98714707230642253015915381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 131619609640856337354553841 98714707230642253015915381)
      ·
        refine ⟨9254503802872711220242067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 98714707230642253015915381 9254503802872711220242067)
        ·
          refine ⟨13881755704309066830363101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9254503802872711220242067 13881755704309066830363101)
          ·
            refine ⟨5205658389115900061386163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13881755704309066830363101 5205658389115900061386163)
            ·
              refine ⟨7808487583673850092079245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5205658389115900061386163 7808487583673850092079245)
              ·
                refine ⟨2928182843877693784529717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7808487583673850092079245 2928182843877693784529717)
                ·
                  refine ⟨274517141613533792299661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2928182843877693784529717 274517141613533792299661)
                  ·
                    rfl

theorem cell22_2405791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 1, 3, 5].length) (baseStart_2405791 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2405791 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2405791 prefixEnd_2405791 := by exact prefixLift 2405791
  have htrace : WordTrace (prefixWord ++ tailWord_2405791) baseStart_2405791 baseEnd_2405791 := by
    simpa [prefixWord, tailWord_2405791, baseEnd_2405791] using wordTrace_append hprefix tailTrace_2405791
  have hstable : (prefixWord ++ tailWord_2405791).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2405791).length < 2 ^ (prefixWord ++ tailWord_2405791).sum := by decide
  have hdescent : baseEnd_2405791 < baseStart_2405791 := by decide
  rcases family_descends (prefixWord ++ tailWord_2405791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2405885 : List Nat := [1, 4, 1, 1, 1, 6, 1, 2, 2, 3]
def baseStart_2405885 : Nat := 118140960795 + 2405885 * 2 ^ 59
def prefixEnd_2405885 : Nat := 4983230072969 + 3 ^ 40 * 2405885 * 2
def baseEnd_2405885 : Nat := 823583602961616465048695

theorem tailTrace_2405885 : CollatzResearch.WordTrace tailWord_2405885 prefixEnd_2405885 823583602961616465048695 := by
  unfold tailWord_2405885
  simp only [CollatzResearch.WordTrace]
  refine ⟨87749834888897012290291109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58499889925931341526860739 87749834888897012290291109)
  ·
    refine ⟨16453094041668189804429583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 87749834888897012290291109 16453094041668189804429583)
    ·
      refine ⟨24679641062502284706644375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16453094041668189804429583 24679641062502284706644375)
      ·
        refine ⟨37019461593753427059966563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24679641062502284706644375 37019461593753427059966563)
        ·
          refine ⟨55529192390630140589949845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37019461593753427059966563 55529192390630140589949845)
          ·
            refine ⟨2602930893310787840153899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 55529192390630140589949845 2602930893310787840153899)
            ·
              refine ⟨3904396339966181760230849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2602930893310787840153899 3904396339966181760230849)
              ·
                refine ⟨2928297254974636320173137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3904396339966181760230849 2928297254974636320173137)
                ·
                  refine ⟨2196222941230977240129853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2928297254974636320173137 2196222941230977240129853)
                  ·
                    refine ⟨823583602961616465048695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2196222941230977240129853 823583602961616465048695)
                    ·
                      rfl

theorem cell22_2405885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 6, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 6, 1, 2, 2, 3].length) (baseStart_2405885 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2405885 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2405885 prefixEnd_2405885 := by exact prefixLift 2405885
  have htrace : WordTrace (prefixWord ++ tailWord_2405885) baseStart_2405885 baseEnd_2405885 := by
    simpa [prefixWord, tailWord_2405885, baseEnd_2405885] using wordTrace_append hprefix tailTrace_2405885
  have hstable : (prefixWord ++ tailWord_2405885).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2405885).length < 2 ^ (prefixWord ++ tailWord_2405885).sum := by decide
  have hdescent : baseEnd_2405885 < baseStart_2405885 := by decide
  rcases family_descends (prefixWord ++ tailWord_2405885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2405902 : List Nat := [4, 1, 1, 2, 4, 1, 3, 1, 2, 3]
def baseStart_2405902 : Nat := 118140960795 + 2405902 * 2 ^ 59
def prefixEnd_2405902 : Nat := 4983230072969 + 3 ^ 40 * 2405902 * 2
def baseEnd_2405902 : Nat := 823589422409034087373643

theorem tailTrace_2405902 : CollatzResearch.WordTrace tailWord_2405902 prefixEnd_2405902 823589422409034087373643 := by
  unfold tailWord_2405902
  simp only [CollatzResearch.WordTrace]
  refine ⟨10968806866229428024207495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 58500303286556949462439973 10968806866229428024207495)
  ·
    refine ⟨16453210299344142036311243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10968806866229428024207495 16453210299344142036311243)
    ·
      refine ⟨24679815449016213054466865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16453210299344142036311243 24679815449016213054466865)
      ·
        refine ⟨18509861586762159790850149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24679815449016213054466865 18509861586762159790850149)
        ·
          refine ⟨3470599047517904960784403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18509861586762159790850149 3470599047517904960784403)
          ·
            refine ⟨5205898571276857441176605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3470599047517904960784403 5205898571276857441176605)
            ·
              refine ⟨1952211964228821540441227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5205898571276857441176605 1952211964228821540441227)
              ·
                refine ⟨2928317946343232310661841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1952211964228821540441227 2928317946343232310661841)
                ·
                  refine ⟨2196238459757424232996381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2928317946343232310661841 2196238459757424232996381)
                  ·
                    refine ⟨823589422409034087373643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2196238459757424232996381 823589422409034087373643)
                    ·
                      rfl

theorem cell22_2405902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 3, 1, 2, 3].length) (baseStart_2405902 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2405902 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2405902 prefixEnd_2405902 := by exact prefixLift 2405902
  have htrace : WordTrace (prefixWord ++ tailWord_2405902) baseStart_2405902 baseEnd_2405902 := by
    simpa [prefixWord, tailWord_2405902, baseEnd_2405902] using wordTrace_append hprefix tailTrace_2405902
  have hstable : (prefixWord ++ tailWord_2405902).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2405902).length < 2 ^ (prefixWord ++ tailWord_2405902).sum := by decide
  have hdescent : baseEnd_2405902 < baseStart_2405902 := by decide
  rcases family_descends (prefixWord ++ tailWord_2405902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2406020 : List Nat := [2, 3, 2, 1, 4, 1, 2, 1, 1, 5]
def baseStart_2406020 : Nat := 118140960795 + 2406020 * 2 ^ 59
def prefixEnd_2406020 : Nat := 4983230072969 + 3 ^ 40 * 2406020 * 2
def baseEnd_2406020 : Nat := 823629816220521112923281

theorem tailTrace_2406020 : CollatzResearch.WordTrace tailWord_2406020 prefixEnd_2406020 823629816220521112923281 := by
  unfold tailWord_2406020
  simp only [CollatzResearch.WordTrace]
  refine ⟨43877379371703965173227757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58503172495605286897637009 43877379371703965173227757)
  ·
    refine ⟨16454017264388986939960409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43877379371703965173227757 16454017264388986939960409)
    ·
      refine ⟨12340512948291740204970307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16454017264388986939960409 12340512948291740204970307)
      ·
        refine ⟨18510769422437610307455461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12340512948291740204970307 18510769422437610307455461)
        ·
          refine ⟨3470769266707051932647899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18510769422437610307455461 3470769266707051932647899)
          ·
            refine ⟨5206153900060577898971849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3470769266707051932647899 5206153900060577898971849)
            ·
              refine ⟨3904615425045433424228887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5206153900060577898971849 3904615425045433424228887)
              ·
                refine ⟨5856923137568150136343331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3904615425045433424228887 5856923137568150136343331)
                ·
                  refine ⟨8785384706352225204514997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5856923137568150136343331 8785384706352225204514997)
                  ·
                    refine ⟨823629816220521112923281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8785384706352225204514997 823629816220521112923281)
                    ·
                      rfl

theorem cell22_2406020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 2, 1, 1, 5].length) (baseStart_2406020 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2406020 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2406020 prefixEnd_2406020 := by exact prefixLift 2406020
  have htrace : WordTrace (prefixWord ++ tailWord_2406020) baseStart_2406020 baseEnd_2406020 := by
    simpa [prefixWord, tailWord_2406020, baseEnd_2406020] using wordTrace_append hprefix tailTrace_2406020
  have hstable : (prefixWord ++ tailWord_2406020).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2406020).length < 2 ^ (prefixWord ++ tailWord_2406020).sum := by decide
  have hdescent : baseEnd_2406020 < baseStart_2406020 := by decide
  rcases family_descends (prefixWord ++ tailWord_2406020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2406050 : List Nat := [3, 3, 1, 4, 1, 1, 9]
def baseStart_2406050 : Nat := 118140960795 + 2406050 * 2 ^ 59
def prefixEnd_2406050 : Nat := 4983230072969 + 3 ^ 40 * 2406050 * 2
def baseEnd_2406050 : Nat := 30505188364207816099007

theorem tailTrace_2406050 : CollatzResearch.WordTrace tailWord_2406050 prefixEnd_2406050 30505188364207816099007 := by
  unfold tailWord_2406050
  simp only [CollatzResearch.WordTrace]
  refine ⟨21938963233324811367511901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58503901955532830313365069 21938963233324811367511901)
  ·
    refine ⟨8227111212496804262816963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21938963233324811367511901 8227111212496804262816963)
    ·
      refine ⟨12340666818745206394225445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8227111212496804262816963 12340666818745206394225445)
      ·
        refine ⟨2313875028514726198917271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12340666818745206394225445 2313875028514726198917271)
        ·
          refine ⟨3470812542772089298375907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2313875028514726198917271 3470812542772089298375907)
          ·
            refine ⟨5206218814158133947563861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3470812542772089298375907 5206218814158133947563861)
            ·
              refine ⟨30505188364207816099007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5206218814158133947563861 30505188364207816099007)
              ·
                rfl

theorem cell22_2406050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 9].length) (baseStart_2406050 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2406050 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2406050 prefixEnd_2406050 := by exact prefixLift 2406050
  have htrace : WordTrace (prefixWord ++ tailWord_2406050) baseStart_2406050 baseEnd_2406050 := by
    simpa [prefixWord, tailWord_2406050, baseEnd_2406050] using wordTrace_append hprefix tailTrace_2406050
  have hstable : (prefixWord ++ tailWord_2406050).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2406050).length < 2 ^ (prefixWord ++ tailWord_2406050).sum := by decide
  have hdescent : baseEnd_2406050 < baseStart_2406050 := by decide
  rcases family_descends (prefixWord ++ tailWord_2406050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2406091 : List Nat := [1, 1, 1, 1, 3, 2, 1, 2, 2, 8]
def baseStart_2406091 : Nat := 118140960795 + 2406091 * 2 ^ 59
def prefixEnd_2406091 : Nat := 4983230072969 + 3 ^ 40 * 2406091 * 2
def baseEnd_2406091 : Nat := 823654120971500594398063

theorem tailTrace_2406091 : CollatzResearch.WordTrace tailWord_2406091 prefixEnd_2406091 823654120971500594398063 := by
  unfold tailWord_2406091
  simp only [CollatzResearch.WordTrace]
  refine ⟨87757348326150709472290127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58504898884100472981526751 87757348326150709472290127)
  ·
    refine ⟨131636022489226064208435191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87757348326150709472290127 131636022489226064208435191)
    ·
      refine ⟨197454033733839096312652787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131636022489226064208435191 197454033733839096312652787)
      ·
        refine ⟨296181050600758644468979181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 197454033733839096312652787 296181050600758644468979181)
        ·
          refine ⟨111067893975284491675867193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 296181050600758644468979181 111067893975284491675867193)
          ·
            refine ⟨83300920481463368756900395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 111067893975284491675867193 83300920481463368756900395)
            ·
              refine ⟨124951380722195053135350593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83300920481463368756900395 124951380722195053135350593)
              ·
                refine ⟨93713535541646289851512945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 124951380722195053135350593 93713535541646289851512945)
                ·
                  refine ⟨70285151656234717388634709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 93713535541646289851512945 70285151656234717388634709)
                  ·
                    refine ⟨823654120971500594398063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 70285151656234717388634709 823654120971500594398063)
                    ·
                      rfl

theorem cell22_2406091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 2, 2, 8].length) (baseStart_2406091 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2406091 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2406091 prefixEnd_2406091 := by exact prefixLift 2406091
  have htrace : WordTrace (prefixWord ++ tailWord_2406091) baseStart_2406091 baseEnd_2406091 := by
    simpa [prefixWord, tailWord_2406091, baseEnd_2406091] using wordTrace_append hprefix tailTrace_2406091
  have hstable : (prefixWord ++ tailWord_2406091).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2406091).length < 2 ^ (prefixWord ++ tailWord_2406091).sum := by decide
  have hdescent : baseEnd_2406091 < baseStart_2406091 := by decide
  rcases family_descends (prefixWord ++ tailWord_2406091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2406123 : List Nat := [1, 1, 1, 1, 2, 4, 5, 1, 6]
def baseStart_2406123 : Nat := 118140960795 + 2406123 * 2 ^ 59
def prefixEnd_2406123 : Nat := 4983230072969 + 3 ^ 40 * 2406123 * 2
def baseEnd_2406123 : Nat := 274555025075154392532655

theorem tailTrace_2406123 : CollatzResearch.WordTrace tailWord_2406123 prefixEnd_2406123 274555025075154392532655 := by
  unfold tailWord_2406123
  simp only [CollatzResearch.WordTrace]
  refine ⟨87758515462034778937455023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58505676974689852624970015 87758515462034778937455023)
  ·
    refine ⟨131637773193052168406182535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87758515462034778937455023 131637773193052168406182535)
    ·
      refine ⟨197456659789578252609273803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131637773193052168406182535 197456659789578252609273803)
      ·
        refine ⟨296184989684367378913910705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 197456659789578252609273803 296184989684367378913910705)
        ·
          refine ⟨222138742263275534185433029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 296184989684367378913910705 222138742263275534185433029)
          ·
            refine ⟨41651014174364162659768693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 222138742263275534185433029 41651014174364162659768693)
            ·
              refine ⟨3904782578846640249353315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 41651014174364162659768693 3904782578846640249353315)
              ·
                refine ⟨5857173868269960374029973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3904782578846640249353315 5857173868269960374029973)
                ·
                  refine ⟨274555025075154392532655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5857173868269960374029973 274555025075154392532655)
                  ·
                    rfl

theorem cell22_2406123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 5, 1, 6].length) (baseStart_2406123 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2406123 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2406123 prefixEnd_2406123 := by exact prefixLift 2406123
  have htrace : WordTrace (prefixWord ++ tailWord_2406123) baseStart_2406123 baseEnd_2406123 := by
    simpa [prefixWord, tailWord_2406123, baseEnd_2406123] using wordTrace_append hprefix tailTrace_2406123
  have hstable : (prefixWord ++ tailWord_2406123).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2406123).length < 2 ^ (prefixWord ++ tailWord_2406123).sum := by decide
  have hdescent : baseEnd_2406123 < baseStart_2406123 := by decide
  rcases family_descends (prefixWord ++ tailWord_2406123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2406138 : List Nat := [3, 1, 1, 1, 1, 3, 1, 5, 1, 5]
def baseStart_2406138 : Nat := 118140960795 + 2406138 * 2 ^ 59
def prefixEnd_2406138 : Nat := 4983230072969 + 3 ^ 40 * 2406138 * 2
def baseEnd_2406138 : Nat := 823670210032008138472919

theorem tailTrace_2406138 : CollatzResearch.WordTrace tailWord_2406138 prefixEnd_2406138 823670210032008138472919 := by
  unfold tailWord_2406138
  simp only [CollatzResearch.WordTrace]
  refine ⟨21939765639245109124812767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58506041704653624332834045 21939765639245109124812767)
  ·
    refine ⟨32909648458867663687219151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21939765639245109124812767 32909648458867663687219151)
    ·
      refine ⟨49364472688301495530828727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32909648458867663687219151 49364472688301495530828727)
      ·
        refine ⟨74046709032452243296243091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49364472688301495530828727 74046709032452243296243091)
        ·
          refine ⟨111070063548678364944364637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74046709032452243296243091 111070063548678364944364637)
          ·
            refine ⟨41651273830754386854136739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 111070063548678364944364637 41651273830754386854136739)
            ·
              refine ⟨62476910746131580281205109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41651273830754386854136739 62476910746131580281205109)
              ·
                refine ⟨5857210382449835651362979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 62476910746131580281205109 5857210382449835651362979)
                ·
                  refine ⟨8785815573674753477044469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5857210382449835651362979 8785815573674753477044469)
                  ·
                    refine ⟨823670210032008138472919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8785815573674753477044469 823670210032008138472919)
                    ·
                      rfl

theorem cell22_2406138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 5, 1, 5].length) (baseStart_2406138 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2406138 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2406138 prefixEnd_2406138 := by exact prefixLift 2406138
  have htrace : WordTrace (prefixWord ++ tailWord_2406138) baseStart_2406138 baseEnd_2406138 := by
    simpa [prefixWord, tailWord_2406138, baseEnd_2406138] using wordTrace_append hprefix tailTrace_2406138
  have hstable : (prefixWord ++ tailWord_2406138).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2406138).length < 2 ^ (prefixWord ++ tailWord_2406138).sum := by decide
  have hdescent : baseEnd_2406138 < baseStart_2406138 := by decide
  rcases family_descends (prefixWord ++ tailWord_2406138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2406142 : List Nat := [4, 2, 2, 1, 3, 1, 1, 1, 3, 4]
def baseStart_2406142 : Nat := 118140960795 + 2406142 * 2 ^ 59
def prefixEnd_2406142 : Nat := 4983230072969 + 3 ^ 40 * 2406142 * 2
def baseEnd_2406142 : Nat := 823671579313753461372907

theorem tailTrace_2406142 : CollatzResearch.WordTrace tailWord_2406142 prefixEnd_2406142 823671579313753461372907 := by
  unfold tailWord_2406142
  simp only [CollatzResearch.WordTrace]
  refine ⟨10969901056120743147799585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 58506138965977296788264453 10969901056120743147799585)
  ·
    refine ⟨8227425792090557360849689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10969901056120743147799585 8227425792090557360849689)
    ·
      refine ⟨6170569344067918020637267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8227425792090557360849689 6170569344067918020637267)
      ·
        refine ⟨9255854016101877030955901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6170569344067918020637267 9255854016101877030955901)
        ·
          refine ⟨3470945256038203886608463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9255854016101877030955901 3470945256038203886608463)
          ·
            refine ⟨5206417884057305829912695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3470945256038203886608463 5206417884057305829912695)
            ·
              refine ⟨7809626826085958744869043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5206417884057305829912695 7809626826085958744869043)
              ·
                refine ⟨11714440239128938117303565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7809626826085958744869043 11714440239128938117303565)
                ·
                  refine ⟨4392915089673351793988837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11714440239128938117303565 4392915089673351793988837)
                  ·
                    refine ⟨823671579313753461372907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4392915089673351793988837 823671579313753461372907)
                    ·
                      rfl

theorem cell22_2406142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 1, 1, 3, 4].length) (baseStart_2406142 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2406142 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2406142 prefixEnd_2406142 := by exact prefixLift 2406142
  have htrace : WordTrace (prefixWord ++ tailWord_2406142) baseStart_2406142 baseEnd_2406142 := by
    simpa [prefixWord, tailWord_2406142, baseEnd_2406142] using wordTrace_append hprefix tailTrace_2406142
  have hstable : (prefixWord ++ tailWord_2406142).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2406142).length < 2 ^ (prefixWord ++ tailWord_2406142).sum := by decide
  have hdescent : baseEnd_2406142 < baseStart_2406142 := by decide
  rcases family_descends (prefixWord ++ tailWord_2406142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2406170 : List Nat := [3, 1, 1, 3, 2, 2, 2, 2, 2, 4]
def baseStart_2406170 : Nat := 118140960795 + 2406170 * 2 ^ 59
def prefixEnd_2406170 : Nat := 4983230072969 + 3 ^ 40 * 2406170 * 2
def baseEnd_2406170 : Nat := 823681164285970721672821

theorem tailTrace_2406170 : CollatzResearch.WordTrace tailWord_2406170 prefixEnd_2406170 823681164285970721672821 := by
  unfold tailWord_2406170
  simp only [CollatzResearch.WordTrace]
  refine ⟨21940057423216126491103991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58506819795243003976277309 21940057423216126491103991)
  ·
    refine ⟨32910086134824189736655987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21940057423216126491103991 32910086134824189736655987)
    ·
      refine ⟨49365129202236284604983981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32910086134824189736655987 49365129202236284604983981)
      ·
        refine ⟨18511923450838606726868993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49365129202236284604983981 18511923450838606726868993)
        ·
          refine ⟨13883942588128955045151745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18511923450838606726868993 13883942588128955045151745)
          ·
            refine ⟨10412956941096716283863809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13883942588128955045151745 10412956941096716283863809)
            ·
              refine ⟨7809717705822537212897857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10412956941096716283863809 7809717705822537212897857)
              ·
                refine ⟨5857288279366902909673393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7809717705822537212897857 5857288279366902909673393)
                ·
                  refine ⟨4392966209525177182255045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5857288279366902909673393 4392966209525177182255045)
                  ·
                    refine ⟨823681164285970721672821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4392966209525177182255045 823681164285970721672821)
                    ·
                      rfl

theorem cell22_2406170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 2, 2, 2, 4].length) (baseStart_2406170 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2406170 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2406170 prefixEnd_2406170 := by exact prefixLift 2406170
  have htrace : WordTrace (prefixWord ++ tailWord_2406170) baseStart_2406170 baseEnd_2406170 := by
    simpa [prefixWord, tailWord_2406170, baseEnd_2406170] using wordTrace_append hprefix tailTrace_2406170
  have hstable : (prefixWord ++ tailWord_2406170).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2406170).length < 2 ^ (prefixWord ++ tailWord_2406170).sum := by decide
  have hdescent : baseEnd_2406170 < baseStart_2406170 := by decide
  rcases family_descends (prefixWord ++ tailWord_2406170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2406172 : List Nat := [2, 2, 3, 1, 1, 2, 4, 2, 2, 3]
def baseStart_2406172 : Nat := 118140960795 + 2406172 * 2 ^ 59
def prefixEnd_2406172 : Nat := 4983230072969 + 3 ^ 40 * 2406172 * 2
def baseEnd_2406172 : Nat := 823681848926843383122815

theorem tailTrace_2406172 : CollatzResearch.WordTrace tailWord_2406172 prefixEnd_2406172 823681848926843383122815 := by
  unfold tailWord_2406172
  simp only [CollatzResearch.WordTrace]
  refine ⟨43880151319428630152994385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58506868425904840203992513 43880151319428630152994385)
  ·
    refine ⟨32910113489571472614745789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43880151319428630152994385 32910113489571472614745789)
    ·
      refine ⟨12341292558589302230529671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32910113489571472614745789 12341292558589302230529671)
      ·
        refine ⟨18511938837883953345794507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12341292558589302230529671 18511938837883953345794507)
        ·
          refine ⟨27767908256825930018691761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18511938837883953345794507 27767908256825930018691761)
          ·
            refine ⟨20825931192619447514018821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27767908256825930018691761 20825931192619447514018821)
            ·
              refine ⟨3904862098616146408878529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20825931192619447514018821 3904862098616146408878529)
              ·
                refine ⟨2928646573962109806658897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3904862098616146408878529 2928646573962109806658897)
                ·
                  refine ⟨2196484930471582354994173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2928646573962109806658897 2196484930471582354994173)
                  ·
                    refine ⟨823681848926843383122815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2196484930471582354994173 823681848926843383122815)
                    ·
                      rfl

theorem cell22_2406172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 4, 2, 2, 3].length) (baseStart_2406172 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2406172 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2406172 prefixEnd_2406172 := by exact prefixLift 2406172
  have htrace : WordTrace (prefixWord ++ tailWord_2406172) baseStart_2406172 baseEnd_2406172 := by
    simpa [prefixWord, tailWord_2406172, baseEnd_2406172] using wordTrace_append hprefix tailTrace_2406172
  have hstable : (prefixWord ++ tailWord_2406172).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2406172).length < 2 ^ (prefixWord ++ tailWord_2406172).sum := by decide
  have hdescent : baseEnd_2406172 < baseStart_2406172 := by decide
  rcases family_descends (prefixWord ++ tailWord_2406172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2406200 : List Nat := [2, 1, 2, 1, 3, 3, 1, 1, 5, 3]
def baseStart_2406200 : Nat := 118140960795 + 2406200 * 2 ^ 59
def prefixEnd_2406200 : Nat := 4983230072969 + 3 ^ 40 * 2406200 * 2
def baseEnd_2406200 : Nat := 823691433899060643422729

theorem tailTrace_2406200 : CollatzResearch.WordTrace tailWord_2406200 prefixEnd_2406200 823691433899060643422729 := by
  unfold tailWord_2406200
  simp only [CollatzResearch.WordTrace]
  refine ⟨43880661941377910544004027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58507549255170547392005369 43880661941377910544004027)
  ·
    refine ⟨65820992912066865816006041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43880661941377910544004027 65820992912066865816006041)
    ·
      refine ⟨49365744684050149362004531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65820992912066865816006041 49365744684050149362004531)
      ·
        refine ⟨74048617026075224043006797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49365744684050149362004531 74048617026075224043006797)
        ·
          refine ⟨27768231384778209016127549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 74048617026075224043006797 27768231384778209016127549)
          ·
            refine ⟨10413086769291828381047831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27768231384778209016127549 10413086769291828381047831)
            ·
              refine ⟨15619630153937742571571747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10413086769291828381047831 15619630153937742571571747)
              ·
                refine ⟨23429445230906613857357621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15619630153937742571571747 23429445230906613857357621)
                ·
                  refine ⟨2196510490397495049127277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 23429445230906613857357621 2196510490397495049127277)
                  ·
                    refine ⟨823691433899060643422729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2196510490397495049127277 823691433899060643422729)
                    ·
                      rfl

theorem cell22_2406200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 1, 1, 5, 3].length) (baseStart_2406200 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2406200 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2406200 prefixEnd_2406200 := by exact prefixLift 2406200
  have htrace : WordTrace (prefixWord ++ tailWord_2406200) baseStart_2406200 baseEnd_2406200 := by
    simpa [prefixWord, tailWord_2406200, baseEnd_2406200] using wordTrace_append hprefix tailTrace_2406200
  have hstable : (prefixWord ++ tailWord_2406200).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2406200).length < 2 ^ (prefixWord ++ tailWord_2406200).sum := by decide
  have hdescent : baseEnd_2406200 < baseStart_2406200 := by decide
  rcases family_descends (prefixWord ++ tailWord_2406200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2406213 : List Nat := [1, 3, 1, 1, 1, 2, 4, 2, 7]
def baseStart_2406213 : Nat := 118140960795 + 2406213 * 2 ^ 59
def prefixEnd_2406213 : Nat := 4983230072969 + 3 ^ 40 * 2406213 * 2
def baseEnd_2406213 : Nat := 274565294688244314282563

theorem tailTrace_2406213 : CollatzResearch.WordTrace tailWord_2406213 prefixEnd_2406213 274565294688244314282563 := by
  unfold tailWord_2406213
  simp only [CollatzResearch.WordTrace]
  refine ⟨87761798031708724308231293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58507865354472482872154195 87761798031708724308231293)
  ·
    refine ⟨32910674261890771615586735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 87761798031708724308231293 32910674261890771615586735)
    ·
      refine ⟨49366011392836157423380103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32910674261890771615586735 49366011392836157423380103)
      ·
        refine ⟨74049017089254236135070155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49366011392836157423380103 74049017089254236135070155)
        ·
          refine ⟨111073525633881354202605233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74049017089254236135070155 111073525633881354202605233)
          ·
            refine ⟨83305144225411015651953925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 111073525633881354202605233 83305144225411015651953925)
            ·
              refine ⟨15619714542264565434741361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 83305144225411015651953925 15619714542264565434741361)
              ·
                refine ⟨11714785906698424076056021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15619714542264565434741361 11714785906698424076056021)
                ·
                  refine ⟨274565294688244314282563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11714785906698424076056021 274565294688244314282563)
                  ·
                    rfl

theorem cell22_2406213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 4, 2, 7].length) (baseStart_2406213 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2406213 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2406213 prefixEnd_2406213 := by exact prefixLift 2406213
  have htrace : WordTrace (prefixWord ++ tailWord_2406213) baseStart_2406213 baseEnd_2406213 := by
    simpa [prefixWord, tailWord_2406213, baseEnd_2406213] using wordTrace_append hprefix tailTrace_2406213
  have hstable : (prefixWord ++ tailWord_2406213).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2406213).length < 2 ^ (prefixWord ++ tailWord_2406213).sum := by decide
  have hdescent : baseEnd_2406213 < baseStart_2406213 := by decide
  rcases family_descends (prefixWord ++ tailWord_2406213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2406247 : List Nat := [1, 1, 5, 1, 2, 1, 5, 1, 5]
def baseStart_2406247 : Nat := 118140960795 + 2406247 * 2 ^ 59
def prefixEnd_2406247 : Nat := 4983230072969 + 3 ^ 40 * 2406247 * 2
def baseEnd_2406247 : Nat := 274569174319856062499195

theorem tailTrace_2406247 : CollatzResearch.WordTrace tailWord_2406247 prefixEnd_2406247 274569174319856062499195 := by
  unfold tailWord_2406247
  simp only [CollatzResearch.WordTrace]
  refine ⟨87763038113585548114968995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58508692075723698743312663 87763038113585548114968995)
  ·
    refine ⟨131644557170378322172453493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87763038113585548114968995 131644557170378322172453493)
    ·
      refine ⟨12341677234722967703667515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 131644557170378322172453493 12341677234722967703667515)
      ·
        refine ⟨18512515852084451555501273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12341677234722967703667515 18512515852084451555501273)
        ·
          refine ⟨13884386889063338666625955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18512515852084451555501273 13884386889063338666625955)
          ·
            refine ⟨20826580333595007999938933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13884386889063338666625955 20826580333595007999938933)
            ·
              refine ⟨1952491906274531999994275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 20826580333595007999938933 1952491906274531999994275)
              ·
                refine ⟨2928737859411797999991413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1952491906274531999994275 2928737859411797999991413)
                ·
                  refine ⟨274569174319856062499195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2928737859411797999991413 274569174319856062499195)
                  ·
                    rfl

theorem cell22_2406247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 5, 1, 5].length) (baseStart_2406247 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2406247 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2406247 prefixEnd_2406247 := by exact prefixLift 2406247
  have htrace : WordTrace (prefixWord ++ tailWord_2406247) baseStart_2406247 baseEnd_2406247 := by
    simpa [prefixWord, tailWord_2406247, baseEnd_2406247] using wordTrace_append hprefix tailTrace_2406247
  have hstable : (prefixWord ++ tailWord_2406247).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2406247).length < 2 ^ (prefixWord ++ tailWord_2406247).sum := by decide
  have hdescent : baseEnd_2406247 < baseStart_2406247 := by decide
  rcases family_descends (prefixWord ++ tailWord_2406247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2406292 : List Nat := [2, 4, 2, 1, 1, 2, 3, 1, 6]
def baseStart_2406292 : Nat := 118140960795 + 2406292 * 2 ^ 59
def prefixEnd_2406292 : Nat := 4983230072969 + 3 ^ 40 * 2406292 * 2
def baseEnd_2406292 : Nat := 274574309126401023374149

theorem tailTrace_2406292 : CollatzResearch.WordTrace tailWord_2406292 prefixEnd_2406292 274574309126401023374149 := by
  unfold tailWord_2406292
  simp only [CollatzResearch.WordTrace]
  refine ⟨43882339699211260400178565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58509786265615013866904753 43882339699211260400178565)
  ·
    refine ⟨8227938693602111325033481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 43882339699211260400178565 8227938693602111325033481)
    ·
      refine ⟨6170954020201583493775111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8227938693602111325033481 6170954020201583493775111)
      ·
        refine ⟨9256431030302375240662667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6170954020201583493775111 9256431030302375240662667)
        ·
          refine ⟨13884646545453562860994001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9256431030302375240662667 13884646545453562860994001)
          ·
            refine ⟨10413484909090172145745501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13884646545453562860994001 10413484909090172145745501)
            ·
              refine ⟨3905056840908814554654563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10413484909090172145745501 3905056840908814554654563)
              ·
                refine ⟨5857585261363221831981845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3905056840908814554654563 5857585261363221831981845)
                ·
                  refine ⟨274574309126401023374149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5857585261363221831981845 274574309126401023374149)
                  ·
                    rfl

theorem cell22_2406292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 3, 1, 6].length) (baseStart_2406292 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2406292 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2406292 prefixEnd_2406292 := by exact prefixLift 2406292
  have htrace : WordTrace (prefixWord ++ tailWord_2406292) baseStart_2406292 baseEnd_2406292 := by
    simpa [prefixWord, tailWord_2406292, baseEnd_2406292] using wordTrace_append hprefix tailTrace_2406292
  have hstable : (prefixWord ++ tailWord_2406292).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2406292).length < 2 ^ (prefixWord ++ tailWord_2406292).sum := by decide
  have hdescent : baseEnd_2406292 < baseStart_2406292 := by decide
  rcases family_descends (prefixWord ++ tailWord_2406292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2406350 : List Nat := [4, 1, 1, 1, 2, 2, 1, 1, 1, 8]
def baseStart_2406350 : Nat := 118140960795 + 2406350 * 2 ^ 59
def prefixEnd_2406350 : Nat := 4983230072969 + 3 ^ 40 * 2406350 * 2
def baseEnd_2406350 : Nat := 823742781964510252172269

theorem tailTrace_2406350 : CollatzResearch.WordTrace tailWord_2406350 prefixEnd_2406350 823742781964510252172269 := by
  unfold tailWord_2406350
  simp only [CollatzResearch.WordTrace]
  refine ⟨10970849354026549588246063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 58511196554808264470645669 10970849354026549588246063)
  ·
    refine ⟨16456274031039824382369095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10970849354026549588246063 16456274031039824382369095)
    ·
      refine ⟨24684411046559736573553643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16456274031039824382369095 24684411046559736573553643)
      ·
        refine ⟨37026616569839604860330465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24684411046559736573553643 37026616569839604860330465)
        ·
          refine ⟨27769962427379703645247849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37026616569839604860330465 27769962427379703645247849)
          ·
            refine ⟨20827471820534777733935887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27769962427379703645247849 20827471820534777733935887)
            ·
              refine ⟨31241207730802166600903831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20827471820534777733935887 31241207730802166600903831)
              ·
                refine ⟨46861811596203249901355747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31241207730802166600903831 46861811596203249901355747)
                ·
                  refine ⟨70292717394304874852033621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 46861811596203249901355747 70292717394304874852033621)
                  ·
                    refine ⟨823742781964510252172269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 70292717394304874852033621 823742781964510252172269)
                    ·
                      rfl

theorem cell22_2406350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 1, 1, 8].length) (baseStart_2406350 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2406350 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2406350 prefixEnd_2406350 := by exact prefixLift 2406350
  have htrace : WordTrace (prefixWord ++ tailWord_2406350) baseStart_2406350 baseEnd_2406350 := by
    simpa [prefixWord, tailWord_2406350, baseEnd_2406350] using wordTrace_append hprefix tailTrace_2406350
  have hstable : (prefixWord ++ tailWord_2406350).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2406350).length < 2 ^ (prefixWord ++ tailWord_2406350).sum := by decide
  have hdescent : baseEnd_2406350 < baseStart_2406350 := by decide
  rcases family_descends (prefixWord ++ tailWord_2406350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2406354 : List Nat := [3, 2, 2, 3, 2, 2, 1, 7]
def baseStart_2406354 : Nat := 118140960795 + 2406354 * 2 ^ 59
def prefixEnd_2406354 : Nat := 4983230072969 + 3 ^ 40 * 2406354 * 2
def baseEnd_2406354 : Nat := 91527127916250619452473

theorem tailTrace_2406354 : CollatzResearch.WordTrace tailWord_2406354 prefixEnd_2406354 91527127916250619452473 := by
  unfold tailWord_2406354
  simp only [CollatzResearch.WordTrace]
  refine ⟨21941735181049476347278529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58511293816131936926076077 21941735181049476347278529)
  ·
    refine ⟨16456301385787107260458897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21941735181049476347278529 16456301385787107260458897)
    ·
      refine ⟨12342226039340330445344173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16456301385787107260458897 12342226039340330445344173)
      ·
        refine ⟨4628334764752623917004065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12342226039340330445344173 4628334764752623917004065)
        ·
          refine ⟨3471251073564467937753049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4628334764752623917004065 3471251073564467937753049)
          ·
            refine ⟨2603438305173350953314787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3471251073564467937753049 2603438305173350953314787)
            ·
              refine ⟨3905157457760026429972181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2603438305173350953314787 3905157457760026429972181)
              ·
                refine ⟨91527127916250619452473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3905157457760026429972181 91527127916250619452473)
                ·
                  rfl

theorem cell22_2406354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 2, 1, 7].length) (baseStart_2406354 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2406354 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2406354 prefixEnd_2406354 := by exact prefixLift 2406354
  have htrace : WordTrace (prefixWord ++ tailWord_2406354) baseStart_2406354 baseEnd_2406354 := by
    simpa [prefixWord, tailWord_2406354, baseEnd_2406354] using wordTrace_append hprefix tailTrace_2406354
  have hstable : (prefixWord ++ tailWord_2406354).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2406354).length < 2 ^ (prefixWord ++ tailWord_2406354).sum := by decide
  have hdescent : baseEnd_2406354 < baseStart_2406354 := by decide
  rcases family_descends (prefixWord ++ tailWord_2406354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2406429 : List Nat := [1, 4, 2, 2, 2, 1, 1, 4, 1, 4]
def baseStart_2406429 : Nat := 118140960795 + 2406429 * 2 ^ 59
def prefixEnd_2406429 : Nat := 4983230072969 + 3 ^ 40 * 2406429 * 2
def baseEnd_2406429 : Nat := 823769825278980379447027

theorem tailTrace_2406429 : CollatzResearch.WordTrace tailWord_2406429 prefixEnd_2406429 823769825278980379447027 := by
  unfold tailWord_2406429
  simp only [CollatzResearch.WordTrace]
  refine ⟨87769676198926193198094341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58513117465950795465396227 87769676198926193198094341)
  ·
    refine ⟨16456814287298661224642689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 87769676198926193198094341 16456814287298661224642689)
    ·
      refine ⟨12342610715473995918482017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16456814287298661224642689 12342610715473995918482017)
      ·
        refine ⟨9256958036605496938861513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12342610715473995918482017 9256958036605496938861513)
        ·
          refine ⟨6942718527454122704146135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9256958036605496938861513 6942718527454122704146135)
          ·
            refine ⟨10414077791181184056219203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6942718527454122704146135 10414077791181184056219203)
            ·
              refine ⟨15621116686771776084328805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10414077791181184056219203 15621116686771776084328805)
              ·
                refine ⟨2928959378769708015811651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15621116686771776084328805 2928959378769708015811651)
                ·
                  refine ⟨4393439068154562023717477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2928959378769708015811651 4393439068154562023717477)
                  ·
                    refine ⟨823769825278980379447027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4393439068154562023717477 823769825278980379447027)
                    ·
                      rfl

theorem cell22_2406429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 1, 4, 1, 4].length) (baseStart_2406429 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2406429 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2406429 prefixEnd_2406429 := by exact prefixLift 2406429
  have htrace : WordTrace (prefixWord ++ tailWord_2406429) baseStart_2406429 baseEnd_2406429 := by
    simpa [prefixWord, tailWord_2406429, baseEnd_2406429] using wordTrace_append hprefix tailTrace_2406429
  have hstable : (prefixWord ++ tailWord_2406429).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2406429).length < 2 ^ (prefixWord ++ tailWord_2406429).sum := by decide
  have hdescent : baseEnd_2406429 < baseStart_2406429 := by decide
  rcases family_descends (prefixWord ++ tailWord_2406429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2406455 : List Nat := [1, 1, 3, 1, 2, 2, 12]
def baseStart_2406455 : Nat := 118140960795 + 2406455 * 2 ^ 59
def prefixEnd_2406455 : Nat := 4983230072969 + 3 ^ 40 * 2406455 * 2
def baseEnd_2406455 : Nat := 30510323170752776973961

theorem tailTrace_2406455 : CollatzResearch.WordTrace tailWord_2406455 prefixEnd_2406455 30510323170752776973961 := by
  unfold tailWord_2406455
  simp only [CollatzResearch.WordTrace]
  refine ⟨87770624496831999638540819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58513749664554666425693879 87770624496831999638540819)
  ·
    refine ⟨131655936745247999457811229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87770624496831999638540819 131655936745247999457811229)
    ·
      refine ⟨49370976279467999796679211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 131655936745247999457811229 49370976279467999796679211)
      ·
        refine ⟨74056464419201999695018817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49370976279467999796679211 74056464419201999695018817)
        ·
          refine ⟨55542348314401499771264113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74056464419201999695018817 55542348314401499771264113)
          ·
            refine ⟨41656761235801124828448085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55542348314401499771264113 41656761235801124828448085)
            ·
              refine ⟨30510323170752776973961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 41656761235801124828448085 30510323170752776973961)
              ·
                rfl

theorem cell22_2406455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 12].length) (baseStart_2406455 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2406455 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2406455 prefixEnd_2406455 := by exact prefixLift 2406455
  have htrace : WordTrace (prefixWord ++ tailWord_2406455) baseStart_2406455 baseEnd_2406455 := by
    simpa [prefixWord, tailWord_2406455, baseEnd_2406455] using wordTrace_append hprefix tailTrace_2406455
  have hstable : (prefixWord ++ tailWord_2406455).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2406455).length < 2 ^ (prefixWord ++ tailWord_2406455).sum := by decide
  have hdescent : baseEnd_2406455 < baseStart_2406455 := by decide
  rcases family_descends (prefixWord ++ tailWord_2406455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2406461 : List Nat := [1, 4, 1, 3, 1, 1, 5, 2, 4]
def baseStart_2406461 : Nat := 118140960795 + 2406461 * 2 ^ 59
def prefixEnd_2406461 : Nat := 4983230072969 + 3 ^ 40 * 2406461 * 2
def baseEnd_2406461 : Nat := 274593593177647654215643

theorem tailTrace_2406461 : CollatzResearch.WordTrace tailWord_2406461 prefixEnd_2406461 274593593177647654215643 := by
  unfold tailWord_2406461
  simp only [CollatzResearch.WordTrace]
  refine ⟨87770843334810262663259237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58513895556540175108839491 87770843334810262663259237)
  ·
    refine ⟨16457033125276924249361107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 87770843334810262663259237 16457033125276924249361107)
    ·
      refine ⟨24685549687915386374041661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16457033125276924249361107 24685549687915386374041661)
      ·
        refine ⟨9257081132968269890265623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24685549687915386374041661 9257081132968269890265623)
        ·
          refine ⟨13885621699452404835398435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9257081132968269890265623 13885621699452404835398435)
          ·
            refine ⟨20828432549178607253097653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13885621699452404835398435 20828432549178607253097653)
            ·
              refine ⟨1952665551485494429977905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 20828432549178607253097653 1952665551485494429977905)
              ·
                refine ⟨1464499163614120822483429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1952665551485494429977905 1464499163614120822483429)
                ·
                  refine ⟨274593593177647654215643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1464499163614120822483429 274593593177647654215643)
                  ·
                    rfl

theorem cell22_2406461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 5, 2, 4].length) (baseStart_2406461 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2406461 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2406461 prefixEnd_2406461 := by exact prefixLift 2406461
  have htrace : WordTrace (prefixWord ++ tailWord_2406461) baseStart_2406461 baseEnd_2406461 := by
    simpa [prefixWord, tailWord_2406461, baseEnd_2406461] using wordTrace_append hprefix tailTrace_2406461
  have hstable : (prefixWord ++ tailWord_2406461).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2406461).length < 2 ^ (prefixWord ++ tailWord_2406461).sum := by decide
  have hdescent : baseEnd_2406461 < baseStart_2406461 := by decide
  rcases family_descends (prefixWord ++ tailWord_2406461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2406476 : List Nat := [2, 2, 1, 3, 1, 1, 6, 1, 2, 3]
def baseStart_2406476 : Nat := 118140960795 + 2406476 * 2 ^ 59
def prefixEnd_2406476 : Nat := 4983230072969 + 3 ^ 40 * 2406476 * 2
def baseEnd_2406476 : Nat := 823785914339487923521883

theorem tailTrace_2406476 : CollatzResearch.WordTrace tailWord_2406476 prefixEnd_2406476 823785914339487923521883 := by
  unfold tailWord_2406476
  simp only [CollatzResearch.WordTrace]
  refine ⟨43885695214877960112527641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58514260286503946816703521 43885695214877960112527641)
  ·
    refine ⟨32914271411158470084395731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43885695214877960112527641 32914271411158470084395731)
    ·
      refine ⟨49371407116737705126593597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32914271411158470084395731 49371407116737705126593597)
      ·
        refine ⟨18514277668776639422472599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49371407116737705126593597 18514277668776639422472599)
        ·
          refine ⟨27771416503164959133708899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18514277668776639422472599 27771416503164959133708899)
          ·
            refine ⟨41657124754747438700563349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27771416503164959133708899 41657124754747438700563349)
            ·
              refine ⟨1952677722878786189088907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 41657124754747438700563349 1952677722878786189088907)
              ·
                refine ⟨2929016584318179283633361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1952677722878786189088907 2929016584318179283633361)
                ·
                  refine ⟨2196762438238634462725021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2929016584318179283633361 2196762438238634462725021)
                  ·
                    refine ⟨823785914339487923521883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2196762438238634462725021 823785914339487923521883)
                    ·
                      rfl

theorem cell22_2406476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 6, 1, 2, 3].length) (baseStart_2406476 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2406476 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2406476 prefixEnd_2406476 := by exact prefixLift 2406476
  have htrace : WordTrace (prefixWord ++ tailWord_2406476) baseStart_2406476 baseEnd_2406476 := by
    simpa [prefixWord, tailWord_2406476, baseEnd_2406476] using wordTrace_append hprefix tailTrace_2406476
  have hstable : (prefixWord ++ tailWord_2406476).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2406476).length < 2 ^ (prefixWord ++ tailWord_2406476).sum := by decide
  have hdescent : baseEnd_2406476 < baseStart_2406476 := by decide
  rcases family_descends (prefixWord ++ tailWord_2406476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2406607 : List Nat := [1, 1, 2, 1, 1, 3, 5, 8]
def baseStart_2406607 : Nat := 118140960795 + 2406607 * 2 ^ 59
def prefixEnd_2406607 : Nat := 4983230072969 + 3 ^ 40 * 2406607 * 2
def baseEnd_2406607 : Nat := 91536750924071916499609

theorem tailTrace_2406607 : CollatzResearch.WordTrace tailWord_2406607 prefixEnd_2406607 91536750924071916499609 := by
  unfold tailWord_2406607
  simp only [CollatzResearch.WordTrace]
  refine ⟨87776168392281329598074075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58517445594854219732049383 87776168392281329598074075)
  ·
    refine ⟨131664252588421994397111113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87776168392281329598074075 131664252588421994397111113)
    ·
      refine ⟨98748189441316495797833335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 131664252588421994397111113 98748189441316495797833335)
      ·
        refine ⟨148122284161974743696750003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98748189441316495797833335 148122284161974743696750003)
        ·
          refine ⟨222183426242962115545125005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 148122284161974743696750003 222183426242962115545125005)
          ·
            refine ⟨83318784841110793329421877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 222183426242962115545125005 83318784841110793329421877)
            ·
              refine ⟨7811136078854136874633301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 83318784841110793329421877 7811136078854136874633301)
              ·
                refine ⟨91536750924071916499609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7811136078854136874633301 91536750924071916499609)
                ·
                  rfl

theorem cell22_2406607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 5, 8].length) (baseStart_2406607 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2406607 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2406607 prefixEnd_2406607 := by exact prefixLift 2406607
  have htrace : WordTrace (prefixWord ++ tailWord_2406607) baseStart_2406607 baseEnd_2406607 := by
    simpa [prefixWord, tailWord_2406607, baseEnd_2406607] using wordTrace_append hprefix tailTrace_2406607
  have hstable : (prefixWord ++ tailWord_2406607).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2406607).length < 2 ^ (prefixWord ++ tailWord_2406607).sum := by decide
  have hdescent : baseEnd_2406607 < baseStart_2406607 := by decide
  rcases family_descends (prefixWord ++ tailWord_2406607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2406684 : List Nat := [2, 2, 3, 1, 1, 1, 1, 4, 2, 5]
def baseStart_2406684 : Nat := 118140960795 + 2406684 * 2 ^ 59
def prefixEnd_2406684 : Nat := 4983230072969 + 3 ^ 40 * 2406684 * 2
def baseEnd_2406684 : Nat := 823857116990244714321245

theorem tailTrace_2406684 : CollatzResearch.WordTrace tailWord_2406684 prefixEnd_2406684 823857116990244714321245 := by
  unfold tailWord_2406684
  simp only [CollatzResearch.WordTrace]
  refine ⟨43889488406501185874313553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58519317875334914499084737 43889488406501185874313553)
  ·
    refine ⟨32917116304875889405735165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43889488406501185874313553 32917116304875889405735165)
    ·
      refine ⟨12343918614328458527150687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32917116304875889405735165 12343918614328458527150687)
      ·
        refine ⟨18515877921492687790726031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12343918614328458527150687 18515877921492687790726031)
        ·
          refine ⟨27773816882239031686089047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18515877921492687790726031 27773816882239031686089047)
          ·
            refine ⟨41660725323358547529133571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27773816882239031686089047 41660725323358547529133571)
            ·
              refine ⟨62491087985037821293700357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41660725323358547529133571 62491087985037821293700357)
              ·
                refine ⟨11717078997194591492568817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 62491087985037821293700357 11717078997194591492568817)
                ·
                  refine ⟨8787809247895943619426613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11717078997194591492568817 8787809247895943619426613)
                  ·
                    refine ⟨823857116990244714321245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8787809247895943619426613 823857116990244714321245)
                    ·
                      rfl

theorem cell22_2406684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 4, 2, 5].length) (baseStart_2406684 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2406684 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2406684 prefixEnd_2406684 := by exact prefixLift 2406684
  have htrace : WordTrace (prefixWord ++ tailWord_2406684) baseStart_2406684 baseEnd_2406684 := by
    simpa [prefixWord, tailWord_2406684, baseEnd_2406684] using wordTrace_append hprefix tailTrace_2406684
  have hstable : (prefixWord ++ tailWord_2406684).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2406684).length < 2 ^ (prefixWord ++ tailWord_2406684).sum := by decide
  have hdescent : baseEnd_2406684 < baseStart_2406684 := by decide
  rcases family_descends (prefixWord ++ tailWord_2406684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2406690 : List Nat := [3, 3, 1, 1, 3, 2, 1, 4, 1, 3]
def baseStart_2406690 : Nat := 118140960795 + 2406690 * 2 ^ 59
def prefixEnd_2406690 : Nat := 4983230072969 + 3 ^ 40 * 2406690 * 2
def baseEnd_2406690 : Nat := 823859170912862698671227

theorem tailTrace_2406690 : CollatzResearch.WordTrace tailWord_2406690 prefixEnd_2406690 823859170912862698671227 := by
  unfold tailWord_2406690
  simp only [CollatzResearch.WordTrace]
  refine ⟨21944798912745158693336381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58519463767320423182230349 21944798912745158693336381)
  ·
    refine ⟨8229299592279434510001143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21944798912745158693336381 8229299592279434510001143)
    ·
      refine ⟨12343949388419151765001715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8229299592279434510001143 12343949388419151765001715)
      ·
        refine ⟨18515924082628727647502573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12343949388419151765001715 18515924082628727647502573)
        ·
          refine ⟨6943471530985772867813465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18515924082628727647502573 6943471530985772867813465)
          ·
            refine ⟨5207603648239329650860099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6943471530985772867813465 5207603648239329650860099)
            ·
              refine ⟨7811405472358994476290149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5207603648239329650860099 7811405472358994476290149)
              ·
                refine ⟨1464638526067311464304403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7811405472358994476290149 1464638526067311464304403)
                ·
                  refine ⟨2196957789100967196456605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1464638526067311464304403 2196957789100967196456605)
                  ·
                    refine ⟨823859170912862698671227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2196957789100967196456605 823859170912862698671227)
                    ·
                      rfl

theorem cell22_2406690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 1, 4, 1, 3].length) (baseStart_2406690 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2406690 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2406690 prefixEnd_2406690 := by exact prefixLift 2406690
  have htrace : WordTrace (prefixWord ++ tailWord_2406690) baseStart_2406690 baseEnd_2406690 := by
    simpa [prefixWord, tailWord_2406690, baseEnd_2406690] using wordTrace_append hprefix tailTrace_2406690
  have hstable : (prefixWord ++ tailWord_2406690).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2406690).length < 2 ^ (prefixWord ++ tailWord_2406690).sum := by decide
  have hdescent : baseEnd_2406690 < baseStart_2406690 := by decide
  rcases family_descends (prefixWord ++ tailWord_2406690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2406714 : List Nat := [3, 1, 1, 1, 4, 2, 1, 1, 8]
def baseStart_2406714 : Nat := 118140960795 + 2406714 * 2 ^ 59
def prefixEnd_2406714 : Nat := 4983230072969 + 3 ^ 40 * 2406714 * 2
def baseEnd_2406714 : Nat := 274622462201111545357051

theorem tailTrace_2406714 : CollatzResearch.WordTrace tailWord_2406714 prefixEnd_2406714 274622462201111545357051 := by
  unfold tailWord_2406714
  simp only [CollatzResearch.WordTrace]
  refine ⟨21945017750723421718054799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58520047335262457914812797 21945017750723421718054799)
  ·
    refine ⟨32917526626085132577082199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21945017750723421718054799 32917526626085132577082199)
    ·
      refine ⟨49376289939127698865623299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32917526626085132577082199 49376289939127698865623299)
      ·
        refine ⟨74064434908691548298434949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49376289939127698865623299 74064434908691548298434949)
        ·
          refine ⟨13887081545379665305956553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 74064434908691548298434949 13887081545379665305956553)
          ·
            refine ⟨10415311159034748979467415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13887081545379665305956553 10415311159034748979467415)
            ·
              refine ⟨15622966738552123469201123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10415311159034748979467415 15622966738552123469201123)
              ·
                refine ⟨23434450107828185203801685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15622966738552123469201123 23434450107828185203801685)
                ·
                  refine ⟨274622462201111545357051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 23434450107828185203801685 274622462201111545357051)
                  ·
                    rfl

theorem cell22_2406714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 1, 1, 8].length) (baseStart_2406714 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2406714 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2406714 prefixEnd_2406714 := by exact prefixLift 2406714
  have htrace : WordTrace (prefixWord ++ tailWord_2406714) baseStart_2406714 baseEnd_2406714 := by
    simpa [prefixWord, tailWord_2406714, baseEnd_2406714] using wordTrace_append hprefix tailTrace_2406714
  have hstable : (prefixWord ++ tailWord_2406714).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2406714).length < 2 ^ (prefixWord ++ tailWord_2406714).sum := by decide
  have hdescent : baseEnd_2406714 < baseStart_2406714 := by decide
  rcases family_descends (prefixWord ++ tailWord_2406714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2406716 : List Nat := [2, 2, 2, 2, 1, 2, 2, 4, 1, 4]
def baseStart_2406716 : Nat := 118140960795 + 2406716 * 2 ^ 59
def prefixEnd_2406716 : Nat := 4983230072969 + 3 ^ 40 * 2406716 * 2
def baseEnd_2406716 : Nat := 823868071244207297521147

theorem tailTrace_2406716 : CollatzResearch.WordTrace tailWord_2406716 prefixEnd_2406716 823868071244207297521147 := by
  unfold tailWord_2406716
  simp only [CollatzResearch.WordTrace]
  refine ⟨43890071974443220606896001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58520095965924294142528001 43890071974443220606896001)
  ·
    refine ⟨32917553980832415455172001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43890071974443220606896001 32917553980832415455172001)
    ·
      refine ⟨24688165485624311591379001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32917553980832415455172001 24688165485624311591379001)
      ·
        refine ⟨18516124114218233693534251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24688165485624311591379001 18516124114218233693534251)
        ·
          refine ⟨27774186171327350540301377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18516124114218233693534251 27774186171327350540301377)
          ·
            refine ⟨20830639628495512905226033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27774186171327350540301377 20830639628495512905226033)
            ·
              refine ⟨15622979721371634678919525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20830639628495512905226033 15622979721371634678919525)
              ·
                refine ⟨2929308697757181502297411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15622979721371634678919525 2929308697757181502297411)
                ·
                  refine ⟨4393963046635772253446117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2929308697757181502297411 4393963046635772253446117)
                  ·
                    refine ⟨823868071244207297521147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4393963046635772253446117 823868071244207297521147)
                    ·
                      rfl

theorem cell22_2406716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 2, 4, 1, 4].length) (baseStart_2406716 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2406716 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2406716 prefixEnd_2406716 := by exact prefixLift 2406716
  have htrace : WordTrace (prefixWord ++ tailWord_2406716) baseStart_2406716 baseEnd_2406716 := by
    simpa [prefixWord, tailWord_2406716, baseEnd_2406716] using wordTrace_append hprefix tailTrace_2406716
  have hstable : (prefixWord ++ tailWord_2406716).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2406716).length < 2 ^ (prefixWord ++ tailWord_2406716).sum := by decide
  have hdescent : baseEnd_2406716 < baseStart_2406716 := by decide
  rcases family_descends (prefixWord ++ tailWord_2406716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2406789 : List Nat := [1, 3, 1, 1, 3, 1, 1, 2, 1, 8]
def baseStart_2406789 : Nat := 118140960795 + 2406789 * 2 ^ 59
def prefixEnd_2406789 : Nat := 4983230072969 + 3 ^ 40 * 2406789 * 2
def baseEnd_2406789 : Nat := 823893060636059440445923

theorem tailTrace_2406789 : CollatzResearch.WordTrace tailWord_2406789 prefixEnd_2406789 823893060636059440445923 := by
  unfold tailWord_2406789
  simp only [CollatzResearch.WordTrace]
  refine ⟨87782806477621974681199421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58521870985081316454132947 87782806477621974681199421)
  ·
    refine ⟨32918552429108240505449783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 87782806477621974681199421 32918552429108240505449783)
    ·
      refine ⟨49377828643662360758174675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32918552429108240505449783 49377828643662360758174675)
      ·
        refine ⟨74066742965493541137262013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49377828643662360758174675 74066742965493541137262013)
        ·
          refine ⟨27775028612060077926473255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 74066742965493541137262013 27775028612060077926473255)
          ·
            refine ⟨41662542918090116889709883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27775028612060077926473255 41662542918090116889709883)
            ·
              refine ⟨62493814377135175334564825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41662542918090116889709883 62493814377135175334564825)
              ·
                refine ⟨46870360782851381500923619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 62493814377135175334564825 46870360782851381500923619)
                ·
                  refine ⟨70305541174277072251385429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 46870360782851381500923619 70305541174277072251385429)
                  ·
                    refine ⟨823893060636059440445923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 70305541174277072251385429 823893060636059440445923)
                    ·
                      rfl

theorem cell22_2406789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 2, 1, 8].length) (baseStart_2406789 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2406789 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2406789 prefixEnd_2406789 := by exact prefixLift 2406789
  have htrace : WordTrace (prefixWord ++ tailWord_2406789) baseStart_2406789 baseEnd_2406789 := by
    simpa [prefixWord, tailWord_2406789, baseEnd_2406789] using wordTrace_append hprefix tailTrace_2406789
  have hstable : (prefixWord ++ tailWord_2406789).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2406789).length < 2 ^ (prefixWord ++ tailWord_2406789).sum := by decide
  have hdescent : baseEnd_2406789 < baseStart_2406789 := by decide
  rcases family_descends (prefixWord ++ tailWord_2406789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2406814 : List Nat := [4, 3, 1, 2, 1, 3, 2, 1, 2, 3]
def baseStart_2406814 : Nat := 118140960795 + 2406814 * 2 ^ 59
def prefixEnd_2406814 : Nat := 4983230072969 + 3 ^ 40 * 2406814 * 2
def baseEnd_2406814 : Nat := 823901618646967708570847

theorem tailTrace_2406814 : CollatzResearch.WordTrace tailWord_2406814 prefixEnd_2406814 823901618646967708570847 := by
  unfold tailWord_2406814
  simp only [CollatzResearch.WordTrace]
  refine ⟨10972964787816425493857437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 58522478868354269300572997 10972964787816425493857437)
  ·
    refine ⟨4114861795431159560196539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10972964787816425493857437 4114861795431159560196539)
    ·
      refine ⟨6172292693146739340294809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4114861795431159560196539 6172292693146739340294809)
      ·
        refine ⟨4629219519860054505221107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6172292693146739340294809 4629219519860054505221107)
        ·
          refine ⟨6943829279790081757831661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4629219519860054505221107 6943829279790081757831661)
          ·
            refine ⟨2603935979921280659186873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6943829279790081757831661 2603935979921280659186873)
            ·
              refine ⟨1952951984940960494390155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2603935979921280659186873 1952951984940960494390155)
              ·
                refine ⟨2929427977411440741585233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1952951984940960494390155 2929427977411440741585233)
                ·
                  refine ⟨2197070983058580556188925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2929427977411440741585233 2197070983058580556188925)
                  ·
                    refine ⟨823901618646967708570847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2197070983058580556188925 823901618646967708570847)
                    ·
                      rfl

theorem cell22_2406814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 3, 2, 1, 2, 3].length) (baseStart_2406814 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2406814 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2406814 prefixEnd_2406814 := by exact prefixLift 2406814
  have htrace : WordTrace (prefixWord ++ tailWord_2406814) baseStart_2406814 baseEnd_2406814 := by
    simpa [prefixWord, tailWord_2406814, baseEnd_2406814] using wordTrace_append hprefix tailTrace_2406814
  have hstable : (prefixWord ++ tailWord_2406814).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2406814).length < 2 ^ (prefixWord ++ tailWord_2406814).sum := by decide
  have hdescent : baseEnd_2406814 < baseStart_2406814 := by decide
  rcases family_descends (prefixWord ++ tailWord_2406814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2406821 : List Nat := [1, 3, 1, 2, 1, 1, 5, 3, 5]
def baseStart_2406821 : Nat := 118140960795 + 2406821 * 2 ^ 59
def prefixEnd_2406821 : Nat := 4983230072969 + 3 ^ 40 * 2406821 * 2
def baseEnd_2406821 : Nat := 274634671630007341215275

theorem tailTrace_2406821 : CollatzResearch.WordTrace tailWord_2406821 prefixEnd_2406821 274634671630007341215275 := by
  unfold tailWord_2406821
  simp only [CollatzResearch.WordTrace]
  refine ⟨87783973613506044146364317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58522649075670696097576211 87783973613506044146364317)
  ·
    refine ⟨32918990105064766554886619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 87783973613506044146364317 32918990105064766554886619)
    ·
      refine ⟨49378485157597149832329929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32918990105064766554886619 49378485157597149832329929)
      ·
        refine ⟨37033863868197862374247447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49378485157597149832329929 37033863868197862374247447)
        ·
          refine ⟨55550795802296793561371171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37033863868197862374247447 55550795802296793561371171)
          ·
            refine ⟨83326193703445190342056757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55550795802296793561371171 83326193703445190342056757)
            ·
              refine ⟨7811830659697986594567821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 83326193703445190342056757 7811830659697986594567821)
              ·
                refine ⟨2929436497386744972962933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7811830659697986594567821 2929436497386744972962933)
                ·
                  refine ⟨274634671630007341215275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2929436497386744972962933 274634671630007341215275)
                  ·
                    rfl

theorem cell22_2406821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 5, 3, 5].length) (baseStart_2406821 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2406821 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2406821 prefixEnd_2406821 := by exact prefixLift 2406821
  have htrace : WordTrace (prefixWord ++ tailWord_2406821) baseStart_2406821 baseEnd_2406821 := by
    simpa [prefixWord, tailWord_2406821, baseEnd_2406821] using wordTrace_append hprefix tailTrace_2406821
  have hstable : (prefixWord ++ tailWord_2406821).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2406821).length < 2 ^ (prefixWord ++ tailWord_2406821).sum := by decide
  have hdescent : baseEnd_2406821 < baseStart_2406821 := by decide
  rcases family_descends (prefixWord ++ tailWord_2406821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2406868 : List Nat := [2, 4, 1, 2, 2, 1, 1, 2, 3, 4]
def baseStart_2406868 : Nat := 118140960795 + 2406868 * 2 ^ 59
def prefixEnd_2406868 : Nat := 4983230072969 + 3 ^ 40 * 2406868 * 2
def baseEnd_2406868 : Nat := 823920103950529567720681

theorem tailTrace_2406868 : CollatzResearch.WordTrace tailWord_2406868 prefixEnd_2406868 823920103950529567720681 := by
  unfold tailWord_2406868
  simp only [CollatzResearch.WordTrace]
  refine ⟨43892843922167885586662629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58523791896223847448883505 43892843922167885586662629)
  ·
    refine ⟨8229908235406478547499243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 43892843922167885586662629 8229908235406478547499243)
    ·
      refine ⟨12344862353109717821248865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8229908235406478547499243 12344862353109717821248865)
      ·
        refine ⟨9258646764832288365936649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12344862353109717821248865 9258646764832288365936649)
        ·
          refine ⟨6943985073624216274452487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9258646764832288365936649 6943985073624216274452487)
          ·
            refine ⟨10415977610436324411678731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6943985073624216274452487 10415977610436324411678731)
            ·
              refine ⟨15623966415654486617518097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10415977610436324411678731 15623966415654486617518097)
              ·
                refine ⟨11717974811740864963138573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15623966415654486617518097 11717974811740864963138573)
                ·
                  refine ⟨4394240554402824361176965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11717974811740864963138573 4394240554402824361176965)
                  ·
                    refine ⟨823920103950529567720681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4394240554402824361176965 823920103950529567720681)
                    ·
                      rfl

theorem cell22_2406868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 1, 2, 3, 4].length) (baseStart_2406868 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2406868 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2406868 prefixEnd_2406868 := by exact prefixLift 2406868
  have htrace : WordTrace (prefixWord ++ tailWord_2406868) baseStart_2406868 baseEnd_2406868 := by
    simpa [prefixWord, tailWord_2406868, baseEnd_2406868] using wordTrace_append hprefix tailTrace_2406868
  have hstable : (prefixWord ++ tailWord_2406868).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2406868).length < 2 ^ (prefixWord ++ tailWord_2406868).sum := by decide
  have hdescent : baseEnd_2406868 < baseStart_2406868 := by decide
  rcases family_descends (prefixWord ++ tailWord_2406868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2406883 : List Nat := [1, 1, 1, 6, 3, 1, 1, 2, 6]
def baseStart_2406883 : Nat := 118140960795 + 2406883 * 2 ^ 59
def prefixEnd_2406883 : Nat := 4983230072969 + 3 ^ 40 * 2406883 * 2
def baseEnd_2406883 : Nat := 274641746252358176198545

theorem tailTrace_2406883 : CollatzResearch.WordTrace tailWord_2406883 prefixEnd_2406883 274641746252358176198545 := by
  unfold tailWord_2406883
  simp only [CollatzResearch.WordTrace]
  refine ⟨87786234939281428735121303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58524156626187619156747535 87786234939281428735121303)
  ·
    refine ⟨131679352408922143102681955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87786234939281428735121303 131679352408922143102681955)
    ·
      refine ⟨197519028613383214654022933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131679352408922143102681955 197519028613383214654022933)
      ·
        refine ⟨9258704466252338186907325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 197519028613383214654022933 9258704466252338186907325)
        ·
          refine ⟨3472014174844626820090247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9258704466252338186907325 3472014174844626820090247)
          ·
            refine ⟨5208021262266940230135371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3472014174844626820090247 5208021262266940230135371)
            ·
              refine ⟨7812031893400410345203057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5208021262266940230135371 7812031893400410345203057)
              ·
                refine ⟨5859023920050307758902293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7812031893400410345203057 5859023920050307758902293)
                ·
                  refine ⟨274641746252358176198545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5859023920050307758902293 274641746252358176198545)
                  ·
                    rfl

theorem cell22_2406883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 1, 2, 6].length) (baseStart_2406883 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2406883 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2406883 prefixEnd_2406883 := by exact prefixLift 2406883
  have htrace : WordTrace (prefixWord ++ tailWord_2406883) baseStart_2406883 baseEnd_2406883 := by
    simpa [prefixWord, tailWord_2406883, baseEnd_2406883] using wordTrace_append hprefix tailTrace_2406883
  have hstable : (prefixWord ++ tailWord_2406883).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2406883).length < 2 ^ (prefixWord ++ tailWord_2406883).sum := by decide
  have hdescent : baseEnd_2406883 < baseStart_2406883 := by decide
  rcases family_descends (prefixWord ++ tailWord_2406883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2406896 : List Nat := [2, 1, 1, 1, 3, 3, 3, 1, 1, 6]
def baseStart_2406896 : Nat := 118140960795 + 2406896 * 2 ^ 59
def prefixEnd_2406896 : Nat := 4983230072969 + 3 ^ 40 * 2406896 * 2
def baseEnd_2406896 : Nat := 823929688922746828020595

theorem tailTrace_2406896 : CollatzResearch.WordTrace tailWord_2406896 prefixEnd_2406896 823929688922746828020595 := by
  unfold tailWord_2406896
  simp only [CollatzResearch.WordTrace]
  refine ⟨43893354544117165977672271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58524472725489554636896361 43893354544117165977672271)
  ·
    refine ⟨65840031816175748966508407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43893354544117165977672271 65840031816175748966508407)
    ·
      refine ⟨98760047724263623449762611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65840031816175748966508407 98760047724263623449762611)
      ·
        refine ⟨148140071586395435174643917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98760047724263623449762611 148140071586395435174643917)
        ·
          refine ⟨55552526844898288190491469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 148140071586395435174643917 55552526844898288190491469)
          ·
            refine ⟨20832197566836858071434301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55552526844898288190491469 20832197566836858071434301)
            ·
              refine ⟨7812074087563821776787863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20832197566836858071434301 7812074087563821776787863)
              ·
                refine ⟨11718111131345732665181795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7812074087563821776787863 11718111131345732665181795)
                ·
                  refine ⟨17577166697018598997772693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11718111131345732665181795 17577166697018598997772693)
                  ·
                    refine ⟨823929688922746828020595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17577166697018598997772693 823929688922746828020595)
                    ·
                      rfl

theorem cell22_2406896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 3, 1, 1, 6].length) (baseStart_2406896 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2406896 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2406896 prefixEnd_2406896 := by exact prefixLift 2406896
  have htrace : WordTrace (prefixWord ++ tailWord_2406896) baseStart_2406896 baseEnd_2406896 := by
    simpa [prefixWord, tailWord_2406896, baseEnd_2406896] using wordTrace_append hprefix tailTrace_2406896
  have hstable : (prefixWord ++ tailWord_2406896).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2406896).length < 2 ^ (prefixWord ++ tailWord_2406896).sum := by decide
  have hdescent : baseEnd_2406896 < baseStart_2406896 := by decide
  rcases family_descends (prefixWord ++ tailWord_2406896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2406932 : List Nat := [2, 4, 3, 1, 1, 3, 1, 1, 1, 5]
def baseStart_2406932 : Nat := 118140960795 + 2406932 * 2 ^ 59
def prefixEnd_2406932 : Nat := 4983230072969 + 3 ^ 40 * 2406932 * 2
def baseEnd_2406932 : Nat := 823942012458454734120485

theorem tailTrace_2406932 : CollatzResearch.WordTrace tailWord_2406932 prefixEnd_2406932 823942012458454734120485 := by
  unfold tailWord_2406932
  simp only [CollatzResearch.WordTrace]
  refine ⟨43894011058051955051827525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58525348077402606735770033 43894011058051955051827525)
  ·
    refine ⟨8230127073384741572217661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 43894011058051955051827525 8230127073384741572217661)
    ·
      refine ⟨3086297652519278089581623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8230127073384741572217661 3086297652519278089581623)
      ·
        refine ⟨4629446478778917134372435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3086297652519278089581623 4629446478778917134372435)
        ·
          refine ⟨6944169718168375701558653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4629446478778917134372435 6944169718168375701558653)
          ·
            refine ⟨2604063644313140888084495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6944169718168375701558653 2604063644313140888084495)
            ·
              refine ⟨3906095466469711332126743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2604063644313140888084495 3906095466469711332126743)
              ·
                refine ⟨5859143199704566998190115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3906095466469711332126743 5859143199704566998190115)
                ·
                  refine ⟨8788714799556850497285173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5859143199704566998190115 8788714799556850497285173)
                  ·
                    refine ⟨823942012458454734120485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8788714799556850497285173 823942012458454734120485)
                    ·
                      rfl

theorem cell22_2406932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 3, 1, 1, 1, 5].length) (baseStart_2406932 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2406932 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2406932 prefixEnd_2406932 := by exact prefixLift 2406932
  have htrace : WordTrace (prefixWord ++ tailWord_2406932) baseStart_2406932 baseEnd_2406932 := by
    simpa [prefixWord, tailWord_2406932, baseEnd_2406932] using wordTrace_append hprefix tailTrace_2406932
  have hstable : (prefixWord ++ tailWord_2406932).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2406932).length < 2 ^ (prefixWord ++ tailWord_2406932).sum := by decide
  have hdescent : baseEnd_2406932 < baseStart_2406932 := by decide
  rcases family_descends (prefixWord ++ tailWord_2406932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2406951 : List Nat := [1, 1, 7, 2, 2, 1, 1, 3, 4]
def baseStart_2406951 : Nat := 118140960795 + 2406951 * 2 ^ 59
def prefixEnd_2406951 : Nat := 4983230072969 + 3 ^ 40 * 2406951 * 2
def baseEnd_2406951 : Nat := 274649505515581672631809

theorem tailTrace_2406951 : CollatzResearch.WordTrace tailWord_2406951 prefixEnd_2406951 274649505515581672631809 := by
  unfold tailWord_2406951
  simp only [CollatzResearch.WordTrace]
  refine ⟨87788715103035076348596707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58525810068690050899064471 87788715103035076348596707)
  ·
    refine ⟨131683072654552614522895061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87788715103035076348596707 131683072654552614522895061)
    ·
      refine ⟨3086322015341076902880353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 131683072654552614522895061 3086322015341076902880353)
      ·
        refine ⟨2314741511505807677160265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3086322015341076902880353 2314741511505807677160265)
        ·
          refine ⟨1736056133629355757870199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2314741511505807677160265 1736056133629355757870199)
          ·
            refine ⟨2604084200444033636805299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1736056133629355757870199 2604084200444033636805299)
            ·
              refine ⟨3906126300666050455207949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2604084200444033636805299 3906126300666050455207949)
              ·
                refine ⟨1464797362749768920702981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3906126300666050455207949 1464797362749768920702981)
                ·
                  refine ⟨274649505515581672631809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1464797362749768920702981 274649505515581672631809)
                  ·
                    rfl

theorem cell22_2406951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 2, 1, 1, 3, 4].length) (baseStart_2406951 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2406951 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2406951 prefixEnd_2406951 := by exact prefixLift 2406951
  have htrace : WordTrace (prefixWord ++ tailWord_2406951) baseStart_2406951 baseEnd_2406951 := by
    simpa [prefixWord, tailWord_2406951, baseEnd_2406951] using wordTrace_append hprefix tailTrace_2406951
  have hstable : (prefixWord ++ tailWord_2406951).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2406951).length < 2 ^ (prefixWord ++ tailWord_2406951).sum := by decide
  have hdescent : baseEnd_2406951 < baseStart_2406951 := by decide
  rcases family_descends (prefixWord ++ tailWord_2406951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2406973 : List Nat := [1, 4, 1, 3, 2, 1, 2, 1, 7]
def baseStart_2406973 : Nat := 118140960795 + 2406973 * 2 ^ 59
def prefixEnd_2406973 : Nat := 4983230072969 + 3 ^ 40 * 2406973 * 2
def baseEnd_2406973 : Nat := 274652015865448097948453

theorem tailTrace_2406973 : CollatzResearch.WordTrace tailWord_2406973 prefixEnd_2406973 274652015865448097948453 := by
  unfold tailWord_2406973
  simp only [CollatzResearch.WordTrace]
  refine ⟨87789517508955374105897573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58526345005970249403931715 87789517508955374105897573)
  ·
    refine ⟨16460534532929132644855795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 87789517508955374105897573 16460534532929132644855795)
    ·
      refine ⟨24690801799393698967283693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16460534532929132644855795 24690801799393698967283693)
      ·
        refine ⟨9259050674772637112731385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24690801799393698967283693 9259050674772637112731385)
        ·
          refine ⟨6944288006079477834548539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9259050674772637112731385 6944288006079477834548539)
          ·
            refine ⟨10416432009119216751822809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6944288006079477834548539 10416432009119216751822809)
            ·
              refine ⟨7812324006839412563867107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10416432009119216751822809 7812324006839412563867107)
              ·
                refine ⟨11718486010259118845800661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7812324006839412563867107 11718486010259118845800661)
                ·
                  refine ⟨274652015865448097948453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11718486010259118845800661 274652015865448097948453)
                  ·
                    rfl

theorem cell22_2406973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 2, 1, 7].length) (baseStart_2406973 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2406973 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2406973 prefixEnd_2406973 := by exact prefixLift 2406973
  have htrace : WordTrace (prefixWord ++ tailWord_2406973) baseStart_2406973 baseEnd_2406973 := by
    simpa [prefixWord, tailWord_2406973, baseEnd_2406973] using wordTrace_append hprefix tailTrace_2406973
  have hstable : (prefixWord ++ tailWord_2406973).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2406973).length < 2 ^ (prefixWord ++ tailWord_2406973).sum := by decide
  have hdescent : baseEnd_2406973 < baseStart_2406973 := by decide
  rcases family_descends (prefixWord ++ tailWord_2406973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2406977 : List Nat := [1, 2, 5, 1, 1, 4, 1, 1, 3, 3]
def baseStart_2406977 : Nat := 118140960795 + 2406977 * 2 ^ 59
def prefixEnd_2406977 : Nat := 4983230072969 + 3 ^ 40 * 2406977 * 2
def baseEnd_2406977 : Nat := 823957416878089616745347

theorem tailTrace_2406977 : CollatzResearch.WordTrace tailWord_2406977 prefixEnd_2406977 823957416878089616745347 := by
  unfold tailWord_2406977
  simp only [CollatzResearch.WordTrace]
  refine ⟨87789663400940882789043185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58526442267293921859362123 87789663400940882789043185)
  ·
    refine ⟨65842247550705662091782389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87789663400940882789043185 65842247550705662091782389)
    ·
      refine ⟨6172710707878655821104599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 65842247550705662091782389 6172710707878655821104599)
      ·
        refine ⟨9259066061817983731656899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6172710707878655821104599 9259066061817983731656899)
        ·
          refine ⟨13888599092726975597485349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9259066061817983731656899 13888599092726975597485349)
          ·
            refine ⟨2604112329886307924528503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13888599092726975597485349 2604112329886307924528503)
            ·
              refine ⟨3906168494829461886792755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2604112329886307924528503 3906168494829461886792755)
              ·
                refine ⟨5859252742244192830189133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3906168494829461886792755 5859252742244192830189133)
                ·
                  refine ⟨2197219778341572311320925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5859252742244192830189133 2197219778341572311320925)
                  ·
                    refine ⟨823957416878089616745347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2197219778341572311320925 823957416878089616745347)
                    ·
                      rfl

theorem cell22_2406977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 4, 1, 1, 3, 3].length) (baseStart_2406977 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2406977 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2406977 prefixEnd_2406977 := by exact prefixLift 2406977
  have htrace : WordTrace (prefixWord ++ tailWord_2406977) baseStart_2406977 baseEnd_2406977 := by
    simpa [prefixWord, tailWord_2406977, baseEnd_2406977] using wordTrace_append hprefix tailTrace_2406977
  have hstable : (prefixWord ++ tailWord_2406977).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2406977).length < 2 ^ (prefixWord ++ tailWord_2406977).sum := by decide
  have hdescent : baseEnd_2406977 < baseStart_2406977 := by decide
  rcases family_descends (prefixWord ++ tailWord_2406977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2406990 : List Nat := [4, 1, 1, 1, 1, 2, 6, 1, 5]
def baseStart_2406990 : Nat := 118140960795 + 2406990 * 2 ^ 59
def prefixEnd_2406990 : Nat := 4983230072969 + 3 ^ 40 * 2406990 * 2
def baseEnd_2406990 : Nat := 274653955681253972056769

theorem tailTrace_2406990 : CollatzResearch.WordTrace tailWord_2406990 prefixEnd_2406990 274653955681253972056769 := by
  unfold tailWord_2406990
  simp only [CollatzResearch.WordTrace]
  refine ⟨10973767193736723251158303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 58526758366595857339510949 10973767193736723251158303)
  ·
    refine ⟨16460650790605084876737455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10973767193736723251158303 16460650790605084876737455)
    ·
      refine ⟨24690976185907627315106183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16460650790605084876737455 24690976185907627315106183)
      ·
        refine ⟨37036464278861440972659275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24690976185907627315106183 37036464278861440972659275)
        ·
          refine ⟨55554696418292161458988913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37036464278861440972659275 55554696418292161458988913)
          ·
            refine ⟨41666022313719121094241685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55554696418292161458988913 41666022313719121094241685)
            ·
              refine ⟨1953094795955583801292579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 41666022313719121094241685 1953094795955583801292579)
              ·
                refine ⟨2929642193933375701938869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1953094795955583801292579 2929642193933375701938869)
                ·
                  refine ⟨274653955681253972056769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2929642193933375701938869 274653955681253972056769)
                  ·
                    rfl

theorem cell22_2406990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 6, 1, 5].length) (baseStart_2406990 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2406990 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2406990 prefixEnd_2406990 := by exact prefixLift 2406990
  have htrace : WordTrace (prefixWord ++ tailWord_2406990) baseStart_2406990 baseEnd_2406990 := by
    simpa [prefixWord, tailWord_2406990, baseEnd_2406990] using wordTrace_append hprefix tailTrace_2406990
  have hstable : (prefixWord ++ tailWord_2406990).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2406990).length < 2 ^ (prefixWord ++ tailWord_2406990).sum := by decide
  have hdescent : baseEnd_2406990 < baseStart_2406990 := by decide
  rcases family_descends (prefixWord ++ tailWord_2406990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2407185 : List Nat := [1, 2, 2, 1, 1, 3, 2, 1, 6, 3]
def baseStart_2407185 : Nat := 118140960795 + 2407185 * 2 ^ 59
def prefixEnd_2407185 : Nat := 4983230072969 + 3 ^ 40 * 2407185 * 2
def baseEnd_2407185 : Nat := 824028619528846407544709

theorem tailTrace_2407185 : CollatzResearch.WordTrace tailWord_2407185 prefixEnd_2407185 824028619528846407544709 := by
  unfold tailWord_2407185
  simp only [CollatzResearch.WordTrace]
  refine ⟨87797249784187334312615009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58531499856124889541743339 87797249784187334312615009)
  ·
    refine ⟨65847937338140500734461257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87797249784187334312615009 65847937338140500734461257)
    ·
      refine ⟨49385953003605375550845943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65847937338140500734461257 49385953003605375550845943)
      ·
        refine ⟨74078929505408063326268915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49385953003605375550845943 74078929505408063326268915)
        ·
          refine ⟨111118394258112094989403373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74078929505408063326268915 111118394258112094989403373)
          ·
            refine ⟨41669397846792035621026265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 111118394258112094989403373 41669397846792035621026265)
            ·
              refine ⟨31252048385094026715769699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41669397846792035621026265 31252048385094026715769699)
              ·
                refine ⟨46878072577641040073654549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31252048385094026715769699 46878072577641040073654549)
                ·
                  refine ⟨2197409652076923753452557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 46878072577641040073654549 2197409652076923753452557)
                  ·
                    refine ⟨824028619528846407544709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2197409652076923753452557 824028619528846407544709)
                    ·
                      rfl

theorem cell22_2407185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 1, 6, 3].length) (baseStart_2407185 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2407185 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2407185 prefixEnd_2407185 := by exact prefixLift 2407185
  have htrace : WordTrace (prefixWord ++ tailWord_2407185) baseStart_2407185 baseEnd_2407185 := by
    simpa [prefixWord, tailWord_2407185, baseEnd_2407185] using wordTrace_append hprefix tailTrace_2407185
  have hstable : (prefixWord ++ tailWord_2407185).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2407185).length < 2 ^ (prefixWord ++ tailWord_2407185).sum := by decide
  have hdescent : baseEnd_2407185 < baseStart_2407185 := by decide
  rcases family_descends (prefixWord ++ tailWord_2407185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2407204 : List Nat := [2, 3, 1, 3, 3, 1, 1, 4, 4]
def baseStart_2407204 : Nat := 118140960795 + 2407204 * 2 ^ 59
def prefixEnd_2407204 : Nat := 4983230072969 + 3 ^ 40 * 2407204 * 2
def baseEnd_2407204 : Nat := 274678374539045563773217

theorem tailTrace_2407204 : CollatzResearch.WordTrace tailWord_2407204 prefixEnd_2407204 274678374539045563773217 := by
  unfold tailWord_2407204
  simp only [CollatzResearch.WordTrace]
  refine ⟨43898971385559250278778333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58531961847412333705037777 43898971385559250278778333)
  ·
    refine ⟨16462114269584718854541875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43898971385559250278778333 16462114269584718854541875)
    ·
      refine ⟨24693171404377078281812813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16462114269584718854541875 24693171404377078281812813)
      ·
        refine ⟨9259939276641404355679805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24693171404377078281812813 9259939276641404355679805)
        ·
          refine ⟨3472477228740526633379927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9259939276641404355679805 3472477228740526633379927)
          ·
            refine ⟨5208715843110789950069891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3472477228740526633379927 5208715843110789950069891)
            ·
              refine ⟨7813073764666184925104837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5208715843110789950069891 7813073764666184925104837)
              ·
                refine ⟨1464951330874909673457157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7813073764666184925104837 1464951330874909673457157)
                ·
                  refine ⟨274678374539045563773217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1464951330874909673457157 274678374539045563773217)
                  ·
                    rfl

theorem cell22_2407204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 1, 4, 4].length) (baseStart_2407204 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2407204 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2407204 prefixEnd_2407204 := by exact prefixLift 2407204
  have htrace : WordTrace (prefixWord ++ tailWord_2407204) baseStart_2407204 baseEnd_2407204 := by
    simpa [prefixWord, tailWord_2407204, baseEnd_2407204] using wordTrace_append hprefix tailTrace_2407204
  have hstable : (prefixWord ++ tailWord_2407204).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2407204).length < 2 ^ (prefixWord ++ tailWord_2407204).sum := by decide
  have hdescent : baseEnd_2407204 < baseStart_2407204 := by decide
  rcases family_descends (prefixWord ++ tailWord_2407204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2407238 : List Nat := [6, 1, 1, 2, 2, 1, 2, 3, 4]
def baseStart_2407238 : Nat := 118140960795 + 2407238 * 2 ^ 59
def prefixEnd_2407238 : Nat := 4983230072969 + 3 ^ 40 * 2407238 * 2
def baseEnd_2407238 : Nat := 274682254170657311989849

theorem tailTrace_2407238 : CollatzResearch.WordTrace tailWord_2407238 prefixEnd_2407238 274682254170657311989849 := by
  unfold tailWord_2407238
  simp only [CollatzResearch.WordTrace]
  refine ⟨2743724464156103886384199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 58532788568663549576196245 2743724464156103886384199)
  ·
    refine ⟨4115586696234155829576299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2743724464156103886384199 4115586696234155829576299)
    ·
      refine ⟨6173380044351233744364449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4115586696234155829576299 6173380044351233744364449)
      ·
        refine ⟨4630035033263425308273337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6173380044351233744364449 4630035033263425308273337)
        ·
          refine ⟨3472526274947568981205003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4630035033263425308273337 3472526274947568981205003)
          ·
            refine ⟨5208789412421353471807505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3472526274947568981205003 5208789412421353471807505)
            ·
              refine ⟨3906592059316015103855629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5208789412421353471807505 3906592059316015103855629)
              ·
                refine ⟨1464972022243505663945861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3906592059316015103855629 1464972022243505663945861)
                ·
                  refine ⟨274682254170657311989849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1464972022243505663945861 274682254170657311989849)
                  ·
                    rfl

theorem cell22_2407238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 2, 3, 4].length) (baseStart_2407238 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2407238 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2407238 prefixEnd_2407238 := by exact prefixLift 2407238
  have htrace : WordTrace (prefixWord ++ tailWord_2407238) baseStart_2407238 baseEnd_2407238 := by
    simpa [prefixWord, tailWord_2407238, baseEnd_2407238] using wordTrace_append hprefix tailTrace_2407238
  have hstable : (prefixWord ++ tailWord_2407238).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2407238).length < 2 ^ (prefixWord ++ tailWord_2407238).sum := by decide
  have hdescent : baseEnd_2407238 < baseStart_2407238 := by decide
  rcases family_descends (prefixWord ++ tailWord_2407238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2407264 : List Nat := [2, 1, 1, 3, 3, 1, 1, 6, 1, 3]
def baseStart_2407264 : Nat := 118140960795 + 2407264 * 2 ^ 59
def prefixEnd_2407264 : Nat := 4983230072969 + 3 ^ 40 * 2407264 * 2
def baseEnd_2407264 : Nat := 824055662843316534819467

theorem tailTrace_2407264 : CollatzResearch.WordTrace tailWord_2407264 prefixEnd_2407264 824055662843316534819467 := by
  unfold tailWord_2407264
  simp only [CollatzResearch.WordTrace]
  refine ⟨43900065575450565402370423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58533420767267420536493897 43900065575450565402370423)
  ·
    refine ⟨65850098363175848103555635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43900065575450565402370423 65850098363175848103555635)
    ·
      refine ⟨98775147544763772155333453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65850098363175848103555635 98775147544763772155333453)
      ·
        refine ⟨37040680329286414558250045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 98775147544763772155333453 37040680329286414558250045)
        ·
          refine ⟨13890255123482405459343767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37040680329286414558250045 13890255123482405459343767)
          ·
            refine ⟨20835382685223608189015651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13890255123482405459343767 20835382685223608189015651)
            ·
              refine ⟨31253074027835412283523477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20835382685223608189015651 31253074027835412283523477)
              ·
                refine ⟨1464987845054784950790163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 31253074027835412283523477 1464987845054784950790163)
                ·
                  refine ⟨2197481767582177426185245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1464987845054784950790163 2197481767582177426185245)
                  ·
                    refine ⟨824055662843316534819467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2197481767582177426185245 824055662843316534819467)
                    ·
                      rfl

theorem cell22_2407264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 6, 1, 3].length) (baseStart_2407264 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2407264 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2407264 prefixEnd_2407264 := by exact prefixLift 2407264
  have htrace : WordTrace (prefixWord ++ tailWord_2407264) baseStart_2407264 baseEnd_2407264 := by
    simpa [prefixWord, tailWord_2407264, baseEnd_2407264] using wordTrace_append hprefix tailTrace_2407264
  have hstable : (prefixWord ++ tailWord_2407264).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2407264).length < 2 ^ (prefixWord ++ tailWord_2407264).sum := by decide
  have hdescent : baseEnd_2407264 < baseStart_2407264 := by decide
  rcases family_descends (prefixWord ++ tailWord_2407264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2407275 : List Nat := [1, 1, 1, 1, 2, 2, 6, 1, 2, 5]
def baseStart_2407275 : Nat := 118140960795 + 2407275 * 2 ^ 59
def prefixEnd_2407275 : Nat := 4983230072969 + 3 ^ 40 * 2407275 * 2
def baseEnd_2407275 : Nat := 824059428368116172794433

theorem tailTrace_2407275 : CollatzResearch.WordTrace tailWord_2407275 prefixEnd_2407275 824059428368116172794433 := by
  unfold tailWord_2407275
  simp only [CollatzResearch.WordTrace]
  refine ⟨87800532353861279683391279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58533688235907519788927519 87800532353861279683391279)
  ·
    refine ⟨131700798530791919525086919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87800532353861279683391279 131700798530791919525086919)
    ·
      refine ⟨197551197796187879287630379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131700798530791919525086919 197551197796187879287630379)
      ·
        refine ⟨296326796694281818931445569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 197551197796187879287630379 296326796694281818931445569)
        ·
          refine ⟨222245097520711364198584177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 296326796694281818931445569 222245097520711364198584177)
          ·
            refine ⟨166683823140533523148938133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 222245097520711364198584177 166683823140533523148938133)
            ·
              refine ⟨7813304209712508897606475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 166683823140533523148938133 7813304209712508897606475)
              ·
                refine ⟨11719956314568763346409713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7813304209712508897606475 11719956314568763346409713)
                ·
                  refine ⟨8789967235926572509807285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11719956314568763346409713 8789967235926572509807285)
                  ·
                    refine ⟨824059428368116172794433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8789967235926572509807285 824059428368116172794433)
                    ·
                      rfl

theorem cell22_2407275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 6, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 6, 1, 2, 5].length) (baseStart_2407275 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2407275 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2407275 prefixEnd_2407275 := by exact prefixLift 2407275
  have htrace : WordTrace (prefixWord ++ tailWord_2407275) baseStart_2407275 baseEnd_2407275 := by
    simpa [prefixWord, tailWord_2407275, baseEnd_2407275] using wordTrace_append hprefix tailTrace_2407275
  have hstable : (prefixWord ++ tailWord_2407275).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2407275).length < 2 ^ (prefixWord ++ tailWord_2407275).sum := by decide
  have hdescent : baseEnd_2407275 < baseStart_2407275 := by decide
  rcases family_descends (prefixWord ++ tailWord_2407275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2407307 : List Nat := [1, 1, 1, 1, 4, 2, 4, 3, 1, 4]
def baseStart_2407307 : Nat := 118140960795 + 2407307 * 2 ^ 59
def prefixEnd_2407307 : Nat := 4983230072969 + 3 ^ 40 * 2407307 * 2
def baseEnd_2407307 : Nat := 824070382622078755994335

theorem tailTrace_2407307 : CollatzResearch.WordTrace tailWord_2407307 prefixEnd_2407307 824070382622078755994335 := by
  unfold tailWord_2407307
  simp only [CollatzResearch.WordTrace]
  refine ⟨87801699489745349148556175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58534466326496899432370783 87801699489745349148556175)
  ·
    refine ⟨131702549234618023722834263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87801699489745349148556175 131702549234618023722834263)
    ·
      refine ⟨197553823851927035584251395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131702549234618023722834263 197553823851927035584251395)
      ·
        refine ⟨296330735777890553376377093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 197553823851927035584251395 296330735777890553376377093)
        ·
          refine ⟨55562012958354478758070705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 296330735777890553376377093 55562012958354478758070705)
          ·
            refine ⟨41671509718765859068553029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55562012958354478758070705 41671509718765859068553029)
            ·
              refine ⟨7813408072268598575353693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 41671509718765859068553029 7813408072268598575353693)
              ·
                refine ⟨2930028027100724465757635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7813408072268598575353693 2930028027100724465757635)
                ·
                  refine ⟨4395042040651086698636453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2930028027100724465757635 4395042040651086698636453)
                  ·
                    refine ⟨824070382622078755994335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4395042040651086698636453 824070382622078755994335)
                    ·
                      rfl

theorem cell22_2407307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 4, 3, 1, 4].length) (baseStart_2407307 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2407307 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2407307 prefixEnd_2407307 := by exact prefixLift 2407307
  have htrace : WordTrace (prefixWord ++ tailWord_2407307) baseStart_2407307 baseEnd_2407307 := by
    simpa [prefixWord, tailWord_2407307, baseEnd_2407307] using wordTrace_append hprefix tailTrace_2407307
  have hstable : (prefixWord ++ tailWord_2407307).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2407307).length < 2 ^ (prefixWord ++ tailWord_2407307).sum := by decide
  have hdescent : baseEnd_2407307 < baseStart_2407307 := by decide
  rcases family_descends (prefixWord ++ tailWord_2407307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2407341 : List Nat := [1, 5, 2, 3, 1, 1, 1, 1, 3, 4]
def baseStart_2407341 : Nat := 118140960795 + 2407341 * 2 ^ 59
def prefixEnd_2407341 : Nat := 4983230072969 + 3 ^ 40 * 2407341 * 2
def baseEnd_2407341 : Nat := 824082021516914000644231

theorem tailTrace_2407341 : CollatzResearch.WordTrace tailWord_2407341 prefixEnd_2407341 824082021516914000644231 := by
  unfold tailWord_2407341
  simp only [CollatzResearch.WordTrace]
  refine ⟨87802939571622172955293877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58535293047748115303529251 87802939571622172955293877)
  ·
    refine ⟨8231525584839578714558801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 87802939571622172955293877 8231525584839578714558801)
    ·
      refine ⟨6173644188629684035919101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8231525584839578714558801 6173644188629684035919101)
      ·
        refine ⟨2315116570736131513469663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6173644188629684035919101 2315116570736131513469663)
        ·
          refine ⟨3472674856104197270204495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2315116570736131513469663 3472674856104197270204495)
          ·
            refine ⟨5209012284156295905306743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3472674856104197270204495 5209012284156295905306743)
            ·
              refine ⟨7813518426234443857960115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5209012284156295905306743 7813518426234443857960115)
              ·
                refine ⟨11720277639351665786940173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7813518426234443857960115 11720277639351665786940173)
                ·
                  refine ⟨4395104114756874670102565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11720277639351665786940173 4395104114756874670102565)
                  ·
                    refine ⟨824082021516914000644231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4395104114756874670102565 824082021516914000644231)
                    ·
                      rfl

theorem cell22_2407341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 1, 1, 3, 4].length) (baseStart_2407341 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2407341 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2407341 prefixEnd_2407341 := by exact prefixLift 2407341
  have htrace : WordTrace (prefixWord ++ tailWord_2407341) baseStart_2407341 baseEnd_2407341 := by
    simpa [prefixWord, tailWord_2407341, baseEnd_2407341] using wordTrace_append hprefix tailTrace_2407341
  have hstable : (prefixWord ++ tailWord_2407341).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2407341).length < 2 ^ (prefixWord ++ tailWord_2407341).sum := by decide
  have hdescent : baseEnd_2407341 < baseStart_2407341 := by decide
  rcases family_descends (prefixWord ++ tailWord_2407341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2407352 : List Nat := [2, 1, 2, 1, 2, 4, 1, 3, 2, 4]
def baseStart_2407352 : Nat := 118140960795 + 2407352 * 2 ^ 59
def prefixEnd_2407352 : Nat := 4983230072969 + 3 ^ 40 * 2407352 * 2
def baseEnd_2407352 : Nat := 824085787041713638619197

theorem tailTrace_2407352 : CollatzResearch.WordTrace tailWord_2407352 prefixEnd_2407352 824085787041713638619197 := by
  unfold tailWord_2407352
  simp only [CollatzResearch.WordTrace]
  refine ⟨43901670387291160916972155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58535560516388214555962873 43901670387291160916972155)
  ·
    refine ⟨65852505580936741375458233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43901670387291160916972155 65852505580936741375458233)
    ·
      refine ⟨49389379185702556031593675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65852505580936741375458233 49389379185702556031593675)
      ·
        refine ⟨74084068778553834047390513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49389379185702556031593675 74084068778553834047390513)
        ·
          refine ⟨55563051583915375535542885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74084068778553834047390513 55563051583915375535542885)
          ·
            refine ⟨10418072171984132912914291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 55563051583915375535542885 10418072171984132912914291)
            ·
              refine ⟨15627108257976199369371437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10418072171984132912914291 15627108257976199369371437)
              ·
                refine ⟨5860165596741074763514289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15627108257976199369371437 5860165596741074763514289)
                ·
                  refine ⟨4395124197555806072635717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5860165596741074763514289 4395124197555806072635717)
                  ·
                    refine ⟨824085787041713638619197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4395124197555806072635717 824085787041713638619197)
                    ·
                      rfl

theorem cell22_2407352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 1, 3, 2, 4].length) (baseStart_2407352 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2407352 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2407352 prefixEnd_2407352 := by exact prefixLift 2407352
  have htrace : WordTrace (prefixWord ++ tailWord_2407352) baseStart_2407352 baseEnd_2407352 := by
    simpa [prefixWord, tailWord_2407352, baseEnd_2407352] using wordTrace_append hprefix tailTrace_2407352
  have hstable : (prefixWord ++ tailWord_2407352).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2407352).length < 2 ^ (prefixWord ++ tailWord_2407352).sum := by decide
  have hdescent : baseEnd_2407352 < baseStart_2407352 := by decide
  rcases family_descends (prefixWord ++ tailWord_2407352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2407365 : List Nat := [1, 3, 1, 1, 1, 1, 1, 2, 4, 7]
def baseStart_2407365 : Nat := 118140960795 + 2407365 * 2 ^ 59
def prefixEnd_2407365 : Nat := 4983230072969 + 3 ^ 40 * 2407365 * 2
def baseEnd_2407365 : Nat := 824090237207385938044157

theorem tailTrace_2407365 : CollatzResearch.WordTrace tailWord_2407365 prefixEnd_2407365 824090237207385938044157 := by
  unfold tailWord_2407365
  simp only [CollatzResearch.WordTrace]
  refine ⟨87803814923535225054167549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58535876615690150036111699 87803814923535225054167549)
  ·
    refine ⟨32926430596325709395312831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 87803814923535225054167549 32926430596325709395312831)
    ·
      refine ⟨49389645894488564092969247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32926430596325709395312831 49389645894488564092969247)
      ·
        refine ⟨74084468841732846139453871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49389645894488564092969247 74084468841732846139453871)
        ·
          refine ⟨111126703262599269209180807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74084468841732846139453871 111126703262599269209180807)
          ·
            refine ⟨166690054893898903813771211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 111126703262599269209180807 166690054893898903813771211)
            ·
              refine ⟨250035082340848355720656817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 166690054893898903813771211 250035082340848355720656817)
              ·
                refine ⟨187526311755636266790492613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 250035082340848355720656817 187526311755636266790492613)
                ·
                  refine ⟨35161183454181800023217365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 187526311755636266790492613 35161183454181800023217365)
                  ·
                    refine ⟨824090237207385938044157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 35161183454181800023217365 824090237207385938044157)
                    ·
                      rfl

theorem cell22_2407365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 2, 4, 7].length) (baseStart_2407365 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2407365 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2407365 prefixEnd_2407365 := by exact prefixLift 2407365
  have htrace : WordTrace (prefixWord ++ tailWord_2407365) baseStart_2407365 baseEnd_2407365 := by
    simpa [prefixWord, tailWord_2407365, baseEnd_2407365] using wordTrace_append hprefix tailTrace_2407365
  have hstable : (prefixWord ++ tailWord_2407365).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2407365).length < 2 ^ (prefixWord ++ tailWord_2407365).sum := by decide
  have hdescent : baseEnd_2407365 < baseStart_2407365 := by decide
  rcases family_descends (prefixWord ++ tailWord_2407365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2407366 : List Nat := [6, 1, 3, 1, 1, 2, 2, 2, 1, 3]
def baseStart_2407366 : Nat := 118140960795 + 2407366 * 2 ^ 59
def prefixEnd_2407366 : Nat := 4983230072969 + 3 ^ 40 * 2407366 * 2
def baseEnd_2407366 : Nat := 824090579527822268769155

theorem tailTrace_2407366 : CollatzResearch.WordTrace tailWord_2407366 prefixEnd_2407366 824090579527822268769155 := by
  unfold tailWord_2407366
  simp only [CollatzResearch.WordTrace]
  refine ⟨2743870356141612569529811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 58535900931021068149969301 2743870356141612569529811)
  ·
    refine ⟨4115805534212418854294717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2743870356141612569529811 4115805534212418854294717)
    ·
      refine ⟨1543427075329657070360519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4115805534212418854294717 1543427075329657070360519)
      ·
        refine ⟨2315140612994485605540779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1543427075329657070360519 2315140612994485605540779)
        ·
          refine ⟨3472710919491728408311169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2315140612994485605540779 3472710919491728408311169)
          ·
            refine ⟨2604533189618796306233377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3472710919491728408311169 2604533189618796306233377)
            ·
              refine ⟨1953399892214097229675033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2604533189618796306233377 1953399892214097229675033)
              ·
                refine ⟨1465049919160572922256275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1953399892214097229675033 1465049919160572922256275)
                ·
                  refine ⟨2197574878740859383384413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1465049919160572922256275 2197574878740859383384413)
                  ·
                    refine ⟨824090579527822268769155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2197574878740859383384413 824090579527822268769155)
                    ·
                      rfl

theorem cell22_2407366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 2, 2, 2, 1, 3].length) (baseStart_2407366 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2407366 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2407366 prefixEnd_2407366 := by exact prefixLift 2407366
  have htrace : WordTrace (prefixWord ++ tailWord_2407366) baseStart_2407366 baseEnd_2407366 := by
    simpa [prefixWord, tailWord_2407366, baseEnd_2407366] using wordTrace_append hprefix tailTrace_2407366
  have hstable : (prefixWord ++ tailWord_2407366).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2407366).length < 2 ^ (prefixWord ++ tailWord_2407366).sum := by decide
  have hdescent : baseEnd_2407366 < baseStart_2407366 := by decide
  rcases family_descends (prefixWord ++ tailWord_2407366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2407399 : List Nat := [1, 1, 5, 2, 2, 1, 1, 1, 5, 3]
def baseStart_2407399 : Nat := 118140960795 + 2407399 * 2 ^ 59
def prefixEnd_2407399 : Nat := 4983230072969 + 3 ^ 40 * 2407399 * 2
def baseEnd_2407399 : Nat := 824101876102221182694053

theorem tailTrace_2407399 : CollatzResearch.WordTrace tailWord_2407399 prefixEnd_2407399 824101876102221182694053 := by
  unfold tailWord_2407399
  simp only [CollatzResearch.WordTrace]
  refine ⟨87805055005412048860905251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58536703336941365907270167 87805055005412048860905251)
  ·
    refine ⟨131707582508118073291357877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87805055005412048860905251 131707582508118073291357877)
    ·
      refine ⟨12347585860136069371064801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 131707582508118073291357877 12347585860136069371064801)
      ·
        refine ⟨9260689395102052028298601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12347585860136069371064801 9260689395102052028298601)
        ·
          refine ⟨6945517046326539021223951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9260689395102052028298601 6945517046326539021223951)
          ·
            refine ⟨10418275569489808531835927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6945517046326539021223951 10418275569489808531835927)
            ·
              refine ⟨15627413354234712797753891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10418275569489808531835927 15627413354234712797753891)
              ·
                refine ⟨23441120031352069196630837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15627413354234712797753891 23441120031352069196630837)
                ·
                  refine ⟨2197605002939256487184141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 23441120031352069196630837 2197605002939256487184141)
                  ·
                    refine ⟨824101876102221182694053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2197605002939256487184141 824101876102221182694053)
                    ·
                      rfl

theorem cell22_2407399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 1, 1, 5, 3].length) (baseStart_2407399 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2407399 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2407399 prefixEnd_2407399 := by exact prefixLift 2407399
  have htrace : WordTrace (prefixWord ++ tailWord_2407399) baseStart_2407399 baseEnd_2407399 := by
    simpa [prefixWord, tailWord_2407399, baseEnd_2407399] using wordTrace_append hprefix tailTrace_2407399
  have hstable : (prefixWord ++ tailWord_2407399).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2407399).length < 2 ^ (prefixWord ++ tailWord_2407399).sum := by decide
  have hdescent : baseEnd_2407399 < baseStart_2407399 := by decide
  rcases family_descends (prefixWord ++ tailWord_2407399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2407459 : List Nat := [1, 1, 1, 4, 3, 2, 1, 4, 1, 4]
def baseStart_2407459 : Nat := 118140960795 + 2407459 * 2 ^ 59
def prefixEnd_2407459 : Nat := 4983230072969 + 3 ^ 40 * 2407459 * 2
def baseEnd_2407459 : Nat := 824122415328401026193869

theorem tailTrace_2407459 : CollatzResearch.WordTrace tailWord_2407459 prefixEnd_2407459 824122415328401026193869 := by
  unfold tailWord_2407459
  simp only [CollatzResearch.WordTrace]
  refine ⟨87807243385194679108089431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58538162256796452738726287 87807243385194679108089431)
  ·
    refine ⟨131710865077792018662134147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87807243385194679108089431 131710865077792018662134147)
    ·
      refine ⟨197566297616688027993201221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131710865077792018662134147 197566297616688027993201221)
      ·
        refine ⟨37043680803129005248725229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 197566297616688027993201221 37043680803129005248725229)
        ·
          refine ⟨13891380301173376968271961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37043680803129005248725229 13891380301173376968271961)
          ·
            refine ⟨10418535225880032726203971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13891380301173376968271961 10418535225880032726203971)
            ·
              refine ⟨15627802838820049089305957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10418535225880032726203971 15627802838820049089305957)
              ·
                refine ⟨2930213032278759204244867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15627802838820049089305957 2930213032278759204244867)
                ·
                  refine ⟨4395319548418138806367301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2930213032278759204244867 4395319548418138806367301)
                  ·
                    refine ⟨824122415328401026193869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4395319548418138806367301 824122415328401026193869)
                    ·
                      rfl

theorem cell22_2407459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 1, 4, 1, 4].length) (baseStart_2407459 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2407459 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2407459 prefixEnd_2407459 := by exact prefixLift 2407459
  have htrace : WordTrace (prefixWord ++ tailWord_2407459) baseStart_2407459 baseEnd_2407459 := by
    simpa [prefixWord, tailWord_2407459, baseEnd_2407459] using wordTrace_append hprefix tailTrace_2407459
  have hstable : (prefixWord ++ tailWord_2407459).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2407459).length < 2 ^ (prefixWord ++ tailWord_2407459).sum := by decide
  have hdescent : baseEnd_2407459 < baseStart_2407459 := by decide
  rcases family_descends (prefixWord ++ tailWord_2407459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
