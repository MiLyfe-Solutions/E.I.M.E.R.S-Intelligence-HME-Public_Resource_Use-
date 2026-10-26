import V185TrunkScan23Chunk0918

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_5439079 : List Nat := [1, 1, 5, 1, 1, 1, 2, 5, 1, 2, 3]
def baseStart_5439079 : Nat := 118140960795 + 5439079 * 2 ^ 59
def prefixEnd_5439079 : Nat := 4983230072969 + 3 ^ 40 * 5439079 * 2
def baseEnd_5439079 : Nat := 2792861844776030312098637

theorem tailTrace_5439079 : CollatzResearch.WordTrace tailWord_5439079 prefixEnd_5439079 2792861844776030312098637 := by
  unfold tailWord_5439079
  simp only [CollatzResearch.WordTrace]
  refine ⟨198379508662153178583152291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132253005774768785722101527 198379508662153178583152291)
  ·
    refine ⟨297569262993229767874728437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198379508662153178583152291 297569262993229767874728437)
    ·
      refine ⟨27897118405615290738255791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 297569262993229767874728437 27897118405615290738255791)
      ·
        refine ⟨41845677608422936107383687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27897118405615290738255791 41845677608422936107383687)
        ·
          refine ⟨62768516412634404161075531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41845677608422936107383687 62768516412634404161075531)
          ·
            refine ⟨94152774618951606241613297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62768516412634404161075531 94152774618951606241613297)
            ·
              refine ⟨70614580964213704681209973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 94152774618951606241613297 70614580964213704681209973)
              ·
                refine ⟨6620116965395034813863435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 70614580964213704681209973 6620116965395034813863435)
                ·
                  refine ⟨9930175448092552220795153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6620116965395034813863435 9930175448092552220795153)
                  ·
                    refine ⟨7447631586069414165596365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9930175448092552220795153 7447631586069414165596365)
                    ·
                      refine ⟨2792861844776030312098637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7447631586069414165596365 2792861844776030312098637)
                      ·
                        rfl

theorem cell23_5439079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 5, 1, 2, 3].length) (baseStart_5439079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5439079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5439079 prefixEnd_5439079 := by exact prefixLift 5439079
  have htrace : WordTrace (prefixWord ++ tailWord_5439079) baseStart_5439079 baseEnd_5439079 := by
    simpa [prefixWord, tailWord_5439079, baseEnd_5439079] using wordTrace_append hprefix tailTrace_5439079
  have hstable : (prefixWord ++ tailWord_5439079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5439079).length < 2 ^ (prefixWord ++ tailWord_5439079).sum := by decide
  have hdescent : baseEnd_5439079 < baseStart_5439079 := by decide
  rcases family_descends (prefixWord ++ tailWord_5439079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5439109 : List Nat := [1, 3, 1, 1, 4, 1, 4, 1, 1, 3, 3]
def baseStart_5439109 : Nat := 118140960795 + 5439109 * 2 ^ 59
def prefixEnd_5439109 : Nat := 4983230072969 + 3 ^ 40 * 5439109 * 2
def baseEnd_5439109 : Nat := 2792877249195665194723499

theorem tailTrace_5439109 : CollatzResearch.WordTrace tailWord_5439109 prefixEnd_5439109 2792877249195665194723499 := by
  unfold tailWord_5439109
  simp only [CollatzResearch.WordTrace]
  refine ⟨198380602852044493706744381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132253735234696329137829587 198380602852044493706744381)
  ·
    refine ⟨74392726069516685140029143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 198380602852044493706744381 74392726069516685140029143)
    ·
      refine ⟨111589089104275027710043715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74392726069516685140029143 111589089104275027710043715)
      ·
        refine ⟨167383633656412541565065573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111589089104275027710043715 167383633656412541565065573)
        ·
          refine ⟨31384431310577351543449795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 167383633656412541565065573 31384431310577351543449795)
          ·
            refine ⟨47076646965866027315174693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31384431310577351543449795 47076646965866027315174693)
            ·
              refine ⟨8826871306099880121595255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 47076646965866027315174693 8826871306099880121595255)
              ·
                refine ⟨13240306959149820182392883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8826871306099880121595255 13240306959149820182392883)
                ·
                  refine ⟨19860460438724730273589325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13240306959149820182392883 19860460438724730273589325)
                  ·
                    refine ⟨7447672664521773852595997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19860460438724730273589325 7447672664521773852595997)
                    ·
                      refine ⟨2792877249195665194723499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7447672664521773852595997 2792877249195665194723499)
                      ·
                        rfl

theorem cell23_5439109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 4, 1, 1, 3, 3].length) (baseStart_5439109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5439109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5439109 prefixEnd_5439109 := by exact prefixLift 5439109
  have htrace : WordTrace (prefixWord ++ tailWord_5439109) baseStart_5439109 baseEnd_5439109 := by
    simpa [prefixWord, tailWord_5439109, baseEnd_5439109] using wordTrace_append hprefix tailTrace_5439109
  have hstable : (prefixWord ++ tailWord_5439109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5439109).length < 2 ^ (prefixWord ++ tailWord_5439109).sum := by decide
  have hdescent : baseEnd_5439109 < baseStart_5439109 := by decide
  rcases family_descends (prefixWord ++ tailWord_5439109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5439152 : List Nat := [2, 1, 1, 1, 2, 1, 4, 1, 1, 6, 3]
def baseStart_5439152 : Nat := 118140960795 + 5439152 * 2 ^ 59
def prefixEnd_5439152 : Nat := 4983230072969 + 3 ^ 40 * 5439152 * 2
def baseEnd_5439152 : Nat := 2792899328863808526485801

theorem tailTrace_5439152 : CollatzResearch.WordTrace tailWord_5439152 prefixEnd_5439152 2792899328863808526485801 := by
  unfold tailWord_5439152
  simp only [CollatzResearch.WordTrace]
  refine ⟨99191085595444356025279855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132254780793925808033706473 99191085595444356025279855)
  ·
    refine ⟨148786628393166534037919783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99191085595444356025279855 148786628393166534037919783)
    ·
      refine ⟨223179942589749801056879675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148786628393166534037919783 223179942589749801056879675)
      ·
        refine ⟨334769913884624701585319513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 223179942589749801056879675 334769913884624701585319513)
        ·
          refine ⟨251077435413468526188989635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 334769913884624701585319513 251077435413468526188989635)
          ·
            refine ⟨376616153120202789283484453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 251077435413468526188989635 376616153120202789283484453)
            ·
              refine ⟨70615528710038022990653335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 376616153120202789283484453 70615528710038022990653335)
              ·
                refine ⟨105923293065057034485980003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70615528710038022990653335 105923293065057034485980003)
                ·
                  refine ⟨158884939597585551728970005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 105923293065057034485980003 158884939597585551728970005)
                  ·
                    refine ⟨7447731543636822737295469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 158884939597585551728970005 7447731543636822737295469)
                    ·
                      refine ⟨2792899328863808526485801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7447731543636822737295469 2792899328863808526485801)
                      ·
                        rfl

theorem cell23_5439152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 1, 1, 6, 3].length) (baseStart_5439152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5439152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5439152 prefixEnd_5439152 := by exact prefixLift 5439152
  have htrace : WordTrace (prefixWord ++ tailWord_5439152) baseStart_5439152 baseEnd_5439152 := by
    simpa [prefixWord, tailWord_5439152, baseEnd_5439152] using wordTrace_append hprefix tailTrace_5439152
  have hstable : (prefixWord ++ tailWord_5439152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5439152).length < 2 ^ (prefixWord ++ tailWord_5439152).sum := by decide
  have hdescent : baseEnd_5439152 < baseStart_5439152 := by decide
  rcases family_descends (prefixWord ++ tailWord_5439152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5439209 : List Nat := [1, 2, 1, 1, 1, 2, 3, 3, 2, 5, 2]
def baseStart_5439209 : Nat := 118140960795 + 5439209 * 2 ^ 59
def prefixEnd_5439209 : Nat := 4983230072969 + 3 ^ 40 * 5439209 * 2
def baseEnd_5439209 : Nat := 2792928597261114803473039

theorem tailTrace_5439209 : CollatzResearch.WordTrace tailWord_5439209 prefixEnd_5439209 2792928597261114803473039 := by
  unfold tailWord_5439209
  simp only [CollatzResearch.WordTrace]
  refine ⟨198384250151682210785384681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132256166767788140523589787 198384250151682210785384681)
  ·
    refine ⟨148788187613761658089038511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 198384250151682210785384681 148788187613761658089038511)
    ·
      refine ⟨223182281420642487133557767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148788187613761658089038511 223182281420642487133557767)
      ·
        refine ⟨334773422130963730700336651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 223182281420642487133557767 334773422130963730700336651)
        ·
          refine ⟨502160133196445596050504977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 334773422130963730700336651 502160133196445596050504977)
          ·
            refine ⟨376620099897334197037878733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 502160133196445596050504977 376620099897334197037878733)
            ·
              refine ⟨141232537461500323889204525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 376620099897334197037878733 141232537461500323889204525)
              ·
                refine ⟨52962201548062621458451697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 141232537461500323889204525 52962201548062621458451697)
                ·
                  refine ⟨39721651161046966093838773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 52962201548062621458451697 39721651161046966093838773)
                  ·
                    refine ⟨3723904796348153071297385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 39721651161046966093838773 3723904796348153071297385)
                    ·
                      refine ⟨2792928597261114803473039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3723904796348153071297385 2792928597261114803473039)
                      ·
                        rfl

theorem cell23_5439209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 3, 2, 5, 2].length) (baseStart_5439209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5439209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5439209 prefixEnd_5439209 := by exact prefixLift 5439209
  have htrace : WordTrace (prefixWord ++ tailWord_5439209) baseStart_5439209 baseEnd_5439209 := by
    simpa [prefixWord, tailWord_5439209, baseEnd_5439209] using wordTrace_append hprefix tailTrace_5439209
  have hstable : (prefixWord ++ tailWord_5439209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5439209).length < 2 ^ (prefixWord ++ tailWord_5439209).sum := by decide
  have hdescent : baseEnd_5439209 < baseStart_5439209 := by decide
  rcases family_descends (prefixWord ++ tailWord_5439209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5439212 : List Nat := [2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 7]
def baseStart_5439212 : Nat := 118140960795 + 5439212 * 2 ^ 59
def prefixEnd_5439212 : Nat := 4983230072969 + 3 ^ 40 * 5439212 * 2
def baseEnd_5439212 : Nat := 2792930137703078291735525

theorem tailTrace_5439212 : CollatzResearch.WordTrace tailWord_5439212 prefixEnd_5439212 2792930137703078291735525 := by
  unfold tailWord_5439212
  simp only [CollatzResearch.WordTrace]
  refine ⟨99192179785335671148871945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132256239713780894865162593 99192179785335671148871945)
  ·
    refine ⟨74394134839001753361653959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99192179785335671148871945 74394134839001753361653959)
    ·
      refine ⟨111591202258502630042480939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74394134839001753361653959 111591202258502630042480939)
      ·
        refine ⟨167386803387753945063721409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111591202258502630042480939 167386803387753945063721409)
        ·
          refine ⟨125540102540815458797791057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 167386803387753945063721409 125540102540815458797791057)
          ·
            refine ⟨94155076905611594098343293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 125540102540815458797791057 94155076905611594098343293)
            ·
              refine ⟨35308153839604347786878735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 94155076905611594098343293 35308153839604347786878735)
              ·
                refine ⟨52962230759406521680318103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35308153839604347786878735 52962230759406521680318103)
                ·
                  refine ⟨79443346139109782520477155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52962230759406521680318103 79443346139109782520477155)
                  ·
                    refine ⟨119165019208664673780715733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 79443346139109782520477155 119165019208664673780715733)
                    ·
                      refine ⟨2792930137703078291735525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 119165019208664673780715733 2792930137703078291735525)
                      ·
                        rfl

theorem cell23_5439212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 7].length) (baseStart_5439212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5439212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5439212 prefixEnd_5439212 := by exact prefixLift 5439212
  have htrace : WordTrace (prefixWord ++ tailWord_5439212) baseStart_5439212 baseEnd_5439212 := by
    simpa [prefixWord, tailWord_5439212, baseEnd_5439212] using wordTrace_append hprefix tailTrace_5439212
  have hstable : (prefixWord ++ tailWord_5439212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5439212).length < 2 ^ (prefixWord ++ tailWord_5439212).sum := by decide
  have hdescent : baseEnd_5439212 < baseStart_5439212 := by decide
  rcases family_descends (prefixWord ++ tailWord_5439212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5439236 : List Nat := [2, 3, 2, 2, 1, 3, 2, 1, 2, 5]
def baseStart_5439236 : Nat := 118140960795 + 5439236 * 2 ^ 59
def prefixEnd_5439236 : Nat := 4983230072969 + 3 ^ 40 * 5439236 * 2
def baseEnd_5439236 : Nat := 930980820412928732611805

theorem tailTrace_5439236 : CollatzResearch.WordTrace tailWord_5439236 prefixEnd_5439236 930980820412928732611805 := by
  unfold tailWord_5439236
  simp only [CollatzResearch.WordTrace]
  refine ⟨99192617461292197198308781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132256823281722929597745041 99192617461292197198308781)
  ·
    refine ⟨37197231547984573949365793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 99192617461292197198308781 37197231547984573949365793)
    ·
      refine ⟨27897923660988430462024345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37197231547984573949365793 27897923660988430462024345)
      ·
        refine ⟨20923442745741322846518259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27897923660988430462024345 20923442745741322846518259)
        ·
          refine ⟨31385164118611984269777389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20923442745741322846518259 31385164118611984269777389)
          ·
            refine ⟨11769436544479494101166521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31385164118611984269777389 11769436544479494101166521)
            ·
              refine ⟨8827077408359620575874891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11769436544479494101166521 8827077408359620575874891)
              ·
                refine ⟨13240616112539430863812337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8827077408359620575874891 13240616112539430863812337)
                ·
                  refine ⟨9930462084404573147859253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13240616112539430863812337 9930462084404573147859253)
                  ·
                    refine ⟨930980820412928732611805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9930462084404573147859253 930980820412928732611805)
                    ·
                      rfl

theorem cell23_5439236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 2, 1, 2, 5].length) (baseStart_5439236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5439236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5439236 prefixEnd_5439236 := by exact prefixLift 5439236
  have htrace : WordTrace (prefixWord ++ tailWord_5439236) baseStart_5439236 baseEnd_5439236 := by
    simpa [prefixWord, tailWord_5439236, baseEnd_5439236] using wordTrace_append hprefix tailTrace_5439236
  have hstable : (prefixWord ++ tailWord_5439236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5439236).length < 2 ^ (prefixWord ++ tailWord_5439236).sum := by decide
  have hdescent : baseEnd_5439236 < baseStart_5439236 := by decide
  rcases family_descends (prefixWord ++ tailWord_5439236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5439238 : List Nat := [6, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2]
def baseStart_5439238 : Nat := 118140960795 + 5439238 * 2 ^ 59
def prefixEnd_5439238 : Nat := 4983230072969 + 3 ^ 40 * 5439238 * 2
def baseEnd_5439238 : Nat := 2792943488200095190010407

theorem tailTrace_5439238 : CollatzResearch.WordTrace tailWord_5439238 prefixEnd_5439238 2792943488200095190010407 := by
  unfold tailWord_5439238
  simp only [CollatzResearch.WordTrace]
  refine ⟨6199540870893035898068449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 132256871912384765825460245 6199540870893035898068449)
  ·
    refine ⟨4649655653169776923551337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6199540870893035898068449 4649655653169776923551337)
    ·
      refine ⟨3487241739877332692663503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4649655653169776923551337 3487241739877332692663503)
      ·
        refine ⟨5230862609815999038995255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3487241739877332692663503 5230862609815999038995255)
        ·
          refine ⟨7846293914723998558492883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5230862609815999038995255 7846293914723998558492883)
          ·
            refine ⟨11769440872085997837739325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7846293914723998558492883 11769440872085997837739325)
            ·
              refine ⟨4413540327032249189152247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11769440872085997837739325 4413540327032249189152247)
              ·
                refine ⟨6620310490548373783728371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4413540327032249189152247 6620310490548373783728371)
                ·
                  refine ⟨9930465735822560675592557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6620310490548373783728371 9930465735822560675592557)
                  ·
                    refine ⟨3723924650933460253347209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9930465735822560675592557 3723924650933460253347209)
                    ·
                      refine ⟨2792943488200095190010407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3723924650933460253347209 2792943488200095190010407)
                      ·
                        rfl

theorem cell23_5439238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2].length) (baseStart_5439238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5439238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5439238 prefixEnd_5439238 := by exact prefixLift 5439238
  have htrace : WordTrace (prefixWord ++ tailWord_5439238) baseStart_5439238 baseEnd_5439238 := by
    simpa [prefixWord, tailWord_5439238, baseEnd_5439238] using wordTrace_append hprefix tailTrace_5439238
  have hstable : (prefixWord ++ tailWord_5439238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5439238).length < 2 ^ (prefixWord ++ tailWord_5439238).sum := by decide
  have hdescent : baseEnd_5439238 < baseStart_5439238 := by decide
  rcases family_descends (prefixWord ++ tailWord_5439238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5439266 : List Nat := [3, 3, 1, 1, 2, 1, 2, 3, 3, 4]
def baseStart_5439266 : Nat := 118140960795 + 5439266 * 2 ^ 59
def prefixEnd_5439266 : Nat := 4983230072969 + 3 ^ 40 * 5439266 * 2
def baseEnd_5439266 : Nat := 930985955219473693486759

theorem tailTrace_5439266 : CollatzResearch.WordTrace tailWord_5439266 prefixEnd_5439266 930985955219473693486759 := by
  unfold tailWord_5439266
  simp only [CollatzResearch.WordTrace]
  refine ⟨49596582278118927380052413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132257552741650473013473101 49596582278118927380052413)
  ·
    refine ⟨18598718354294597767519655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49596582278118927380052413 18598718354294597767519655)
    ·
      refine ⟨27898077531441896651279483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18598718354294597767519655 27898077531441896651279483)
      ·
        refine ⟨41847116297162844976919225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27898077531441896651279483 41847116297162844976919225)
        ·
          refine ⟨31385337222872133732689419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41847116297162844976919225 31385337222872133732689419)
          ·
            refine ⟨47078005834308200599034129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31385337222872133732689419 47078005834308200599034129)
            ·
              refine ⟨35308504375731150449275597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47078005834308200599034129 35308504375731150449275597)
              ·
                refine ⟨13240689140899181418478349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35308504375731150449275597 13240689140899181418478349)
                ·
                  refine ⟨4965258427837193031929381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13240689140899181418478349 4965258427837193031929381)
                  ·
                    refine ⟨930985955219473693486759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4965258427837193031929381 930985955219473693486759)
                    ·
                      rfl

theorem cell23_5439266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 2, 3, 3, 4].length) (baseStart_5439266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5439266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5439266 prefixEnd_5439266 := by exact prefixLift 5439266
  have htrace : WordTrace (prefixWord ++ tailWord_5439266) baseStart_5439266 baseEnd_5439266 := by
    simpa [prefixWord, tailWord_5439266, baseEnd_5439266] using wordTrace_append hprefix tailTrace_5439266
  have hstable : (prefixWord ++ tailWord_5439266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5439266).length < 2 ^ (prefixWord ++ tailWord_5439266).sum := by decide
  have hdescent : baseEnd_5439266 < baseStart_5439266 := by decide
  rcases family_descends (prefixWord ++ tailWord_5439266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5439293 : List Nat := [1, 4, 1, 4, 1, 1, 3, 1, 2, 2, 3]
def baseStart_5439293 : Nat := 118140960795 + 5439293 * 2 ^ 59
def prefixEnd_5439293 : Nat := 4983230072969 + 3 ^ 40 * 5439293 * 2
def baseEnd_5439293 : Nat := 2792971729636092474822653

theorem tailTrace_5439293 : CollatzResearch.WordTrace tailWord_5439293 prefixEnd_5439293 2792971729636092474822653 := by
  unfold tailWord_5439293
  simp only [CollatzResearch.WordTrace]
  refine ⟨198387313883377893131442533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132258209255585262087628355 198387313883377893131442533)
  ·
    refine ⟨37197621353133354962145475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 198387313883377893131442533 37197621353133354962145475)
    ·
      refine ⟨55796432029700032443218213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37197621353133354962145475 55796432029700032443218213)
      ·
        refine ⟨10461831005568756083103415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 55796432029700032443218213 10461831005568756083103415)
        ·
          refine ⟨15692746508353134124655123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10461831005568756083103415 15692746508353134124655123)
          ·
            refine ⟨23539119762529701186982685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15692746508353134124655123 23539119762529701186982685)
            ·
              refine ⟨8827169910948637945118507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23539119762529701186982685 8827169910948637945118507)
              ·
                refine ⟨13240754866422956917677761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8827169910948637945118507 13240754866422956917677761)
                ·
                  refine ⟨9930566149817217688258321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13240754866422956917677761 9930566149817217688258321)
                  ·
                    refine ⟨7447924612362913266193741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9930566149817217688258321 7447924612362913266193741)
                    ·
                      refine ⟨2792971729636092474822653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7447924612362913266193741 2792971729636092474822653)
                      ·
                        rfl

theorem cell23_5439293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 3, 1, 2, 2, 3].length) (baseStart_5439293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5439293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5439293 prefixEnd_5439293 := by exact prefixLift 5439293
  have htrace : WordTrace (prefixWord ++ tailWord_5439293) baseStart_5439293 baseEnd_5439293 := by
    simpa [prefixWord, tailWord_5439293, baseEnd_5439293] using wordTrace_append hprefix tailTrace_5439293
  have hstable : (prefixWord ++ tailWord_5439293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5439293).length < 2 ^ (prefixWord ++ tailWord_5439293).sum := by decide
  have hdescent : baseEnd_5439293 < baseStart_5439293 := by decide
  rcases family_descends (prefixWord ++ tailWord_5439293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5439306 : List Nat := [3, 1, 2, 1, 1, 1, 3, 2, 5, 1, 3]
def baseStart_5439306 : Nat := 118140960795 + 5439306 * 2 ^ 59
def prefixEnd_5439306 : Nat := 4983230072969 + 3 ^ 40 * 5439306 * 2
def baseEnd_5439306 : Nat := 2792978404884600923960093

theorem tailTrace_5439306 : CollatzResearch.WordTrace tailWord_5439306 prefixEnd_5439306 2792978404884600923960093 := by
  unfold tailWord_5439306
  simp only [CollatzResearch.WordTrace]
  refine ⟨49596947008082699087916443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132258525354887197567777181 49596947008082699087916443)
  ·
    refine ⟨74395420512124048631874665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49596947008082699087916443 74395420512124048631874665)
    ·
      refine ⟨55796565384093036473905999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74395420512124048631874665 55796565384093036473905999)
      ·
        refine ⟨83694848076139554710858999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55796565384093036473905999 83694848076139554710858999)
        ·
          refine ⟨125542272114209332066288499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83694848076139554710858999 125542272114209332066288499)
          ·
            refine ⟨188313408171313998099432749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 125542272114209332066288499 188313408171313998099432749)
            ·
              refine ⟨70617528064242749287287281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 188313408171313998099432749 70617528064242749287287281)
              ·
                refine ⟨52963146048182061965465461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 70617528064242749287287281 52963146048182061965465461)
                ·
                  refine ⟨4965294942017068309262387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 52963146048182061965465461 4965294942017068309262387)
                  ·
                    refine ⟨7447942413025602463893581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4965294942017068309262387 7447942413025602463893581)
                    ·
                      refine ⟨2792978404884600923960093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7447942413025602463893581 2792978404884600923960093)
                      ·
                        rfl

theorem cell23_5439306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 2, 5, 1, 3].length) (baseStart_5439306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5439306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5439306 prefixEnd_5439306 := by exact prefixLift 5439306
  have htrace : WordTrace (prefixWord ++ tailWord_5439306) baseStart_5439306 baseEnd_5439306 := by
    simpa [prefixWord, tailWord_5439306, baseEnd_5439306] using wordTrace_append hprefix tailTrace_5439306
  have hstable : (prefixWord ++ tailWord_5439306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5439306).length < 2 ^ (prefixWord ++ tailWord_5439306).sum := by decide
  have hdescent : baseEnd_5439306 < baseStart_5439306 := by decide
  rcases family_descends (prefixWord ++ tailWord_5439306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5439346 : List Nat := [3, 2, 1, 2, 1, 1, 1, 1, 1, 8, 2]
def baseStart_5439346 : Nat := 118140960795 + 5439346 * 2 ^ 59
def prefixEnd_5439346 : Nat := 4983230072969 + 3 ^ 40 * 5439346 * 2
def baseEnd_5439346 : Nat := 2792998944110780767459909

theorem tailTrace_5439346 : CollatzResearch.WordTrace tailWord_5439346 prefixEnd_5439346 2792998944110780767459909 := by
  unfold tailWord_5439346
  simp only [CollatzResearch.WordTrace]
  refine ⟨49597311738046470795780473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132259497968123922122081261 49597311738046470795780473)
  ·
    refine ⟨37197983803534853096835355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49597311738046470795780473 37197983803534853096835355)
    ·
      refine ⟨55796975705302279645253033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37197983803534853096835355 55796975705302279645253033)
      ·
        refine ⟨41847731778976709733939775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55796975705302279645253033 41847731778976709733939775)
        ·
          refine ⟨62771597668465064600909663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41847731778976709733939775 62771597668465064600909663)
          ·
            refine ⟨94157396502697596901364495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62771597668465064600909663 94157396502697596901364495)
            ·
              refine ⟨141236094754046395352046743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 94157396502697596901364495 141236094754046395352046743)
              ·
                refine ⟨211854142131069593028070115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 141236094754046395352046743 211854142131069593028070115)
                ·
                  refine ⟨317781213196604389542105173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 211854142131069593028070115 317781213196604389542105173)
                  ·
                    refine ⟨3723998592147707689946545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 317781213196604389542105173 3723998592147707689946545)
                    ·
                      refine ⟨2792998944110780767459909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3723998592147707689946545 2792998944110780767459909)
                      ·
                        rfl

theorem cell23_5439346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 1, 1, 8, 2].length) (baseStart_5439346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5439346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5439346 prefixEnd_5439346 := by exact prefixLift 5439346
  have htrace : WordTrace (prefixWord ++ tailWord_5439346) baseStart_5439346 baseEnd_5439346 := by
    simpa [prefixWord, tailWord_5439346, baseEnd_5439346] using wordTrace_append hprefix tailTrace_5439346
  have hstable : (prefixWord ++ tailWord_5439346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5439346).length < 2 ^ (prefixWord ++ tailWord_5439346).sum := by decide
  have hdescent : baseEnd_5439346 < baseStart_5439346 := by decide
  rcases family_descends (prefixWord ++ tailWord_5439346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5439359 : List Nat := [1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 4]
def baseStart_5439359 : Nat := 118140960795 + 5439359 * 2 ^ 59
def prefixEnd_5439359 : Nat := 4983230072969 + 3 ^ 40 * 5439359 * 2
def baseEnd_5439359 : Nat := 2793005619359289216597349

theorem tailTrace_5439359 : CollatzResearch.WordTrace tailWord_5439359 prefixEnd_5439359 2793005619359289216597349 := by
  unfold tailWord_5439359
  simp only [CollatzResearch.WordTrace]
  refine ⟨198389721101138786403345131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132259814067425857602230087 198389721101138786403345131)
  ·
    refine ⟨297584581651708179605017697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198389721101138786403345131 297584581651708179605017697)
    ·
      refine ⟨223188436238781134703763273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 297584581651708179605017697 223188436238781134703763273)
      ·
        refine ⟨167391327179085851027822455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 223188436238781134703763273 167391327179085851027822455)
        ·
          refine ⟨251086990768628776541733683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 167391327179085851027822455 251086990768628776541733683)
          ·
            refine ⟨376630486152943164812600525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 251086990768628776541733683 376630486152943164812600525)
            ·
              refine ⟨141236432307353686804725197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 376630486152943164812600525 141236432307353686804725197)
              ·
                refine ⟨52963662115257632551771949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 141236432307353686804725197 52963662115257632551771949)
                ·
                  refine ⟨19861373293221612206914481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 52963662115257632551771949 19861373293221612206914481)
                  ·
                    refine ⟨14896029969916209155185861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19861373293221612206914481 14896029969916209155185861)
                    ·
                      refine ⟨2793005619359289216597349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14896029969916209155185861 2793005619359289216597349)
                      ·
                        rfl

theorem cell23_5439359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 4].length) (baseStart_5439359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5439359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5439359 prefixEnd_5439359 := by exact prefixLift 5439359
  have htrace : WordTrace (prefixWord ++ tailWord_5439359) baseStart_5439359 baseEnd_5439359 := by
    simpa [prefixWord, tailWord_5439359, baseEnd_5439359] using wordTrace_append hprefix tailTrace_5439359
  have hstable : (prefixWord ++ tailWord_5439359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5439359).length < 2 ^ (prefixWord ++ tailWord_5439359).sum := by decide
  have hdescent : baseEnd_5439359 < baseStart_5439359 := by decide
  rcases family_descends (prefixWord ++ tailWord_5439359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5439374 : List Nat := [4, 1, 1, 5, 2, 1, 1, 1, 3, 1, 3]
def baseStart_5439374 : Nat := 118140960795 + 5439374 * 2 ^ 59
def prefixEnd_5439374 : Nat := 4983230072969 + 3 ^ 40 * 5439374 * 2
def baseEnd_5439374 : Nat := 2793013321569106657909781

theorem tailTrace_5439374 : CollatzResearch.WordTrace tailWord_5439374 prefixEnd_5439374 2793013321569106657909781 := by
  unfold tailWord_5439374
  simp only [CollatzResearch.WordTrace]
  refine ⟨24798783524510555495642647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 132260178797389629310094117 24798783524510555495642647)
  ·
    refine ⟨37198175286765833243463971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24798783524510555495642647 37198175286765833243463971)
    ·
      refine ⟨55797262930148749865195957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37198175286765833243463971 55797262930148749865195957)
      ·
        refine ⟨5230993399701445299862121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 55797262930148749865195957 5230993399701445299862121)
        ·
          refine ⟨3923245049776083974896591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5230993399701445299862121 3923245049776083974896591)
          ·
            refine ⟨5884867574664125962344887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3923245049776083974896591 5884867574664125962344887)
            ·
              refine ⟨8827301361996188943517331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5884867574664125962344887 8827301361996188943517331)
              ·
                refine ⟨13240952042994283415275997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8827301361996188943517331 13240952042994283415275997)
                ·
                  refine ⟨4965357016122856280728499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13240952042994283415275997 4965357016122856280728499)
                  ·
                    refine ⟨7448035524184284421092749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4965357016122856280728499 7448035524184284421092749)
                    ·
                      refine ⟨2793013321569106657909781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7448035524184284421092749 2793013321569106657909781)
                      ·
                        rfl

theorem cell23_5439374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 2, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 2, 1, 1, 1, 3, 1, 3].length) (baseStart_5439374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5439374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5439374 prefixEnd_5439374 := by exact prefixLift 5439374
  have htrace : WordTrace (prefixWord ++ tailWord_5439374) baseStart_5439374 baseEnd_5439374 := by
    simpa [prefixWord, tailWord_5439374, baseEnd_5439374] using wordTrace_append hprefix tailTrace_5439374
  have hstable : (prefixWord ++ tailWord_5439374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5439374).length < 2 ^ (prefixWord ++ tailWord_5439374).sum := by decide
  have hdescent : baseEnd_5439374 < baseStart_5439374 := by decide
  rcases family_descends (prefixWord ++ tailWord_5439374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5439386 : List Nat := [3, 1, 1, 4, 2, 2, 2, 8]
def baseStart_5439386 : Nat := 118140960795 + 5439386 * 2 ^ 59
def prefixEnd_5439386 : Nat := 4983230072969 + 3 ^ 40 * 5439386 * 2
def baseEnd_5439386 : Nat := 103445166049517059665175

theorem tailTrace_5439386 : CollatzResearch.WordTrace tailWord_5439386 prefixEnd_5439386 103445166049517059665175 := by
  unfold tailWord_5439386
  simp only [CollatzResearch.WordTrace]
  refine ⟨49597676468010242503644503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132260470581360646676385341 49597676468010242503644503)
  ·
    refine ⟨74396514702015363755466755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49597676468010242503644503 74396514702015363755466755)
    ·
      refine ⟨111594772053023045633200133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74396514702015363755466755 111594772053023045633200133)
      ·
        refine ⟨20924019759941821056225025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 111594772053023045633200133 20924019759941821056225025)
        ·
          refine ⟨15693014819956365792168769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20924019759941821056225025 15693014819956365792168769)
          ·
            refine ⟨11769761114967274344126577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15693014819956365792168769 11769761114967274344126577)
            ·
              refine ⟨8827320836225455758094933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11769761114967274344126577 8827320836225455758094933)
              ·
                refine ⟨103445166049517059665175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8827320836225455758094933 103445166049517059665175)
                ·
                  rfl

theorem cell23_5439386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 2, 8].length) (baseStart_5439386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5439386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5439386 prefixEnd_5439386 := by exact prefixLift 5439386
  have htrace : WordTrace (prefixWord ++ tailWord_5439386) baseStart_5439386 baseEnd_5439386 := by
    simpa [prefixWord, tailWord_5439386, baseEnd_5439386] using wordTrace_append hprefix tailTrace_5439386
  have hstable : (prefixWord ++ tailWord_5439386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5439386).length < 2 ^ (prefixWord ++ tailWord_5439386).sum := by decide
  have hdescent : baseEnd_5439386 < baseStart_5439386 := by decide
  rcases family_descends (prefixWord ++ tailWord_5439386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5439413 : List Nat := [1, 3, 3, 2, 1, 3, 1, 2, 1, 3, 3]
def baseStart_5439413 : Nat := 118140960795 + 5439413 * 2 ^ 59
def prefixEnd_5439413 : Nat := 4983230072969 + 3 ^ 40 * 5439413 * 2
def baseEnd_5439413 : Nat := 2793033347314632005322101

theorem tailTrace_5439413 : CollatzResearch.WordTrace tailWord_5439413 prefixEnd_5439413 2793033347314632005322101 := by
  unfold tailWord_5439413
  simp only [CollatzResearch.WordTrace]
  refine ⟨198391690642943153625810893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132261127095295435750540595 198391690642943153625810893)
  ·
    refine ⟨74396883991103682609679085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 198391690642943153625810893 74396883991103682609679085)
    ·
      refine ⟨27898831496663880978629657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74396883991103682609679085 27898831496663880978629657)
      ·
        refine ⟨20924123622497910733972243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27898831496663880978629657 20924123622497910733972243)
        ·
          refine ⟨31386185433746866100958365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20924123622497910733972243 31386185433746866100958365)
          ·
            refine ⟨11769819537655074787859387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31386185433746866100958365 11769819537655074787859387)
            ·
              refine ⟨17654729306482612181789081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11769819537655074787859387 17654729306482612181789081)
              ·
                refine ⟨13241046979861959136341811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17654729306482612181789081 13241046979861959136341811)
                ·
                  refine ⟨19861570469792938704512717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13241046979861959136341811 19861570469792938704512717)
                  ·
                    refine ⟨7448088926172352014192269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19861570469792938704512717 7448088926172352014192269)
                    ·
                      refine ⟨2793033347314632005322101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7448088926172352014192269 2793033347314632005322101)
                      ·
                        rfl

theorem cell23_5439413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 1, 2, 1, 3, 3].length) (baseStart_5439413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5439413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5439413 prefixEnd_5439413 := by exact prefixLift 5439413
  have htrace : WordTrace (prefixWord ++ tailWord_5439413) baseStart_5439413 baseEnd_5439413 := by
    simpa [prefixWord, tailWord_5439413, baseEnd_5439413] using wordTrace_append hprefix tailTrace_5439413
  have hstable : (prefixWord ++ tailWord_5439413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5439413).length < 2 ^ (prefixWord ++ tailWord_5439413).sum := by decide
  have hdescent : baseEnd_5439413 < baseStart_5439413 := by decide
  rcases family_descends (prefixWord ++ tailWord_5439413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5439419 : List Nat := [1, 1, 1, 1, 1, 2, 2, 4, 1, 5, 4]
def baseStart_5439419 : Nat := 118140960795 + 5439419 * 2 ^ 59
def prefixEnd_5439419 : Nat := 4983230072969 + 3 ^ 40 * 5439419 * 2
def baseEnd_5439419 : Nat := 2793036428198558981847073

theorem tailTrace_5439419 : CollatzResearch.WordTrace tailWord_5439419 prefixEnd_5439419 2793036428198558981847073 := by
  unfold tailWord_5439419
  simp only [CollatzResearch.WordTrace]
  refine ⟨198391909480921416650529311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132261272987280944433686207 198391909480921416650529311)
  ·
    refine ⟨297587864221382124975793967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198391909480921416650529311 297587864221382124975793967)
    ·
      refine ⟨446381796332073187463690951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 297587864221382124975793967 446381796332073187463690951)
      ·
        refine ⟨669572694498109781195536427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 446381796332073187463690951 669572694498109781195536427)
        ·
          refine ⟨1004359041747164671793304641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 669572694498109781195536427 1004359041747164671793304641)
          ·
            refine ⟨753269281310373503844978481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1004359041747164671793304641 753269281310373503844978481)
            ·
              refine ⟨564951960982780127883733861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 753269281310373503844978481 564951960982780127883733861)
              ·
                refine ⟨105928492684271273978200099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 564951960982780127883733861 105928492684271273978200099)
                ·
                  refine ⟨158892739026406910967300149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 105928492684271273978200099 158892739026406910967300149)
                  ·
                    refine ⟨14896194283725647903184389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 158892739026406910967300149 14896194283725647903184389)
                    ·
                      refine ⟨2793036428198558981847073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14896194283725647903184389 2793036428198558981847073)
                      ·
                        rfl

theorem cell23_5439419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 4, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 4, 1, 5, 4].length) (baseStart_5439419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5439419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5439419 prefixEnd_5439419 := by exact prefixLift 5439419
  have htrace : WordTrace (prefixWord ++ tailWord_5439419) baseStart_5439419 baseEnd_5439419 := by
    simpa [prefixWord, tailWord_5439419, baseEnd_5439419] using wordTrace_append hprefix tailTrace_5439419
  have hstable : (prefixWord ++ tailWord_5439419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5439419).length < 2 ^ (prefixWord ++ tailWord_5439419).sum := by decide
  have hdescent : baseEnd_5439419 < baseStart_5439419 := by decide
  rcases family_descends (prefixWord ++ tailWord_5439419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5439436 : List Nat := [2, 2, 1, 4, 1, 2, 1, 1, 2, 3, 4]
def baseStart_5439436 : Nat := 118140960795 + 5439436 * 2 ^ 59
def prefixEnd_5439436 : Nat := 4983230072969 + 3 ^ 40 * 5439436 * 2
def baseEnd_5439436 : Nat := 2793045157369685415334495

theorem tailTrace_5439436 : CollatzResearch.WordTrace tailWord_5439436 prefixEnd_5439436 2793045157369685415334495 := by
  unfold tailWord_5439436
  simp only [CollatzResearch.WordTrace]
  refine ⟨99196264760929914276949081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132261686347906552369265441 99196264760929914276949081)
  ·
    refine ⟨74397198570697435707711811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99196264760929914276949081 74397198570697435707711811)
    ·
      refine ⟨111595797856046153561567717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74397198570697435707711811 111595797856046153561567717)
      ·
        refine ⟨20924212098008653792793947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 111595797856046153561567717 20924212098008653792793947)
        ·
          refine ⟨31386318147012980689190921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20924212098008653792793947 31386318147012980689190921)
          ·
            refine ⟨23539738610259735516893191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31386318147012980689190921 23539738610259735516893191)
            ·
              refine ⟨35309607915389603275339787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23539738610259735516893191 35309607915389603275339787)
              ·
                refine ⟨52964411873084404913009681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35309607915389603275339787 52964411873084404913009681)
                ·
                  refine ⟨39723308904813303684757261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 52964411873084404913009681 39723308904813303684757261)
                  ·
                    refine ⟨14896240839304988881783973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 39723308904813303684757261 14896240839304988881783973)
                    ·
                      refine ⟨2793045157369685415334495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14896240839304988881783973 2793045157369685415334495)
                      ·
                        rfl

theorem cell23_5439436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 1, 1, 2, 3, 4].length) (baseStart_5439436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5439436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5439436 prefixEnd_5439436 := by exact prefixLift 5439436
  have htrace : WordTrace (prefixWord ++ tailWord_5439436) baseStart_5439436 baseEnd_5439436 := by
    simpa [prefixWord, tailWord_5439436, baseEnd_5439436] using wordTrace_append hprefix tailTrace_5439436
  have hstable : (prefixWord ++ tailWord_5439436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5439436).length < 2 ^ (prefixWord ++ tailWord_5439436).sum := by decide
  have hdescent : baseEnd_5439436 < baseStart_5439436 := by decide
  rcases family_descends (prefixWord ++ tailWord_5439436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5439466 : List Nat := [3, 1, 3, 1, 2, 1, 1, 2, 1, 4, 4]
def baseStart_5439466 : Nat := 118140960795 + 5439466 * 2 ^ 59
def prefixEnd_5439466 : Nat := 4983230072969 + 3 ^ 40 * 5439466 * 2
def baseEnd_5439466 : Nat := 2793060561789320297959357

theorem tailTrace_5439466 : CollatzResearch.WordTrace tailWord_5439466 prefixEnd_5439466 2793060561789320297959357 := by
  unfold tailWord_5439466
  simp only [CollatzResearch.WordTrace]
  refine ⟨49598405927937785919372563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132262415807834095784993501 49598405927937785919372563)
  ·
    refine ⟨74397608891906678879058845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49598405927937785919372563 74397608891906678879058845)
    ·
      refine ⟨27899103334465004579647067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74397608891906678879058845 27899103334465004579647067)
      ·
        refine ⟨41848655001697506869470601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27899103334465004579647067 41848655001697506869470601)
        ·
          refine ⟨31386491251273130152102951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41848655001697506869470601 31386491251273130152102951)
          ·
            refine ⟨47079736876909695228154427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31386491251273130152102951 47079736876909695228154427)
            ·
              refine ⟨70619605315364542842231641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47079736876909695228154427 70619605315364542842231641)
              ·
                refine ⟨52964703986523407131673731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 70619605315364542842231641 52964703986523407131673731)
                ·
                  refine ⟨79447055979785110697510597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52964703986523407131673731 79447055979785110697510597)
                  ·
                    refine ⟨14896322996209708255783237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 79447055979785110697510597 14896322996209708255783237)
                    ·
                      refine ⟨2793060561789320297959357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14896322996209708255783237 2793060561789320297959357)
                      ·
                        rfl

theorem cell23_5439466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 2, 1, 4, 4].length) (baseStart_5439466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5439466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5439466 prefixEnd_5439466 := by exact prefixLift 5439466
  have htrace : WordTrace (prefixWord ++ tailWord_5439466) baseStart_5439466 baseEnd_5439466 := by
    simpa [prefixWord, tailWord_5439466, baseEnd_5439466] using wordTrace_append hprefix tailTrace_5439466
  have hstable : (prefixWord ++ tailWord_5439466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5439466).length < 2 ^ (prefixWord ++ tailWord_5439466).sum := by decide
  have hdescent : baseEnd_5439466 < baseStart_5439466 := by decide
  rcases family_descends (prefixWord ++ tailWord_5439466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5439470 : List Nat := [4, 1, 2, 1, 3, 1, 2, 2, 1, 4, 2]
def baseStart_5439470 : Nat := 118140960795 + 5439470 * 2 ^ 59
def prefixEnd_5439470 : Nat := 4983230072969 + 3 ^ 40 * 5439470 * 2
def baseEnd_5439470 : Nat := 2793062615711938282309339

theorem tailTrace_5439470 : CollatzResearch.WordTrace tailWord_5439470 prefixEnd_5439470 2793062615711938282309339 := by
  unfold tailWord_5439470
  simp only [CollatzResearch.WordTrace]
  refine ⟨24799221200467081545079483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 132262513069157768240423909 24799221200467081545079483)
  ·
    refine ⟨37198831800700622317619225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24799221200467081545079483 37198831800700622317619225)
    ·
      refine ⟨27899123850525466738214419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37198831800700622317619225 27899123850525466738214419)
      ·
        refine ⟨41848685775788200107321629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27899123850525466738214419 41848685775788200107321629)
        ·
          refine ⟨15693257165920575040245611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41848685775788200107321629 15693257165920575040245611)
          ·
            refine ⟨23539885748880862560368417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15693257165920575040245611 23539885748880862560368417)
            ·
              refine ⟨17654914311660646920276313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23539885748880862560368417 17654914311660646920276313)
              ·
                refine ⟨13241185733745485190207235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17654914311660646920276313 13241185733745485190207235)
                ·
                  refine ⟨19861778600618227785310853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13241185733745485190207235 19861778600618227785310853)
                  ·
                    refine ⟨3724083487615917709745785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19861778600618227785310853 3724083487615917709745785)
                    ·
                      refine ⟨2793062615711938282309339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3724083487615917709745785 2793062615711938282309339)
                      ·
                        rfl

theorem cell23_5439470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 2, 2, 1, 4, 2].length) (baseStart_5439470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5439470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5439470 prefixEnd_5439470 := by exact prefixLift 5439470
  have htrace : WordTrace (prefixWord ++ tailWord_5439470) baseStart_5439470 baseEnd_5439470 := by
    simpa [prefixWord, tailWord_5439470, baseEnd_5439470] using wordTrace_append hprefix tailTrace_5439470
  have hstable : (prefixWord ++ tailWord_5439470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5439470).length < 2 ^ (prefixWord ++ tailWord_5439470).sum := by decide
  have hdescent : baseEnd_5439470 < baseStart_5439470 := by decide
  rcases family_descends (prefixWord ++ tailWord_5439470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5439493 : List Nat := [1, 3, 1, 1, 2, 4, 2, 4, 5]
def baseStart_5439493 : Nat := 118140960795 + 5439493 * 2 ^ 59
def prefixEnd_5439493 : Nat := 4983230072969 + 3 ^ 40 * 5439493 * 2
def baseEnd_5439493 : Nat := 310341602862999076924637

theorem tailTrace_5439493 : CollatzResearch.WordTrace tailWord_5439493 prefixEnd_5439493 310341602862999076924637 := by
  unfold tailWord_5439493
  simp only [CollatzResearch.WordTrace]
  refine ⟨198394608482653327288723133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132263072321768884859148755 198394608482653327288723133)
  ·
    refine ⟨74397978180994997733271175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 198394608482653327288723133 74397978180994997733271175)
    ·
      refine ⟨111596967271492496599906763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74397978180994997733271175 111596967271492496599906763)
      ·
        refine ⟨167395450907238744899860145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111596967271492496599906763 167395450907238744899860145)
        ·
          refine ⟨125546588180429058674895109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 167395450907238744899860145 125546588180429058674895109)
          ·
            refine ⟨23539985283830448501542833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 125546588180429058674895109 23539985283830448501542833)
            ·
              refine ⟨17654988962872836376157125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23539985283830448501542833 17654988962872836376157125)
              ·
                refine ⟨3310310430538656820529461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17654988962872836376157125 3310310430538656820529461)
                ·
                  refine ⟨310341602862999076924637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3310310430538656820529461 310341602862999076924637)
                  ·
                    rfl

theorem cell23_5439493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 2, 4, 5].length) (baseStart_5439493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5439493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5439493 prefixEnd_5439493 := by exact prefixLift 5439493
  have htrace : WordTrace (prefixWord ++ tailWord_5439493) baseStart_5439493 baseEnd_5439493 := by
    simpa [prefixWord, tailWord_5439493, baseEnd_5439493] using wordTrace_append hprefix tailTrace_5439493
  have hstable : (prefixWord ++ tailWord_5439493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5439493).length < 2 ^ (prefixWord ++ tailWord_5439493).sum := by decide
  have hdescent : baseEnd_5439493 < baseStart_5439493 := by decide
  rcases family_descends (prefixWord ++ tailWord_5439493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5439543 : List Nat := [1, 1, 3, 1, 2, 2, 2, 1, 4, 4, 2]
def baseStart_5439543 : Nat := 118140960795 + 5439543 * 2 ^ 59
def prefixEnd_5439543 : Nat := 4983230072969 + 3 ^ 40 * 5439543 * 2
def baseEnd_5439543 : Nat := 2793100099799716496696503

theorem tailTrace_5439543 : CollatzResearch.WordTrace tailWord_5439543 prefixEnd_5439543 2793100099799716496696503 := by
  unfold tailWord_5439543
  simp only [CollatzResearch.WordTrace]
  refine ⟨198396432132472185828043283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132264288088314790552028855 198396432132472185828043283)
  ·
    refine ⟨297594648198708278742064925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198396432132472185828043283 297594648198708278742064925)
    ·
      refine ⟨111597993074515604528274347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 297594648198708278742064925 111597993074515604528274347)
      ·
        refine ⟨167396989611773406792411521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111597993074515604528274347 167396989611773406792411521)
        ·
          refine ⟨125547742208830055094308641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 167396989611773406792411521 125547742208830055094308641)
          ·
            refine ⟨94160806656622541320731481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 125547742208830055094308641 94160806656622541320731481)
            ·
              refine ⟨70620604992466905990548611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 94160806656622541320731481 70620604992466905990548611)
              ·
                refine ⟨105930907488700358985822917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70620604992466905990548611 105930907488700358985822917)
                ·
                  refine ⟨19862045154131317309841797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 105930907488700358985822917 19862045154131317309841797)
                  ·
                    refine ⟨3724133466399621995595337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19862045154131317309841797 3724133466399621995595337)
                    ·
                      refine ⟨2793100099799716496696503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3724133466399621995595337 2793100099799716496696503)
                      ·
                        rfl

theorem cell23_5439543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 1, 4, 4, 2].length) (baseStart_5439543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5439543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5439543 prefixEnd_5439543 := by exact prefixLift 5439543
  have htrace : WordTrace (prefixWord ++ tailWord_5439543) baseStart_5439543 baseEnd_5439543 := by
    simpa [prefixWord, tailWord_5439543, baseEnd_5439543] using wordTrace_append hprefix tailTrace_5439543
  have hstable : (prefixWord ++ tailWord_5439543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5439543).length < 2 ^ (prefixWord ++ tailWord_5439543).sum := by decide
  have hdescent : baseEnd_5439543 < baseStart_5439543 := by decide
  rcases family_descends (prefixWord ++ tailWord_5439543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5439550 : List Nat := [4, 2, 1, 3, 2, 1, 1, 1, 1, 2, 5]
def baseStart_5439550 : Nat := 118140960795 + 5439550 * 2 ^ 59
def prefixEnd_5439550 : Nat := 4983230072969 + 3 ^ 40 * 5439550 * 2
def baseEnd_5439550 : Nat := 2793103694164297969308971

theorem tailTrace_5439550 : CollatzResearch.WordTrace tailWord_5439550 prefixEnd_5439550 2793103694164297969308971 := by
  unfold tailWord_5439550
  simp only [CollatzResearch.WordTrace]
  refine ⟨24799585930430853252943513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 132264458295631217349032069 24799585930430853252943513)
  ·
    refine ⟨18599689447823139939707635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24799585930430853252943513 18599689447823139939707635)
    ·
      refine ⟨27899534171734709909561453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18599689447823139939707635 27899534171734709909561453)
      ·
        refine ⟨10462325314400516216085545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27899534171734709909561453 10462325314400516216085545)
        ·
          refine ⟨7846743985800387162064159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10462325314400516216085545 7846743985800387162064159)
          ·
            refine ⟨11770115978700580743096239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7846743985800387162064159 11770115978700580743096239)
            ·
              refine ⟨17655173968050871114644359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11770115978700580743096239 17655173968050871114644359)
              ·
                refine ⟨26482760952076306671966539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17655173968050871114644359 26482760952076306671966539)
                ·
                  refine ⟨39724141428114460007949809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26482760952076306671966539 39724141428114460007949809)
                  ·
                    refine ⟨29793106071085845005962357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 39724141428114460007949809 29793106071085845005962357)
                    ·
                      refine ⟨2793103694164297969308971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29793106071085845005962357 2793103694164297969308971)
                      ·
                        rfl

theorem cell23_5439550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 1, 1, 1, 2, 5].length) (baseStart_5439550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5439550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5439550 prefixEnd_5439550 := by exact prefixLift 5439550
  have htrace : WordTrace (prefixWord ++ tailWord_5439550) baseStart_5439550 baseEnd_5439550 := by
    simpa [prefixWord, tailWord_5439550, baseEnd_5439550] using wordTrace_append hprefix tailTrace_5439550
  have hstable : (prefixWord ++ tailWord_5439550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5439550).length < 2 ^ (prefixWord ++ tailWord_5439550).sum := by decide
  have hdescent : baseEnd_5439550 < baseStart_5439550 := by decide
  rcases family_descends (prefixWord ++ tailWord_5439550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5439580 : List Nat := [2, 2, 4, 1, 1, 2, 1, 3, 2, 2, 3]
def baseStart_5439580 : Nat := 118140960795 + 5439580 * 2 ^ 59
def prefixEnd_5439580 : Nat := 4983230072969 + 3 ^ 40 * 5439580 * 2
def baseEnd_5439580 : Nat := 2793119098583932851933833

theorem tailTrace_5439580 : CollatzResearch.WordTrace tailWord_5439580 prefixEnd_5439580 2793119098583932851933833 := by
  unfold tailWord_5439580
  simp only [CollatzResearch.WordTrace]
  refine ⟨99198890816669070573570097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132265187755558760764760129 99198890816669070573570097)
  ·
    refine ⟨74399168112501802930177573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99198890816669070573570097 74399168112501802930177573)
    ·
      refine ⟨13949844021094088049408295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 74399168112501802930177573 13949844021094088049408295)
      ·
        refine ⟨20924766031641132074112443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13949844021094088049408295 20924766031641132074112443)
        ·
          refine ⟨31387149047461698111168665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20924766031641132074112443 31387149047461698111168665)
          ·
            refine ⟨23540361785596273583376499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31387149047461698111168665 23540361785596273583376499)
            ·
              refine ⟨35310542678394410375064749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23540361785596273583376499 35310542678394410375064749)
              ·
                refine ⟨13241453504397903890649281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35310542678394410375064749 13241453504397903890649281)
                ·
                  refine ⟨9931090128298427917986961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13241453504397903890649281 9931090128298427917986961)
                  ·
                    refine ⟨7448317596223820938490221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9931090128298427917986961 7448317596223820938490221)
                    ·
                      refine ⟨2793119098583932851933833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7448317596223820938490221 2793119098583932851933833)
                      ·
                        rfl

theorem cell23_5439580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 1, 3, 2, 2, 3].length) (baseStart_5439580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5439580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5439580 prefixEnd_5439580 := by exact prefixLift 5439580
  have htrace : WordTrace (prefixWord ++ tailWord_5439580) baseStart_5439580 baseEnd_5439580 := by
    simpa [prefixWord, tailWord_5439580, baseEnd_5439580] using wordTrace_append hprefix tailTrace_5439580
  have hstable : (prefixWord ++ tailWord_5439580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5439580).length < 2 ^ (prefixWord ++ tailWord_5439580).sum := by decide
  have hdescent : baseEnd_5439580 < baseStart_5439580 := by decide
  rcases family_descends (prefixWord ++ tailWord_5439580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5439613 : List Nat := [1, 4, 1, 1, 3, 2, 1, 2, 3, 5]
def baseStart_5439613 : Nat := 118140960795 + 5439613 * 2 ^ 59
def prefixEnd_5439613 : Nat := 4983230072969 + 3 ^ 40 * 5439613 * 2
def baseEnd_5439613 : Nat := 931045347815177074273727

theorem tailTrace_5439613 : CollatzResearch.WordTrace tailWord_5439613 prefixEnd_5439613 931045347815177074273727 := by
  unfold tailWord_5439613
  simp only [CollatzResearch.WordTrace]
  refine ⟨198398985242218587783091493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132265990161479058522060995 198398985242218587783091493)
  ·
    refine ⟨37199809732915985209329655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 198398985242218587783091493 37199809732915985209329655)
    ·
      refine ⟨55799714599373977813994483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37199809732915985209329655 55799714599373977813994483)
      ·
        refine ⟨83699571899060966720991725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55799714599373977813994483 83699571899060966720991725)
        ·
          refine ⟨31387339462147862520371897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 83699571899060966720991725 31387339462147862520371897)
          ·
            refine ⟨23540504596610896890278923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31387339462147862520371897 23540504596610896890278923)
            ·
              refine ⟨35310756894916345335418385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23540504596610896890278923 35310756894916345335418385)
              ·
                refine ⟨26483067671187259001563789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35310756894916345335418385 26483067671187259001563789)
                ·
                  refine ⟨9931150376695222125586421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26483067671187259001563789 9931150376695222125586421)
                  ·
                    refine ⟨931045347815177074273727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9931150376695222125586421 931045347815177074273727)
                    ·
                      rfl

theorem cell23_5439613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 1, 2, 3, 5].length) (baseStart_5439613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5439613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5439613 prefixEnd_5439613 := by exact prefixLift 5439613
  have htrace : WordTrace (prefixWord ++ tailWord_5439613) baseStart_5439613 baseEnd_5439613 := by
    simpa [prefixWord, tailWord_5439613, baseEnd_5439613] using wordTrace_append hprefix tailTrace_5439613
  have hstable : (prefixWord ++ tailWord_5439613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5439613).length < 2 ^ (prefixWord ++ tailWord_5439613).sum := by decide
  have hdescent : baseEnd_5439613 < baseStart_5439613 := by decide
  rcases family_descends (prefixWord ++ tailWord_5439613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5439620 : List Nat := [2, 3, 2, 1, 2, 1, 2, 2, 1, 5, 2]
def baseStart_5439620 : Nat := 118140960795 + 5439620 * 2 ^ 59
def prefixEnd_5439620 : Nat := 4983230072969 + 3 ^ 40 * 5439620 * 2
def baseEnd_5439620 : Nat := 2793139637810112695433649

theorem tailTrace_5439620 : CollatzResearch.WordTrace tailWord_5439620 prefixEnd_5439620 2793139637810112695433649 := by
  unfold tailWord_5439620
  simp only [CollatzResearch.WordTrace]
  refine ⟨99199620276596613989298157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132266160368795485319064209 99199620276596613989298157)
  ·
    refine ⟨37199857603723730245986809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 99199620276596613989298157 37199857603723730245986809)
    ·
      refine ⟨27899893202792797684490107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37199857603723730245986809 27899893202792797684490107)
      ·
        refine ⟨41849839804189196526735161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27899893202792797684490107 41849839804189196526735161)
        ·
          refine ⟨31387379853141897395051371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41849839804189196526735161 31387379853141897395051371)
          ·
            refine ⟨47081069779712846092577057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31387379853141897395051371 47081069779712846092577057)
            ·
              refine ⟨35310802334784634569432793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47081069779712846092577057 35310802334784634569432793)
              ·
                refine ⟨26483101751088475927074595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35310802334784634569432793 26483101751088475927074595)
                ·
                  refine ⟨39724652626632713890611893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26483101751088475927074595 39724652626632713890611893)
                  ·
                    refine ⟨3724186183746816927244865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 39724652626632713890611893 3724186183746816927244865)
                    ·
                      refine ⟨2793139637810112695433649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3724186183746816927244865 2793139637810112695433649)
                      ·
                        rfl

theorem cell23_5439620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 2, 2, 1, 5, 2].length) (baseStart_5439620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5439620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5439620 prefixEnd_5439620 := by exact prefixLift 5439620
  have htrace : WordTrace (prefixWord ++ tailWord_5439620) baseStart_5439620 baseEnd_5439620 := by
    simpa [prefixWord, tailWord_5439620, baseEnd_5439620] using wordTrace_append hprefix tailTrace_5439620
  have hstable : (prefixWord ++ tailWord_5439620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5439620).length < 2 ^ (prefixWord ++ tailWord_5439620).sum := by decide
  have hdescent : baseEnd_5439620 < baseStart_5439620 := by decide
  rcases family_descends (prefixWord ++ tailWord_5439620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5439644 : List Nat := [2, 2, 3, 2, 1, 1, 4, 3, 1, 1, 3]
def baseStart_5439644 : Nat := 118140960795 + 5439644 * 2 ^ 59
def prefixEnd_5439644 : Nat := 4983230072969 + 3 ^ 40 * 5439644 * 2
def baseEnd_5439644 : Nat := 2793151961345820601533539

theorem tailTrace_5439644 : CollatzResearch.WordTrace tailWord_5439644 prefixEnd_5439644 2793151961345820601533539 := by
  unfold tailWord_5439644
  simp only [CollatzResearch.WordTrace]
  refine ⟨99200057952553140038734993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132266743936737520051646657 99200057952553140038734993)
  ·
    refine ⟨74400043464414855029051245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99200057952553140038734993 74400043464414855029051245)
    ·
      refine ⟨27900016299155570635894217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74400043464414855029051245 27900016299155570635894217)
      ·
        refine ⟨20925012224366677976920663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27900016299155570635894217 20925012224366677976920663)
        ·
          refine ⟨31387518336550016965380995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20925012224366677976920663 31387518336550016965380995)
          ·
            refine ⟨47081277504825025448071493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31387518336550016965380995 47081277504825025448071493)
            ·
              refine ⟨8827739532154692271513405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 47081277504825025448071493 8827739532154692271513405)
              ·
                refine ⟨3310402324558009601817527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8827739532154692271513405 3310402324558009601817527)
                ·
                  refine ⟨4965603486837014402726291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3310402324558009601817527 4965603486837014402726291)
                  ·
                    refine ⟨7448405230255521604089437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4965603486837014402726291 7448405230255521604089437)
                    ·
                      refine ⟨2793151961345820601533539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7448405230255521604089437 2793151961345820601533539)
                      ·
                        rfl

theorem cell23_5439644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 4, 3, 1, 1, 3].length) (baseStart_5439644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5439644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5439644 prefixEnd_5439644 := by exact prefixLift 5439644
  have htrace : WordTrace (prefixWord ++ tailWord_5439644) baseStart_5439644 baseEnd_5439644 := by
    simpa [prefixWord, tailWord_5439644, baseEnd_5439644] using wordTrace_append hprefix tailTrace_5439644
  have hstable : (prefixWord ++ tailWord_5439644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5439644).length < 2 ^ (prefixWord ++ tailWord_5439644).sum := by decide
  have hdescent : baseEnd_5439644 < baseStart_5439644 := by decide
  rcases family_descends (prefixWord ++ tailWord_5439644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5439647 : List Nat := [1, 1, 2, 6, 1, 1, 4, 1, 1, 5]
def baseStart_5439647 : Nat := 118140960795 + 5439647 * 2 ^ 59
def prefixEnd_5439647 : Nat := 4983230072969 + 3 ^ 40 * 5439647 * 2
def baseEnd_5439647 : Nat := 931051167262594696598675

theorem tailTrace_5439647 : CollatzResearch.WordTrace tailWord_5439647 prefixEnd_5439647 931051167262594696598675 := by
  unfold tailWord_5439647
  simp only [CollatzResearch.WordTrace]
  refine ⟨198400225324095411589829195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132266816882730274393219463 198400225324095411589829195)
  ·
    refine ⟨297600337986143117384743793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198400225324095411589829195 297600337986143117384743793)
    ·
      refine ⟨223200253489607338038557845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 297600337986143117384743793 223200253489607338038557845)
      ·
        refine ⟨10462511882325343970557399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 223200253489607338038557845 10462511882325343970557399)
        ·
          refine ⟨15693767823488015955836099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10462511882325343970557399 15693767823488015955836099)
          ·
            refine ⟨23540651735232023933754149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15693767823488015955836099 23540651735232023933754149)
            ·
              refine ⟨4413872200356004487578903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23540651735232023933754149 4413872200356004487578903)
              ·
                refine ⟨6620808300534006731368355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4413872200356004487578903 6620808300534006731368355)
                ·
                  refine ⟨9931212450801010097052533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6620808300534006731368355 9931212450801010097052533)
                  ·
                    refine ⟨931051167262594696598675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9931212450801010097052533 931051167262594696598675)
                    ·
                      rfl

theorem cell23_5439647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 4, 1, 1, 5].length) (baseStart_5439647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5439647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5439647 prefixEnd_5439647 := by exact prefixLift 5439647
  have htrace : WordTrace (prefixWord ++ tailWord_5439647) baseStart_5439647 baseEnd_5439647 := by
    simpa [prefixWord, tailWord_5439647, baseEnd_5439647] using wordTrace_append hprefix tailTrace_5439647
  have hstable : (prefixWord ++ tailWord_5439647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5439647).length < 2 ^ (prefixWord ++ tailWord_5439647).sum := by decide
  have hdescent : baseEnd_5439647 < baseStart_5439647 := by decide
  rcases family_descends (prefixWord ++ tailWord_5439647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5439653 : List Nat := [1, 3, 1, 2, 1, 3, 2, 3, 1, 1, 5]
def baseStart_5439653 : Nat := 118140960795 + 5439653 * 2 ^ 59
def prefixEnd_5439653 : Nat := 4983230072969 + 3 ^ 40 * 5439653 * 2
def baseEnd_5439653 : Nat := 2793156582671711066320997

theorem tailTrace_5439653 : CollatzResearch.WordTrace tailWord_5439653 prefixEnd_5439653 2793156582671711066320997 := by
  unfold tailWord_5439653
  simp only [CollatzResearch.WordTrace]
  refine ⟨198400444162073674614547613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132266962774715783076365075 198400444162073674614547613)
  ·
    refine ⟨74400166560777627980455355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 198400444162073674614547613 74400166560777627980455355)
    ·
      refine ⟨111600249841166441970683033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74400166560777627980455355 111600249841166441970683033)
      ·
        refine ⟨83700187380874831478012275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111600249841166441970683033 83700187380874831478012275)
        ·
          refine ⟨125550281071312247217018413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83700187380874831478012275 125550281071312247217018413)
          ·
            refine ⟨47081355401742092706381905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 125550281071312247217018413 47081355401742092706381905)
            ·
              refine ⟨35311016551306569529786429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47081355401742092706381905 35311016551306569529786429)
              ·
                refine ⟨13241631206739963573669911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35311016551306569529786429 13241631206739963573669911)
                ·
                  refine ⟨19862446810109945360504867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13241631206739963573669911 19862446810109945360504867)
                  ·
                    refine ⟨29793670215164918040757301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19862446810109945360504867 29793670215164918040757301)
                    ·
                      refine ⟨2793156582671711066320997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29793670215164918040757301 2793156582671711066320997)
                      ·
                        rfl

theorem cell23_5439653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 2, 3, 1, 1, 5].length) (baseStart_5439653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5439653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5439653 prefixEnd_5439653 := by exact prefixLift 5439653
  have htrace : WordTrace (prefixWord ++ tailWord_5439653) baseStart_5439653 baseEnd_5439653 := by
    simpa [prefixWord, tailWord_5439653, baseEnd_5439653] using wordTrace_append hprefix tailTrace_5439653
  have hstable : (prefixWord ++ tailWord_5439653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5439653).length < 2 ^ (prefixWord ++ tailWord_5439653).sum := by decide
  have hdescent : baseEnd_5439653 < baseStart_5439653 := by decide
  rcases family_descends (prefixWord ++ tailWord_5439653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5439680 : List Nat := [2, 1, 1, 2, 5, 1, 3, 1, 1, 2, 4]
def baseStart_5439680 : Nat := 118140960795 + 5439680 * 2 ^ 59
def prefixEnd_5439680 : Nat := 4983230072969 + 3 ^ 40 * 5439680 * 2
def baseEnd_5439680 : Nat := 2793170446649382460683373

theorem tailTrace_5439680 : CollatzResearch.WordTrace tailWord_5439680 prefixEnd_5439680 2793170446649382460683373 := by
  unfold tailWord_5439680
  simp only [CollatzResearch.WordTrace]
  refine ⟨99200714466487929112890247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132267619288650572150520329 99200714466487929112890247)
  ·
    refine ⟨148801071699731893669335371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99200714466487929112890247 148801071699731893669335371)
    ·
      refine ⟨223201607549597840504003057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148801071699731893669335371 223201607549597840504003057)
      ·
        refine ⟨167401205662198380378002293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 223201607549597840504003057 167401205662198380378002293)
        ·
          refine ⟨15693863030831098160437715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 167401205662198380378002293 15693863030831098160437715)
          ·
            refine ⟨23540794546246647240656573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15693863030831098160437715 23540794546246647240656573)
            ·
              refine ⟨8827797954842492715246215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23540794546246647240656573 8827797954842492715246215)
              ·
                refine ⟨13241696932263739072869323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8827797954842492715246215 13241696932263739072869323)
                ·
                  refine ⟨19862545398395608609303985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13241696932263739072869323 19862545398395608609303985)
                  ·
                    refine ⟨14896909048796706456977989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19862545398395608609303985 14896909048796706456977989)
                    ·
                      refine ⟨2793170446649382460683373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14896909048796706456977989 2793170446649382460683373)
                      ·
                        rfl

theorem cell23_5439680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 3, 1, 1, 2, 4].length) (baseStart_5439680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5439680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5439680 prefixEnd_5439680 := by exact prefixLift 5439680
  have htrace : WordTrace (prefixWord ++ tailWord_5439680) baseStart_5439680 baseEnd_5439680 := by
    simpa [prefixWord, tailWord_5439680, baseEnd_5439680] using wordTrace_append hprefix tailTrace_5439680
  have hstable : (prefixWord ++ tailWord_5439680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5439680).length < 2 ^ (prefixWord ++ tailWord_5439680).sum := by decide
  have hdescent : baseEnd_5439680 < baseStart_5439680 := by decide
  rcases family_descends (prefixWord ++ tailWord_5439680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5439684 : List Nat := [2, 3, 3, 1, 2, 1, 2, 2, 3, 2, 2]
def baseStart_5439684 : Nat := 118140960795 + 5439684 * 2 ^ 59
def prefixEnd_5439684 : Nat := 4983230072969 + 3 ^ 40 * 5439684 * 2
def baseEnd_5439684 : Nat := 2793172500572000445033355

theorem tailTrace_5439684 : CollatzResearch.WordTrace tailWord_5439684 prefixEnd_5439684 2793172500572000445033355 := by
  unfold tailWord_5439684
  simp only [CollatzResearch.WordTrace]
  refine ⟨99200787412480683454463053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132267716549974244605950737 99200787412480683454463053)
  ·
    refine ⟨37200295279680256295423645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 99200787412480683454463053 37200295279680256295423645)
    ·
      refine ⟨13950110729880096110783867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37200295279680256295423645 13950110729880096110783867)
      ·
        refine ⟨20925166094820144166175801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13950110729880096110783867 20925166094820144166175801)
        ·
          refine ⟨15693874571115108124631851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20925166094820144166175801 15693874571115108124631851)
          ·
            refine ⟨23540811856672662186947777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15693874571115108124631851 23540811856672662186947777)
            ·
              refine ⟨17655608892504496640210833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23540811856672662186947777 17655608892504496640210833)
              ·
                refine ⟨13241706669378372480158125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17655608892504496640210833 13241706669378372480158125)
                ·
                  refine ⟨4965640001016889680059297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13241706669378372480158125 4965640001016889680059297)
                  ·
                    refine ⟨3724230000762667260044473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4965640001016889680059297 3724230000762667260044473)
                    ·
                      refine ⟨2793172500572000445033355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3724230000762667260044473 2793172500572000445033355)
                      ·
                        rfl

theorem cell23_5439684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 2, 2, 3, 2, 2].length) (baseStart_5439684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5439684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5439684 prefixEnd_5439684 := by exact prefixLift 5439684
  have htrace : WordTrace (prefixWord ++ tailWord_5439684) baseStart_5439684 baseEnd_5439684 := by
    simpa [prefixWord, tailWord_5439684, baseEnd_5439684] using wordTrace_append hprefix tailTrace_5439684
  have hstable : (prefixWord ++ tailWord_5439684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5439684).length < 2 ^ (prefixWord ++ tailWord_5439684).sum := by decide
  have hdescent : baseEnd_5439684 < baseStart_5439684 := by decide
  rcases family_descends (prefixWord ++ tailWord_5439684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5439713 : List Nat := [1, 2, 3, 1, 3, 1, 1, 2, 2, 2, 5]
def baseStart_5439713 : Nat := 118140960795 + 5439713 * 2 ^ 59
def prefixEnd_5439713 : Nat := 4983230072969 + 3 ^ 40 * 5439713 * 2
def baseEnd_5439713 : Nat := 2793187391510980831570721

theorem tailTrace_5439713 : CollatzResearch.WordTrace tailWord_5439713 prefixEnd_5439713 2793187391510980831570721 := by
  unfold tailWord_5439713
  simp only [CollatzResearch.WordTrace]
  refine ⟨198402632541856304861731793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132268421694570869907821195 198402632541856304861731793)
  ·
    refine ⟨148801974406392228646298845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 198402632541856304861731793 148801974406392228646298845)
    ·
      refine ⟨55800740402397085742362067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 148801974406392228646298845 55800740402397085742362067)
      ·
        refine ⟨83701110603595628613543101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55800740402397085742362067 83701110603595628613543101)
        ·
          refine ⟨31387916476348360730078663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 83701110603595628613543101 31387916476348360730078663)
          ·
            refine ⟨47081874714522541095117995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31387916476348360730078663 47081874714522541095117995)
            ·
              refine ⟨70622812071783811642676993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47081874714522541095117995 70622812071783811642676993)
              ·
                refine ⟨52967109053837858732007745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 70622812071783811642676993 52967109053837858732007745)
                ·
                  refine ⟨39725331790378394049005809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 52967109053837858732007745 39725331790378394049005809)
                  ·
                    refine ⟨29793998842783795536754357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 39725331790378394049005809 29793998842783795536754357)
                    ·
                      refine ⟨2793187391510980831570721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29793998842783795536754357 2793187391510980831570721)
                      ·
                        rfl

theorem cell23_5439713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 2, 2, 2, 5].length) (baseStart_5439713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5439713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5439713 prefixEnd_5439713 := by exact prefixLift 5439713
  have htrace : WordTrace (prefixWord ++ tailWord_5439713) baseStart_5439713 baseEnd_5439713 := by
    simpa [prefixWord, tailWord_5439713, baseEnd_5439713] using wordTrace_append hprefix tailTrace_5439713
  have hstable : (prefixWord ++ tailWord_5439713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5439713).length < 2 ^ (prefixWord ++ tailWord_5439713).sum := by decide
  have hdescent : baseEnd_5439713 < baseStart_5439713 := by decide
  rcases family_descends (prefixWord ++ tailWord_5439713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5439717 : List Nat := [1, 3, 1, 4, 2, 1, 2, 1, 4, 1, 3]
def baseStart_5439717 : Nat := 118140960795 + 5439717 * 2 ^ 59
def prefixEnd_5439717 : Nat := 4983230072969 + 3 ^ 40 * 5439717 * 2
def baseEnd_5439717 : Nat := 2793189445433598815920703

theorem tailTrace_5439717 : CollatzResearch.WordTrace tailWord_5439717 prefixEnd_5439717 2793189445433598815920703 := by
  unfold tailWord_5439717
  simp only [CollatzResearch.WordTrace]
  refine ⟨198402778433841813544877405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132268518955894542363251603 198402778433841813544877405)
  ·
    refine ⟨74401041912690680079329027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 198402778433841813544877405 74401041912690680079329027)
    ·
      refine ⟨111601562869036020118993541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74401041912690680079329027 111601562869036020118993541)
      ·
        refine ⟨20925293037944253772311289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 111601562869036020118993541 20925293037944253772311289)
        ·
          refine ⟨15693969778458190329233467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20925293037944253772311289 15693969778458190329233467)
          ·
            refine ⟨23540954667687285493850201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15693969778458190329233467 23540954667687285493850201)
            ·
              refine ⟨17655716000765464120387651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23540954667687285493850201 17655716000765464120387651)
              ·
                refine ⟨26483574001148196180581477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17655716000765464120387651 26483574001148196180581477)
                ·
                  refine ⟨4965670125215286783859027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26483574001148196180581477 4965670125215286783859027)
                  ·
                    refine ⟨7448505187822930175788541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4965670125215286783859027 7448505187822930175788541)
                    ·
                      refine ⟨2793189445433598815920703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7448505187822930175788541 2793189445433598815920703)
                      ·
                        rfl

theorem cell23_5439717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 2, 1, 4, 1, 3].length) (baseStart_5439717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5439717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5439717 prefixEnd_5439717 := by exact prefixLift 5439717
  have htrace : WordTrace (prefixWord ++ tailWord_5439717) baseStart_5439717 baseEnd_5439717 := by
    simpa [prefixWord, tailWord_5439717, baseEnd_5439717] using wordTrace_append hprefix tailTrace_5439717
  have hstable : (prefixWord ++ tailWord_5439717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5439717).length < 2 ^ (prefixWord ++ tailWord_5439717).sum := by decide
  have hdescent : baseEnd_5439717 < baseStart_5439717 := by decide
  rcases family_descends (prefixWord ++ tailWord_5439717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5439723 : List Nat := [1, 1, 1, 1, 2, 5, 2, 1, 2, 3, 4]
def baseStart_5439723 : Nat := 118140960795 + 5439723 * 2 ^ 59
def prefixEnd_5439723 : Nat := 4983230072969 + 3 ^ 40 * 5439723 * 2
def baseEnd_5439723 : Nat := 2793192526317525792445675

theorem tailTrace_5439723 : CollatzResearch.WordTrace tailWord_5439723 prefixEnd_5439723 2793192526317525792445675 := by
  unfold tailWord_5439723
  simp only [CollatzResearch.WordTrace]
  refine ⟨198402997271820076569595823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132268664847880051046397215 198402997271820076569595823)
  ·
    refine ⟨297604495907730114854393735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198402997271820076569595823 297604495907730114854393735)
    ·
      refine ⟨446406743861595172281590603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 297604495907730114854393735 446406743861595172281590603)
      ·
        refine ⟨669610115792392758422385905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 446406743861595172281590603 669610115792392758422385905)
        ·
          refine ⟨502207586844294568816789429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 669610115792392758422385905 502207586844294568816789429)
          ·
            refine ⟨47081961266652615826574009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 502207586844294568816789429 47081961266652615826574009)
            ·
              refine ⟨35311470949989461869930507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47081961266652615826574009 35311470949989461869930507)
              ·
                refine ⟨52967206424984192804895761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35311470949989461869930507 52967206424984192804895761)
                ·
                  refine ⟨39725404818738144603671821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 52967206424984192804895761 39725404818738144603671821)
                  ·
                    refine ⟨14897026807026804226376933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 39725404818738144603671821 14897026807026804226376933)
                    ·
                      refine ⟨2793192526317525792445675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14897026807026804226376933 2793192526317525792445675)
                      ·
                        rfl

theorem cell23_5439723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 2, 1, 2, 3, 4].length) (baseStart_5439723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5439723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5439723 prefixEnd_5439723 := by exact prefixLift 5439723
  have htrace : WordTrace (prefixWord ++ tailWord_5439723) baseStart_5439723 baseEnd_5439723 := by
    simpa [prefixWord, tailWord_5439723, baseEnd_5439723] using wordTrace_append hprefix tailTrace_5439723
  have hstable : (prefixWord ++ tailWord_5439723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5439723).length < 2 ^ (prefixWord ++ tailWord_5439723).sum := by decide
  have hdescent : baseEnd_5439723 < baseStart_5439723 := by decide
  rcases family_descends (prefixWord ++ tailWord_5439723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5439743 : List Nat := [1, 1, 2, 2, 1, 4, 1, 1, 4, 1, 5]
def baseStart_5439743 : Nat := 118140960795 + 5439743 * 2 ^ 59
def prefixEnd_5439743 : Nat := 4983230072969 + 3 ^ 40 * 5439743 * 2
def baseEnd_5439743 : Nat := 2793202795930615714195583

theorem tailTrace_5439743 : CollatzResearch.WordTrace tailWord_5439743 prefixEnd_5439743 2793202795930615714195583 := by
  unfold tailWord_5439743
  simp only [CollatzResearch.WordTrace]
  refine ⟨198403726731747619985323883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132269151154498413323549255 198403726731747619985323883)
  ·
    refine ⟨297605590097621429977985825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198403726731747619985323883 297605590097621429977985825)
    ·
      refine ⟨223204192573216072483489369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 297605590097621429977985825 223204192573216072483489369)
      ·
        refine ⟨167403144429912054362617027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 223204192573216072483489369 167403144429912054362617027)
        ·
          refine ⟨251104716644868081543925541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 167403144429912054362617027 251104716644868081543925541)
          ·
            refine ⟨47082134370912765289486039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 251104716644868081543925541 47082134370912765289486039)
            ·
              refine ⟨70623201556369147934229059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47082134370912765289486039 70623201556369147934229059)
              ·
                refine ⟨105934802334553721901343589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70623201556369147934229059 105934802334553721901343589)
                ·
                  refine ⟨19862775437728822856501923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 105934802334553721901343589 19862775437728822856501923)
                  ·
                    refine ⟨29794163156593234284752885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19862775437728822856501923 29794163156593234284752885)
                    ·
                      refine ⟨2793202795930615714195583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29794163156593234284752885 2793202795930615714195583)
                      ·
                        rfl

theorem cell23_5439743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 1, 4, 1, 5].length) (baseStart_5439743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5439743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5439743 prefixEnd_5439743 := by exact prefixLift 5439743
  have htrace : WordTrace (prefixWord ++ tailWord_5439743) baseStart_5439743 baseEnd_5439743 := by
    simpa [prefixWord, tailWord_5439743, baseEnd_5439743] using wordTrace_append hprefix tailTrace_5439743
  have hstable : (prefixWord ++ tailWord_5439743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5439743).length < 2 ^ (prefixWord ++ tailWord_5439743).sum := by decide
  have hdescent : baseEnd_5439743 < baseStart_5439743 := by decide
  rcases family_descends (prefixWord ++ tailWord_5439743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5439904 : List Nat := [2, 1, 1, 4, 1, 5, 2, 1, 6]
def baseStart_5439904 : Nat := 118140960795 + 5439904 * 2 ^ 59
def prefixEnd_5439904 : Nat := 4983230072969 + 3 ^ 40 * 5439904 * 2
def baseEnd_5439904 : Nat := 310365051812887731586927

theorem tailTrace_5439904 : CollatzResearch.WordTrace tailWord_5439904 prefixEnd_5439904 310365051812887731586927 := by
  unfold tailWord_5439904
  simp only [CollatzResearch.WordTrace]
  refine ⟨99204799442082172240967383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132273065922776229654623177 99204799442082172240967383)
  ·
    refine ⟨148807199163123258361451075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99204799442082172240967383 148807199163123258361451075)
    ·
      refine ⟨223210798744684887542176613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148807199163123258361451075 223210798744684887542176613)
      ·
        refine ⟨41852024764628416414158115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 223210798744684887542176613 41852024764628416414158115)
        ·
          refine ⟨62778037146942624621237173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41852024764628416414158115 62778037146942624621237173)
          ·
            refine ⟨5885440982525871058240985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 62778037146942624621237173 5885440982525871058240985)
            ·
              refine ⟨4414080736894403293680739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5885440982525871058240985 4414080736894403293680739)
              ·
                refine ⟨6621121105341604940521109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4414080736894403293680739 6621121105341604940521109)
                ·
                  refine ⟨310365051812887731586927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6621121105341604940521109 310365051812887731586927)
                  ·
                    rfl

theorem cell23_5439904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 5, 2, 1, 6].length) (baseStart_5439904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5439904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5439904 prefixEnd_5439904 := by exact prefixLift 5439904
  have htrace : WordTrace (prefixWord ++ tailWord_5439904) baseStart_5439904 baseEnd_5439904 := by
    simpa [prefixWord, tailWord_5439904, baseEnd_5439904] using wordTrace_append hprefix tailTrace_5439904
  have hstable : (prefixWord ++ tailWord_5439904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5439904).length < 2 ^ (prefixWord ++ tailWord_5439904).sum := by decide
  have hdescent : baseEnd_5439904 < baseStart_5439904 := by decide
  rcases family_descends (prefixWord ++ tailWord_5439904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5439948 : List Nat := [2, 2, 1, 4, 3, 1, 1, 4, 1, 1, 3]
def baseStart_5439948 : Nat := 118140960795 + 5439948 * 2 ^ 59
def prefixEnd_5439948 : Nat := 4983230072969 + 3 ^ 40 * 5439948 * 2
def baseEnd_5439948 : Nat := 2793308059464787412132141

theorem tailTrace_5439948 : CollatzResearch.WordTrace tailWord_5439948 prefixEnd_5439948 2793308059464787412132141 := by
  unfold tailWord_5439948
  simp only [CollatzResearch.WordTrace]
  refine ⟨99205601848002469998268249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132274135797336626664357665 99205601848002469998268249)
  ·
    refine ⟨74404201386001852498701187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99205601848002469998268249 74404201386001852498701187)
    ·
      refine ⟨111606302079002778748051781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74404201386001852498701187 111606302079002778748051781)
      ·
        refine ⟨20926181639813021015259709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 111606302079002778748051781 20926181639813021015259709)
        ·
          refine ⟨7847318114929882880722391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20926181639813021015259709 7847318114929882880722391)
          ·
            refine ⟨11770977172394824321083587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7847318114929882880722391 11770977172394824321083587)
            ·
              refine ⟨17656465758592236481625381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11770977172394824321083587 17656465758592236481625381)
              ·
                refine ⟨3310587329736044340304759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17656465758592236481625381 3310587329736044340304759)
                ·
                  refine ⟨4965880994604066510457139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3310587329736044340304759 4965880994604066510457139)
                  ·
                    refine ⟨7448821491906099765685709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4965880994604066510457139 7448821491906099765685709)
                    ·
                      refine ⟨2793308059464787412132141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7448821491906099765685709 2793308059464787412132141)
                      ·
                        rfl

theorem cell23_5439948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 1, 4, 1, 1, 3].length) (baseStart_5439948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5439948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5439948 prefixEnd_5439948 := by exact prefixLift 5439948
  have htrace : WordTrace (prefixWord ++ tailWord_5439948) baseStart_5439948 baseEnd_5439948 := by
    simpa [prefixWord, tailWord_5439948, baseEnd_5439948] using wordTrace_append hprefix tailTrace_5439948
  have hstable : (prefixWord ++ tailWord_5439948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5439948).length < 2 ^ (prefixWord ++ tailWord_5439948).sum := by decide
  have hdescent : baseEnd_5439948 < baseStart_5439948 := by decide
  rcases family_descends (prefixWord ++ tailWord_5439948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5439967 : List Nat := [1, 1, 2, 3, 3, 2, 1, 3, 1, 2, 4]
def baseStart_5439967 : Nat := 118140960795 + 5439967 * 2 ^ 59
def prefixEnd_5439967 : Nat := 4983230072969 + 3 ^ 40 * 5439967 * 2
def baseEnd_5439967 : Nat := 2793317815597222837794553

theorem tailTrace_5439967 : CollatzResearch.WordTrace tailWord_5439967 prefixEnd_5439967 2793317815597222837794553 := by
  unfold tailWord_5439967
  simp only [CollatzResearch.WordTrace]
  refine ⟨198411896682936106241478155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132274597788624070827652103 198411896682936106241478155)
  ·
    refine ⟨297617845024404159362217233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198411896682936106241478155 297617845024404159362217233)
    ·
      refine ⟨223213383768303119521662925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 297617845024404159362217233 223213383768303119521662925)
      ·
        refine ⟨83705018913113669820623597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 223213383768303119521662925 83705018913113669820623597)
        ·
          refine ⟨31389382092417626182733849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 83705018913113669820623597 31389382092417626182733849)
          ·
            refine ⟨23542036569313219637050387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31389382092417626182733849 23542036569313219637050387)
            ·
              refine ⟨35313054853969829455575581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23542036569313219637050387 35313054853969829455575581)
              ·
                refine ⟨13242395570238686045840843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35313054853969829455575581 13242395570238686045840843)
                ·
                  refine ⟨19863593355358029068761265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13242395570238686045840843 19863593355358029068761265)
                  ·
                    refine ⟨14897695016518521801570949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19863593355358029068761265 14897695016518521801570949)
                    ·
                      refine ⟨2793317815597222837794553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14897695016518521801570949 2793317815597222837794553)
                      ·
                        rfl

theorem cell23_5439967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 1, 3, 1, 2, 4].length) (baseStart_5439967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5439967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5439967 prefixEnd_5439967 := by exact prefixLift 5439967
  have htrace : WordTrace (prefixWord ++ tailWord_5439967) baseStart_5439967 baseEnd_5439967 := by
    simpa [prefixWord, tailWord_5439967, baseEnd_5439967] using wordTrace_append hprefix tailTrace_5439967
  have hstable : (prefixWord ++ tailWord_5439967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5439967).length < 2 ^ (prefixWord ++ tailWord_5439967).sum := by decide
  have hdescent : baseEnd_5439967 < baseStart_5439967 := by decide
  rcases family_descends (prefixWord ++ tailWord_5439967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5439987 : List Nat := [1, 1, 1, 2, 2, 2, 3, 4, 1, 3, 3]
def baseStart_5439987 : Nat := 118140960795 + 5439987 * 2 ^ 59
def prefixEnd_5439987 : Nat := 4983230072969 + 3 ^ 40 * 5439987 * 2
def baseEnd_5439987 : Nat := 2793328085210312759544461

theorem tailTrace_5439987 : CollatzResearch.WordTrace tailWord_5439987 prefixEnd_5439987 2793328085210312759544461 := by
  unfold tailWord_5439987
  simp only [CollatzResearch.WordTrace]
  refine ⟨198412626142863649657206215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132275084095242433104804143 198412626142863649657206215)
  ·
    refine ⟨297618939214295474485809323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198412626142863649657206215 297618939214295474485809323)
    ·
      refine ⟨446428408821443211728713985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 297618939214295474485809323 446428408821443211728713985)
      ·
        refine ⟨334821306616082408796535489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 446428408821443211728713985 334821306616082408796535489)
        ·
          refine ⟨251115979962061806597401617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 334821306616082408796535489 251115979962061806597401617)
          ·
            refine ⟨188336984971546354948051213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 251115979962061806597401617 188336984971546354948051213)
            ·
              refine ⟨70626369364329883105519205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 188336984971546354948051213 70626369364329883105519205)
              ·
                refine ⟨13242444255811853082284851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 70626369364329883105519205 13242444255811853082284851)
                ·
                  refine ⟨19863666383717779623427277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13242444255811853082284851 19863666383717779623427277)
                  ·
                    refine ⟨7448874893894167358785229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19863666383717779623427277 7448874893894167358785229)
                    ·
                      refine ⟨2793328085210312759544461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7448874893894167358785229 2793328085210312759544461)
                      ·
                        rfl

theorem cell23_5439987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 4, 1, 3, 3].length) (baseStart_5439987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5439987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5439987 prefixEnd_5439987 := by exact prefixLift 5439987
  have htrace : WordTrace (prefixWord ++ tailWord_5439987) baseStart_5439987 baseEnd_5439987 := by
    simpa [prefixWord, tailWord_5439987, baseEnd_5439987] using wordTrace_append hprefix tailTrace_5439987
  have hstable : (prefixWord ++ tailWord_5439987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5439987).length < 2 ^ (prefixWord ++ tailWord_5439987).sum := by decide
  have hdescent : baseEnd_5439987 < baseStart_5439987 := by decide
  rcases family_descends (prefixWord ++ tailWord_5439987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5440039 : List Nat := [1, 1, 7, 2, 1, 2, 1, 3, 1, 2, 2]
def baseStart_5440039 : Nat := 118140960795 + 5440039 * 2 ^ 59
def prefixEnd_5440039 : Nat := 4983230072969 + 3 ^ 40 * 5440039 * 2
def baseEnd_5440039 : Nat := 2793354786204346556094223

theorem tailTrace_5440039 : CollatzResearch.WordTrace tailWord_5440039 prefixEnd_5440039 2793354786204346556094223 := by
  unfold tailWord_5440039
  simp only [CollatzResearch.WordTrace]
  refine ⟨198414522738675262538099171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132276348492450175025399447 198414522738675262538099171)
  ·
    refine ⟨297621784108012893807148757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198414522738675262538099171 297621784108012893807148757)
    ·
      refine ⟨6975510565031552198605049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 297621784108012893807148757 6975510565031552198605049)
      ·
        refine ⟨5231632923773664148953787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6975510565031552198605049 5231632923773664148953787)
        ·
          refine ⟨7847449385660496223430681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5231632923773664148953787 7847449385660496223430681)
          ·
            refine ⟨5885587039245372167573011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7847449385660496223430681 5885587039245372167573011)
            ·
              refine ⟨8828380558868058251359517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5885587039245372167573011 8828380558868058251359517)
              ·
                refine ⟨3310642709575521844259819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8828380558868058251359517 3310642709575521844259819)
                ·
                  refine ⟨4965964064363282766389729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3310642709575521844259819 4965964064363282766389729)
                  ·
                    refine ⟨3724473048272462074792297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4965964064363282766389729 3724473048272462074792297)
                    ·
                      refine ⟨2793354786204346556094223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3724473048272462074792297 2793354786204346556094223)
                      ·
                        rfl

theorem cell23_5440039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 2, 1, 3, 1, 2, 2].length) (baseStart_5440039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5440039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5440039 prefixEnd_5440039 := by exact prefixLift 5440039
  have htrace : WordTrace (prefixWord ++ tailWord_5440039) baseStart_5440039 baseEnd_5440039 := by
    simpa [prefixWord, tailWord_5440039, baseEnd_5440039] using wordTrace_append hprefix tailTrace_5440039
  have hstable : (prefixWord ++ tailWord_5440039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5440039).length < 2 ^ (prefixWord ++ tailWord_5440039).sum := by decide
  have hdescent : baseEnd_5440039 < baseStart_5440039 := by decide
  rcases family_descends (prefixWord ++ tailWord_5440039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5440044 : List Nat := [2, 2, 1, 1, 1, 2, 1, 6, 1, 4, 2]
def baseStart_5440044 : Nat := 118140960795 + 5440044 * 2 ^ 59
def prefixEnd_5440044 : Nat := 4983230072969 + 3 ^ 40 * 5440044 * 2
def baseEnd_5440044 : Nat := 2793357353607619036531699

theorem tailTrace_5440044 : CollatzResearch.WordTrace tailWord_5440044 prefixEnd_5440044 2793357353607619036531699 := by
  unfold tailWord_5440044
  simp only [CollatzResearch.WordTrace]
  refine ⟨99207352551828574196015593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132276470069104765594687457 99207352551828574196015593)
  ·
    refine ⟨74405514413871430647011695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99207352551828574196015593 74405514413871430647011695)
    ·
      refine ⟨111608271620807145970517543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74405514413871430647011695 111608271620807145970517543)
      ·
        refine ⟨167412407431210718955776315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111608271620807145970517543 167412407431210718955776315)
        ·
          refine ⟨251118611146816078433664473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 167412407431210718955776315 251118611146816078433664473)
          ·
            refine ⟨188338958360112058825248355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 251118611146816078433664473 188338958360112058825248355)
            ·
              refine ⟨282508437540168088237872533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 188338958360112058825248355 282508437540168088237872533)
              ·
                refine ⟨13242583009695379136150275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 282508437540168088237872533 13242583009695379136150275)
                ·
                  refine ⟨19863874514543068704225413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13242583009695379136150275 19863874514543068704225413)
                  ·
                    refine ⟨3724476471476825382042265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19863874514543068704225413 3724476471476825382042265)
                    ·
                      refine ⟨2793357353607619036531699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3724476471476825382042265 2793357353607619036531699)
                      ·
                        rfl

theorem cell23_5440044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 4, 2].length) (baseStart_5440044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5440044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5440044 prefixEnd_5440044 := by exact prefixLift 5440044
  have htrace : WordTrace (prefixWord ++ tailWord_5440044) baseStart_5440044 baseEnd_5440044 := by
    simpa [prefixWord, tailWord_5440044, baseEnd_5440044] using wordTrace_append hprefix tailTrace_5440044
  have hstable : (prefixWord ++ tailWord_5440044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5440044).length < 2 ^ (prefixWord ++ tailWord_5440044).sum := by decide
  have hdescent : baseEnd_5440044 < baseStart_5440044 := by decide
  rcases family_descends (prefixWord ++ tailWord_5440044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5440118 : List Nat := [5, 1, 1, 2, 3, 1, 1, 4, 5]
def baseStart_5440118 : Nat := 118140960795 + 5440118 * 2 ^ 59
def prefixEnd_5440118 : Nat := 4983230072969 + 3 ^ 40 * 5440118 * 2
def baseEnd_5440118 : Nat := 310377261241783527445151

theorem tailTrace_5440118 : CollatzResearch.WordTrace tailWord_5440118 prefixEnd_5440118 310377261241783527445151 := by
  unfold tailWord_5440118
  simp only [CollatzResearch.WordTrace]
  refine ⟨12401087756586816189389063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 132278269403592706020150005 12401087756586816189389063)
  ·
    refine ⟨18601631634880224284083595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12401087756586816189389063 18601631634880224284083595)
    ·
      refine ⟨27902447452320336426125393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18601631634880224284083595 27902447452320336426125393)
      ·
        refine ⟨20926835589240252319594045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27902447452320336426125393 20926835589240252319594045)
        ·
          refine ⟨7847563345965094619847767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20926835589240252319594045 7847563345965094619847767)
          ·
            refine ⟨11771345018947641929771651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7847563345965094619847767 11771345018947641929771651)
            ·
              refine ⟨17657017528421462894657477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11771345018947641929771651 17657017528421462894657477)
              ·
                refine ⟨3310690786579024292748277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17657017528421462894657477 3310690786579024292748277)
                ·
                  refine ⟨310377261241783527445151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3310690786579024292748277 310377261241783527445151)
                  ·
                    rfl

theorem cell23_5440118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 1, 4, 5].length) (baseStart_5440118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5440118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5440118 prefixEnd_5440118 := by exact prefixLift 5440118
  have htrace : WordTrace (prefixWord ++ tailWord_5440118) baseStart_5440118 baseEnd_5440118 := by
    simpa [prefixWord, tailWord_5440118, baseEnd_5440118] using wordTrace_append hprefix tailTrace_5440118
  have hstable : (prefixWord ++ tailWord_5440118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5440118).length < 2 ^ (prefixWord ++ tailWord_5440118).sum := by decide
  have hdescent : baseEnd_5440118 < baseStart_5440118 := by decide
  rcases family_descends (prefixWord ++ tailWord_5440118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5440147 : List Nat := [1, 1, 1, 2, 1, 2, 2, 3, 2, 4, 4]
def baseStart_5440147 : Nat := 118140960795 + 5440147 * 2 ^ 59
def prefixEnd_5440147 : Nat := 4983230072969 + 3 ^ 40 * 5440147 * 2
def baseEnd_5440147 : Nat := 2793410242115032133543725

theorem tailTrace_5440147 : CollatzResearch.WordTrace tailWord_5440147 prefixEnd_5440147 2793410242115032133543725 := by
  unfold tailWord_5440147
  simp only [CollatzResearch.WordTrace]
  refine ⟨198418461822283996983030695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132278974548189331322020463 198418461822283996983030695)
  ·
    refine ⟨297627692733425995474546043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198418461822283996983030695 297627692733425995474546043)
    ·
      refine ⟨446441539100138993211819065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 297627692733425995474546043 446441539100138993211819065)
      ·
        refine ⟨334831154325104244908864299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 446441539100138993211819065 334831154325104244908864299)
        ·
          refine ⟨502246731487656367363296449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 334831154325104244908864299 502246731487656367363296449)
          ·
            refine ⟨376685048615742275522472337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 502246731487656367363296449 376685048615742275522472337)
            ·
              refine ⟨282513786461806706641854253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 376685048615742275522472337 282513786461806706641854253)
              ·
                refine ⟨105942669923177514990695345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 282513786461806706641854253 105942669923177514990695345)
                ·
                  refine ⟨79457002442383136243021509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 105942669923177514990695345 79457002442383136243021509)
                  ·
                    refine ⟨14898187957946838045566533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 79457002442383136243021509 14898187957946838045566533)
                    ·
                      refine ⟨2793410242115032133543725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14898187957946838045566533 2793410242115032133543725)
                      ·
                        rfl

theorem cell23_5440147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 3, 2, 4, 4].length) (baseStart_5440147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5440147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5440147 prefixEnd_5440147 := by exact prefixLift 5440147
  have htrace : WordTrace (prefixWord ++ tailWord_5440147) baseStart_5440147 baseEnd_5440147 := by
    simpa [prefixWord, tailWord_5440147, baseEnd_5440147] using wordTrace_append hprefix tailTrace_5440147
  have hstable : (prefixWord ++ tailWord_5440147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5440147).length < 2 ^ (prefixWord ++ tailWord_5440147).sum := by decide
  have hdescent : baseEnd_5440147 < baseStart_5440147 := by decide
  rcases family_descends (prefixWord ++ tailWord_5440147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5440148 : List Nat := [2, 4, 2, 2, 1, 3, 1, 1, 2, 5]
def baseStart_5440148 : Nat := 118140960795 + 5440148 * 2 ^ 59
def prefixEnd_5440148 : Nat := 4983230072969 + 3 ^ 40 * 5440148 * 2
def baseEnd_5440148 : Nat := 931136918531895543210407

theorem tailTrace_5440148 : CollatzResearch.WordTrace tailWord_5440148 prefixEnd_5440148 931136918531895543210407 := by
  unfold tailWord_5440148
  simp only [CollatzResearch.WordTrace]
  refine ⟨99209249147640187076908549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132278998863520249435878065 99209249147640187076908549)
  ·
    refine ⟨18601734215182535076920353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 99209249147640187076908549 18601734215182535076920353)
    ·
      refine ⟨13951300661386901307690265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18601734215182535076920353 13951300661386901307690265)
      ·
        refine ⟨10463475496040175980767699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13951300661386901307690265 10463475496040175980767699)
        ·
          refine ⟨15695213244060263971151549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10463475496040175980767699 15695213244060263971151549)
          ·
            refine ⟨5885704966522598989181831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15695213244060263971151549 5885704966522598989181831)
            ·
              refine ⟨8828557449783898483772747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5885704966522598989181831 8828557449783898483772747)
              ·
                refine ⟨13242836174675847725659121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8828557449783898483772747 13242836174675847725659121)
                ·
                  refine ⟨9932127131006885794244341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13242836174675847725659121 9932127131006885794244341)
                  ·
                    refine ⟨931136918531895543210407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9932127131006885794244341 931136918531895543210407)
                    ·
                      rfl

theorem cell23_5440148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 3, 1, 1, 2, 5].length) (baseStart_5440148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5440148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5440148 prefixEnd_5440148 := by exact prefixLift 5440148
  have htrace : WordTrace (prefixWord ++ tailWord_5440148) baseStart_5440148 baseEnd_5440148 := by
    simpa [prefixWord, tailWord_5440148, baseEnd_5440148] using wordTrace_append hprefix tailTrace_5440148
  have hstable : (prefixWord ++ tailWord_5440148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5440148).length < 2 ^ (prefixWord ++ tailWord_5440148).sum := by decide
  have hdescent : baseEnd_5440148 < baseStart_5440148 := by decide
  rcases family_descends (prefixWord ++ tailWord_5440148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5440191 : List Nat := [1, 1, 2, 2, 2, 5, 3, 1, 6]
def baseStart_5440191 : Nat := 118140960795 + 5440191 * 2 ^ 59
def prefixEnd_5440191 : Nat := 4983230072969 + 3 ^ 40 * 5440191 * 2
def baseEnd_5440191 : Nat := 310381426140425551265947

theorem tailTrace_5440191 : CollatzResearch.WordTrace tailWord_5440191 prefixEnd_5440191 310381426140425551265947 := by
  unfold tailWord_5440191
  simp only [CollatzResearch.WordTrace]
  refine ⟨198420066634124592497632427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132280044422749728331754951 198420066634124592497632427)
  ·
    refine ⟨297630099951186888746448641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198420066634124592497632427 297630099951186888746448641)
    ·
      refine ⟨223222574963390166559836481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 297630099951186888746448641 223222574963390166559836481)
      ·
        refine ⟨167416931222542624919877361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 223222574963390166559836481 167416931222542624919877361)
        ·
          refine ⟨125562698416906968689908021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 167416931222542624919877361 125562698416906968689908021)
          ·
            refine ⟨11771502976585028314678877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 125562698416906968689908021 11771502976585028314678877)
            ·
              refine ⟨4414313616219385618004579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11771502976585028314678877 4414313616219385618004579)
              ·
                refine ⟨6621470424329078427006869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4414313616219385618004579 6621470424329078427006869)
                ·
                  refine ⟨310381426140425551265947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6621470424329078427006869 310381426140425551265947)
                  ·
                    rfl

theorem cell23_5440191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 3, 1, 6].length) (baseStart_5440191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5440191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5440191 prefixEnd_5440191 := by exact prefixLift 5440191
  have htrace : WordTrace (prefixWord ++ tailWord_5440191) baseStart_5440191 baseEnd_5440191 := by
    simpa [prefixWord, tailWord_5440191, baseEnd_5440191] using wordTrace_append hprefix tailTrace_5440191
  have hstable : (prefixWord ++ tailWord_5440191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5440191).length < 2 ^ (prefixWord ++ tailWord_5440191).sum := by decide
  have hdescent : baseEnd_5440191 < baseStart_5440191 := by decide
  rcases family_descends (prefixWord ++ tailWord_5440191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5440212 : List Nat := [2, 4, 1, 3, 2, 2, 1, 3, 1, 4]
def baseStart_5440212 : Nat := 118140960795 + 5440212 * 2 ^ 59
def prefixEnd_5440212 : Nat := 4983230072969 + 3 ^ 40 * 5440212 * 2
def baseEnd_5440212 : Nat := 931147872785858126410309

theorem tailTrace_5440212 : CollatzResearch.WordTrace tailWord_5440212 prefixEnd_5440212 931147872785858126410309 := by
  unfold tailWord_5440212
  simp only [CollatzResearch.WordTrace]
  refine ⟨99210416283524256542073445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132280555044699008722764593 99210416283524256542073445)
  ·
    refine ⟨18601953053160798101638771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 99210416283524256542073445 18601953053160798101638771)
    ·
      refine ⟨27902929579741197152458157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18601953053160798101638771 27902929579741197152458157)
      ·
        refine ⟨10463598592402948932171809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27902929579741197152458157 10463598592402948932171809)
        ·
          refine ⟨7847698944302211699128857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10463598592402948932171809 7847698944302211699128857)
          ·
            refine ⟨5885774208226658774346643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7847698944302211699128857 5885774208226658774346643)
            ·
              refine ⟨8828661312339988161519965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5885774208226658774346643 8828661312339988161519965)
              ·
                refine ⟨3310747992127495560569987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8828661312339988161519965 3310747992127495560569987)
                ·
                  refine ⟨4966121988191243340854981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3310747992127495560569987 4966121988191243340854981)
                  ·
                    refine ⟨931147872785858126410309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4966121988191243340854981 931147872785858126410309)
                    ·
                      rfl

theorem cell23_5440212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 2, 1, 3, 1, 4].length) (baseStart_5440212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5440212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5440212 prefixEnd_5440212 := by exact prefixLift 5440212
  have htrace : WordTrace (prefixWord ++ tailWord_5440212) baseStart_5440212 baseEnd_5440212 := by
    simpa [prefixWord, tailWord_5440212, baseEnd_5440212] using wordTrace_append hprefix tailTrace_5440212
  have hstable : (prefixWord ++ tailWord_5440212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5440212).length < 2 ^ (prefixWord ++ tailWord_5440212).sum := by decide
  have hdescent : baseEnd_5440212 < baseStart_5440212 := by decide
  rcases family_descends (prefixWord ++ tailWord_5440212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5440224 : List Nat := [2, 1, 1, 3, 1, 2, 1, 2, 5, 1, 4]
def baseStart_5440224 : Nat := 118140960795 + 5440224 * 2 ^ 59
def prefixEnd_5440224 : Nat := 4983230072969 + 3 ^ 40 * 5440224 * 2
def baseEnd_5440224 : Nat := 2793449780125428332280871

theorem tailTrace_5440224 : CollatzResearch.WordTrace tailWord_5440224 prefixEnd_5440224 2793449780125428332280871 := by
  unfold tailWord_5440224
  simp only [CollatzResearch.WordTrace]
  refine ⟨99210635121502519566791863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132280846828670026089055817 99210635121502519566791863)
  ·
    refine ⟨148815952682253779350187795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99210635121502519566791863 148815952682253779350187795)
    ·
      refine ⟨223223929023380669025281693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148815952682253779350187795 223223929023380669025281693)
      ·
        refine ⟨83708973383767750884480635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 223223929023380669025281693 83708973383767750884480635)
        ·
          refine ⟨125563460075651626326720953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83708973383767750884480635 125563460075651626326720953)
          ·
            refine ⟨94172595056738719745040715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 125563460075651626326720953 94172595056738719745040715)
            ·
              refine ⟨141258892585108079617561073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 94172595056738719745040715 141258892585108079617561073)
              ·
                refine ⟨105944169438831059713170805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 141258892585108079617561073 105944169438831059713170805)
                ·
                  refine ⟨9932265884890411848109763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 105944169438831059713170805 9932265884890411848109763)
                  ·
                    refine ⟨14898398827335617772164645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9932265884890411848109763 14898398827335617772164645)
                    ·
                      refine ⟨2793449780125428332280871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14898398827335617772164645 2793449780125428332280871)
                      ·
                        rfl

theorem cell23_5440224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 2, 5, 1, 4].length) (baseStart_5440224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5440224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5440224 prefixEnd_5440224 := by exact prefixLift 5440224
  have htrace : WordTrace (prefixWord ++ tailWord_5440224) baseStart_5440224 baseEnd_5440224 := by
    simpa [prefixWord, tailWord_5440224, baseEnd_5440224] using wordTrace_append hprefix tailTrace_5440224
  have hstable : (prefixWord ++ tailWord_5440224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5440224).length < 2 ^ (prefixWord ++ tailWord_5440224).sum := by decide
  have hdescent : baseEnd_5440224 < baseStart_5440224 := by decide
  rcases family_descends (prefixWord ++ tailWord_5440224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5440228 : List Nat := [2, 3, 1, 1, 1, 5, 1, 2, 2, 3, 2]
def baseStart_5440228 : Nat := 118140960795 + 5440228 * 2 ^ 59
def prefixEnd_5440228 : Nat := 4983230072969 + 3 ^ 40 * 5440228 * 2
def baseEnd_5440228 : Nat := 2793451834048046316630853

theorem tailTrace_5440228 : CollatzResearch.WordTrace tailWord_5440228 prefixEnd_5440228 2793451834048046316630853 := by
  unfold tailWord_5440228
  simp only [CollatzResearch.WordTrace]
  refine ⟨99210708067495273908364669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132280944089993698544486225 99210708067495273908364669)
  ·
    refine ⟨37204015525310727715636751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 99210708067495273908364669 37204015525310727715636751)
    ·
      refine ⟨55806023287966091573455127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37204015525310727715636751 55806023287966091573455127)
      ·
        refine ⟨83709034931949137360182691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55806023287966091573455127 83709034931949137360182691)
        ·
          refine ⟨125563552397923706040274037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83709034931949137360182691 125563552397923706040274037)
          ·
            refine ⟨11771583037305347441275691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 125563552397923706040274037 11771583037305347441275691)
            ·
              refine ⟨17657374555958021161913537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11771583037305347441275691 17657374555958021161913537)
              ·
                refine ⟨13243030916968515871435153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17657374555958021161913537 13243030916968515871435153)
                ·
                  refine ⟨9932273187726386903576365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13243030916968515871435153 9932273187726386903576365)
                  ·
                    refine ⟨3724602445397395088841137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9932273187726386903576365 3724602445397395088841137)
                    ·
                      refine ⟨2793451834048046316630853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3724602445397395088841137 2793451834048046316630853)
                      ·
                        rfl

theorem cell23_5440228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 1, 2, 2, 3, 2].length) (baseStart_5440228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5440228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5440228 prefixEnd_5440228 := by exact prefixLift 5440228
  have htrace : WordTrace (prefixWord ++ tailWord_5440228) baseStart_5440228 baseEnd_5440228 := by
    simpa [prefixWord, tailWord_5440228, baseEnd_5440228] using wordTrace_append hprefix tailTrace_5440228
  have hstable : (prefixWord ++ tailWord_5440228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5440228).length < 2 ^ (prefixWord ++ tailWord_5440228).sum := by decide
  have hdescent : baseEnd_5440228 < baseStart_5440228 := by decide
  rcases family_descends (prefixWord ++ tailWord_5440228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5440258 : List Nat := [3, 4, 1, 1, 1, 3, 1, 1, 3, 1, 4]
def baseStart_5440258 : Nat := 118140960795 + 5440258 * 2 ^ 59
def prefixEnd_5440258 : Nat := 4983230072969 + 3 ^ 40 * 5440258 * 2
def baseEnd_5440258 : Nat := 2793467238467681199255715

theorem tailTrace_5440258 : CollatzResearch.WordTrace tailWord_5440258 prefixEnd_5440258 2793467238467681199255715 := by
  unfold tailWord_5440258
  simp only [CollatzResearch.WordTrace]
  refine ⟨49605627581220465735080357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132281673549921241960214285 49605627581220465735080357)
  ·
    refine ⟨9301055171478837325327567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 49605627581220465735080357 9301055171478837325327567)
    ·
      refine ⟨13951582757218255987991351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9301055171478837325327567 13951582757218255987991351)
      ·
        refine ⟨20927374135827383981987027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13951582757218255987991351 20927374135827383981987027)
        ·
          refine ⟨31391061203741075972980541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20927374135827383981987027 31391061203741075972980541)
          ·
            refine ⟨11771647951402903489867703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31391061203741075972980541 11771647951402903489867703)
            ·
              refine ⟨17657471927104355234801555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11771647951402903489867703 17657471927104355234801555)
              ·
                refine ⟨26486207890656532852202333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17657471927104355234801555 26486207890656532852202333)
                ·
                  refine ⟨9932327958996199819575875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26486207890656532852202333 9932327958996199819575875)
                  ·
                    refine ⟨14898491938494299729363813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9932327958996199819575875 14898491938494299729363813)
                    ·
                      refine ⟨2793467238467681199255715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14898491938494299729363813 2793467238467681199255715)
                      ·
                        rfl

theorem cell23_5440258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 1, 1, 3, 1, 4].length) (baseStart_5440258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5440258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5440258 prefixEnd_5440258 := by exact prefixLift 5440258
  have htrace : WordTrace (prefixWord ++ tailWord_5440258) baseStart_5440258 baseEnd_5440258 := by
    simpa [prefixWord, tailWord_5440258, baseEnd_5440258] using wordTrace_append hprefix tailTrace_5440258
  have hstable : (prefixWord ++ tailWord_5440258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5440258).length < 2 ^ (prefixWord ++ tailWord_5440258).sum := by decide
  have hdescent : baseEnd_5440258 < baseStart_5440258 := by decide
  rcases family_descends (prefixWord ++ tailWord_5440258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5440264 : List Nat := [2, 1, 3, 2, 2, 2, 2, 9]
def baseStart_5440264 : Nat := 118140960795 + 5440264 * 2 ^ 59
def prefixEnd_5440264 : Nat := 4983230072969 + 3 ^ 40 * 5440264 * 2
def baseEnd_5440264 : Nat := 103461863679689191695581

theorem tailTrace_5440264 : CollatzResearch.WordTrace tailWord_5440264 prefixEnd_5440264 103461863679689191695581 := by
  unfold tailWord_5440264
  simp only [CollatzResearch.WordTrace]
  refine ⟨99211364581430062982519923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132281819441906750643359897 99211364581430062982519923)
  ·
    refine ⟨148817046872145094473779885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99211364581430062982519923 148817046872145094473779885)
    ·
      refine ⟨55806392577054410427667457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 148817046872145094473779885 55806392577054410427667457)
      ·
        refine ⟨41854794432790807820750593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55806392577054410427667457 41854794432790807820750593)
        ·
          refine ⟨31391095824593105865562945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41854794432790807820750593 31391095824593105865562945)
          ·
            refine ⟨23543321868444829399172209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31391095824593105865562945 23543321868444829399172209)
            ·
              refine ⟨17657491401333622049379157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23543321868444829399172209 17657491401333622049379157)
              ·
                refine ⟨103461863679689191695581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 17657491401333622049379157 103461863679689191695581)
                ·
                  rfl

theorem cell23_5440264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 2, 9].length) (baseStart_5440264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5440264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5440264 prefixEnd_5440264 := by exact prefixLift 5440264
  have htrace : WordTrace (prefixWord ++ tailWord_5440264) baseStart_5440264 baseEnd_5440264 := by
    simpa [prefixWord, tailWord_5440264, baseEnd_5440264] using wordTrace_append hprefix tailTrace_5440264
  have hstable : (prefixWord ++ tailWord_5440264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5440264).length < 2 ^ (prefixWord ++ tailWord_5440264).sum := by decide
  have hdescent : baseEnd_5440264 < baseStart_5440264 := by decide
  rcases family_descends (prefixWord ++ tailWord_5440264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5440275 : List Nat := [1, 1, 1, 2, 1, 3, 4, 5, 1, 2, 2]
def baseStart_5440275 : Nat := 118140960795 + 5440275 * 2 ^ 59
def prefixEnd_5440275 : Nat := 4983230072969 + 3 ^ 40 * 5440275 * 2
def baseEnd_5440275 : Nat := 2793475967638807632743137

theorem tailTrace_5440275 : CollatzResearch.WordTrace tailWord_5440275 prefixEnd_5440275 2793475967638807632743137 := by
  unfold tailWord_5440275
  simp only [CollatzResearch.WordTrace]
  refine ⟨198423130365820274843690279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132282086910546849895793519 198423130365820274843690279)
  ·
    refine ⟨297634695548730412265535419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198423130365820274843690279 297634695548730412265535419)
    ·
      refine ⟨446452043323095618398303129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 297634695548730412265535419 446452043323095618398303129)
      ·
        refine ⟨334839032492321713798727347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 446452043323095618398303129 334839032492321713798727347)
        ·
          refine ⟨502258548738482570698091021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 334839032492321713798727347 502258548738482570698091021)
          ·
            refine ⟨188346955776930964011784133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 502258548738482570698091021 188346955776930964011784133)
            ·
              refine ⟨35315054208174555752209525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 188346955776930964011784133 35315054208174555752209525)
              ·
                refine ⟨3310786332016364601769643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 35315054208174555752209525 3310786332016364601769643)
                ·
                  refine ⟨4966179498024546902654465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3310786332016364601769643 4966179498024546902654465)
                  ·
                    refine ⟨3724634623518410176990849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4966179498024546902654465 3724634623518410176990849)
                    ·
                      refine ⟨2793475967638807632743137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3724634623518410176990849 2793475967638807632743137)
                      ·
                        rfl

theorem cell23_5440275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 4, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 4, 5, 1, 2, 2].length) (baseStart_5440275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5440275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5440275 prefixEnd_5440275 := by exact prefixLift 5440275
  have htrace : WordTrace (prefixWord ++ tailWord_5440275) baseStart_5440275 baseEnd_5440275 := by
    simpa [prefixWord, tailWord_5440275, baseEnd_5440275] using wordTrace_append hprefix tailTrace_5440275
  have hstable : (prefixWord ++ tailWord_5440275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5440275).length < 2 ^ (prefixWord ++ tailWord_5440275).sum := by decide
  have hdescent : baseEnd_5440275 < baseStart_5440275 := by decide
  rcases family_descends (prefixWord ++ tailWord_5440275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5440326 : List Nat := [6, 1, 1, 2, 3, 1, 2, 1, 1, 1, 4]
def baseStart_5440326 : Nat := 118140960795 + 5440326 * 2 ^ 59
def prefixEnd_5440326 : Nat := 4983230072969 + 3 ^ 40 * 5440326 * 2
def baseEnd_5440326 : Nat := 2793502155152186933205403

theorem tailTrace_5440326 : CollatzResearch.WordTrace tailWord_5440326 prefixEnd_5440326 2793502155152186933205403 := by
  unfold tailWord_5440326
  simp only [CollatzResearch.WordTrace]
  refine ⟨6200780952769859704806151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 132283326992423673702531221 6200780952769859704806151)
  ·
    refine ⟨9301171429154789557209227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6200780952769859704806151 9301171429154789557209227)
    ·
      refine ⟨13951757143732184335813841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9301171429154789557209227 13951757143732184335813841)
      ·
        refine ⟨10463817857799138251860381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13951757143732184335813841 10463817857799138251860381)
        ·
          refine ⟨3923931696674676844447643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10463817857799138251860381 3923931696674676844447643)
          ·
            refine ⟨5885897545012015266671465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3923931696674676844447643 5885897545012015266671465)
            ·
              refine ⟨4414423158759011450003599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5885897545012015266671465 4414423158759011450003599)
              ·
                refine ⟨6621634738138517175005399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4414423158759011450003599 6621634738138517175005399)
                ·
                  refine ⟨9932452107207775762508099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6621634738138517175005399 9932452107207775762508099)
                  ·
                    refine ⟨14898678160811663643762149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9932452107207775762508099 14898678160811663643762149)
                    ·
                      refine ⟨2793502155152186933205403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14898678160811663643762149 2793502155152186933205403)
                      ·
                        rfl

theorem cell23_5440326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 3, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 3, 1, 2, 1, 1, 1, 4].length) (baseStart_5440326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5440326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5440326 prefixEnd_5440326 := by exact prefixLift 5440326
  have htrace : WordTrace (prefixWord ++ tailWord_5440326) baseStart_5440326 baseEnd_5440326 := by
    simpa [prefixWord, tailWord_5440326, baseEnd_5440326] using wordTrace_append hprefix tailTrace_5440326
  have hstable : (prefixWord ++ tailWord_5440326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5440326).length < 2 ^ (prefixWord ++ tailWord_5440326).sum := by decide
  have hdescent : baseEnd_5440326 < baseStart_5440326 := by decide
  rcases family_descends (prefixWord ++ tailWord_5440326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5440381 : List Nat := [1, 4, 1, 1, 2, 1, 2, 2, 1, 5, 3]
def baseStart_5440381 : Nat := 118140960795 + 5440381 * 2 ^ 59
def prefixEnd_5440381 : Nat := 4983230072969 + 3 ^ 40 * 5440381 * 2
def baseEnd_5440381 : Nat := 2793530396588184218017649

theorem tailTrace_5440381 : CollatzResearch.WordTrace tailWord_5440381 prefixEnd_5440381 2793530396588184218017649 := by
  unfold tailWord_5440381
  simp only [CollatzResearch.WordTrace]
  refine ⟨198426996503436254947048997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132284664335624169964699331 198426996503436254947048997)
  ·
    refine ⟨37205061844394297802571687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 198426996503436254947048997 37205061844394297802571687)
    ·
      refine ⟨55807592766591446703857531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37205061844394297802571687 55807592766591446703857531)
      ·
        refine ⟨83711389149887170055786297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55807592766591446703857531 83711389149887170055786297)
        ·
          refine ⟨62783541862415377541839723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83711389149887170055786297 62783541862415377541839723)
          ·
            refine ⟨94175312793623066312759585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62783541862415377541839723 94175312793623066312759585)
            ·
              refine ⟨70631484595217299734569689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 94175312793623066312759585 70631484595217299734569689)
              ·
                refine ⟨52973613446412974800927267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 70631484595217299734569689 52973613446412974800927267)
                ·
                  refine ⟨79460420169619462201390901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52973613446412974800927267 79460420169619462201390901)
                  ·
                    refine ⟨7449414390901824581380397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 79460420169619462201390901 7449414390901824581380397)
                    ·
                      refine ⟨2793530396588184218017649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7449414390901824581380397 2793530396588184218017649)
                      ·
                        rfl

theorem cell23_5440381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 2, 1, 5, 3].length) (baseStart_5440381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5440381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5440381 prefixEnd_5440381 := by exact prefixLift 5440381
  have htrace : WordTrace (prefixWord ++ tailWord_5440381) baseStart_5440381 baseEnd_5440381 := by
    simpa [prefixWord, tailWord_5440381, baseEnd_5440381] using wordTrace_append hprefix tailTrace_5440381
  have hstable : (prefixWord ++ tailWord_5440381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5440381).length < 2 ^ (prefixWord ++ tailWord_5440381).sum := by decide
  have hdescent : baseEnd_5440381 < baseStart_5440381 := by decide
  rcases family_descends (prefixWord ++ tailWord_5440381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5440405 : List Nat := [1, 3, 2, 1, 1, 5, 3, 2, 5]
def baseStart_5440405 : Nat := 118140960795 + 5440405 * 2 ^ 59
def prefixEnd_5440405 : Nat := 4983230072969 + 3 ^ 40 * 5440405 * 2
def baseEnd_5440405 : Nat := 310393635569321347124171

theorem tailTrace_5440405 : CollatzResearch.WordTrace tailWord_5440405 prefixEnd_5440405 310393635569321347124171 := by
  unfold tailWord_5440405
  simp only [CollatzResearch.WordTrace]
  refine ⟨198427871855349307045922669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132285247903566204697281779 198427871855349307045922669)
  ·
    refine ⟨74410451945755990142221001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 198427871855349307045922669 74410451945755990142221001)
    ·
      refine ⟨55807838959316992606665751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74410451945755990142221001 55807838959316992606665751)
      ·
        refine ⟨83711758438975488909998627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55807838959316992606665751 83711758438975488909998627)
        ·
          refine ⟨125567637658463233364997941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83711758438975488909998627 125567637658463233364997941)
          ·
            refine ⟨11771966030480928127968557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 125567637658463233364997941 11771966030480928127968557)
            ·
              refine ⟨4414487261430348047988209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11771966030480928127968557 4414487261430348047988209)
              ·
                refine ⟨3310865446072761035991157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4414487261430348047988209 3310865446072761035991157)
                ·
                  refine ⟨310393635569321347124171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3310865446072761035991157 310393635569321347124171)
                  ·
                    rfl

theorem cell23_5440405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 3, 2, 5].length) (baseStart_5440405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5440405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5440405 prefixEnd_5440405 := by exact prefixLift 5440405
  have htrace : WordTrace (prefixWord ++ tailWord_5440405) baseStart_5440405 baseEnd_5440405 := by
    simpa [prefixWord, tailWord_5440405, baseEnd_5440405] using wordTrace_append hprefix tailTrace_5440405
  have hstable : (prefixWord ++ tailWord_5440405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5440405).length < 2 ^ (prefixWord ++ tailWord_5440405).sum := by decide
  have hdescent : baseEnd_5440405 < baseStart_5440405 := by decide
  rcases family_descends (prefixWord ++ tailWord_5440405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5440465 : List Nat := [1, 2, 2, 1, 2, 1, 5, 4, 1, 4]
def baseStart_5440465 : Nat := 118140960795 + 5440465 * 2 ^ 59
def prefixEnd_5440465 : Nat := 4983230072969 + 3 ^ 40 * 5440465 * 2
def baseEnd_5440465 : Nat := 931191176321053963122421

theorem tailTrace_5440465 : CollatzResearch.WordTrace tailWord_5440465 prefixEnd_5440465 931191176321053963122421 := by
  unfold tailWord_5440465
  simp only [CollatzResearch.WordTrace]
  refine ⟨198430060235131937293106849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132286706823421291528737899 198430060235131937293106849)
  ·
    refine ⟨148822545176348952969830137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 198430060235131937293106849 148822545176348952969830137)
    ·
      refine ⟨111616908882261714727372603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 148822545176348952969830137 111616908882261714727372603)
      ·
        refine ⟨167425363323392572091058905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111616908882261714727372603 167425363323392572091058905)
        ·
          refine ⟨125569022492544429068294179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 167425363323392572091058905 125569022492544429068294179)
          ·
            refine ⟨188353533738816643602441269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 125569022492544429068294179 188353533738816643602441269)
            ·
              refine ⟨17658143788014060337728869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 188353533738816643602441269 17658143788014060337728869)
              ·
                refine ⟨3310901960252636313324163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17658143788014060337728869 3310901960252636313324163)
                ·
                  refine ⟨4966352940378954469986245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3310901960252636313324163 4966352940378954469986245)
                  ·
                    refine ⟨931191176321053963122421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4966352940378954469986245 931191176321053963122421)
                    ·
                      rfl

theorem cell23_5440465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 5, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 5, 4, 1, 4].length) (baseStart_5440465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5440465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5440465 prefixEnd_5440465 := by exact prefixLift 5440465
  have htrace : WordTrace (prefixWord ++ tailWord_5440465) baseStart_5440465 baseEnd_5440465 := by
    simpa [prefixWord, tailWord_5440465, baseEnd_5440465] using wordTrace_append hprefix tailTrace_5440465
  have hstable : (prefixWord ++ tailWord_5440465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5440465).length < 2 ^ (prefixWord ++ tailWord_5440465).sum := by decide
  have hdescent : baseEnd_5440465 < baseStart_5440465 := by decide
  rcases family_descends (prefixWord ++ tailWord_5440465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5440482 : List Nat := [3, 3, 3, 1, 1, 2, 1, 2, 3, 4]
def baseStart_5440482 : Nat := 118140960795 + 5440482 * 2 ^ 59
def prefixEnd_5440482 : Nat := 4983230072969 + 3 ^ 40 * 5440482 * 2
def baseEnd_5440482 : Nat := 931194086044762774284895

theorem tailTrace_5440482 : CollatzResearch.WordTrace tailWord_5440482 prefixEnd_5440482 931194086044762774284895 := by
  unfold tailWord_5440482
  simp only [CollatzResearch.WordTrace]
  refine ⟨49607670069017587299118925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132287120184046899464317133 49607670069017587299118925)
  ·
    refine ⟨18602876275881595237169597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49607670069017587299118925 18602876275881595237169597)
    ·
      refine ⟨6976078603455598213938599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18602876275881595237169597 6976078603455598213938599)
      ·
        refine ⟨10464117905183397320907899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6976078603455598213938599 10464117905183397320907899)
        ·
          refine ⟨15696176857775095981361849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10464117905183397320907899 15696176857775095981361849)
          ·
            refine ⟨11772132643331321986021387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15696176857775095981361849 11772132643331321986021387)
            ·
              refine ⟨17658198964996982979032081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11772132643331321986021387 17658198964996982979032081)
              ·
                refine ⟨13243649223747737234274061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17658198964996982979032081 13243649223747737234274061)
                ·
                  refine ⟨4966368458905401462852773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13243649223747737234274061 4966368458905401462852773)
                  ·
                    refine ⟨931194086044762774284895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4966368458905401462852773 931194086044762774284895)
                    ·
                      rfl

theorem cell23_5440482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 1, 2, 3, 4].length) (baseStart_5440482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5440482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5440482 prefixEnd_5440482 := by exact prefixLift 5440482
  have htrace : WordTrace (prefixWord ++ tailWord_5440482) baseStart_5440482 baseEnd_5440482 := by
    simpa [prefixWord, tailWord_5440482, baseEnd_5440482] using wordTrace_append hprefix tailTrace_5440482
  have hstable : (prefixWord ++ tailWord_5440482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5440482).length < 2 ^ (prefixWord ++ tailWord_5440482).sum := by decide
  have hdescent : baseEnd_5440482 < baseStart_5440482 := by decide
  rcases family_descends (prefixWord ++ tailWord_5440482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5440521 : List Nat := [1, 2, 1, 1, 3, 1, 1, 4, 3, 6]
def baseStart_5440521 : Nat := 118140960795 + 5440521 * 2 ^ 59
def prefixEnd_5440521 : Nat := 4983230072969 + 3 ^ 40 * 5440521 * 2
def baseEnd_5440521 : Nat := 931200761293271223422335

theorem tailTrace_5440521 : CollatzResearch.WordTrace tailWord_5440521 prefixEnd_5440521 931200761293271223422335 := by
  unfold tailWord_5440521
  simp only [CollatzResearch.WordTrace]
  refine ⟨198432102722929058857145417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132288068481952705904763611 198432102722929058857145417)
  ·
    refine ⟨148824077042196794142859063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 198432102722929058857145417 148824077042196794142859063)
    ·
      refine ⟨223236115563295191214288595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148824077042196794142859063 223236115563295191214288595)
      ·
        refine ⟨334854173344942786821432893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 223236115563295191214288595 334854173344942786821432893)
        ·
          refine ⟨125570315004353545058037335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 334854173344942786821432893 125570315004353545058037335)
          ·
            refine ⟨188355472506530317587056003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 125570315004353545058037335 188355472506530317587056003)
            ·
              refine ⟨282533208759795476380584005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 188355472506530317587056003 282533208759795476380584005)
              ·
                refine ⟨52974976642461651821359501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 282533208759795476380584005 52974976642461651821359501)
                ·
                  refine ⟨19865616240923119433009813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 52974976642461651821359501 19865616240923119433009813)
                  ·
                    refine ⟨931200761293271223422335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19865616240923119433009813 931200761293271223422335)
                    ·
                      rfl

theorem cell23_5440521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 4, 3, 6].length) (baseStart_5440521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5440521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5440521 prefixEnd_5440521 := by exact prefixLift 5440521
  have htrace : WordTrace (prefixWord ++ tailWord_5440521) baseStart_5440521 baseEnd_5440521 := by
    simpa [prefixWord, tailWord_5440521, baseEnd_5440521] using wordTrace_append hprefix tailTrace_5440521
  have hstable : (prefixWord ++ tailWord_5440521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5440521).length < 2 ^ (prefixWord ++ tailWord_5440521).sum := by decide
  have hdescent : baseEnd_5440521 < baseStart_5440521 := by decide
  rcases family_descends (prefixWord ++ tailWord_5440521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5440522 : List Nat := [3, 1, 2, 2, 3, 2, 2, 1, 3, 1, 3]
def baseStart_5440522 : Nat := 118140960795 + 5440522 * 2 ^ 59
def prefixEnd_5440522 : Nat := 4983230072969 + 3 ^ 40 * 5440522 * 2
def baseEnd_5440522 : Nat := 2793602797360468166354501

theorem tailTrace_5440522 : CollatzResearch.WordTrace tailWord_5440522 prefixEnd_5440522 2793602797360468166354501 := by
  unfold tailWord_5440522
  simp only [CollatzResearch.WordTrace]
  refine ⟨49608034798981359006982955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132288092797283624018621213 49608034798981359006982955)
  ·
    refine ⟨74412052198472038510474433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49608034798981359006982955 74412052198472038510474433)
    ·
      refine ⟨55809039148854028882855825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74412052198472038510474433 55809039148854028882855825)
      ·
        refine ⟨41856779361640521662141869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55809039148854028882855825 41856779361640521662141869)
        ·
          refine ⟨15696292260615195623303201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41856779361640521662141869 15696292260615195623303201)
          ·
            refine ⟨11772219195461396717477401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15696292260615195623303201 11772219195461396717477401)
            ·
              refine ⟨8829164396596047538108051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11772219195461396717477401 8829164396596047538108051)
              ·
                refine ⟨13243746594894071307162077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8829164396596047538108051 13243746594894071307162077)
                ·
                  refine ⟨4966404973085276740185779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13243746594894071307162077 4966404973085276740185779)
                  ·
                    refine ⟨7449607459627915110278669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4966404973085276740185779 7449607459627915110278669)
                    ·
                      refine ⟨2793602797360468166354501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7449607459627915110278669 2793602797360468166354501)
                      ·
                        rfl

theorem cell23_5440522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 2, 1, 3, 1, 3].length) (baseStart_5440522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5440522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5440522 prefixEnd_5440522 := by exact prefixLift 5440522
  have htrace : WordTrace (prefixWord ++ tailWord_5440522) baseStart_5440522 baseEnd_5440522 := by
    simpa [prefixWord, tailWord_5440522, baseEnd_5440522] using wordTrace_append hprefix tailTrace_5440522
  have hstable : (prefixWord ++ tailWord_5440522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5440522).length < 2 ^ (prefixWord ++ tailWord_5440522).sum := by decide
  have hdescent : baseEnd_5440522 < baseStart_5440522 := by decide
  rcases family_descends (prefixWord ++ tailWord_5440522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5440528 : List Nat := [2, 1, 1, 1, 1, 1, 1, 3, 4, 6, 2]
def baseStart_5440528 : Nat := 118140960795 + 5440528 * 2 ^ 59
def prefixEnd_5440528 : Nat := 4983230072969 + 3 ^ 40 * 5440528 * 2
def baseEnd_5440528 : Nat := 2793605878244395142879473

theorem tailTrace_5440528 : CollatzResearch.WordTrace tailWord_5440528 prefixEnd_5440528 2793605878244395142879473 := by
  unfold tailWord_5440528
  simp only [CollatzResearch.WordTrace]
  refine ⟨99216179016951849526325119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132288238689269132701766825 99216179016951849526325119)
  ·
    refine ⟨148824268525427774289487679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99216179016951849526325119 148824268525427774289487679)
    ·
      refine ⟨223236402788141661434231519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148824268525427774289487679 223236402788141661434231519)
      ·
        refine ⟨334854604182212492151347279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 223236402788141661434231519 334854604182212492151347279)
        ·
          refine ⟨502281906273318738227020919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 334854604182212492151347279 502281906273318738227020919)
          ·
            refine ⟨753422859409978107340531379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 502281906273318738227020919 753422859409978107340531379)
            ·
              refine ⟨1130134289114967161010797069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 753422859409978107340531379 1130134289114967161010797069)
              ·
                refine ⟨423800358418112685379048901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1130134289114967161010797069 423800358418112685379048901)
                ·
                  refine ⟨79462567203396128508571669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 423800358418112685379048901 79462567203396128508571669)
                  ·
                    refine ⟨3724807837659193523839297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 79462567203396128508571669 3724807837659193523839297)
                    ·
                      refine ⟨2793605878244395142879473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3724807837659193523839297 2793605878244395142879473)
                      ·
                        rfl

theorem cell23_5440528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 3, 4, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 3, 4, 6, 2].length) (baseStart_5440528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5440528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5440528 prefixEnd_5440528 := by exact prefixLift 5440528
  have htrace : WordTrace (prefixWord ++ tailWord_5440528) baseStart_5440528 baseEnd_5440528 := by
    simpa [prefixWord, tailWord_5440528, baseEnd_5440528] using wordTrace_append hprefix tailTrace_5440528
  have hstable : (prefixWord ++ tailWord_5440528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5440528).length < 2 ^ (prefixWord ++ tailWord_5440528).sum := by decide
  have hdescent : baseEnd_5440528 < baseStart_5440528 := by decide
  rcases family_descends (prefixWord ++ tailWord_5440528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5440545 : List Nat := [1, 2, 3, 2, 3, 1, 1, 4, 1, 1, 4]
def baseStart_5440545 : Nat := 118140960795 + 5440545 * 2 ^ 59
def prefixEnd_5440545 : Nat := 4983230072969 + 3 ^ 40 * 5440545 * 2
def baseEnd_5440545 : Nat := 2793614607415521576366895

theorem tailTrace_5440545 : CollatzResearch.WordTrace tailWord_5440545 prefixEnd_5440545 2793614607415521576366895 := by
  unfold tailWord_5440545
  simp only [CollatzResearch.WordTrace]
  refine ⟨198432978074842110956019089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132288652049894740637346059 198432978074842110956019089)
  ·
    refine ⟨148824733556131583217014317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 198432978074842110956019089 148824733556131583217014317)
    ·
      refine ⟨55809275083549343706380369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 148824733556131583217014317 55809275083549343706380369)
      ·
        refine ⟨41856956312662007779785277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55809275083549343706380369 41856956312662007779785277)
        ·
          refine ⟨15696358617248252917419479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41856956312662007779785277 15696358617248252917419479)
          ·
            refine ⟨23544537925872379376129219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15696358617248252917419479 23544537925872379376129219)
            ·
              refine ⟨35316806888808569064193829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23544537925872379376129219 35316806888808569064193829)
              ·
                refine ⟨6621901291651606699536343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35316806888808569064193829 6621901291651606699536343)
                ·
                  refine ⟨9932851937477410049304515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6621901291651606699536343 9932851937477410049304515)
                  ·
                    refine ⟨14899277906216115073956773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9932851937477410049304515 14899277906216115073956773)
                    ·
                      refine ⟨2793614607415521576366895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14899277906216115073956773 2793614607415521576366895)
                      ·
                        rfl

theorem cell23_5440545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 1, 4, 1, 1, 4].length) (baseStart_5440545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5440545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5440545 prefixEnd_5440545 := by exact prefixLift 5440545
  have htrace : WordTrace (prefixWord ++ tailWord_5440545) baseStart_5440545 baseEnd_5440545 := by
    simpa [prefixWord, tailWord_5440545, baseEnd_5440545] using wordTrace_append hprefix tailTrace_5440545
  have hstable : (prefixWord ++ tailWord_5440545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5440545).length < 2 ^ (prefixWord ++ tailWord_5440545).sum := by decide
  have hdescent : baseEnd_5440545 < baseStart_5440545 := by decide
  rcases family_descends (prefixWord ++ tailWord_5440545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5440568 : List Nat := [2, 1, 2, 1, 5, 3, 9]
def baseStart_5440568 : Nat := 118140960795 + 5440568 * 2 ^ 59
def prefixEnd_5440568 : Nat := 4983230072969 + 3 ^ 40 * 5440568 * 2
def baseEnd_5440568 : Nat := 34489215030500925757769

theorem tailTrace_5440568 : CollatzResearch.WordTrace tailWord_5440568 prefixEnd_5440568 34489215030500925757769 := by
  unfold tailWord_5440568
  simp only [CollatzResearch.WordTrace]
  refine ⟨99216908476879392942053179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132289211302505857256070905 99216908476879392942053179)
  ·
    refine ⟨148825362715319089413079769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99216908476879392942053179 148825362715319089413079769)
    ·
      refine ⟨111619022036489317059809827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 148825362715319089413079769 111619022036489317059809827)
      ·
        refine ⟨167428533054733975589714741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111619022036489317059809827 167428533054733975589714741)
        ·
          refine ⟨15696424973881310211535757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 167428533054733975589714741 15696424973881310211535757)
          ·
            refine ⟨5886159365205491329325909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15696424973881310211535757 5886159365205491329325909)
            ·
              refine ⟨34489215030500925757769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5886159365205491329325909 34489215030500925757769)
              ·
                rfl

theorem cell23_5440568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 3, 9].length) (baseStart_5440568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5440568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5440568 prefixEnd_5440568 := by exact prefixLift 5440568
  have htrace : WordTrace (prefixWord ++ tailWord_5440568) baseStart_5440568 baseEnd_5440568 := by
    simpa [prefixWord, tailWord_5440568, baseEnd_5440568] using wordTrace_append hprefix tailTrace_5440568
  have hstable : (prefixWord ++ tailWord_5440568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5440568).length < 2 ^ (prefixWord ++ tailWord_5440568).sum := by decide
  have hdescent : baseEnd_5440568 < baseStart_5440568 := by decide
  rcases family_descends (prefixWord ++ tailWord_5440568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5440571 : List Nat := [1, 1, 1, 1, 1, 2, 1, 3, 4, 2, 6]
def baseStart_5440571 : Nat := 118140960795 + 5440571 * 2 ^ 59
def prefixEnd_5440571 : Nat := 4983230072969 + 3 ^ 40 * 5440571 * 2
def baseEnd_5440571 : Nat := 2793627957912538474641775

theorem tailTrace_5440571 : CollatzResearch.WordTrace tailWord_5440571 prefixEnd_5440571 2793627957912538474641775 := by
  unfold tailWord_5440571
  simp only [CollatzResearch.WordTrace]
  refine ⟨198433926372747917396465567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132289284248498611597643711 198433926372747917396465567)
  ·
    refine ⟨297650889559121876094698351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198433926372747917396465567 297650889559121876094698351)
    ·
      refine ⟨446476334338682814142047527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 297650889559121876094698351 446476334338682814142047527)
      ·
        refine ⟨669714501508024221213071291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 446476334338682814142047527 669714501508024221213071291)
        ·
          refine ⟨1004571752262036331819606937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 669714501508024221213071291 1004571752262036331819606937)
          ·
            refine ⟨753428814196527248864705203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1004571752262036331819606937 753428814196527248864705203)
            ·
              refine ⟨1130143221294790873297057805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 753428814196527248864705203 1130143221294790873297057805)
              ·
                refine ⟨423803707985546577486396677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1130143221294790873297057805 423803707985546577486396677)
                ·
                  refine ⟨79463195247289983278699377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 423803707985546577486396677 79463195247289983278699377)
                  ·
                    refine ⟨59597396435467487459024533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 79463195247289983278699377 59597396435467487459024533)
                    ·
                      refine ⟨2793627957912538474641775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 59597396435467487459024533 2793627957912538474641775)
                      ·
                        rfl

theorem cell23_5440571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 3, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 3, 4, 2, 6].length) (baseStart_5440571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5440571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5440571 prefixEnd_5440571 := by exact prefixLift 5440571
  have htrace : WordTrace (prefixWord ++ tailWord_5440571) baseStart_5440571 baseEnd_5440571 := by
    simpa [prefixWord, tailWord_5440571, baseEnd_5440571] using wordTrace_append hprefix tailTrace_5440571
  have hstable : (prefixWord ++ tailWord_5440571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5440571).length < 2 ^ (prefixWord ++ tailWord_5440571).sum := by decide
  have hdescent : baseEnd_5440571 < baseStart_5440571 := by decide
  rcases family_descends (prefixWord ++ tailWord_5440571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5440582 : List Nat := [6, 1, 1, 1, 1, 2, 2, 2, 1, 1, 5]
def baseStart_5440582 : Nat := 118140960795 + 5440582 * 2 ^ 59
def prefixEnd_5440582 : Nat := 4983230072969 + 3 ^ 40 * 5440582 * 2
def baseEnd_5440582 : Nat := 2793633606199737931604225

theorem tailTrace_5440582 : CollatzResearch.WordTrace tailWord_5440582 prefixEnd_5440582 2793633606199737931604225 := by
  unfold tailWord_5440582
  simp only [CollatzResearch.WordTrace]
  refine ⟨6201072736740877071097375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 132289551717138710850077333 6201072736740877071097375)
  ·
    refine ⟨9301609105111315606646063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6201072736740877071097375 9301609105111315606646063)
    ·
      refine ⟨13952413657666973409969095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9301609105111315606646063 13952413657666973409969095)
      ·
        refine ⟨20928620486500460114953643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13952413657666973409969095 20928620486500460114953643)
        ·
          refine ⟨31392930729750690172430465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20928620486500460114953643 31392930729750690172430465)
          ·
            refine ⟨23544698047313017629322849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31392930729750690172430465 23544698047313017629322849)
            ·
              refine ⟨17658523535484763221992137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23544698047313017629322849 17658523535484763221992137)
              ·
                refine ⟨13243892651613572416494103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17658523535484763221992137 13243892651613572416494103)
                ·
                  refine ⟨19865838977420358624741155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13243892651613572416494103 19865838977420358624741155)
                  ·
                    refine ⟨29798758466130537937111733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19865838977420358624741155 29798758466130537937111733)
                    ·
                      refine ⟨2793633606199737931604225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29798758466130537937111733 2793633606199737931604225)
                      ·
                        rfl

theorem cell23_5440582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 2, 2, 1, 1, 5].length) (baseStart_5440582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5440582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5440582 prefixEnd_5440582 := by exact prefixLift 5440582
  have htrace : WordTrace (prefixWord ++ tailWord_5440582) baseStart_5440582 baseEnd_5440582 := by
    simpa [prefixWord, tailWord_5440582, baseEnd_5440582] using wordTrace_append hprefix tailTrace_5440582
  have hstable : (prefixWord ++ tailWord_5440582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5440582).length < 2 ^ (prefixWord ++ tailWord_5440582).sum := by decide
  have hdescent : baseEnd_5440582 < baseStart_5440582 := by decide
  rcases family_descends (prefixWord ++ tailWord_5440582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5440589 : List Nat := [1, 6, 1, 1, 1, 2, 4, 1, 2, 4]
def baseStart_5440589 : Nat := 118140960795 + 5440589 * 2 ^ 59
def prefixEnd_5440589 : Nat := 4983230072969 + 3 ^ 40 * 5440589 * 2
def baseEnd_5440589 : Nat := 931212400188106468072231

theorem tailTrace_5440589 : CollatzResearch.WordTrace tailWord_5440589 prefixEnd_5440589 931212400188106468072231 := by
  unfold tailWord_5440589
  simp only [CollatzResearch.WordTrace]
  refine ⟨198434582886682706470620821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132289721924455137647080547 198434582886682706470620821)
  ·
    refine ⟨9301621072813251865810351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 198434582886682706470620821 9301621072813251865810351)
    ·
      refine ⟨13952431609219877798715527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9301621072813251865810351 13952431609219877798715527)
      ·
        refine ⟨20928647413829816698073291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13952431609219877798715527 20928647413829816698073291)
        ·
          refine ⟨31392971120744725047109937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20928647413829816698073291 31392971120744725047109937)
          ·
            refine ⟨23544728340558543785332453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31392971120744725047109937 23544728340558543785332453)
            ·
              refine ⟨4414636563854726959749835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23544728340558543785332453 4414636563854726959749835)
              ·
                refine ⟨6621954845782090439624753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4414636563854726959749835 6621954845782090439624753)
                ·
                  refine ⟨4966466134336567829718565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6621954845782090439624753 4966466134336567829718565)
                  ·
                    refine ⟨931212400188106468072231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4966466134336567829718565 931212400188106468072231)
                    ·
                      rfl

theorem cell23_5440589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 4, 1, 2, 4].length) (baseStart_5440589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5440589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5440589 prefixEnd_5440589 := by exact prefixLift 5440589
  have htrace : WordTrace (prefixWord ++ tailWord_5440589) baseStart_5440589 baseEnd_5440589 := by
    simpa [prefixWord, tailWord_5440589, baseEnd_5440589] using wordTrace_append hprefix tailTrace_5440589
  have hstable : (prefixWord ++ tailWord_5440589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5440589).length < 2 ^ (prefixWord ++ tailWord_5440589).sum := by decide
  have hdescent : baseEnd_5440589 < baseStart_5440589 := by decide
  rcases family_descends (prefixWord ++ tailWord_5440589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5440616 : List Nat := [2, 1, 4, 4, 1, 1, 3, 1, 1, 2, 3]
def baseStart_5440616 : Nat := 118140960795 + 5440616 * 2 ^ 59
def prefixEnd_5440616 : Nat := 4983230072969 + 3 ^ 40 * 5440616 * 2
def baseEnd_5440616 : Nat := 2793651064541990798579069

theorem tailTrace_5440616 : CollatzResearch.WordTrace tailWord_5440616 prefixEnd_5440616 2793651064541990798579069 := by
  unfold tailWord_5440616
  simp only [CollatzResearch.WordTrace]
  refine ⟨99217783828792445040926851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132290378438389926721235801 99217783828792445040926851)
  ·
    refine ⟨148826675743188667561390277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99217783828792445040926851 148826675743188667561390277)
    ·
      refine ⟨27905001701847875167760677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 148826675743188667561390277 27905001701847875167760677)
      ·
        refine ⟨5232187819096476593955127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27905001701847875167760677 5232187819096476593955127)
        ·
          refine ⟨7848281728644714890932691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5232187819096476593955127 7848281728644714890932691)
          ·
            refine ⟨11772422592967072336399037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7848281728644714890932691 11772422592967072336399037)
            ·
              refine ⟨4414658472362652126149639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11772422592967072336399037 4414658472362652126149639)
              ·
                refine ⟨6621987708543978189224459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4414658472362652126149639 6621987708543978189224459)
                ·
                  refine ⟨9932981562815967283836689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6621987708543978189224459 9932981562815967283836689)
                  ·
                    refine ⟨7449736172111975462877517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9932981562815967283836689 7449736172111975462877517)
                    ·
                      refine ⟨2793651064541990798579069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7449736172111975462877517 2793651064541990798579069)
                      ·
                        rfl

theorem cell23_5440616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 3, 1, 1, 2, 3].length) (baseStart_5440616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5440616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5440616 prefixEnd_5440616 := by exact prefixLift 5440616
  have htrace : WordTrace (prefixWord ++ tailWord_5440616) baseStart_5440616 baseEnd_5440616 := by
    simpa [prefixWord, tailWord_5440616, baseEnd_5440616] using wordTrace_append hprefix tailTrace_5440616
  have hstable : (prefixWord ++ tailWord_5440616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5440616).length < 2 ^ (prefixWord ++ tailWord_5440616).sum := by decide
  have hdescent : baseEnd_5440616 < baseStart_5440616 := by decide
  rcases family_descends (prefixWord ++ tailWord_5440616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5440645 : List Nat := [1, 3, 1, 1, 6, 1, 1, 1, 2, 6]
def baseStart_5440645 : Nat := 118140960795 + 5440645 * 2 ^ 59
def prefixEnd_5440645 : Nat := 4983230072969 + 3 ^ 40 * 5440645 * 2
def baseEnd_5440645 : Nat := 931221985160323728372145

theorem tailTrace_5440645 : CollatzResearch.WordTrace tailWord_5440645 prefixEnd_5440645 931221985160323728372145 := by
  unfold tailWord_5440645
  simp only [CollatzResearch.WordTrace]
  refine ⟨198436625374479828034659389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132291083582986552023106259 198436625374479828034659389)
  ·
    refine ⟨74413734515429935512997271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 198436625374479828034659389 74413734515429935512997271)
    ·
      refine ⟨111620601773144903269495907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74413734515429935512997271 111620601773144903269495907)
      ·
        refine ⟨167430902659717354904243861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111620601773144903269495907 167430902659717354904243861)
        ·
          refine ⟨7848323562174251011136431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 167430902659717354904243861 7848323562174251011136431)
          ·
            refine ⟨11772485343261376516704647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7848323562174251011136431 11772485343261376516704647)
            ·
              refine ⟨17658728014892064775056971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11772485343261376516704647 17658728014892064775056971)
              ·
                refine ⟨26488092022338097162585457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17658728014892064775056971 26488092022338097162585457)
                ·
                  refine ⟨19866069016753572871939093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26488092022338097162585457 19866069016753572871939093)
                  ·
                    refine ⟨931221985160323728372145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19866069016753572871939093 931221985160323728372145)
                    ·
                      rfl

theorem cell23_5440645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 1, 1, 2, 6].length) (baseStart_5440645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5440645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5440645 prefixEnd_5440645 := by exact prefixLift 5440645
  have htrace : WordTrace (prefixWord ++ tailWord_5440645) baseStart_5440645 baseEnd_5440645 := by
    simpa [prefixWord, tailWord_5440645, baseEnd_5440645] using wordTrace_append hprefix tailTrace_5440645
  have hstable : (prefixWord ++ tailWord_5440645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5440645).length < 2 ^ (prefixWord ++ tailWord_5440645).sum := by decide
  have hdescent : baseEnd_5440645 < baseStart_5440645 := by decide
  rcases family_descends (prefixWord ++ tailWord_5440645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5440682 : List Nat := [3, 1, 5, 1, 1, 1, 1, 2, 2, 2, 4]
def baseStart_5440682 : Nat := 118140960795 + 5440682 * 2 ^ 59
def prefixEnd_5440682 : Nat := 4983230072969 + 3 ^ 40 * 5440682 * 2
def baseEnd_5440682 : Nat := 2793684954265187540353765

theorem tailTrace_5440682 : CollatzResearch.WordTrace tailWord_5440682 prefixEnd_5440682 2793684954265187540353765 := by
  unfold tailWord_5440682
  simp only [CollatzResearch.WordTrace]
  refine ⟨49609493718836445838439075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132291983250230522235837533 49609493718836445838439075)
  ·
    refine ⟨74414240578254668757658613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49609493718836445838439075 74414240578254668757658613)
    ·
      refine ⟨6976335054211375196030495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 74414240578254668757658613 6976335054211375196030495)
      ·
        refine ⟨10464502581317062794045743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6976335054211375196030495 10464502581317062794045743)
        ·
          refine ⟨15696753871975594191068615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10464502581317062794045743 15696753871975594191068615)
          ·
            refine ⟨23545130807963391286602923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15696753871975594191068615 23545130807963391286602923)
            ·
              refine ⟨35317696211945086929904385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23545130807963391286602923 35317696211945086929904385)
              ·
                refine ⟨26488272158958815197428289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35317696211945086929904385 26488272158958815197428289)
                ·
                  refine ⟨19866204119219111398071217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26488272158958815197428289 19866204119219111398071217)
                  ·
                    refine ⟨14899653089414333548553413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19866204119219111398071217 14899653089414333548553413)
                    ·
                      refine ⟨2793684954265187540353765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14899653089414333548553413 2793684954265187540353765)
                      ·
                        rfl

theorem cell23_5440682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 1, 2, 2, 2, 4].length) (baseStart_5440682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5440682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5440682 prefixEnd_5440682 := by exact prefixLift 5440682
  have htrace : WordTrace (prefixWord ++ tailWord_5440682) baseStart_5440682 baseEnd_5440682 := by
    simpa [prefixWord, tailWord_5440682, baseEnd_5440682] using wordTrace_append hprefix tailTrace_5440682
  have hstable : (prefixWord ++ tailWord_5440682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5440682).length < 2 ^ (prefixWord ++ tailWord_5440682).sum := by decide
  have hdescent : baseEnd_5440682 < baseStart_5440682 := by decide
  rcases family_descends (prefixWord ++ tailWord_5440682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5440698 : List Nat := [3, 1, 1, 1, 2, 2, 1, 3, 1, 1, 7]
def baseStart_5440698 : Nat := 118140960795 + 5440698 * 2 ^ 59
def prefixEnd_5440698 : Nat := 4983230072969 + 3 ^ 40 * 5440698 * 2
def baseEnd_5440698 : Nat := 2793693169955659477753691

theorem tailTrace_5440698 : CollatzResearch.WordTrace tailWord_5440698 prefixEnd_5440698 2793693169955659477753691 := by
  unfold tailWord_5440698
  simp only [CollatzResearch.WordTrace]
  refine ⟨49609639610821954521584687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132292372295525212057559165 49609639610821954521584687)
  ·
    refine ⟨74414459416232931782377031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49609639610821954521584687 74414459416232931782377031)
    ·
      refine ⟨111621689124349397673565547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74414459416232931782377031 111621689124349397673565547)
      ·
        refine ⟨167432533686524096510348321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111621689124349397673565547 167432533686524096510348321)
        ·
          refine ⟨125574400264893072382761241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 167432533686524096510348321 125574400264893072382761241)
          ·
            refine ⟨94180800198669804287070931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 125574400264893072382761241 94180800198669804287070931)
            ·
              refine ⟨141271200298004706430606397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 94180800198669804287070931 141271200298004706430606397)
              ·
                refine ⟨52976700111751764911477399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 141271200298004706430606397 52976700111751764911477399)
                ·
                  refine ⟨79465050167627647367216099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52976700111751764911477399 79465050167627647367216099)
                  ·
                    refine ⟨119197575251441471050824149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 79465050167627647367216099 119197575251441471050824149)
                    ·
                      refine ⟨2793693169955659477753691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 119197575251441471050824149 2793693169955659477753691)
                      ·
                        rfl

theorem cell23_5440698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 3, 1, 1, 7].length) (baseStart_5440698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5440698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5440698 prefixEnd_5440698 := by exact prefixLift 5440698
  have htrace : WordTrace (prefixWord ++ tailWord_5440698) baseStart_5440698 baseEnd_5440698 := by
    simpa [prefixWord, tailWord_5440698, baseEnd_5440698] using wordTrace_append hprefix tailTrace_5440698
  have hstable : (prefixWord ++ tailWord_5440698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5440698).length < 2 ^ (prefixWord ++ tailWord_5440698).sum := by decide
  have hdescent : baseEnd_5440698 < baseStart_5440698 := by decide
  rcases family_descends (prefixWord ++ tailWord_5440698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5440702 : List Nat := [4, 2, 1, 1, 3, 1, 2, 1, 2, 3, 3]
def baseStart_5440702 : Nat := 118140960795 + 5440702 * 2 ^ 59
def prefixEnd_5440702 : Nat := 4983230072969 + 3 ^ 40 * 5440702 * 2
def baseEnd_5440702 : Nat := 2793695223878277462103673

theorem tailTrace_5440702 : CollatzResearch.WordTrace tailWord_5440702 prefixEnd_5440702 2793695223878277462103673 := by
  unfold tailWord_5440702
  simp only [CollatzResearch.WordTrace]
  refine ⟨24804838041909165846185545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 132292469556848884512989573 24804838041909165846185545)
  ·
    refine ⟨18603628531431874384639159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24804838041909165846185545 18603628531431874384639159)
    ·
      refine ⟨27905442797147811576958739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18603628531431874384639159 27905442797147811576958739)
      ·
        refine ⟨41858164195721717365438109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27905442797147811576958739 41858164195721717365438109)
        ·
          refine ⟨15696811573395644012039291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41858164195721717365438109 15696811573395644012039291)
          ·
            refine ⟨23545217360093466018058937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15696811573395644012039291 23545217360093466018058937)
            ·
              refine ⟨17658913020070099513544203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23545217360093466018058937 17658913020070099513544203)
              ·
                refine ⟨26488369530105149270316305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17658913020070099513544203 26488369530105149270316305)
                ·
                  refine ⟨19866277147578861952737229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26488369530105149270316305 19866277147578861952737229)
                  ·
                    refine ⟨7449853930342073232276461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19866277147578861952737229 7449853930342073232276461)
                    ·
                      refine ⟨2793695223878277462103673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7449853930342073232276461 2793695223878277462103673)
                      ·
                        rfl

theorem cell23_5440702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 2, 1, 2, 3, 3].length) (baseStart_5440702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5440702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5440702 prefixEnd_5440702 := by exact prefixLift 5440702
  have htrace : WordTrace (prefixWord ++ tailWord_5440702) baseStart_5440702 baseEnd_5440702 := by
    simpa [prefixWord, tailWord_5440702, baseEnd_5440702] using wordTrace_append hprefix tailTrace_5440702
  have hstable : (prefixWord ++ tailWord_5440702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5440702).length < 2 ^ (prefixWord ++ tailWord_5440702).sum := by decide
  have hdescent : baseEnd_5440702 < baseStart_5440702 := by decide
  rcases family_descends (prefixWord ++ tailWord_5440702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5440735 : List Nat := [1, 1, 2, 3, 2, 1, 2, 2, 5, 4]
def baseStart_5440735 : Nat := 118140960795 + 5440735 * 2 ^ 59
def prefixEnd_5440735 : Nat := 4983230072969 + 3 ^ 40 * 5440735 * 2
def baseEnd_5440735 : Nat := 931237389579958610997007

theorem tailTrace_5440735 : CollatzResearch.WordTrace tailWord_5440735 prefixEnd_5440735 931237389579958610997007 := by
  unfold tailWord_5440735
  simp only [CollatzResearch.WordTrace]
  refine ⟨198439907944153773405435659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132293271962769182270290439 198439907944153773405435659)
  ·
    refine ⟨297659861916230660108153489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198439907944153773405435659 297659861916230660108153489)
    ·
      refine ⟨223244896437172995081115117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 297659861916230660108153489 223244896437172995081115117)
      ·
        refine ⟨83716836163939873155418169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 223244896437172995081115117 83716836163939873155418169)
        ·
          refine ⟨62787627122954904866563627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83716836163939873155418169 62787627122954904866563627)
          ·
            refine ⟨94181440684432357299845441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62787627122954904866563627 94181440684432357299845441)
            ·
              refine ⟨70636080513324267974884081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 94181440684432357299845441 70636080513324267974884081)
              ·
                refine ⟨52977060384993200981163061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 70636080513324267974884081 52977060384993200981163061)
                ·
                  refine ⟨4966599411093112591984037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 52977060384993200981163061 4966599411093112591984037)
                  ·
                    refine ⟨931237389579958610997007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4966599411093112591984037 931237389579958610997007)
                    ·
                      rfl

theorem cell23_5440735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 2, 5, 4].length) (baseStart_5440735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5440735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5440735 prefixEnd_5440735 := by exact prefixLift 5440735
  have htrace : WordTrace (prefixWord ++ tailWord_5440735) baseStart_5440735 baseEnd_5440735 := by
    simpa [prefixWord, tailWord_5440735, baseEnd_5440735] using wordTrace_append hprefix tailTrace_5440735
  have hstable : (prefixWord ++ tailWord_5440735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5440735).length < 2 ^ (prefixWord ++ tailWord_5440735).sum := by decide
  have hdescent : baseEnd_5440735 < baseStart_5440735 := by decide
  rcases family_descends (prefixWord ++ tailWord_5440735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5440832 : List Nat := [2, 1, 1, 2, 2, 1, 4, 4, 1, 1, 4]
def baseStart_5440832 : Nat := 118140960795 + 5440832 * 2 ^ 59
def prefixEnd_5440832 : Nat := 4983230072969 + 3 ^ 40 * 5440832 * 2
def baseEnd_5440832 : Nat := 2793761976363361953478075

theorem tailTrace_5440832 : CollatzResearch.WordTrace tailWord_5440832 prefixEnd_5440832 2793761976363361953478075 := by
  unfold tailWord_5440832
  simp only [CollatzResearch.WordTrace]
  refine ⟨99221722912401179485858375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132295630549868239314477833 99221722912401179485858375)
  ·
    refine ⟨148832584368601769228787563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99221722912401179485858375 148832584368601769228787563)
    ·
      refine ⟨223248876552902653843181345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148832584368601769228787563 223248876552902653843181345)
      ·
        refine ⟨167436657414676990382386009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 223248876552902653843181345 167436657414676990382386009)
        ·
          refine ⟨125577493061007742786789507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 167436657414676990382386009 125577493061007742786789507)
          ·
            refine ⟨188366239591511614180184261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 125577493061007742786789507 188366239591511614180184261)
            ·
              refine ⟨35318669923408427658784549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 188366239591511614180184261 35318669923408427658784549)
              ·
                refine ⟨6622250610639080186022103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35318669923408427658784549 6622250610639080186022103)
                ·
                  refine ⟨9933375915958620279033155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6622250610639080186022103 9933375915958620279033155)
                  ·
                    refine ⟨14900063873937930418549733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9933375915958620279033155 14900063873937930418549733)
                    ·
                      refine ⟨2793761976363361953478075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14900063873937930418549733 2793761976363361953478075)
                      ·
                        rfl

theorem cell23_5440832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 4, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 4, 4, 1, 1, 4].length) (baseStart_5440832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5440832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5440832 prefixEnd_5440832 := by exact prefixLift 5440832
  have htrace : WordTrace (prefixWord ++ tailWord_5440832) baseStart_5440832 baseEnd_5440832 := by
    simpa [prefixWord, tailWord_5440832, baseEnd_5440832] using wordTrace_append hprefix tailTrace_5440832
  have hstable : (prefixWord ++ tailWord_5440832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5440832).length < 2 ^ (prefixWord ++ tailWord_5440832).sum := by decide
  have hdescent : baseEnd_5440832 < baseStart_5440832 := by decide
  rcases family_descends (prefixWord ++ tailWord_5440832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5440836 : List Nat := [2, 3, 4, 1, 1, 2, 1, 1, 1, 5, 2]
def baseStart_5440836 : Nat := 118140960795 + 5440836 * 2 ^ 59
def prefixEnd_5440836 : Nat := 4983230072969 + 3 ^ 40 * 5440836 * 2
def baseEnd_5440836 : Nat := 2793764030285979937828057

theorem tailTrace_5440836 : CollatzResearch.WordTrace tailWord_5440836 prefixEnd_5440836 2793764030285979937828057 := by
  unfold tailWord_5440836
  simp only [CollatzResearch.WordTrace]
  refine ⟨99221795858393933827431181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132295727811191911769908241 99221795858393933827431181)
  ·
    refine ⟨37208173446897725185286693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 99221795858393933827431181 37208173446897725185286693)
    ·
      refine ⟨6976532521293323472241255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 37208173446897725185286693 6976532521293323472241255)
      ·
        refine ⟨10464798781939985208361883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6976532521293323472241255 10464798781939985208361883)
        ·
          refine ⟨15697198172909977812542825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10464798781939985208361883 15697198172909977812542825)
          ·
            refine ⟨11772898629682483359407119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15697198172909977812542825 11772898629682483359407119)
            ·
              refine ⟨17659347944523725039110679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11772898629682483359407119 17659347944523725039110679)
              ·
                refine ⟨26489021916785587558666019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17659347944523725039110679 26489021916785587558666019)
                ·
                  refine ⟨39733532875178381337999029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26489021916785587558666019 39733532875178381337999029)
                  ·
                    refine ⟨3725018707047973250437409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 39733532875178381337999029 3725018707047973250437409)
                    ·
                      refine ⟨2793764030285979937828057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3725018707047973250437409 2793764030285979937828057)
                      ·
                        rfl

theorem cell23_5440836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 1, 1, 1, 5, 2].length) (baseStart_5440836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5440836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5440836 prefixEnd_5440836 := by exact prefixLift 5440836
  have htrace : WordTrace (prefixWord ++ tailWord_5440836) baseStart_5440836 baseEnd_5440836 := by
    simpa [prefixWord, tailWord_5440836, baseEnd_5440836] using wordTrace_append hprefix tailTrace_5440836
  have hstable : (prefixWord ++ tailWord_5440836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5440836).length < 2 ^ (prefixWord ++ tailWord_5440836).sum := by decide
  have hdescent : baseEnd_5440836 < baseStart_5440836 := by decide
  rcases family_descends (prefixWord ++ tailWord_5440836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5440849 : List Nat := [1, 2, 2, 1, 4, 1, 1, 2, 5, 2, 2]
def baseStart_5440849 : Nat := 118140960795 + 5440849 * 2 ^ 59
def prefixEnd_5440849 : Nat := 4983230072969 + 3 ^ 40 * 5440849 * 2
def baseEnd_5440849 : Nat := 2793770705534488386965497

theorem tailTrace_5440849 : CollatzResearch.WordTrace tailWord_5440849 prefixEnd_5440849 2793770705534488386965497 := by
  unfold tailWord_5440849
  simp only [CollatzResearch.WordTrace]
  refine ⟨198444065865740770875085601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132296043910493847250057067 198444065865740770875085601)
  ·
    refine ⟨148833049399305578156314201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 198444065865740770875085601 148833049399305578156314201)
    ·
      refine ⟨111624787049479183617235651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 148833049399305578156314201 111624787049479183617235651)
      ·
        refine ⟨167437180574218775425853477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111624787049479183617235651 167437180574218775425853477)
        ·
          refine ⟨31394471357666020392347527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 167437180574218775425853477 31394471357666020392347527)
          ·
            refine ⟨47091707036499030588521291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31394471357666020392347527 47091707036499030588521291)
            ·
              refine ⟨70637560554748545882781937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47091707036499030588521291 70637560554748545882781937)
              ·
                refine ⟨52978170416061409412086453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 70637560554748545882781937 52978170416061409412086453)
                ·
                  refine ⟨4966703476505757132383105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 52978170416061409412086453 4966703476505757132383105)
                  ·
                    refine ⟨3725027607379317849287329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4966703476505757132383105 3725027607379317849287329)
                    ·
                      refine ⟨2793770705534488386965497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3725027607379317849287329 2793770705534488386965497)
                      ·
                        rfl

theorem cell23_5440849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 2, 5, 2, 2].length) (baseStart_5440849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5440849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5440849 prefixEnd_5440849 := by exact prefixLift 5440849
  have htrace : WordTrace (prefixWord ++ tailWord_5440849) baseStart_5440849 baseEnd_5440849 := by
    simpa [prefixWord, tailWord_5440849, baseEnd_5440849] using wordTrace_append hprefix tailTrace_5440849
  have hstable : (prefixWord ++ tailWord_5440849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5440849).length < 2 ^ (prefixWord ++ tailWord_5440849).sum := by decide
  have hdescent : baseEnd_5440849 < baseStart_5440849 := by decide
  rcases family_descends (prefixWord ++ tailWord_5440849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5440852 : List Nat := [2, 4, 1, 1, 2, 1, 2, 3, 1, 1, 5]
def baseStart_5440852 : Nat := 118140960795 + 5440852 * 2 ^ 59
def prefixEnd_5440852 : Nat := 4983230072969 + 3 ^ 40 * 5440852 * 2
def baseEnd_5440852 : Nat := 2793772245976451875227983

theorem tailTrace_5440852 : CollatzResearch.WordTrace tailWord_5440852 prefixEnd_5440852 2793772245976451875227983 := by
  unfold tailWord_5440852
  simp only [CollatzResearch.WordTrace]
  refine ⟨99222087642364951193722405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132296116856486601591629873 99222087642364951193722405)
  ·
    refine ⟨18604141432943428348822951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 99222087642364951193722405 18604141432943428348822951)
    ·
      refine ⟨27906212149415142523234427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18604141432943428348822951 27906212149415142523234427)
      ·
        refine ⟨41859318224122713784851641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27906212149415142523234427 41859318224122713784851641)
        ·
          refine ⟨31394488668092035338638731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41859318224122713784851641 31394488668092035338638731)
          ·
            refine ⟨47091733002138053007958097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31394488668092035338638731 47091733002138053007958097)
            ·
              refine ⟨35318799751603539755968573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47091733002138053007958097 35318799751603539755968573)
              ·
                refine ⟨13244549906851327408488215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35318799751603539755968573 13244549906851327408488215)
                ·
                  refine ⟨19866824860276991112732323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13244549906851327408488215 19866824860276991112732323)
                  ·
                    refine ⟨29800237290415486669098485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19866824860276991112732323 29800237290415486669098485)
                    ·
                      refine ⟨2793772245976451875227983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29800237290415486669098485 2793772245976451875227983)
                      ·
                        rfl

theorem cell23_5440852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 2, 3, 1, 1, 5].length) (baseStart_5440852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5440852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5440852 prefixEnd_5440852 := by exact prefixLift 5440852
  have htrace : WordTrace (prefixWord ++ tailWord_5440852) baseStart_5440852 baseEnd_5440852 := by
    simpa [prefixWord, tailWord_5440852, baseEnd_5440852] using wordTrace_append hprefix tailTrace_5440852
  have hstable : (prefixWord ++ tailWord_5440852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5440852).length < 2 ^ (prefixWord ++ tailWord_5440852).sum := by decide
  have hdescent : baseEnd_5440852 < baseStart_5440852 := by decide
  rcases family_descends (prefixWord ++ tailWord_5440852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5440855 : List Nat := [1, 1, 3, 2, 3, 3, 10]
def baseStart_5440855 : Nat := 118140960795 + 5440855 * 2 ^ 59
def prefixEnd_5440855 : Nat := 4983230072969 + 3 ^ 40 * 5440855 * 2
def baseEnd_5440855 : Nat := 34491034400227350166549

theorem tailTrace_5440855 : CollatzResearch.WordTrace tailWord_5440855 prefixEnd_5440855 34491034400227350166549 := by
  unfold tailWord_5440855
  simp only [CollatzResearch.WordTrace]
  refine ⟨198444284703719033899804019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132296189802479355933202679 198444284703719033899804019)
  ·
    refine ⟨297666427055578550849706029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198444284703719033899804019 297666427055578550849706029)
    ·
      refine ⟨111624910145841956568639761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 297666427055578550849706029 111624910145841956568639761)
      ·
        refine ⟨83718682609381467426479821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111624910145841956568639761 83718682609381467426479821)
        ·
          refine ⟨31394505978518050284929933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 83718682609381467426479821 31394505978518050284929933)
          ·
            refine ⟨11772939741944268856848725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31394505978518050284929933 11772939741944268856848725)
            ·
              refine ⟨34491034400227350166549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 11772939741944268856848725 34491034400227350166549)
              ·
                rfl

theorem cell23_5440855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 10].length) (baseStart_5440855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5440855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5440855 prefixEnd_5440855 := by exact prefixLift 5440855
  have htrace : WordTrace (prefixWord ++ tailWord_5440855) baseStart_5440855 baseEnd_5440855 := by
    simpa [prefixWord, tailWord_5440855, baseEnd_5440855] using wordTrace_append hprefix tailTrace_5440855
  have hstable : (prefixWord ++ tailWord_5440855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5440855).length < 2 ^ (prefixWord ++ tailWord_5440855).sum := by decide
  have hdescent : baseEnd_5440855 < baseStart_5440855 := by decide
  rcases family_descends (prefixWord ++ tailWord_5440855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5440876 : List Nat := [2, 2, 1, 1, 5, 2, 3, 1, 2, 4]
def baseStart_5440876 : Nat := 118140960795 + 5440876 * 2 ^ 59
def prefixEnd_5440876 : Nat := 4983230072969 + 3 ^ 40 * 5440876 * 2
def baseEnd_5440876 : Nat := 931261523170719927109291

theorem tailTrace_5440876 : CollatzResearch.WordTrace tailWord_5440876 prefixEnd_5440876 931261523170719927109291 := by
  unfold tailWord_5440876
  simp only [CollatzResearch.WordTrace]
  refine ⟨99222525318321477243159241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132296700424428636324212321 99222525318321477243159241)
  ·
    refine ⟨74416893988741107932369431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99222525318321477243159241 74416893988741107932369431)
    ·
      refine ⟨111625340983111661898554147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74416893988741107932369431 111625340983111661898554147)
      ·
        refine ⟨167438011474667492847831221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111625340983111661898554147 167438011474667492847831221)
        ·
          refine ⟨15697313575750077454484177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 167438011474667492847831221 15697313575750077454484177)
          ·
            refine ⟨11772985181812558090863133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15697313575750077454484177 11772985181812558090863133)
            ·
              refine ⟨4414869443179709284073675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11772985181812558090863133 4414869443179709284073675)
              ·
                refine ⟨6622304164769563926110513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4414869443179709284073675 6622304164769563926110513)
                ·
                  refine ⟨4966728123577172944582885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6622304164769563926110513 4966728123577172944582885)
                  ·
                    refine ⟨931261523170719927109291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4966728123577172944582885 931261523170719927109291)
                    ·
                      rfl

theorem cell23_5440876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 2, 4].length) (baseStart_5440876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5440876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5440876 prefixEnd_5440876 := by exact prefixLift 5440876
  have htrace : WordTrace (prefixWord ++ tailWord_5440876) baseStart_5440876 baseEnd_5440876 := by
    simpa [prefixWord, tailWord_5440876, baseEnd_5440876] using wordTrace_append hprefix tailTrace_5440876
  have hstable : (prefixWord ++ tailWord_5440876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5440876).length < 2 ^ (prefixWord ++ tailWord_5440876).sum := by decide
  have hdescent : baseEnd_5440876 < baseStart_5440876 := by decide
  rcases family_descends (prefixWord ++ tailWord_5440876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5440894 : List Nat := [4, 2, 3, 2, 2, 1, 1, 3, 1, 1, 3]
def baseStart_5440894 : Nat := 118140960795 + 5440894 * 2 ^ 59
def prefixEnd_5440894 : Nat := 4983230072969 + 3 ^ 40 * 5440894 * 2
def baseEnd_5440894 : Nat := 2793793812163940710902791

theorem tailTrace_5440894 : CollatzResearch.WordTrace tailWord_5440894 prefixEnd_5440894 2793793812163940710902791 := by
  unfold tailWord_5440894
  simp only [CollatzResearch.WordTrace]
  refine ⟨24805713393822217945059217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 132297138100385162373649157 24805713393822217945059217)
  ·
    refine ⟨18604285045366663458794413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24805713393822217945059217 18604285045366663458794413)
    ·
      refine ⟨6976606892012498797047905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18604285045366663458794413 6976606892012498797047905)
      ·
        refine ⟨5232455169009374097785929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6976606892012498797047905 5232455169009374097785929)
        ·
          refine ⟨3924341376757030573339447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5232455169009374097785929 3924341376757030573339447)
          ·
            refine ⟨5886512065135545860009171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3924341376757030573339447 5886512065135545860009171)
            ·
              refine ⟨8829768097703318790013757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5886512065135545860009171 8829768097703318790013757)
              ·
                refine ⟨3311163036638744546255159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8829768097703318790013757 3311163036638744546255159)
                ·
                  refine ⟨4966744554958116819382739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3311163036638744546255159 4966744554958116819382739)
                  ·
                    refine ⟨7450116832437175229074109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4966744554958116819382739 7450116832437175229074109)
                    ·
                      refine ⟨2793793812163940710902791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7450116832437175229074109 2793793812163940710902791)
                      ·
                        rfl

theorem cell23_5440894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 2, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 2, 1, 1, 3, 1, 1, 3].length) (baseStart_5440894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5440894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5440894 prefixEnd_5440894 := by exact prefixLift 5440894
  have htrace : WordTrace (prefixWord ++ tailWord_5440894) baseStart_5440894 baseEnd_5440894 := by
    simpa [prefixWord, tailWord_5440894, baseEnd_5440894] using wordTrace_append hprefix tailTrace_5440894
  have hstable : (prefixWord ++ tailWord_5440894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5440894).length < 2 ^ (prefixWord ++ tailWord_5440894).sum := by decide
  have hdescent : baseEnd_5440894 < baseStart_5440894 := by decide
  rcases family_descends (prefixWord ++ tailWord_5440894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5440899 : List Nat := [1, 1, 1, 3, 5, 1, 1, 2, 4, 1, 3]
def baseStart_5440899 : Nat := 118140960795 + 5440899 * 2 ^ 59
def prefixEnd_5440899 : Nat := 4983230072969 + 3 ^ 40 * 5440899 * 2
def baseEnd_5440899 : Nat := 2793796379567213191340267

theorem tailTrace_5440899 : CollatzResearch.WordTrace tailWord_5440899 prefixEnd_5440899 2793796379567213191340267 := by
  unfold tailWord_5440899
  simp only [CollatzResearch.WordTrace]
  refine ⟨198445889515559629414405751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132297259677039752942937167 198445889515559629414405751)
  ·
    refine ⟨297668834273339444121608627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198445889515559629414405751 297668834273339444121608627)
    ·
      refine ⟨446503251410009166182412941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 297668834273339444121608627 446503251410009166182412941)
      ·
        refine ⟨167438719278753437318404853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 446503251410009166182412941 167438719278753437318404853)
        ·
          refine ⟨15697379932383134748600455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 167438719278753437318404853 15697379932383134748600455)
          ·
            refine ⟨23546069898574702122900683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15697379932383134748600455 23546069898574702122900683)
            ·
              refine ⟨35319104847862053184351025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23546069898574702122900683 35319104847862053184351025)
              ·
                refine ⟨26489328635896539888263269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35319104847862053184351025 26489328635896539888263269)
                ·
                  refine ⟨4966749119230601229049363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26489328635896539888263269 4966749119230601229049363)
                  ·
                    refine ⟨7450123678845901843574045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4966749119230601229049363 7450123678845901843574045)
                    ·
                      refine ⟨2793796379567213191340267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7450123678845901843574045 2793796379567213191340267)
                      ·
                        rfl

theorem cell23_5440899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 1, 2, 4, 1, 3].length) (baseStart_5440899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5440899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5440899 prefixEnd_5440899 := by exact prefixLift 5440899
  have htrace : WordTrace (prefixWord ++ tailWord_5440899) baseStart_5440899 baseEnd_5440899 := by
    simpa [prefixWord, tailWord_5440899, baseEnd_5440899] using wordTrace_append hprefix tailTrace_5440899
  have hstable : (prefixWord ++ tailWord_5440899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5440899).length < 2 ^ (prefixWord ++ tailWord_5440899).sum := by decide
  have hdescent : baseEnd_5440899 < baseStart_5440899 := by decide
  rcases family_descends (prefixWord ++ tailWord_5440899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5440900 : List Nat := [2, 3, 2, 1, 1, 5, 1, 3, 1, 2, 2]
def baseStart_5440900 : Nat := 118140960795 + 5440900 * 2 ^ 59
def prefixEnd_5440900 : Nat := 4983230072969 + 3 ^ 40 * 5440900 * 2
def baseEnd_5440900 : Nat := 2793796893047867687427763

theorem tailTrace_5440900 : CollatzResearch.WordTrace tailWord_5440900 prefixEnd_5440900 2793796893047867687427763 := by
  unfold tailWord_5440900
  simp only [CollatzResearch.WordTrace]
  refine ⟨99222962994278003292596077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132297283992370671056794769 99222962994278003292596077)
  ·
    refine ⟨37208611122854251234723529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 99222962994278003292596077 37208611122854251234723529)
    ·
      refine ⟨27906458342140688426042647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37208611122854251234723529 27906458342140688426042647)
      ·
        refine ⟨41859687513211032639063971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27906458342140688426042647 41859687513211032639063971)
        ·
          refine ⟨62789531269816548958595957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41859687513211032639063971 62789531269816548958595957)
          ·
            refine ⟨5886518556545301464868371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 62789531269816548958595957 5886518556545301464868371)
            ·
              refine ⟨8829777834817952197302557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5886518556545301464868371 8829777834817952197302557)
              ·
                refine ⟨3311166688056732073988459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8829777834817952197302557 3311166688056732073988459)
                ·
                  refine ⟨4966750032085098110982689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3311166688056732073988459 4966750032085098110982689)
                  ·
                    refine ⟨3725062524063823583237017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4966750032085098110982689 3725062524063823583237017)
                    ·
                      refine ⟨2793796893047867687427763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3725062524063823583237017 2793796893047867687427763)
                      ·
                        rfl

theorem cell23_5440900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 5, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 5, 1, 3, 1, 2, 2].length) (baseStart_5440900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5440900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5440900 prefixEnd_5440900 := by exact prefixLift 5440900
  have htrace : WordTrace (prefixWord ++ tailWord_5440900) baseStart_5440900 baseEnd_5440900 := by
    simpa [prefixWord, tailWord_5440900, baseEnd_5440900] using wordTrace_append hprefix tailTrace_5440900
  have hstable : (prefixWord ++ tailWord_5440900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5440900).length < 2 ^ (prefixWord ++ tailWord_5440900).sum := by decide
  have hdescent : baseEnd_5440900 < baseStart_5440900 := by decide
  rcases family_descends (prefixWord ++ tailWord_5440900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5440916 : List Nat := [2, 4, 2, 1, 2, 1, 2, 1, 4, 1, 3]
def baseStart_5440916 : Nat := 118140960795 + 5440916 * 2 ^ 59
def prefixEnd_5440916 : Nat := 4983230072969 + 3 ^ 40 * 5440916 * 2
def baseEnd_5440916 : Nat := 2793805108738339624827689

theorem tailTrace_5440916 : CollatzResearch.WordTrace tailWord_5440916 prefixEnd_5440916 2793805108738339624827689 := by
  unfold tailWord_5440916
  simp only [CollatzResearch.WordTrace]
  refine ⟨99223254778249020658887301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132297673037665360878516401 99223254778249020658887301)
  ·
    refine ⟨18604360270921691373541369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 99223254778249020658887301 18604360270921691373541369)
    ·
      refine ⟨13953270203191268530156027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18604360270921691373541369 13953270203191268530156027)
      ·
        refine ⟨20929905304786902795234041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13953270203191268530156027 20929905304786902795234041)
        ·
          refine ⟨15697428978590177096425531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20929905304786902795234041 15697428978590177096425531)
          ·
            refine ⟨23546143467885265644638297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15697428978590177096425531 23546143467885265644638297)
            ·
              refine ⟨17659607600913949233478723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23546143467885265644638297 17659607600913949233478723)
              ·
                refine ⟨26489411401370923850218085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17659607600913949233478723 26489411401370923850218085)
                ·
                  refine ⟨4966764637757048221915891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26489411401370923850218085 4966764637757048221915891)
                  ·
                    refine ⟨7450146956635572332873837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4966764637757048221915891 7450146956635572332873837)
                    ·
                      refine ⟨2793805108738339624827689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7450146956635572332873837 2793805108738339624827689)
                      ·
                        rfl

theorem cell23_5440916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 2, 1, 4, 1, 3].length) (baseStart_5440916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5440916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5440916 prefixEnd_5440916 := by exact prefixLift 5440916
  have htrace : WordTrace (prefixWord ++ tailWord_5440916) baseStart_5440916 baseEnd_5440916 := by
    simpa [prefixWord, tailWord_5440916, baseEnd_5440916] using wordTrace_append hprefix tailTrace_5440916
  have hstable : (prefixWord ++ tailWord_5440916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5440916).length < 2 ^ (prefixWord ++ tailWord_5440916).sum := by decide
  have hdescent : baseEnd_5440916 < baseStart_5440916 := by decide
  rcases family_descends (prefixWord ++ tailWord_5440916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5440922 : List Nat := [3, 1, 1, 4, 1, 1, 2, 1, 2, 3, 4]
def baseStart_5440922 : Nat := 118140960795 + 5440922 * 2 ^ 59
def prefixEnd_5440922 : Nat := 4983230072969 + 3 ^ 40 * 5440922 * 2
def baseEnd_5440922 : Nat := 2793808189622266601352661

theorem tailTrace_5440922 : CollatzResearch.WordTrace tailWord_5440922 prefixEnd_5440922 2793808189622266601352661 := by
  unfold tailWord_5440922
  simp only [CollatzResearch.WordTrace]
  refine ⟨49611682098619076085623255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132297818929650869561662013 49611682098619076085623255)
  ·
    refine ⟨74417523147928614128434883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49611682098619076085623255 74417523147928614128434883)
    ·
      refine ⟨111626284721892921192652325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74417523147928614128434883 111626284721892921192652325)
      ·
        refine ⟨20929928385354922723622311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 111626284721892921192652325 20929928385354922723622311)
        ·
          refine ⟨31394892578032384085433467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20929928385354922723622311 31394892578032384085433467)
          ·
            refine ⟨47092338867048576128150201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31394892578032384085433467 47092338867048576128150201)
            ·
              refine ⟨35319254150286432096112651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47092338867048576128150201 35319254150286432096112651)
              ·
                refine ⟨52978881225429648144168977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35319254150286432096112651 52978881225429648144168977)
                ·
                  refine ⟨39734160919072236108126733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 52978881225429648144168977 39734160919072236108126733)
                  ·
                    refine ⟨14900310344652088540547525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 39734160919072236108126733 14900310344652088540547525)
                    ·
                      refine ⟨2793808189622266601352661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14900310344652088540547525 2793808189622266601352661)
                      ·
                        rfl

theorem cell23_5440922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 2, 1, 2, 3, 4].length) (baseStart_5440922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5440922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5440922 prefixEnd_5440922 := by exact prefixLift 5440922
  have htrace : WordTrace (prefixWord ++ tailWord_5440922) baseStart_5440922 baseEnd_5440922 := by
    simpa [prefixWord, tailWord_5440922, baseEnd_5440922] using wordTrace_append hprefix tailTrace_5440922
  have hstable : (prefixWord ++ tailWord_5440922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5440922).length < 2 ^ (prefixWord ++ tailWord_5440922).sum := by decide
  have hdescent : baseEnd_5440922 < baseStart_5440922 := by decide
  rcases family_descends (prefixWord ++ tailWord_5440922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5440989 : List Nat := [1, 4, 3, 1, 1, 2, 1, 1, 1, 5, 3]
def baseStart_5440989 : Nat := 118140960795 + 5440989 * 2 ^ 59
def prefixEnd_5440989 : Nat := 4983230072969 + 3 ^ 40 * 5440989 * 2
def baseEnd_5440989 : Nat := 2793842592826117839214853

theorem tailTrace_5440989 : CollatzResearch.WordTrace tailWord_5440989 prefixEnd_5440989 2793842592826117839214853 := by
  unfold tailWord_5440989
  simp only [CollatzResearch.WordTrace]
  refine ⟨198449172085233574785182021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132299448056822383190121347 198449172085233574785182021)
  ·
    refine ⟨37209219765981295272221629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 198449172085233574785182021 37209219765981295272221629)
    ·
      refine ⟨13953457412242985727083111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37209219765981295272221629 13953457412242985727083111)
      ·
        refine ⟨20930186118364478590624667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13953457412242985727083111 20930186118364478590624667)
        ·
          refine ⟨31395279177546717885937001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20930186118364478590624667 31395279177546717885937001)
          ·
            refine ⟨23546459383160038414452751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31395279177546717885937001 23546459383160038414452751)
            ·
              refine ⟨35319689074740057621679127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23546459383160038414452751 35319689074740057621679127)
              ·
                refine ⟨52979533612110086432518691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35319689074740057621679127 52979533612110086432518691)
                ·
                  refine ⟨79469300418165129648778037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52979533612110086432518691 79469300418165129648778037)
                  ·
                    refine ⟨7450246914202980904572941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 79469300418165129648778037 7450246914202980904572941)
                    ·
                      refine ⟨2793842592826117839214853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7450246914202980904572941 2793842592826117839214853)
                      ·
                        rfl

theorem cell23_5440989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 1, 1, 1, 5, 3].length) (baseStart_5440989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5440989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5440989 prefixEnd_5440989 := by exact prefixLift 5440989
  have htrace : WordTrace (prefixWord ++ tailWord_5440989) baseStart_5440989 baseEnd_5440989 := by
    simpa [prefixWord, tailWord_5440989, baseEnd_5440989] using wordTrace_append hprefix tailTrace_5440989
  have hstable : (prefixWord ++ tailWord_5440989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5440989).length < 2 ^ (prefixWord ++ tailWord_5440989).sum := by decide
  have hdescent : baseEnd_5440989 < baseStart_5440989 := by decide
  rcases family_descends (prefixWord ++ tailWord_5440989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5441009 : List Nat := [1, 2, 2, 2, 3, 2, 3, 1, 2, 5]
def baseStart_5441009 : Nat := 118140960795 + 5441009 * 2 ^ 59
def prefixEnd_5441009 : Nat := 4983230072969 + 3 ^ 40 * 5441009 * 2
def baseEnd_5441009 : Nat := 931284287479735920321587

theorem tailTrace_5441009 : CollatzResearch.WordTrace tailWord_5441009 prefixEnd_5441009 931284287479735920321587 := by
  unfold tailWord_5441009
  simp only [CollatzResearch.WordTrace]
  refine ⟨198449901545161118200910081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132299934363440745467273387 198449901545161118200910081)
  ·
    refine ⟨148837426158870838650682561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 198449901545161118200910081 148837426158870838650682561)
    ·
      refine ⟨111628069619153128988011921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 148837426158870838650682561 111628069619153128988011921)
      ·
        refine ⟨83721052214364846741008941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111628069619153128988011921 83721052214364846741008941)
        ·
          refine ⟨31395394580386817527878353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 83721052214364846741008941 31395394580386817527878353)
          ·
            refine ⟨23546545935290113145908765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31395394580386817527878353 23546545935290113145908765)
            ·
              refine ⟨8829954725733792429715787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23546545935290113145908765 8829954725733792429715787)
              ·
                refine ⟨13244932088600688644573681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8829954725733792429715787 13244932088600688644573681)
                ·
                  refine ⟨9933699066450516483430261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13244932088600688644573681 9933699066450516483430261)
                  ·
                    refine ⟨931284287479735920321587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9933699066450516483430261 931284287479735920321587)
                    ·
                      rfl

theorem cell23_5441009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 3, 1, 2, 5].length) (baseStart_5441009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5441009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5441009 prefixEnd_5441009 := by exact prefixLift 5441009
  have htrace : WordTrace (prefixWord ++ tailWord_5441009) baseStart_5441009 baseEnd_5441009 := by
    simpa [prefixWord, tailWord_5441009, baseEnd_5441009] using wordTrace_append hprefix tailTrace_5441009
  have hstable : (prefixWord ++ tailWord_5441009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5441009).length < 2 ^ (prefixWord ++ tailWord_5441009).sum := by decide
  have hdescent : baseEnd_5441009 < baseStart_5441009 := by decide
  rcases family_descends (prefixWord ++ tailWord_5441009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5441013 : List Nat := [1, 3, 5, 1, 1, 2, 2, 3, 5]
def baseStart_5441013 : Nat := 118140960795 + 5441013 * 2 ^ 59
def prefixEnd_5441013 : Nat := 4983230072969 + 3 ^ 40 * 5441013 * 2
def baseEnd_5441013 : Nat := 310428324040202860590527

theorem tailTrace_5441013 : CollatzResearch.WordTrace tailWord_5441013 prefixEnd_5441013 310428324040202860590527 := by
  unfold tailWord_5441013
  simp only [CollatzResearch.WordTrace]
  refine ⟨198450047437146626884055693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132300031624764417922703795 198450047437146626884055693)
  ·
    refine ⟨74418767788929985081520885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 198450047437146626884055693 74418767788929985081520885)
    ·
      refine ⟨6976759480212186101392583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 74418767788929985081520885 6976759480212186101392583)
      ·
        refine ⟨10465139220318279152088875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6976759480212186101392583 10465139220318279152088875)
        ·
          refine ⟨15697708830477418728133313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10465139220318279152088875 15697708830477418728133313)
          ·
            refine ⟨11773281622858064046099985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15697708830477418728133313 11773281622858064046099985)
            ·
              refine ⟨8829961217143548034574989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11773281622858064046099985 8829961217143548034574989)
              ·
                refine ⟨3311235456428830512965621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8829961217143548034574989 3311235456428830512965621)
                ·
                  refine ⟨310428324040202860590527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3311235456428830512965621 310428324040202860590527)
                  ·
                    rfl

theorem cell23_5441013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 2, 3, 5].length) (baseStart_5441013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5441013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5441013 prefixEnd_5441013 := by exact prefixLift 5441013
  have htrace : WordTrace (prefixWord ++ tailWord_5441013) baseStart_5441013 baseEnd_5441013 := by
    simpa [prefixWord, tailWord_5441013, baseEnd_5441013] using wordTrace_append hprefix tailTrace_5441013
  have hstable : (prefixWord ++ tailWord_5441013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5441013).length < 2 ^ (prefixWord ++ tailWord_5441013).sum := by decide
  have hdescent : baseEnd_5441013 < baseStart_5441013 := by decide
  rcases family_descends (prefixWord ++ tailWord_5441013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5441030 : List Nat := [6, 2, 1, 1, 2, 1, 2, 1, 7]
def baseStart_5441030 : Nat := 118140960795 + 5441030 * 2 ^ 59
def prefixEnd_5441030 : Nat := 4983230072969 + 3 ^ 40 * 5441030 * 2
def baseEnd_5441030 : Nat := 310429293948105797644685

theorem tailTrace_5441030 : CollatzResearch.WordTrace tailWord_5441030 prefixEnd_5441030 310429293948105797644685 := by
  unfold tailWord_5441030
  simp only [CollatzResearch.WordTrace]
  refine ⟨6201583358690157462107017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 132300444985390025858283029 6201583358690157462107017)
  ·
    refine ⟨4651187519017618096580263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6201583358690157462107017 4651187519017618096580263)
    ·
      refine ⟨6976781278526427144870395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4651187519017618096580263 6976781278526427144870395)
      ·
        refine ⟨10465171917789640717305593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6976781278526427144870395 10465171917789640717305593)
        ·
          refine ⟨7848878938342230537979195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10465171917789640717305593 7848878938342230537979195)
          ·
            refine ⟨11773318407513345806968793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7848878938342230537979195 11773318407513345806968793)
            ·
              refine ⟨8829988805635009355226595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11773318407513345806968793 8829988805635009355226595)
              ·
                refine ⟨13244983208452514032839893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8829988805635009355226595 13244983208452514032839893)
                ·
                  refine ⟨310429293948105797644685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13244983208452514032839893 310429293948105797644685)
                  ·
                    rfl

theorem cell23_5441030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 2, 1, 7].length) (baseStart_5441030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5441030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5441030 prefixEnd_5441030 := by exact prefixLift 5441030
  have htrace : WordTrace (prefixWord ++ tailWord_5441030) baseStart_5441030 baseEnd_5441030 := by
    simpa [prefixWord, tailWord_5441030, baseEnd_5441030] using wordTrace_append hprefix tailTrace_5441030
  have hstable : (prefixWord ++ tailWord_5441030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5441030).length < 2 ^ (prefixWord ++ tailWord_5441030).sum := by decide
  have hdescent : baseEnd_5441030 < baseStart_5441030 := by decide
  rcases family_descends (prefixWord ++ tailWord_5441030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5441032 : List Nat := [2, 1, 3, 2, 1, 1, 2, 1, 2, 3, 5]
def baseStart_5441032 : Nat := 118140960795 + 5441032 * 2 ^ 59
def prefixEnd_5441032 : Nat := 4983230072969 + 3 ^ 40 * 5441032 * 2
def baseEnd_5441032 : Nat := 2793864672494261170977155

theorem tailTrace_5441032 : CollatzResearch.WordTrace tailWord_5441032 prefixEnd_5441032 2793864672494261170977155 := by
  unfold tailWord_5441032
  simp only [CollatzResearch.WordTrace]
  refine ⟨99225370212038896564498675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132300493616051862085998233 99225370212038896564498675)
  ·
    refine ⟨148838055318058344846748013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99225370212038896564498675 148838055318058344846748013)
    ·
      refine ⟨55814270744271879317530505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 148838055318058344846748013 55814270744271879317530505)
      ·
        refine ⟨41860703058203909488147879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55814270744271879317530505 41860703058203909488147879)
        ·
          refine ⟨62791054587305864232221819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41860703058203909488147879 62791054587305864232221819)
          ·
            refine ⟨94186581880958796348332729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62791054587305864232221819 94186581880958796348332729)
            ·
              refine ⟨70639936410719097261249547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 94186581880958796348332729 70639936410719097261249547)
              ·
                refine ⟨105959904616078645891874321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70639936410719097261249547 105959904616078645891874321)
                ·
                  refine ⟨79469928462058984418905741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 105959904616078645891874321 79469928462058984418905741)
                  ·
                    refine ⟨29801223173272119157089653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 79469928462058984418905741 29801223173272119157089653)
                    ·
                      refine ⟨2793864672494261170977155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29801223173272119157089653 2793864672494261170977155)
                      ·
                        rfl

theorem cell23_5441032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 1, 2, 3, 5].length) (baseStart_5441032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5441032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5441032 prefixEnd_5441032 := by exact prefixLift 5441032
  have htrace : WordTrace (prefixWord ++ tailWord_5441032) baseStart_5441032 baseEnd_5441032 := by
    simpa [prefixWord, tailWord_5441032, baseEnd_5441032] using wordTrace_append hprefix tailTrace_5441032
  have hstable : (prefixWord ++ tailWord_5441032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5441032).length < 2 ^ (prefixWord ++ tailWord_5441032).sum := by decide
  have hdescent : baseEnd_5441032 < baseStart_5441032 := by decide
  rcases family_descends (prefixWord ++ tailWord_5441032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5441056 : List Nat := [2, 1, 1, 6, 1, 1, 2, 2, 3, 4]
def baseStart_5441056 : Nat := 118140960795 + 5441056 * 2 ^ 59
def prefixEnd_5441056 : Nat := 4983230072969 + 3 ^ 40 * 5441056 * 2
def baseEnd_5441056 : Nat := 931292332009989692359015

theorem tailTrace_5441056 : CollatzResearch.WordTrace tailWord_5441056 prefixEnd_5441056 931292332009989692359015 := by
  unfold tailWord_5441056
  simp only [CollatzResearch.WordTrace]
  refine ⟨99225807887995422613935511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132301077183993896818580681 99225807887995422613935511)
  ·
    refine ⟨148838711831993133920903267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99225807887995422613935511 148838711831993133920903267)
    ·
      refine ⟨223258067747989700881354901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148838711831993133920903267 223258067747989700881354901)
      ·
        refine ⟨10465221925687017228813511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 223258067747989700881354901 10465221925687017228813511)
        ·
          refine ⟨15697832888530525843220267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10465221925687017228813511 15697832888530525843220267)
          ·
            refine ⟨23546749332795788764830401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15697832888530525843220267 23546749332795788764830401)
            ·
              refine ⟨17660061999596841573622801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23546749332795788764830401 17660061999596841573622801)
              ·
                refine ⟨13245046499697631180217101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17660061999596841573622801 13245046499697631180217101)
                ·
                  refine ⟨4966892437386611692581413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13245046499697631180217101 4966892437386611692581413)
                  ·
                    refine ⟨931292332009989692359015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4966892437386611692581413 931292332009989692359015)
                    ·
                      rfl

theorem cell23_5441056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 2, 2, 3, 4].length) (baseStart_5441056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5441056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5441056 prefixEnd_5441056 := by exact prefixLift 5441056
  have htrace : WordTrace (prefixWord ++ tailWord_5441056) baseStart_5441056 baseEnd_5441056 := by
    simpa [prefixWord, tailWord_5441056, baseEnd_5441056] using wordTrace_append hprefix tailTrace_5441056
  have hstable : (prefixWord ++ tailWord_5441056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5441056).length < 2 ^ (prefixWord ++ tailWord_5441056).sum := by decide
  have hdescent : baseEnd_5441056 < baseStart_5441056 := by decide
  rcases family_descends (prefixWord ++ tailWord_5441056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5441066 : List Nat := [3, 1, 4, 1, 1, 1, 2, 3, 2, 2, 3]
def baseStart_5441066 : Nat := 118140960795 + 5441066 * 2 ^ 59
def prefixEnd_5441066 : Nat := 4983230072969 + 3 ^ 40 * 5441066 * 2
def baseEnd_5441066 : Nat := 2793882130836514037951999

theorem tailTrace_5441066 : CollatzResearch.WordTrace tailWord_5441066 prefixEnd_5441066 2793882130836514037951999 := by
  unfold tailWord_5441066
  simp only [CollatzResearch.WordTrace]
  refine ⟨49612995126488654233933763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132301320337303077957156701 49612995126488654233933763)
  ·
    refine ⟨74419492689732981350900645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49612995126488654233933763 74419492689732981350900645)
    ·
      refine ⟨13953654879324934003293871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 74419492689732981350900645 13953654879324934003293871)
      ·
        refine ⟨20930482318987401004940807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13953654879324934003293871 20930482318987401004940807)
        ·
          refine ⟨31395723478481101507411211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20930482318987401004940807 31395723478481101507411211)
          ·
            refine ⟨47093585217721652261116817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31395723478481101507411211 47093585217721652261116817)
            ·
              refine ⟨35320188913291239195837613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47093585217721652261116817 35320188913291239195837613)
              ·
                refine ⟨13245070842484214698439105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35320188913291239195837613 13245070842484214698439105)
                ·
                  refine ⟨9933803131863161023829329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13245070842484214698439105 9933803131863161023829329)
                  ·
                    refine ⟨7450352348897370767871997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9933803131863161023829329 7450352348897370767871997)
                    ·
                      refine ⟨2793882130836514037951999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7450352348897370767871997 2793882130836514037951999)
                      ·
                        rfl

theorem cell23_5441066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 2, 3, 2, 2, 3].length) (baseStart_5441066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5441066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5441066 prefixEnd_5441066 := by exact prefixLift 5441066
  have htrace : WordTrace (prefixWord ++ tailWord_5441066) baseStart_5441066 baseEnd_5441066 := by
    simpa [prefixWord, tailWord_5441066, baseEnd_5441066] using wordTrace_append hprefix tailTrace_5441066
  have hstable : (prefixWord ++ tailWord_5441066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5441066).length < 2 ^ (prefixWord ++ tailWord_5441066).sum := by decide
  have hdescent : baseEnd_5441066 < baseStart_5441066 := by decide
  rcases family_descends (prefixWord ++ tailWord_5441066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5441116 : List Nat := [2, 2, 4, 1, 2, 2, 1, 1, 3, 5]
def baseStart_5441116 : Nat := 118140960795 + 5441116 * 2 ^ 59
def prefixEnd_5441116 : Nat := 4983230072969 + 3 ^ 40 * 5441116 * 2
def baseEnd_5441116 : Nat := 931302601623079614108923

theorem tailTrace_5441116 : CollatzResearch.WordTrace tailWord_5441116 prefixEnd_5441116 931302601623079614108923 := by
  unfold tailWord_5441116
  simp only [CollatzResearch.WordTrace]
  refine ⟨99226902077886737737527601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132302536103848983650036801 99226902077886737737527601)
  ·
    refine ⟨74420176558415053303145701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99226902077886737737527601 74420176558415053303145701)
    ·
      refine ⟨13953783104702822494339819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 74420176558415053303145701 13953783104702822494339819)
      ·
        refine ⟨20930674657054233741509729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13953783104702822494339819 20930674657054233741509729)
        ·
          refine ⟨15698005992790675306132297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20930674657054233741509729 15698005992790675306132297)
          ·
            refine ⟨11773504494593006479599223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15698005992790675306132297 11773504494593006479599223)
            ·
              refine ⟨17660256741889509719398835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11773504494593006479599223 17660256741889509719398835)
              ·
                refine ⟨26490385112834264579098253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17660256741889509719398835 26490385112834264579098253)
                ·
                  refine ⟨9933894417312849217161845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26490385112834264579098253 9933894417312849217161845)
                  ·
                    refine ⟨931302601623079614108923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9933894417312849217161845 931302601623079614108923)
                    ·
                      rfl

theorem cell23_5441116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 1, 1, 3, 5].length) (baseStart_5441116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5441116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5441116 prefixEnd_5441116 := by exact prefixLift 5441116
  have htrace : WordTrace (prefixWord ++ tailWord_5441116) baseStart_5441116 baseEnd_5441116 := by
    simpa [prefixWord, tailWord_5441116, baseEnd_5441116] using wordTrace_append hprefix tailTrace_5441116
  have hstable : (prefixWord ++ tailWord_5441116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5441116).length < 2 ^ (prefixWord ++ tailWord_5441116).sum := by decide
  have hdescent : baseEnd_5441116 < baseStart_5441116 := by decide
  rcases family_descends (prefixWord ++ tailWord_5441116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5441123 : List Nat := [1, 1, 1, 5, 1, 4, 2, 1, 2, 3, 2]
def baseStart_5441123 : Nat := 118140960795 + 5441123 * 2 ^ 59
def prefixEnd_5441123 : Nat := 4983230072969 + 3 ^ 40 * 5441123 * 2
def baseEnd_5441123 : Nat := 2793911399233820314939237

theorem tailTrace_5441123 : CollatzResearch.WordTrace tailWord_5441123 prefixEnd_5441123 2793911399233820314939237 := by
  unfold tailWord_5441123
  simp only [CollatzResearch.WordTrace]
  refine ⟨198454059466748115670560023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132302706311165410447040015 198454059466748115670560023)
  ·
    refine ⟨297681089200122173505840035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198454059466748115670560023 297681089200122173505840035)
    ·
      refine ⟨446521633800183260258760053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 297681089200122173505840035 446521633800183260258760053)
      ·
        refine ⟨41861403168767180649258755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 446521633800183260258760053 41861403168767180649258755)
        ·
          refine ⟨62792104753150770973888133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41861403168767180649258755 62792104753150770973888133)
          ·
            refine ⟨11773519641215769557604025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 62792104753150770973888133 11773519641215769557604025)
            ·
              refine ⟨8830139730911827168203019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11773519641215769557604025 8830139730911827168203019)
              ·
                refine ⟨13245209596367740752304529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8830139730911827168203019 13245209596367740752304529)
                ·
                  refine ⟨9933907197275805564228397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13245209596367740752304529 9933907197275805564228397)
                  ·
                    refine ⟨3725215198978427086585649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9933907197275805564228397 3725215198978427086585649)
                    ·
                      refine ⟨2793911399233820314939237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3725215198978427086585649 2793911399233820314939237)
                      ·
                        rfl

theorem cell23_5441123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 2, 1, 2, 3, 2].length) (baseStart_5441123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5441123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5441123 prefixEnd_5441123 := by exact prefixLift 5441123
  have htrace : WordTrace (prefixWord ++ tailWord_5441123) baseStart_5441123 baseEnd_5441123 := by
    simpa [prefixWord, tailWord_5441123, baseEnd_5441123] using wordTrace_append hprefix tailTrace_5441123
  have hstable : (prefixWord ++ tailWord_5441123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5441123).length < 2 ^ (prefixWord ++ tailWord_5441123).sum := by decide
  have hdescent : baseEnd_5441123 < baseStart_5441123 := by decide
  rcases family_descends (prefixWord ++ tailWord_5441123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5441129 : List Nat := [1, 2, 1, 1, 1, 4, 2, 1, 6, 4]
def baseStart_5441129 : Nat := 118140960795 + 5441129 * 2 ^ 59
def prefixEnd_5441129 : Nat := 4983230072969 + 3 ^ 40 * 5441129 * 2
def baseEnd_5441129 : Nat := 931304826705915763821403

theorem tailTrace_5441129 : CollatzResearch.WordTrace tailWord_5441129 prefixEnd_5441129 931304826705915763821403 := by
  unfold tailWord_5441129
  simp only [CollatzResearch.WordTrace]
  refine ⟨198454278304726378695278441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132302852203150919130185627 198454278304726378695278441)
  ·
    refine ⟨148840708728544784021458831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 198454278304726378695278441 148840708728544784021458831)
    ·
      refine ⟨223261063092817176032188247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148840708728544784021458831 223261063092817176032188247)
      ·
        refine ⟨334891594639225764048282371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 223261063092817176032188247 334891594639225764048282371)
        ·
          refine ⟨502337391958838646072423557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 334891594639225764048282371 502337391958838646072423557)
          ·
            refine ⟨94188260992282246138579417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 502337391958838646072423557 94188260992282246138579417)
            ·
              refine ⟨70641195744211684603934563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 94188260992282246138579417 70641195744211684603934563)
              ·
                refine ⟨105961793616317526905901845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70641195744211684603934563 105961793616317526905901845)
                ·
                  refine ⟨4966959075764884073714149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 105961793616317526905901845 4966959075764884073714149)
                  ·
                    refine ⟨931304826705915763821403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4966959075764884073714149 931304826705915763821403)
                    ·
                      rfl

theorem cell23_5441129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 1, 6, 4].length) (baseStart_5441129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5441129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5441129 prefixEnd_5441129 := by exact prefixLift 5441129
  have htrace : WordTrace (prefixWord ++ tailWord_5441129) baseStart_5441129 baseEnd_5441129 := by
    simpa [prefixWord, tailWord_5441129, baseEnd_5441129] using wordTrace_append hprefix tailTrace_5441129
  have hstable : (prefixWord ++ tailWord_5441129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5441129).length < 2 ^ (prefixWord ++ tailWord_5441129).sum := by decide
  have hdescent : baseEnd_5441129 < baseStart_5441129 := by decide
  rcases family_descends (prefixWord ++ tailWord_5441129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5441159 : List Nat := [1, 1, 4, 2, 1, 3, 3, 8]
def baseStart_5441159 : Nat := 118140960795 + 5441159 * 2 ^ 59
def prefixEnd_5441159 : Nat := 4983230072969 + 3 ^ 40 * 5441159 * 2
def baseEnd_5441159 : Nat := 103478884612495636077373

theorem tailTrace_5441159 : CollatzResearch.WordTrace tailWord_5441159 prefixEnd_5441159 103478884612495636077373 := by
  unfold tailWord_5441159
  simp only [CollatzResearch.WordTrace]
  refine ⟨198455372494617693818870531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132303581663078462545913687 198455372494617693818870531)
  ·
    refine ⟨297683058741926540728305797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198455372494617693818870531 297683058741926540728305797)
    ·
      refine ⟨55815573514111226386557337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 297683058741926540728305797 55815573514111226386557337)
      ·
        refine ⟨41861680135583419789918003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55815573514111226386557337 41861680135583419789918003)
        ·
          refine ⟨62792520203375129684877005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41861680135583419789918003 62792520203375129684877005)
          ·
            refine ⟨23547195076265673631828877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62792520203375129684877005 23547195076265673631828877)
            ·
              refine ⟨8830198153599627611935829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23547195076265673631828877 8830198153599627611935829)
              ·
                refine ⟨103478884612495636077373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8830198153599627611935829 103478884612495636077373)
                ·
                  rfl

theorem cell23_5441159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 3, 8].length) (baseStart_5441159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5441159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5441159 prefixEnd_5441159 := by exact prefixLift 5441159
  have htrace : WordTrace (prefixWord ++ tailWord_5441159) baseStart_5441159 baseEnd_5441159 := by
    simpa [prefixWord, tailWord_5441159, baseEnd_5441159] using wordTrace_append hprefix tailTrace_5441159
  have hstable : (prefixWord ++ tailWord_5441159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5441159).length < 2 ^ (prefixWord ++ tailWord_5441159).sum := by decide
  have hdescent : baseEnd_5441159 < baseStart_5441159 := by decide
  rcases family_descends (prefixWord ++ tailWord_5441159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5441166 : List Nat := [4, 1, 1, 3, 1, 2, 1, 3, 1, 2, 4]
def baseStart_5441166 : Nat := 118140960795 + 5441166 * 2 ^ 59
def prefixEnd_5441166 : Nat := 4983230072969 + 3 ^ 40 * 5441166 * 2
def baseEnd_5441166 : Nat := 2793933478901963646701539

theorem tailTrace_5441166 : CollatzResearch.WordTrace tailWord_5441166 prefixEnd_5441166 2793933478901963646701539 := by
  unfold tailWord_5441166
  simp only [CollatzResearch.WordTrace]
  refine ⟨24806953475699041751796919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 132303751870394889342916901 24806953475699041751796919)
  ·
    refine ⟨37210430213548562627695379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24806953475699041751796919 37210430213548562627695379)
    ·
      refine ⟨55815645320322843941543069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37210430213548562627695379 55815645320322843941543069)
      ·
        refine ⟨20930866995121066478078651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55815645320322843941543069 20930866995121066478078651)
        ·
          refine ⟨31396300492681599717117977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20930866995121066478078651 31396300492681599717117977)
          ·
            refine ⟨23547225369511199787838483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31396300492681599717117977 23547225369511199787838483)
            ·
              refine ⟨35320838054266799681757725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23547225369511199787838483 35320838054266799681757725)
              ·
                refine ⟨13245314270350049880659147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35320838054266799681757725 13245314270350049880659147)
                ·
                  refine ⟨19867971405525074820988721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13245314270350049880659147 19867971405525074820988721)
                  ·
                    refine ⟨14900978554143806115741541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19867971405525074820988721 14900978554143806115741541)
                    ·
                      refine ⟨2793933478901963646701539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14900978554143806115741541 2793933478901963646701539)
                      ·
                        rfl

theorem cell23_5441166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 1, 3, 1, 2, 4].length) (baseStart_5441166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5441166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5441166 prefixEnd_5441166 := by exact prefixLift 5441166
  have htrace : WordTrace (prefixWord ++ tailWord_5441166) baseStart_5441166 baseEnd_5441166 := by
    simpa [prefixWord, tailWord_5441166, baseEnd_5441166] using wordTrace_append hprefix tailTrace_5441166
  have hstable : (prefixWord ++ tailWord_5441166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5441166).length < 2 ^ (prefixWord ++ tailWord_5441166).sum := by decide
  have hdescent : baseEnd_5441166 < baseStart_5441166 := by decide
  rcases family_descends (prefixWord ++ tailWord_5441166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5441176 : List Nat := [2, 1, 2, 4, 1, 3, 3, 7]
def baseStart_5441176 : Nat := 118140960795 + 5441176 * 2 ^ 59
def prefixEnd_5441176 : Nat := 4983230072969 + 3 ^ 40 * 5441176 * 2
def baseEnd_5441176 : Nat := 103479207915129948428759

theorem tailTrace_5441176 : CollatzResearch.WordTrace tailWord_5441176 prefixEnd_5441176 103479207915129948428759 := by
  unfold tailWord_5441176
  simp only [CollatzResearch.WordTrace]
  refine ⟨99227996267778052861119691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132303995023704070481492921 99227996267778052861119691)
  ·
    refine ⟨148841994401667079291679537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99227996267778052861119691 148841994401667079291679537)
    ·
      refine ⟨111631495801250309468759653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 148841994401667079291679537 111631495801250309468759653)
      ·
        refine ⟨20930905462734433025392435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 111631495801250309468759653 20930905462734433025392435)
        ·
          refine ⟨31396358194101649538088653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20930905462734433025392435 31396358194101649538088653)
          ·
            refine ⟨11773634322788118576783245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31396358194101649538088653 11773634322788118576783245)
            ·
              refine ⟨4415112871045544466293717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11773634322788118576783245 4415112871045544466293717)
              ·
                refine ⟨103479207915129948428759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4415112871045544466293717 103479207915129948428759)
                ·
                  rfl

theorem cell23_5441176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 3, 7].length) (baseStart_5441176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5441176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5441176 prefixEnd_5441176 := by exact prefixLift 5441176
  have htrace : WordTrace (prefixWord ++ tailWord_5441176) baseStart_5441176 baseEnd_5441176 := by
    simpa [prefixWord, tailWord_5441176, baseEnd_5441176] using wordTrace_append hprefix tailTrace_5441176
  have hstable : (prefixWord ++ tailWord_5441176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5441176).length < 2 ^ (prefixWord ++ tailWord_5441176).sum := by decide
  have hdescent : baseEnd_5441176 < baseStart_5441176 := by decide
  rcases family_descends (prefixWord ++ tailWord_5441176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5441209 : List Nat := [1, 2, 1, 4, 1, 1, 2, 1, 1, 5, 4]
def baseStart_5441209 : Nat := 118140960795 + 5441209 * 2 ^ 59
def prefixEnd_5441209 : Nat := 4983230072969 + 3 ^ 40 * 5441209 * 2
def baseEnd_5441209 : Nat := 2793955558570106978463841

theorem tailTrace_5441209 : CollatzResearch.WordTrace tailWord_5441209 prefixEnd_5441209 2793955558570106978463841 := by
  unfold tailWord_5441209
  simp only [CollatzResearch.WordTrace]
  refine ⟨198457196144436552358190681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132304797429624368238793787 198457196144436552358190681)
  ·
    refine ⟨148842897108327414268643011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 198457196144436552358190681 148842897108327414268643011)
    ·
      refine ⟨223264345662491121402964517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148842897108327414268643011 223264345662491121402964517)
      ·
        refine ⟨41862064811717085263055847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 223264345662491121402964517 41862064811717085263055847)
        ·
          refine ⟨62793097217575627894583771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41862064811717085263055847 62793097217575627894583771)
          ·
            refine ⟨94189645826363441841875657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62793097217575627894583771 94189645826363441841875657)
            ·
              refine ⟨70642234369772581381406743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 94189645826363441841875657 70642234369772581381406743)
              ·
                refine ⟨105963351554658872072110115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70642234369772581381406743 105963351554658872072110115)
                ·
                  refine ⟨158945027331988308108165173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 105963351554658872072110115 158945027331988308108165173)
                  ·
                    refine ⟨14901096312373903885140485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 158945027331988308108165173 14901096312373903885140485)
                    ·
                      refine ⟨2793955558570106978463841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14901096312373903885140485 2793955558570106978463841)
                      ·
                        rfl

theorem cell23_5441209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 1, 1, 5, 4].length) (baseStart_5441209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5441209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5441209 prefixEnd_5441209 := by exact prefixLift 5441209
  have htrace : WordTrace (prefixWord ++ tailWord_5441209) baseStart_5441209 baseEnd_5441209 := by
    simpa [prefixWord, tailWord_5441209, baseEnd_5441209] using wordTrace_append hprefix tailTrace_5441209
  have hstable : (prefixWord ++ tailWord_5441209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5441209).length < 2 ^ (prefixWord ++ tailWord_5441209).sum := by decide
  have hdescent : baseEnd_5441209 < baseStart_5441209 := by decide
  rcases family_descends (prefixWord ++ tailWord_5441209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5441230 : List Nat := [4, 1, 1, 1, 3, 1, 4, 2, 1, 3, 2]
def baseStart_5441230 : Nat := 118140960795 + 5441230 * 2 ^ 59
def prefixEnd_5441230 : Nat := 4983230072969 + 3 ^ 40 * 5441230 * 2
def baseEnd_5441230 : Nat := 2793966341663851396301245

theorem tailTrace_5441230 : CollatzResearch.WordTrace tailWord_5441230 prefixEnd_5441230 2793966341663851396301245 := by
  unfold tailWord_5441230
  simp only [CollatzResearch.WordTrace]
  refine ⟨24807245259670059118088143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 132305308051573648629803429 24807245259670059118088143)
  ·
    refine ⟨37210867889505088677132215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24807245259670059118088143 37210867889505088677132215)
    ·
      refine ⟨55816301834257633015698323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37210867889505088677132215 55816301834257633015698323)
      ·
        refine ⟨83724452751386449523547485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55816301834257633015698323 83724452751386449523547485)
        ·
          refine ⟨31396669781769918571330307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 83724452751386449523547485 31396669781769918571330307)
          ·
            refine ⟨47095004672654877856995461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31396669781769918571330307 47095004672654877856995461)
            ·
              refine ⟨8830313376122789598186649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 47095004672654877856995461 8830313376122789598186649)
              ·
                refine ⟨6622735032092092198639987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8830313376122789598186649 6622735032092092198639987)
                ·
                  refine ⟨9934102548138138297959981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6622735032092092198639987 9934102548138138297959981)
                  ·
                    refine ⟨3725288455551801861734993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9934102548138138297959981 3725288455551801861734993)
                    ·
                      refine ⟨2793966341663851396301245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3725288455551801861734993 2793966341663851396301245)
                      ·
                        rfl

theorem cell23_5441230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 4, 2, 1, 3, 2].length) (baseStart_5441230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5441230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5441230 prefixEnd_5441230 := by exact prefixLift 5441230
  have htrace : WordTrace (prefixWord ++ tailWord_5441230) baseStart_5441230 baseEnd_5441230 := by
    simpa [prefixWord, tailWord_5441230, baseEnd_5441230] using wordTrace_append hprefix tailTrace_5441230
  have hstable : (prefixWord ++ tailWord_5441230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5441230).length < 2 ^ (prefixWord ++ tailWord_5441230).sum := by decide
  have hdescent : baseEnd_5441230 < baseStart_5441230 := by decide
  rcases family_descends (prefixWord ++ tailWord_5441230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5441238 : List Nat := [5, 2, 1, 3, 1, 2, 1, 3, 1, 2, 2]
def baseStart_5441238 : Nat := 118140960795 + 5441238 * 2 ^ 59
def prefixEnd_5441238 : Nat := 4983230072969 + 3 ^ 40 * 5441238 * 2
def baseEnd_5441238 : Nat := 2793970449509087365001209

theorem tailTrace_5441238 : CollatzResearch.WordTrace tailWord_5441238 prefixEnd_5441238 2793970449509087365001209 := by
  unfold tailWord_5441238
  simp only [CollatzResearch.WordTrace]
  refine ⟨12403640866333218144437273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 132305502574220993540664245 12403640866333218144437273)
  ·
    refine ⟨9302730649749913608327955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12403640866333218144437273 9302730649749913608327955)
    ·
      refine ⟨13954095974624870412491933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9302730649749913608327955 13954095974624870412491933)
      ·
        refine ⟨5232785990484326404684475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13954095974624870412491933 5232785990484326404684475)
        ·
          refine ⟨7849178985726489607026713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5232785990484326404684475 7849178985726489607026713)
          ·
            refine ⟨5886884239294867205270035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7849178985726489607026713 5886884239294867205270035)
            ·
              refine ⟨8830326358942300807905053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5886884239294867205270035 8830326358942300807905053)
              ·
                refine ⟨3311372384603362802964395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8830326358942300807905053 3311372384603362802964395)
                ·
                  refine ⟨4967058576905044204446593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3311372384603362802964395 4967058576905044204446593)
                  ·
                    refine ⟨3725293932678783153334945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4967058576905044204446593 3725293932678783153334945)
                    ·
                      refine ⟨2793970449509087365001209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3725293932678783153334945 2793970449509087365001209)
                      ·
                        rfl

theorem cell23_5441238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 2, 1, 3, 1, 2, 2].length) (baseStart_5441238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5441238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5441238 prefixEnd_5441238 := by exact prefixLift 5441238
  have htrace : WordTrace (prefixWord ++ tailWord_5441238) baseStart_5441238 baseEnd_5441238 := by
    simpa [prefixWord, tailWord_5441238, baseEnd_5441238] using wordTrace_append hprefix tailTrace_5441238
  have hstable : (prefixWord ++ tailWord_5441238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5441238).length < 2 ^ (prefixWord ++ tailWord_5441238).sum := by decide
  have hdescent : baseEnd_5441238 < baseStart_5441238 := by decide
  rcases family_descends (prefixWord ++ tailWord_5441238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5441276 : List Nat := [2, 2, 2, 1, 3, 1, 2, 1, 1, 5, 3]
def baseStart_5441276 : Nat := 118140960795 + 5441276 * 2 ^ 59
def prefixEnd_5441276 : Nat := 4983230072969 + 3 ^ 40 * 5441276 * 2
def baseEnd_5441276 : Nat := 2793989961773958216326033

theorem tailTrace_5441276 : CollatzResearch.WordTrace tailWord_5441276 prefixEnd_5441276 2793989961773958216326033 := by
  unfold tailWord_5441276
  simp only [CollatzResearch.WordTrace]
  refine ⟨99229819917596911400439841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132306426556795881867253121 99229819917596911400439841)
  ·
    refine ⟨74422364938197683550329881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99229819917596911400439841 74422364938197683550329881)
    ·
      refine ⟨55816773703648262662747411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74422364938197683550329881 55816773703648262662747411)
      ·
        refine ⟨83725160555472393994121117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55816773703648262662747411 83725160555472393994121117)
        ·
          refine ⟨31396935208302147747795419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 83725160555472393994121117 31396935208302147747795419)
          ·
            refine ⟨47095402812453221621693129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31396935208302147747795419 47095402812453221621693129)
            ·
              refine ⟨35321552109339916216269847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47095402812453221621693129 35321552109339916216269847)
              ·
                refine ⟨52982328164009874324404771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35321552109339916216269847 52982328164009874324404771)
                ·
                  refine ⟨79473492246014811486607157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52982328164009874324404771 79473492246014811486607157)
                  ·
                    refine ⟨7450639898063888576869421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 79473492246014811486607157 7450639898063888576869421)
                    ·
                      refine ⟨2793989961773958216326033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7450639898063888576869421 2793989961773958216326033)
                      ·
                        rfl

theorem cell23_5441276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 2, 1, 1, 5, 3].length) (baseStart_5441276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5441276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5441276 prefixEnd_5441276 := by exact prefixLift 5441276
  have htrace : WordTrace (prefixWord ++ tailWord_5441276) baseStart_5441276 baseEnd_5441276 := by
    simpa [prefixWord, tailWord_5441276, baseEnd_5441276] using wordTrace_append hprefix tailTrace_5441276
  have hstable : (prefixWord ++ tailWord_5441276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5441276).length < 2 ^ (prefixWord ++ tailWord_5441276).sum := by decide
  have hdescent : baseEnd_5441276 < baseStart_5441276 := by decide
  rcases family_descends (prefixWord ++ tailWord_5441276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5441279 : List Nat := [1, 1, 2, 2, 1, 3, 2, 1, 3, 7]
def baseStart_5441279 : Nat := 118140960795 + 5441279 * 2 ^ 59
def prefixEnd_5441279 : Nat := 4983230072969 + 3 ^ 40 * 5441279 * 2
def baseEnd_5441279 : Nat := 931330500738640568196173

theorem tailTrace_5441279 : CollatzResearch.WordTrace tailWord_5441279 prefixEnd_5441279 931330500738640568196173 := by
  unfold tailWord_5441279
  simp only [CollatzResearch.WordTrace]
  refine ⟨198459749254182954313238891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132306499502788636208825927 198459749254182954313238891)
  ·
    refine ⟨297689623881274431469858337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198459749254182954313238891 297689623881274431469858337)
    ·
      refine ⟨223267217910955823602393753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 297689623881274431469858337 223267217910955823602393753)
      ·
        refine ⟨167450413433216867701795315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 223267217910955823602393753 167450413433216867701795315)
        ·
          refine ⟨251175620149825301552692973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 167450413433216867701795315 251175620149825301552692973)
          ·
            refine ⟨94190857556184488082259865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 251175620149825301552692973 94190857556184488082259865)
            ·
              refine ⟨70643143167138366061694899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 94190857556184488082259865 70643143167138366061694899)
              ·
                refine ⟨105964714750707549092542349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70643143167138366061694899 105964714750707549092542349)
                ·
                  refine ⟨39736768031515330909703381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 105964714750707549092542349 39736768031515330909703381)
                  ·
                    refine ⟨931330500738640568196173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 39736768031515330909703381 931330500738640568196173)
                    ·
                      rfl

theorem cell23_5441279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 1, 3, 7].length) (baseStart_5441279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5441279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5441279 prefixEnd_5441279 := by exact prefixLift 5441279
  have htrace : WordTrace (prefixWord ++ tailWord_5441279) baseStart_5441279 baseEnd_5441279 := by
    simpa [prefixWord, tailWord_5441279, baseEnd_5441279] using wordTrace_append hprefix tailTrace_5441279
  have hstable : (prefixWord ++ tailWord_5441279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5441279).length < 2 ^ (prefixWord ++ tailWord_5441279).sum := by decide
  have hdescent : baseEnd_5441279 < baseStart_5441279 := by decide
  rcases family_descends (prefixWord ++ tailWord_5441279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5441289 : List Nat := [1, 2, 1, 1, 3, 2, 1, 1, 3, 1, 7]
def baseStart_5441289 : Nat := 118140960795 + 5441289 * 2 ^ 59
def prefixEnd_5441289 : Nat := 4983230072969 + 3 ^ 40 * 5441289 * 2
def baseEnd_5441289 : Nat := 2793996637022466665463473

theorem tailTrace_5441289 : CollatzResearch.WordTrace tailWord_5441289 prefixEnd_5441289 2793996637022466665463473 := by
  unfold tailWord_5441289
  simp only [CollatzResearch.WordTrace]
  refine ⟨198460113984146726021102921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132306742656097817347401947 198460113984146726021102921)
  ·
    refine ⟨148845085488110044515827191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 198460113984146726021102921 148845085488110044515827191)
    ·
      refine ⟨223267628232165066773740787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148845085488110044515827191 223267628232165066773740787)
      ·
        refine ⟨334901442348247600160611181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 223267628232165066773740787 334901442348247600160611181)
        ·
          refine ⟨125588040880592850060229193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 334901442348247600160611181 125588040880592850060229193)
          ·
            refine ⟨94191030660444637545171895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 125588040880592850060229193 94191030660444637545171895)
            ·
              refine ⟨141286545990666956317757843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 94191030660444637545171895 141286545990666956317757843)
              ·
                refine ⟨211929818986000434476636765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 141286545990666956317757843 211929818986000434476636765)
                ·
                  refine ⟨79473682119750162928738787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 211929818986000434476636765 79473682119750162928738787)
                  ·
                    refine ⟨119210523179625244393108181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 79473682119750162928738787 119210523179625244393108181)
                    ·
                      refine ⟨2793996637022466665463473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 119210523179625244393108181 2793996637022466665463473)
                      ·
                        rfl

theorem cell23_5441289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 1, 3, 1, 7].length) (baseStart_5441289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5441289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5441289 prefixEnd_5441289 := by exact prefixLift 5441289
  have htrace : WordTrace (prefixWord ++ tailWord_5441289) baseStart_5441289 baseEnd_5441289 := by
    simpa [prefixWord, tailWord_5441289, baseEnd_5441289] using wordTrace_append hprefix tailTrace_5441289
  have hstable : (prefixWord ++ tailWord_5441289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5441289).length < 2 ^ (prefixWord ++ tailWord_5441289).sum := by decide
  have hdescent : baseEnd_5441289 < baseStart_5441289 := by decide
  rcases family_descends (prefixWord ++ tailWord_5441289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5441306 : List Nat := [3, 1, 1, 3, 2, 2, 1, 2, 1, 2, 5]
def baseStart_5441306 : Nat := 118140960795 + 5441306 * 2 ^ 59
def prefixEnd_5441306 : Nat := 4983230072969 + 3 ^ 40 * 5441306 * 2
def baseEnd_5441306 : Nat := 2794005366193593098950895

theorem tailTrace_5441306 : CollatzResearch.WordTrace tailWord_5441306 prefixEnd_5441306 2794005366193593098950895 := by
  unfold tailWord_5441306
  simp only [CollatzResearch.WordTrace]
  refine ⟨49615183506271284481117943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132307156016723425282981181 49615183506271284481117943)
  ·
    refine ⟨74422775259406926721676915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49615183506271284481117943 74422775259406926721676915)
    ·
      refine ⟨111634162889110390082515373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74422775259406926721676915 111634162889110390082515373)
      ·
        refine ⟨41862811083416396280943265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 111634162889110390082515373 41862811083416396280943265)
        ·
          refine ⟨31397108312562297210707449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41862811083416396280943265 31397108312562297210707449)
          ·
            refine ⟨23547831234421722908030587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31397108312562297210707449 23547831234421722908030587)
            ·
              refine ⟨35321746851632584362045881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23547831234421722908030587 35321746851632584362045881)
              ·
                refine ⟨26491310138724438271534411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35321746851632584362045881 26491310138724438271534411)
                ·
                  refine ⟨39736965208086657407301617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26491310138724438271534411 39736965208086657407301617)
                  ·
                    refine ⟨29802723906064993055476213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 39736965208086657407301617 29802723906064993055476213)
                    ·
                      refine ⟨2794005366193593098950895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29802723906064993055476213 2794005366193593098950895)
                      ·
                        rfl

theorem cell23_5441306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 1, 2, 1, 2, 5].length) (baseStart_5441306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5441306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5441306 prefixEnd_5441306 := by exact prefixLift 5441306
  have htrace : WordTrace (prefixWord ++ tailWord_5441306) baseStart_5441306 baseEnd_5441306 := by
    simpa [prefixWord, tailWord_5441306, baseEnd_5441306] using wordTrace_append hprefix tailTrace_5441306
  have hstable : (prefixWord ++ tailWord_5441306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5441306).length < 2 ^ (prefixWord ++ tailWord_5441306).sum := by decide
  have hdescent : baseEnd_5441306 < baseStart_5441306 := by decide
  rcases family_descends (prefixWord ++ tailWord_5441306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5441376 : List Nat := [2, 1, 1, 3, 3, 2, 1, 1, 1, 2, 6]
def baseStart_5441376 : Nat := 118140960795 + 5441376 * 2 ^ 59
def prefixEnd_5441376 : Nat := 4983230072969 + 3 ^ 40 * 5441376 * 2
def baseEnd_5441376 : Nat := 2794041309839407825075573

theorem tailTrace_5441376 : CollatzResearch.WordTrace tailWord_5441376 prefixEnd_5441376 2794041309839407825075573 := by
  unfold tailWord_5441376
  simp only [CollatzResearch.WordTrace]
  refine ⟨99231643567415769939759991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132308858089887693253013321 99231643567415769939759991)
  ·
    refine ⟨148847465351123654909639987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99231643567415769939759991 148847465351123654909639987)
    ·
      refine ⟨223271198026685482364459981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148847465351123654909639987 223271198026685482364459981)
      ·
        refine ⟨83726699260007055886672493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 223271198026685482364459981 83726699260007055886672493)
        ·
          refine ⟨31397512222502645957502185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 83726699260007055886672493 31397512222502645957502185)
          ·
            refine ⟨23548134166876984468126639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31397512222502645957502185 23548134166876984468126639)
            ·
              refine ⟨35322201250315476702189959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23548134166876984468126639 35322201250315476702189959)
              ·
                refine ⟨52983301875473215053284939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35322201250315476702189959 52983301875473215053284939)
                ·
                  refine ⟨79474952813209822579927409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52983301875473215053284939 79474952813209822579927409)
                  ·
                    refine ⟨59606214609907366934945557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 79474952813209822579927409 59606214609907366934945557)
                    ·
                      refine ⟨2794041309839407825075573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 59606214609907366934945557 2794041309839407825075573)
                      ·
                        rfl

theorem cell23_5441376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 1, 1, 1, 2, 6].length) (baseStart_5441376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5441376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5441376 prefixEnd_5441376 := by exact prefixLift 5441376
  have htrace : WordTrace (prefixWord ++ tailWord_5441376) baseStart_5441376 baseEnd_5441376 := by
    simpa [prefixWord, tailWord_5441376, baseEnd_5441376] using wordTrace_append hprefix tailTrace_5441376
  have hstable : (prefixWord ++ tailWord_5441376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5441376).length < 2 ^ (prefixWord ++ tailWord_5441376).sum := by decide
  have hdescent : baseEnd_5441376 < baseStart_5441376 := by decide
  rcases family_descends (prefixWord ++ tailWord_5441376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5441393 : List Nat := [1, 2, 2, 2, 1, 3, 1, 1, 3, 5, 2]
def baseStart_5441393 : Nat := 118140960795 + 5441393 * 2 ^ 59
def prefixEnd_5441393 : Nat := 4983230072969 + 3 ^ 40 * 5441393 * 2
def baseEnd_5441393 : Nat := 2794050039010534258562995

theorem tailTrace_5441393 : CollatzResearch.WordTrace tailWord_5441393 prefixEnd_5441393 2794050039010534258562995 := by
  unfold tailWord_5441393
  simp only [CollatzResearch.WordTrace]
  refine ⟨198463907175769951782888833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132309271450513301188592555 198463907175769951782888833)
  ·
    refine ⟨148847930381827463837166625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 198463907175769951782888833 148847930381827463837166625)
    ·
      refine ⟨111635947786370597877874969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 148847930381827463837166625 111635947786370597877874969)
      ·
        refine ⟨83726960839777948408406227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111635947786370597877874969 83726960839777948408406227)
        ·
          refine ⟨125590441259666922612609341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83726960839777948408406227 125590441259666922612609341)
          ·
            refine ⟨47096415472375095979728503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 125590441259666922612609341 47096415472375095979728503)
            ·
              refine ⟨70644623208562643969592755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47096415472375095979728503 70644623208562643969592755)
              ·
                refine ⟨105966934812843965954389133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70644623208562643969592755 105966934812843965954389133)
                ·
                  refine ⟨39737600554816487232895925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 105966934812843965954389133 39737600554816487232895925)
                  ·
                    refine ⟨3725400052014045678083993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 39737600554816487232895925 3725400052014045678083993)
                    ·
                      refine ⟨2794050039010534258562995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3725400052014045678083993 2794050039010534258562995)
                      ·
                        rfl

theorem cell23_5441393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 1, 3, 5, 2].length) (baseStart_5441393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5441393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5441393 prefixEnd_5441393 := by exact prefixLift 5441393
  have htrace : WordTrace (prefixWord ++ tailWord_5441393) baseStart_5441393 baseEnd_5441393 := by
    simpa [prefixWord, tailWord_5441393, baseEnd_5441393] using wordTrace_append hprefix tailTrace_5441393
  have hstable : (prefixWord ++ tailWord_5441393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5441393).length < 2 ^ (prefixWord ++ tailWord_5441393).sum := by decide
  have hdescent : baseEnd_5441393 < baseStart_5441393 := by decide
  rcases family_descends (prefixWord ++ tailWord_5441393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5441433 : List Nat := [1, 2, 1, 2, 1, 3, 4, 1, 4, 4]
def baseStart_5441433 : Nat := 118140960795 + 5441433 * 2 ^ 59
def prefixEnd_5441433 : Nat := 4983230072969 + 3 ^ 40 * 5441433 * 2
def baseEnd_5441433 : Nat := 931356859412238034020937

theorem tailTrace_5441433 : CollatzResearch.WordTrace tailWord_5441433 prefixEnd_5441433 931356859412238034020937 := by
  unfold tailWord_5441433
  simp only [CollatzResearch.WordTrace]
  refine ⟨198465366095625038614344953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132310244063750025742896635 198465366095625038614344953)
  ·
    refine ⟨148849024571718778960758715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 198465366095625038614344953 148849024571718778960758715)
    ·
      refine ⟨223273536857578168441138073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148849024571718778960758715 223273536857578168441138073)
      ·
        refine ⟨167455152643183626330853555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 223273536857578168441138073 167455152643183626330853555)
        ·
          refine ⟨251182728964775439496280333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 167455152643183626330853555 251182728964775439496280333)
          ·
            refine ⟨94193523361790789811105125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 251182728964775439496280333 94193523361790789811105125)
            ·
              refine ⟨17661285630335773089582211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 94193523361790789811105125 17661285630335773089582211)
              ·
                refine ⟨26491928445503659634373317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17661285630335773089582211 26491928445503659634373317)
                ·
                  refine ⟨4967236583531936181444997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26491928445503659634373317 4967236583531936181444997)
                  ·
                    refine ⟨931356859412238034020937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4967236583531936181444997 931356859412238034020937)
                    ·
                      rfl

theorem cell23_5441433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 4, 1, 4, 4].length) (baseStart_5441433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5441433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5441433 prefixEnd_5441433 := by exact prefixLift 5441433
  have htrace : WordTrace (prefixWord ++ tailWord_5441433) baseStart_5441433 baseEnd_5441433 := by
    simpa [prefixWord, tailWord_5441433, baseEnd_5441433] using wordTrace_append hprefix tailTrace_5441433
  have hstable : (prefixWord ++ tailWord_5441433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5441433).length < 2 ^ (prefixWord ++ tailWord_5441433).sum := by decide
  have hdescent : baseEnd_5441433 < baseStart_5441433 := by decide
  rcases family_descends (prefixWord ++ tailWord_5441433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5441443 : List Nat := [1, 1, 1, 4, 1, 2, 1, 4, 3, 2, 3]
def baseStart_5441443 : Nat := 118140960795 + 5441443 * 2 ^ 59
def prefixEnd_5441443 : Nat := 4983230072969 + 3 ^ 40 * 5441443 * 2
def baseEnd_5441443 : Nat := 2794075713043259062937765

theorem tailTrace_5441443 : CollatzResearch.WordTrace tailWord_5441443 prefixEnd_5441443 2794075713043259062937765 := by
  unfold tailWord_5441443
  simp only [CollatzResearch.WordTrace]
  refine ⟨198465730825588810322208983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132310487217059206881472655 198465730825588810322208983)
  ·
    refine ⟨297698596238383215483313475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198465730825588810322208983 297698596238383215483313475)
    ·
      refine ⟨446547894357574823224970213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 297698596238383215483313475 446547894357574823224970213)
      ·
        refine ⟨83727730192045279354681915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 446547894357574823224970213 83727730192045279354681915)
        ·
          refine ⟨125591595288067919032022873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83727730192045279354681915 125591595288067919032022873)
          ·
            refine ⟨94193696466050939274017155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 125591595288067919032022873 94193696466050939274017155)
            ·
              refine ⟨141290544699076408911025733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 94193696466050939274017155 141290544699076408911025733)
              ·
                refine ⟨26491977131076826670817325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 141290544699076408911025733 26491977131076826670817325)
                ·
                  refine ⟨9934491424153810001556497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26491977131076826670817325 9934491424153810001556497)
                  ·
                    refine ⟨7450868568115357501167373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9934491424153810001556497 7450868568115357501167373)
                    ·
                      refine ⟨2794075713043259062937765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7450868568115357501167373 2794075713043259062937765)
                      ·
                        rfl

theorem cell23_5441443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 4, 3, 2, 3].length) (baseStart_5441443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5441443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5441443 prefixEnd_5441443 := by exact prefixLift 5441443
  have htrace : WordTrace (prefixWord ++ tailWord_5441443) baseStart_5441443 baseEnd_5441443 := by
    simpa [prefixWord, tailWord_5441443, baseEnd_5441443] using wordTrace_append hprefix tailTrace_5441443
  have hstable : (prefixWord ++ tailWord_5441443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5441443).length < 2 ^ (prefixWord ++ tailWord_5441443).sum := by decide
  have hdescent : baseEnd_5441443 < baseStart_5441443 := by decide
  rcases family_descends (prefixWord ++ tailWord_5441443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5441454 : List Nat := [4, 1, 5, 1, 1, 1, 1, 1, 3, 5]
def baseStart_5441454 : Nat := 118140960795 + 5441454 * 2 ^ 59
def prefixEnd_5441454 : Nat := 4983230072969 + 3 ^ 40 * 5441454 * 2
def baseEnd_5441454 : Nat := 931360453776819506633405

theorem tailTrace_5441454 : CollatzResearch.WordTrace tailWord_5441454 prefixEnd_5441454 931360453776819506633405 := by
  unfold tailWord_5441454
  simp only [CollatzResearch.WordTrace]
  refine ⟨24808266503568619900107427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 132310754685699306133906277 24808266503568619900107427)
  ·
    refine ⟨37212399755352929850161141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24808266503568619900107427 37212399755352929850161141)
    ·
      refine ⟨3488662477064337173452607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 37212399755352929850161141 3488662477064337173452607)
      ·
        refine ⟨5232993715596505760178911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3488662477064337173452607 5232993715596505760178911)
        ·
          refine ⟨7849490573394758640268367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5232993715596505760178911 7849490573394758640268367)
          ·
            refine ⟨11774235860092137960402551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7849490573394758640268367 11774235860092137960402551)
            ·
              refine ⟨17661353790138206940603827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11774235860092137960402551 17661353790138206940603827)
              ·
                refine ⟨26492030685207310410905741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17661353790138206940603827 26492030685207310410905741)
                ·
                  refine ⟨9934511506952741404089653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26492030685207310410905741 9934511506952741404089653)
                  ·
                    refine ⟨931360453776819506633405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9934511506952741404089653 931360453776819506633405)
                    ·
                      rfl

theorem cell23_5441454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 1, 1, 3, 5].length) (baseStart_5441454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5441454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5441454 prefixEnd_5441454 := by exact prefixLift 5441454
  have htrace : WordTrace (prefixWord ++ tailWord_5441454) baseStart_5441454 baseEnd_5441454 := by
    simpa [prefixWord, tailWord_5441454, baseEnd_5441454] using wordTrace_append hprefix tailTrace_5441454
  have hstable : (prefixWord ++ tailWord_5441454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5441454).length < 2 ^ (prefixWord ++ tailWord_5441454).sum := by decide
  have hdescent : baseEnd_5441454 < baseStart_5441454 := by decide
  rcases family_descends (prefixWord ++ tailWord_5441454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5441457 : List Nat := [1, 2, 2, 4, 2, 3, 1, 2, 1, 1, 4]
def baseStart_5441457 : Nat := 118140960795 + 5441457 * 2 ^ 59
def prefixEnd_5441457 : Nat := 4983230072969 + 3 ^ 40 * 5441457 * 2
def baseEnd_5441457 : Nat := 2794082901772422008162701

theorem tailTrace_5441457 : CollatzResearch.WordTrace tailWord_5441457 prefixEnd_5441457 2794082901772422008162701 := by
  unfold tailWord_5441457
  simp only [CollatzResearch.WordTrace]
  refine ⟨198466241447538090713218625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132310827631692060475479083 198466241447538090713218625)
  ·
    refine ⟨148849681085653568034913969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 198466241447538090713218625 148849681085653568034913969)
    ·
      refine ⟨111637260814240176026185477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 148849681085653568034913969 111637260814240176026185477)
      ·
        refine ⟨20931986402670033004909777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 111637260814240176026185477 20931986402670033004909777)
        ·
          refine ⟨15698989802002524753682333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20931986402670033004909777 15698989802002524753682333)
          ·
            refine ⟨5887121175750946782630875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15698989802002524753682333 5887121175750946782630875)
            ·
              refine ⟨8830681763626420173946313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5887121175750946782630875 8830681763626420173946313)
              ·
                refine ⟨6623011322719815130459735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8830681763626420173946313 6623011322719815130459735)
                ·
                  refine ⟨9934516984079722695689603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6623011322719815130459735 9934516984079722695689603)
                  ·
                    refine ⟨14901775476119584043534405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9934516984079722695689603 14901775476119584043534405)
                    ·
                      refine ⟨2794082901772422008162701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14901775476119584043534405 2794082901772422008162701)
                      ·
                        rfl

theorem cell23_5441457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 3, 1, 2, 1, 1, 4].length) (baseStart_5441457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5441457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5441457 prefixEnd_5441457 := by exact prefixLift 5441457
  have htrace : WordTrace (prefixWord ++ tailWord_5441457) baseStart_5441457 baseEnd_5441457 := by
    simpa [prefixWord, tailWord_5441457, baseEnd_5441457] using wordTrace_append hprefix tailTrace_5441457
  have hstable : (prefixWord ++ tailWord_5441457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5441457).length < 2 ^ (prefixWord ++ tailWord_5441457).sum := by decide
  have hdescent : baseEnd_5441457 < baseStart_5441457 := by decide
  rcases family_descends (prefixWord ++ tailWord_5441457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5441470 : List Nat := [4, 2, 1, 1, 1, 4, 1, 2, 1, 2, 4]
def baseStart_5441470 : Nat := 118140960795 + 5441470 * 2 ^ 59
def prefixEnd_5441470 : Nat := 4983230072969 + 3 ^ 40 * 5441470 * 2
def baseEnd_5441470 : Nat := 2794089577020930457300141

theorem tailTrace_5441470 : CollatzResearch.WordTrace tailWord_5441470 prefixEnd_5441470 2794089577020930457300141 := by
  unfold tailWord_5441470
  simp only [CollatzResearch.WordTrace]
  refine ⟨24808339449561374241680233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 132311143730993995955627909 24808339449561374241680233)
  ·
    refine ⟨18606254587171030681260175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24808339449561374241680233 18606254587171030681260175)
    ·
      refine ⟨27909381880756546021890263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18606254587171030681260175 27909381880756546021890263)
      ·
        refine ⟨41864072821134819032835395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27909381880756546021890263 41864072821134819032835395)
        ·
          refine ⟨62796109231702228549253093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41864072821134819032835395 62796109231702228549253093)
          ·
            refine ⟨11774270480944167852984955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 62796109231702228549253093 11774270480944167852984955)
            ·
              refine ⟨17661405721416251779477433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11774270480944167852984955 17661405721416251779477433)
              ·
                refine ⟨13246054291062188834608075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17661405721416251779477433 13246054291062188834608075)
                ·
                  refine ⟨19869081436593283251912113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13246054291062188834608075 19869081436593283251912113)
                  ·
                    refine ⟨14901811077444962438934085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19869081436593283251912113 14901811077444962438934085)
                    ·
                      refine ⟨2794089577020930457300141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14901811077444962438934085 2794089577020930457300141)
                      ·
                        rfl

theorem cell23_5441470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 1, 2, 1, 2, 4].length) (baseStart_5441470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5441470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5441470 prefixEnd_5441470 := by exact prefixLift 5441470
  have htrace : WordTrace (prefixWord ++ tailWord_5441470) baseStart_5441470 baseEnd_5441470 := by
    simpa [prefixWord, tailWord_5441470, baseEnd_5441470] using wordTrace_append hprefix tailTrace_5441470
  have hstable : (prefixWord ++ tailWord_5441470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5441470).length < 2 ^ (prefixWord ++ tailWord_5441470).sum := by decide
  have hdescent : baseEnd_5441470 < baseStart_5441470 := by decide
  rcases family_descends (prefixWord ++ tailWord_5441470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5441493 : List Nat := [1, 3, 2, 3, 2, 1, 1, 1, 2, 7]
def baseStart_5441493 : Nat := 118140960795 + 5441493 * 2 ^ 59
def prefixEnd_5441493 : Nat := 4983230072969 + 3 ^ 40 * 5441493 * 2
def baseEnd_5441493 : Nat := 931367129025327955770845

theorem tailTrace_5441493 : CollatzResearch.WordTrace tailWord_5441493 prefixEnd_5441493 931367129025327955770845 := by
  unfold tailWord_5441493
  simp only [CollatzResearch.WordTrace]
  refine ⟨198467554475407668861529133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132311702983605112574352755 198467554475407668861529133)
  ·
    refine ⟨74425332928277875823073425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 198467554475407668861529133 74425332928277875823073425)
    ·
      refine ⟨55818999696208406867305069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74425332928277875823073425 55818999696208406867305069)
      ·
        refine ⟨20932124886078152575239401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55818999696208406867305069 20932124886078152575239401)
        ·
          refine ⟨15699093664558614431429551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20932124886078152575239401 15699093664558614431429551)
          ·
            refine ⟨23548640496837921647144327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15699093664558614431429551 23548640496837921647144327)
            ·
              refine ⟨35322960745256882470716491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23548640496837921647144327 35322960745256882470716491)
              ·
                refine ⟨52984441117885323706074737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35322960745256882470716491 52984441117885323706074737)
                ·
                  refine ⟨39738330838413992779556053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 52984441117885323706074737 39738330838413992779556053)
                  ·
                    refine ⟨931367129025327955770845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 39738330838413992779556053 931367129025327955770845)
                    ·
                      rfl

theorem cell23_5441493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 1, 1, 2, 7].length) (baseStart_5441493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5441493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5441493 prefixEnd_5441493 := by exact prefixLift 5441493
  have htrace : WordTrace (prefixWord ++ tailWord_5441493) baseStart_5441493 baseEnd_5441493 := by
    simpa [prefixWord, tailWord_5441493, baseEnd_5441493] using wordTrace_append hprefix tailTrace_5441493
  have hstable : (prefixWord ++ tailWord_5441493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5441493).length < 2 ^ (prefixWord ++ tailWord_5441493).sum := by decide
  have hdescent : baseEnd_5441493 < baseStart_5441493 := by decide
  rcases family_descends (prefixWord ++ tailWord_5441493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5441507 : List Nat := [1, 1, 1, 6, 1, 2, 2, 3, 2, 1, 3]
def baseStart_5441507 : Nat := 118140960795 + 5441507 * 2 ^ 59
def prefixEnd_5441507 : Nat := 4983230072969 + 3 ^ 40 * 5441507 * 2
def baseEnd_5441507 : Nat := 2794108575805146812537471

theorem tailTrace_5441507 : CollatzResearch.WordTrace tailWord_5441507 prefixEnd_5441507 2794108575805146812537471 := by
  unfold tailWord_5441507
  simp only [CollatzResearch.WordTrace]
  refine ⟨198468065097356949252538775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132312043398237966168359183 198468065097356949252538775)
  ·
    refine ⟨297702097646035423878808163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198468065097356949252538775 297702097646035423878808163)
    ·
      refine ⟨446553146469053135818212245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 297702097646035423878808163 446553146469053135818212245)
      ·
        refine ⟨20932178740736865741478699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 446553146469053135818212245 20932178740736865741478699)
        ·
          refine ⟨31398268111105298612218049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20932178740736865741478699 31398268111105298612218049)
          ·
            refine ⟨23548701083328973959163537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31398268111105298612218049 23548701083328973959163537)
            ·
              refine ⟨17661525812496730469372653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23548701083328973959163537 17661525812496730469372653)
              ·
                refine ⟨6623072179686273926014745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17661525812496730469372653 6623072179686273926014745)
                ·
                  refine ⟨4967304134764705444511059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6623072179686273926014745 4967304134764705444511059)
                  ·
                    refine ⟨7450956202147058166766589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4967304134764705444511059 7450956202147058166766589)
                    ·
                      refine ⟨2794108575805146812537471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7450956202147058166766589 2794108575805146812537471)
                      ·
                        rfl

theorem cell23_5441507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 2, 3, 2, 1, 3].length) (baseStart_5441507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5441507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5441507 prefixEnd_5441507 := by exact prefixLift 5441507
  have htrace : WordTrace (prefixWord ++ tailWord_5441507) baseStart_5441507 baseEnd_5441507 := by
    simpa [prefixWord, tailWord_5441507, baseEnd_5441507] using wordTrace_append hprefix tailTrace_5441507
  have hstable : (prefixWord ++ tailWord_5441507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5441507).length < 2 ^ (prefixWord ++ tailWord_5441507).sum := by decide
  have hdescent : baseEnd_5441507 < baseStart_5441507 := by decide
  rcases family_descends (prefixWord ++ tailWord_5441507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5441533 : List Nat := [1, 4, 1, 1, 1, 2, 2, 3, 2, 1, 5]
def baseStart_5441533 : Nat := 118140960795 + 5441533 * 2 ^ 59
def prefixEnd_5441533 : Nat := 4983230072969 + 3 ^ 40 * 5441533 * 2
def baseEnd_5441533 : Nat := 2794121926302163710812351

theorem tailTrace_5441533 : CollatzResearch.WordTrace tailWord_5441533 prefixEnd_5441533 2794121926302163710812351 := by
  unfold tailWord_5441533
  simp only [CollatzResearch.WordTrace]
  refine ⟨198469013395262755692985253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132312675596841837128656835 198469013395262755692985253)
  ·
    refine ⟨37212940011611766692434735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 198469013395262755692985253 37212940011611766692434735)
    ·
      refine ⟨55819410017417650038652103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37212940011611766692434735 55819410017417650038652103)
      ·
        refine ⟨83729115026126475057978155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55819410017417650038652103 83729115026126475057978155)
        ·
          refine ⟨125593672539189712586967233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83729115026126475057978155 125593672539189712586967233)
          ·
            refine ⟨94195254404392284440225425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 125593672539189712586967233 94195254404392284440225425)
            ·
              refine ⟨70646440803294213330169069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 94195254404392284440225425 70646440803294213330169069)
              ·
                refine ⟨26492415301235329998813401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 70646440803294213330169069 26492415301235329998813401)
                ·
                  refine ⟨19869311475926497499110051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26492415301235329998813401 19869311475926497499110051)
                  ·
                    refine ⟨29803967213889746248665077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19869311475926497499110051 29803967213889746248665077)
                    ·
                      refine ⟨2794121926302163710812351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29803967213889746248665077 2794121926302163710812351)
                      ·
                        rfl

theorem cell23_5441533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 3, 2, 1, 5].length) (baseStart_5441533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5441533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5441533 prefixEnd_5441533 := by exact prefixLift 5441533
  have htrace : WordTrace (prefixWord ++ tailWord_5441533) baseStart_5441533 baseEnd_5441533 := by
    simpa [prefixWord, tailWord_5441533, baseEnd_5441533] using wordTrace_append hprefix tailTrace_5441533
  have hstable : (prefixWord ++ tailWord_5441533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5441533).length < 2 ^ (prefixWord ++ tailWord_5441533).sum := by decide
  have hdescent : baseEnd_5441533 < baseStart_5441533 := by decide
  rcases family_descends (prefixWord ++ tailWord_5441533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5441547 : List Nat := [1, 1, 1, 1, 6, 1, 3, 1, 4, 2, 2]
def baseStart_5441547 : Nat := 118140960795 + 5441547 * 2 ^ 59
def prefixEnd_5441547 : Nat := 4983230072969 + 3 ^ 40 * 5441547 * 2
def baseEnd_5441547 : Nat := 2794129115031326656037287

theorem tailTrace_5441547 : CollatzResearch.WordTrace tailWord_5441547 prefixEnd_5441547 2794129115031326656037287 := by
  unfold tailWord_5441547
  simp only [CollatzResearch.WordTrace]
  refine ⟨198469524017212036083994895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132313016011474690722663263 198469524017212036083994895)
  ·
    refine ⟨297704286025818054125992343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198469524017212036083994895 297704286025818054125992343)
    ·
      refine ⟨446556429038727081188988515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 297704286025818054125992343 446556429038727081188988515)
      ·
        refine ⟨669834643558090621783482773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 446556429038727081188988515 669834643558090621783482773)
        ·
          refine ⟨31398498916785497896100755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 669834643558090621783482773 31398498916785497896100755)
          ·
            refine ⟨47097748375178246844151133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31398498916785497896100755 47097748375178246844151133)
            ·
              refine ⟨17661655640691842566556675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47097748375178246844151133 17661655640691842566556675)
              ·
                refine ⟨26492483461037763849835013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17661655640691842566556675 26492483461037763849835013)
                ·
                  refine ⟨4967340648944580721844065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26492483461037763849835013 4967340648944580721844065)
                  ·
                    refine ⟨3725505486708435541383049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4967340648944580721844065 3725505486708435541383049)
                    ·
                      refine ⟨2794129115031326656037287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3725505486708435541383049 2794129115031326656037287)
                      ·
                        rfl

theorem cell23_5441547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 3, 1, 4, 2, 2].length) (baseStart_5441547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5441547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5441547 prefixEnd_5441547 := by exact prefixLift 5441547
  have htrace : WordTrace (prefixWord ++ tailWord_5441547) baseStart_5441547 baseEnd_5441547 := by
    simpa [prefixWord, tailWord_5441547, baseEnd_5441547] using wordTrace_append hprefix tailTrace_5441547
  have hstable : (prefixWord ++ tailWord_5441547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5441547).length < 2 ^ (prefixWord ++ tailWord_5441547).sum := by decide
  have hdescent : baseEnd_5441547 < baseStart_5441547 := by decide
  rcases family_descends (prefixWord ++ tailWord_5441547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5441563 : List Nat := [1, 1, 1, 1, 1, 1, 3, 5, 1, 5, 3]
def baseStart_5441563 : Nat := 118140960795 + 5441563 * 2 ^ 59
def prefixEnd_5441563 : Nat := 4983230072969 + 3 ^ 40 * 5441563 * 2
def baseEnd_5441563 : Nat := 2794137330721798593437213

theorem tailTrace_5441563 : CollatzResearch.WordTrace tailWord_5441563 prefixEnd_5441563 2794137330721798593437213 := by
  unfold tailWord_5441563
  simp only [CollatzResearch.WordTrace]
  refine ⟨198470107585154070816577343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132313405056769380544384895 198470107585154070816577343)
  ·
    refine ⟨297705161377731106224866015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198470107585154070816577343 297705161377731106224866015)
    ·
      refine ⟨446557742066596659337299023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 297705161377731106224866015 446557742066596659337299023)
      ·
        refine ⟨669836613099894989005948535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 446557742066596659337299023 669836613099894989005948535)
        ·
          refine ⟨1004754919649842483508922803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 669836613099894989005948535 1004754919649842483508922803)
          ·
            refine ⟨1507132379474763725263384205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1004754919649842483508922803 1507132379474763725263384205)
            ·
              refine ⟨565174642303036396973769077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1507132379474763725263384205 565174642303036396973769077)
              ·
                refine ⟨52985122715909662216290851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 565174642303036396973769077 52985122715909662216290851)
                ·
                  refine ⟨79477684073864493324436277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52985122715909662216290851 79477684073864493324436277)
                  ·
                    refine ⟨7451032881924796249165901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 79477684073864493324436277 7451032881924796249165901)
                    ·
                      refine ⟨2794137330721798593437213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7451032881924796249165901 2794137330721798593437213)
                      ·
                        rfl

theorem cell23_5441563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 5, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 5, 1, 5, 3].length) (baseStart_5441563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5441563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5441563 prefixEnd_5441563 := by exact prefixLift 5441563
  have htrace : WordTrace (prefixWord ++ tailWord_5441563) baseStart_5441563 baseEnd_5441563 := by
    simpa [prefixWord, tailWord_5441563, baseEnd_5441563] using wordTrace_append hprefix tailTrace_5441563
  have hstable : (prefixWord ++ tailWord_5441563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5441563).length < 2 ^ (prefixWord ++ tailWord_5441563).sum := by decide
  have hdescent : baseEnd_5441563 < baseStart_5441563 := by decide
  rcases family_descends (prefixWord ++ tailWord_5441563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5441564 : List Nat := [2, 2, 3, 1, 3, 3, 1, 1, 1, 4, 2]
def baseStart_5441564 : Nat := 118140960795 + 5441564 * 2 ^ 59
def prefixEnd_5441564 : Nat := 4983230072969 + 3 ^ 40 * 5441564 * 2
def baseEnd_5441564 : Nat := 2794137844202453089524709

theorem tailTrace_5441564 : CollatzResearch.WordTrace tailWord_5441564 prefixEnd_5441564 2794137844202453089524709 := by
  unfold tailWord_5441564
  simp only [CollatzResearch.WordTrace]
  refine ⟨99235072029075223993681873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132313429372100298658242497 99235072029075223993681873)
  ·
    refine ⟨74426304021806417995261405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99235072029075223993681873 74426304021806417995261405)
    ·
      refine ⟨27909864008177406748223027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74426304021806417995261405 27909864008177406748223027)
      ·
        refine ⟨41864796012266110122334541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27909864008177406748223027 41864796012266110122334541)
        ·
          refine ⟨15699298504599791295875453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41864796012266110122334541 15699298504599791295875453)
          ·
            refine ⟨5887236939224921735953295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15699298504599791295875453 5887236939224921735953295)
            ·
              refine ⟨8830855408837382603929943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5887236939224921735953295 8830855408837382603929943)
              ·
                refine ⟨13246283113256073905894915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8830855408837382603929943 13246283113256073905894915)
                ·
                  refine ⟨19869424669884110858842373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13246283113256073905894915 19869424669884110858842373)
                  ·
                    refine ⟨3725517125603270786032945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19869424669884110858842373 3725517125603270786032945)
                    ·
                      refine ⟨2794137844202453089524709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3725517125603270786032945 2794137844202453089524709)
                      ·
                        rfl

theorem cell23_5441564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 3, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 3, 1, 1, 1, 4, 2].length) (baseStart_5441564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5441564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5441564 prefixEnd_5441564 := by exact prefixLift 5441564
  have htrace : WordTrace (prefixWord ++ tailWord_5441564) baseStart_5441564 baseEnd_5441564 := by
    simpa [prefixWord, tailWord_5441564, baseEnd_5441564] using wordTrace_append hprefix tailTrace_5441564
  have hstable : (prefixWord ++ tailWord_5441564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5441564).length < 2 ^ (prefixWord ++ tailWord_5441564).sum := by decide
  have hdescent : baseEnd_5441564 < baseStart_5441564 := by decide
  rcases family_descends (prefixWord ++ tailWord_5441564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5441600 : List Nat := [2, 1, 1, 2, 2, 5, 1, 2, 2, 5]
def baseStart_5441600 : Nat := 118140960795 + 5441600 * 2 ^ 59
def prefixEnd_5441600 : Nat := 4983230072969 + 3 ^ 40 * 5441600 * 2
def baseEnd_5441600 : Nat := 931385443168671649558181

theorem tailTrace_5441600 : CollatzResearch.WordTrace tailWord_5441600 prefixEnd_5441600 931385443168671649558181 := by
  unfold tailWord_5441600
  simp only [CollatzResearch.WordTrace]
  refine ⟨99235728543010013067837127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132314304724013350757116169 99235728543010013067837127)
  ·
    refine ⟨148853592814515019601755691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99235728543010013067837127 148853592814515019601755691)
    ·
      refine ⟨223280389221772529402633537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148853592814515019601755691 223280389221772529402633537)
      ·
        refine ⟨167460291916329397051975153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 223280389221772529402633537 167460291916329397051975153)
        ·
          refine ⟨125595218937247047788981365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 167460291916329397051975153 125595218937247047788981365)
          ·
            refine ⟨11774551775366910730217003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 125595218937247047788981365 11774551775366910730217003)
            ·
              refine ⟨17661827663050366095325505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11774551775366910730217003 17661827663050366095325505)
              ·
                refine ⟨13246370747287774571494129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17661827663050366095325505 13246370747287774571494129)
                ·
                  refine ⟨9934778060465830928620597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13246370747287774571494129 9934778060465830928620597)
                  ·
                    refine ⟨931385443168671649558181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9934778060465830928620597 931385443168671649558181)
                    ·
                      rfl

theorem cell23_5441600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 1, 2, 2, 5].length) (baseStart_5441600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5441600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5441600 prefixEnd_5441600 := by exact prefixLift 5441600
  have htrace : WordTrace (prefixWord ++ tailWord_5441600) baseStart_5441600 baseEnd_5441600 := by
    simpa [prefixWord, tailWord_5441600, baseEnd_5441600] using wordTrace_append hprefix tailTrace_5441600
  have hstable : (prefixWord ++ tailWord_5441600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5441600).length < 2 ^ (prefixWord ++ tailWord_5441600).sum := by decide
  have hdescent : baseEnd_5441600 < baseStart_5441600 := by decide
  rcases family_descends (prefixWord ++ tailWord_5441600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5441603 : List Nat := [1, 1, 1, 3, 1, 2, 2, 2, 3, 3, 4]
def baseStart_5441603 : Nat := 118140960795 + 5441603 * 2 ^ 59
def prefixEnd_5441603 : Nat := 4983230072969 + 3 ^ 40 * 5441603 * 2
def baseEnd_5441603 : Nat := 2794157869947978436937029

theorem tailTrace_5441603 : CollatzResearch.WordTrace tailWord_5441603 prefixEnd_5441603 2794157869947978436937029 := by
  unfold tailWord_5441603
  simp only [CollatzResearch.WordTrace]
  refine ⟨198471566505009157648033463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132314377670006105098688975 198471566505009157648033463)
  ·
    refine ⟨297707349757513736472050195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198471566505009157648033463 297707349757513736472050195)
    ·
      refine ⟨446561024636270604708075293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 297707349757513736472050195 446561024636270604708075293)
      ·
        refine ⟨167460384238601476765528235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 446561024636270604708075293 167460384238601476765528235)
        ·
          refine ⟨251190576357902215148292353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 167460384238601476765528235 251190576357902215148292353)
          ·
            refine ⟨188392932268426661361219265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 251190576357902215148292353 188392932268426661361219265)
            ·
              refine ⟨141294699201319996020914449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 188392932268426661361219265 141294699201319996020914449)
              ·
                refine ⟨105971024400989997015685837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 141294699201319996020914449 105971024400989997015685837)
                ·
                  refine ⟨39739134150371248880882189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 105971024400989997015685837 39739134150371248880882189)
                  ·
                    refine ⟨14902175306389218330330821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 39739134150371248880882189 14902175306389218330330821)
                    ·
                      refine ⟨2794157869947978436937029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14902175306389218330330821 2794157869947978436937029)
                      ·
                        rfl

theorem cell23_5441603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 2, 3, 3, 4].length) (baseStart_5441603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5441603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5441603 prefixEnd_5441603 := by exact prefixLift 5441603
  have htrace : WordTrace (prefixWord ++ tailWord_5441603) baseStart_5441603 baseEnd_5441603 := by
    simpa [prefixWord, tailWord_5441603, baseEnd_5441603] using wordTrace_append hprefix tailTrace_5441603
  have hstable : (prefixWord ++ tailWord_5441603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5441603).length < 2 ^ (prefixWord ++ tailWord_5441603).sum := by decide
  have hdescent : baseEnd_5441603 < baseStart_5441603 := by decide
  rcases family_descends (prefixWord ++ tailWord_5441603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5441620 : List Nat := [2, 4, 1, 1, 1, 1, 1, 1, 6, 1, 4]
def baseStart_5441620 : Nat := 118140960795 + 5441620 * 2 ^ 59
def prefixEnd_5441620 : Nat := 4983230072969 + 3 ^ 40 * 5441620 * 2
def baseEnd_5441620 : Nat := 2794166599119104870424451

theorem tailTrace_5441620 : CollatzResearch.WordTrace tailWord_5441620 prefixEnd_5441620 2794166599119104870424451 := by
  unfold tailWord_5441620
  simp only [CollatzResearch.WordTrace]
  refine ⟨99236093272973784775701157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132314791030631713034268209 99236093272973784775701157)
  ·
    refine ⟨18606767488682584645443967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 99236093272973784775701157 18606767488682584645443967)
    ·
      refine ⟨27910151233023876968165951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18606767488682584645443967 27910151233023876968165951)
      ·
        refine ⟨41865226849535815452248927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27910151233023876968165951 41865226849535815452248927)
        ·
          refine ⟨62797840274303723178373391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41865226849535815452248927 62797840274303723178373391)
          ·
            refine ⟨94196760411455584767560087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62797840274303723178373391 94196760411455584767560087)
            ·
              refine ⟨141295140617183377151340131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 94196760411455584767560087 141295140617183377151340131)
              ·
                refine ⟨211942710925775065727010197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 141295140617183377151340131 211942710925775065727010197)
                ·
                  refine ⟨9934814574645706205953603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 211942710925775065727010197 9934814574645706205953603)
                  ·
                    refine ⟨14902221861968559308930405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9934814574645706205953603 14902221861968559308930405)
                    ·
                      refine ⟨2794166599119104870424451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14902221861968559308930405 2794166599119104870424451)
                      ·
                        rfl

theorem cell23_5441620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 1, 6, 1, 4].length) (baseStart_5441620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5441620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5441620 prefixEnd_5441620 := by exact prefixLift 5441620
  have htrace : WordTrace (prefixWord ++ tailWord_5441620) baseStart_5441620 baseEnd_5441620 := by
    simpa [prefixWord, tailWord_5441620, baseEnd_5441620] using wordTrace_append hprefix tailTrace_5441620
  have hstable : (prefixWord ++ tailWord_5441620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5441620).length < 2 ^ (prefixWord ++ tailWord_5441620).sum := by decide
  have hdescent : baseEnd_5441620 < baseStart_5441620 := by decide
  rcases family_descends (prefixWord ++ tailWord_5441620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5441633 : List Nat := [1, 2, 3, 1, 1, 2, 1, 2, 1, 3, 6]
def baseStart_5441633 : Nat := 118140960795 + 5441633 * 2 ^ 59
def prefixEnd_5441633 : Nat := 4983230072969 + 3 ^ 40 * 5441633 * 2
def baseEnd_5441633 : Nat := 2794173274367613319561891

theorem tailTrace_5441633 : CollatzResearch.WordTrace tailWord_5441633 prefixEnd_5441633 2794173274367613319561891 := by
  unfold tailWord_5441633
  simp only [CollatzResearch.WordTrace]
  refine ⟨198472660694900472771625553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132315107129933648514417035 198472660694900472771625553)
  ·
    refine ⟨148854495521175354578719165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 198472660694900472771625553 148854495521175354578719165)
    ·
      refine ⟨55820435820440757967019687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 148854495521175354578719165 55820435820440757967019687)
      ·
        refine ⟨83730653730661136950529531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55820435820440757967019687 83730653730661136950529531)
        ·
          refine ⟨125595980595991705425794297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83730653730661136950529531 125595980595991705425794297)
          ·
            refine ⟨94196985446993779069345723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 125595980595991705425794297 94196985446993779069345723)
            ·
              refine ⟨141295478170490668604018585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 94196985446993779069345723 141295478170490668604018585)
              ·
                refine ⟨105971608627868001453013939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 141295478170490668604018585 105971608627868001453013939)
                ·
                  refine ⟨158957412941802002179520909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 105971608627868001453013939 158957412941802002179520909)
                  ·
                    refine ⟨59609029853175750817320341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 158957412941802002179520909 59609029853175750817320341)
                    ·
                      refine ⟨2794173274367613319561891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 59609029853175750817320341 2794173274367613319561891)
                      ·
                        rfl

theorem cell23_5441633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 2, 1, 3, 6].length) (baseStart_5441633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5441633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5441633 prefixEnd_5441633 := by exact prefixLift 5441633
  have htrace : WordTrace (prefixWord ++ tailWord_5441633) baseStart_5441633 baseEnd_5441633 := by
    simpa [prefixWord, tailWord_5441633, baseEnd_5441633] using wordTrace_append hprefix tailTrace_5441633
  have hstable : (prefixWord ++ tailWord_5441633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5441633).length < 2 ^ (prefixWord ++ tailWord_5441633).sum := by decide
  have hdescent : baseEnd_5441633 < baseStart_5441633 := by decide
  rcases family_descends (prefixWord ++ tailWord_5441633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5441634 : List Nat := [3, 3, 2, 2, 2, 1, 2, 1, 2, 5]
def baseStart_5441634 : Nat := 118140960795 + 5441634 * 2 ^ 59
def prefixEnd_5441634 : Nat := 4983230072969 + 3 ^ 40 * 5441634 * 2
def baseEnd_5441634 : Nat := 931391262616089271883129

theorem tailTrace_5441634 : CollatzResearch.WordTrace tailWord_5441634 prefixEnd_5441634 931391262616089271883129 := by
  unfold tailWord_5441634
  simp only [CollatzResearch.WordTrace]
  refine ⟨49618174291974212485602989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132315131445264566628274637 49618174291974212485602989)
  ·
    refine ⟨18606815359490329682101121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49618174291974212485602989 18606815359490329682101121)
    ·
      refine ⟨13955111519617747261575841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18606815359490329682101121 13955111519617747261575841)
      ·
        refine ⟨10466333639713310446181881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13955111519617747261575841 10466333639713310446181881)
        ·
          refine ⟨7849750229784982834636411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10466333639713310446181881 7849750229784982834636411)
          ·
            refine ⟨11774625344677474251954617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7849750229784982834636411 11774625344677474251954617)
            ·
              refine ⟨8830969008508105688965963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11774625344677474251954617 8830969008508105688965963)
              ·
                refine ⟨13246453512762158533448945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8830969008508105688965963 13246453512762158533448945)
                ·
                  refine ⟨9934840134571618900086709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13246453512762158533448945 9934840134571618900086709)
                  ·
                    refine ⟨931391262616089271883129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9934840134571618900086709 931391262616089271883129)
                    ·
                      rfl

theorem cell23_5441634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 2, 1, 2, 5].length) (baseStart_5441634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5441634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5441634 prefixEnd_5441634 := by exact prefixLift 5441634
  have htrace : WordTrace (prefixWord ++ tailWord_5441634) baseStart_5441634 baseEnd_5441634 := by
    simpa [prefixWord, tailWord_5441634, baseEnd_5441634] using wordTrace_append hprefix tailTrace_5441634
  have hstable : (prefixWord ++ tailWord_5441634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5441634).length < 2 ^ (prefixWord ++ tailWord_5441634).sum := by decide
  have hdescent : baseEnd_5441634 < baseStart_5441634 := by decide
  rcases family_descends (prefixWord ++ tailWord_5441634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5441637 : List Nat := [1, 3, 1, 3, 2, 3, 2, 1, 2, 1, 4]
def baseStart_5441637 : Nat := 118140960795 + 5441637 * 2 ^ 59
def prefixEnd_5441637 : Nat := 4983230072969 + 3 ^ 40 * 5441637 * 2
def baseEnd_5441637 : Nat := 2794175328290231303911873

theorem tailTrace_5441637 : CollatzResearch.WordTrace tailWord_5441637 prefixEnd_5441637 2794175328290231303911873 := by
  unfold tailWord_5441637
  simp only [CollatzResearch.WordTrace]
  refine ⟨198472806586885981454771165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132315204391257320969847443 198472806586885981454771165)
  ·
    refine ⟨74427302470082243045539187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 198472806586885981454771165 74427302470082243045539187)
    ·
      refine ⟨111640953705123364568308781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74427302470082243045539187 111640953705123364568308781)
      ·
        refine ⟨41865357639421261713115793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 111640953705123364568308781 41865357639421261713115793)
        ·
          refine ⟨31399018229565946284836845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41865357639421261713115793 31399018229565946284836845)
          ·
            refine ⟨11774631836087229856813817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31399018229565946284836845 11774631836087229856813817)
            ·
              refine ⟨8830973877065422392610363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11774631836087229856813817 8830973877065422392610363)
              ·
                refine ⟨13246460815598133588915545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8830973877065422392610363 13246460815598133588915545)
                ·
                  refine ⟨9934845611698600191686659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13246460815598133588915545 9934845611698600191686659)
                  ·
                    refine ⟨14902268417547900287529989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9934845611698600191686659 14902268417547900287529989)
                    ·
                      refine ⟨2794175328290231303911873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14902268417547900287529989 2794175328290231303911873)
                      ·
                        rfl

theorem cell23_5441637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 2, 1, 2, 1, 4].length) (baseStart_5441637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5441637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5441637 prefixEnd_5441637 := by exact prefixLift 5441637
  have htrace : WordTrace (prefixWord ++ tailWord_5441637) baseStart_5441637 baseEnd_5441637 := by
    simpa [prefixWord, tailWord_5441637, baseEnd_5441637] using wordTrace_append hprefix tailTrace_5441637
  have hstable : (prefixWord ++ tailWord_5441637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5441637).length < 2 ^ (prefixWord ++ tailWord_5441637).sum := by decide
  have hdescent : baseEnd_5441637 < baseStart_5441637 := by decide
  rcases family_descends (prefixWord ++ tailWord_5441637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5441657 : List Nat := [1, 2, 1, 3, 4, 1, 2, 2, 2, 2, 3]
def baseStart_5441657 : Nat := 118140960795 + 5441657 * 2 ^ 59
def prefixEnd_5441657 : Nat := 4983230072969 + 3 ^ 40 * 5441657 * 2
def baseEnd_5441657 : Nat := 2794185597903321225661781

theorem tailTrace_5441657 : CollatzResearch.WordTrace tailWord_5441657 prefixEnd_5441657 2794185597903321225661781 := by
  unfold tailWord_5441657
  simp only [CollatzResearch.WordTrace]
  refine ⟨198473536046813524870499225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132315690697875683246999483 198473536046813524870499225)
  ·
    refine ⟨148855152035110143652874419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 198473536046813524870499225 148855152035110143652874419)
    ·
      refine ⟨223282728052665215479311629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148855152035110143652874419 223282728052665215479311629)
      ·
        refine ⟨83731023019749455804741861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 223282728052665215479311629 83731023019749455804741861)
        ·
          refine ⟨15699566816203022963389099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 83731023019749455804741861 15699566816203022963389099)
          ·
            refine ⟨23549350224304534445083649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15699566816203022963389099 23549350224304534445083649)
            ·
              refine ⟨17662012668228400833812737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23549350224304534445083649 17662012668228400833812737)
              ·
                refine ⟨13246509501171300625359553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17662012668228400833812737 13246509501171300625359553)
                ·
                  refine ⟨9934882125878475469019665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13246509501171300625359553 9934882125878475469019665)
                  ·
                    refine ⟨7451161594408856601764749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9934882125878475469019665 7451161594408856601764749)
                    ·
                      refine ⟨2794185597903321225661781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7451161594408856601764749 2794185597903321225661781)
                      ·
                        rfl

theorem cell23_5441657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 2, 2, 2, 2, 3].length) (baseStart_5441657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5441657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5441657 prefixEnd_5441657 := by exact prefixLift 5441657
  have htrace : WordTrace (prefixWord ++ tailWord_5441657) baseStart_5441657 baseEnd_5441657 := by
    simpa [prefixWord, tailWord_5441657, baseEnd_5441657] using wordTrace_append hprefix tailTrace_5441657
  have hstable : (prefixWord ++ tailWord_5441657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5441657).length < 2 ^ (prefixWord ++ tailWord_5441657).sum := by decide
  have hdescent : baseEnd_5441657 < baseStart_5441657 := by decide
  rcases family_descends (prefixWord ++ tailWord_5441657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5441660 : List Nat := [2, 2, 2, 1, 1, 4, 1, 4, 6]
def baseStart_5441660 : Nat := 118140960795 + 5441660 * 2 ^ 59
def prefixEnd_5441660 : Nat := 4983230072969 + 3 ^ 40 * 5441660 * 2
def baseEnd_5441660 : Nat := 310465237593920523769363

theorem tailTrace_5441660 : CollatzResearch.WordTrace tailWord_5441660 prefixEnd_5441660 310465237593920523769363 := by
  unfold tailWord_5441660
  simp only [CollatzResearch.WordTrace]
  refine ⟨99236822732901328191429217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132315763643868437588572289 99236822732901328191429217)
  ·
    refine ⟨74427617049675996143571913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99236822732901328191429217 74427617049675996143571913)
    ·
      refine ⟨55820712787256997107678935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74427617049675996143571913 55820712787256997107678935)
      ·
        refine ⟨83731069180885495661518403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55820712787256997107678935 83731069180885495661518403)
        ·
          refine ⟨125596603771328243492277605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83731069180885495661518403 125596603771328243492277605)
          ·
            refine ⟨23549363207124045654802051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 125596603771328243492277605 23549363207124045654802051)
            ·
              refine ⟨35324044810686068482203077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23549363207124045654802051 35324044810686068482203077)
              ·
                refine ⟨6623258402003637840413077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35324044810686068482203077 6623258402003637840413077)
                ·
                  refine ⟨310465237593920523769363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6623258402003637840413077 310465237593920523769363)
                  ·
                    rfl

theorem cell23_5441660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 1, 4, 6].length) (baseStart_5441660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5441660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5441660 prefixEnd_5441660 := by exact prefixLift 5441660
  have htrace : WordTrace (prefixWord ++ tailWord_5441660) baseStart_5441660 baseEnd_5441660 := by
    simpa [prefixWord, tailWord_5441660, baseEnd_5441660] using wordTrace_append hprefix tailTrace_5441660
  have hstable : (prefixWord ++ tailWord_5441660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5441660).length < 2 ^ (prefixWord ++ tailWord_5441660).sum := by decide
  have hdescent : baseEnd_5441660 < baseStart_5441660 := by decide
  rcases family_descends (prefixWord ++ tailWord_5441660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5441683 : List Nat := [1, 1, 1, 2, 1, 2, 3, 1, 1, 3, 7]
def baseStart_5441683 : Nat := 118140960795 + 5441683 * 2 ^ 59
def prefixEnd_5441683 : Nat := 4983230072969 + 3 ^ 40 * 5441683 * 2
def baseEnd_5441683 : Nat := 2794198948400338123936661

theorem tailTrace_5441683 : CollatzResearch.WordTrace tailWord_5441683 prefixEnd_5441683 2794198948400338123936661 := by
  unfold tailWord_5441683
  simp only [CollatzResearch.WordTrace]
  refine ⟨198474484344719331310945703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132316322896479554207297135 198474484344719331310945703)
  ·
    refine ⟨297711726517078996966418555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198474484344719331310945703 297711726517078996966418555)
    ·
      refine ⟨446567589775618495449627833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 297711726517078996966418555 446567589775618495449627833)
      ·
        refine ⟨334925692331713871587220875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 446567589775618495449627833 334925692331713871587220875)
        ·
          refine ⟨502388538497570807380831313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 334925692331713871587220875 502388538497570807380831313)
          ·
            refine ⟨376791403873178105535623485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 502388538497570807380831313 376791403873178105535623485)
            ·
              refine ⟨141296776452441789575858807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 376791403873178105535623485 141296776452441789575858807)
              ·
                refine ⟨211945164678662684363788211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 141296776452441789575858807 211945164678662684363788211)
                ·
                  refine ⟨317917747017994026545682317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 211945164678662684363788211 317917747017994026545682317)
                  ·
                    refine ⟨119219155131747759954630869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 317917747017994026545682317 119219155131747759954630869)
                    ·
                      refine ⟨2794198948400338123936661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 119219155131747759954630869 2794198948400338123936661)
                      ·
                        rfl

theorem cell23_5441683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 1, 1, 3, 7].length) (baseStart_5441683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5441683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5441683 prefixEnd_5441683 := by exact prefixLift 5441683
  have htrace : WordTrace (prefixWord ++ tailWord_5441683) baseStart_5441683 baseEnd_5441683 := by
    simpa [prefixWord, tailWord_5441683, baseEnd_5441683] using wordTrace_append hprefix tailTrace_5441683
  have hstable : (prefixWord ++ tailWord_5441683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5441683).length < 2 ^ (prefixWord ++ tailWord_5441683).sum := by decide
  have hdescent : baseEnd_5441683 < baseStart_5441683 := by decide
  rcases family_descends (prefixWord ++ tailWord_5441683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5441767 : List Nat := [1, 1, 5, 3, 1, 3, 9]
def baseStart_5441767 : Nat := 118140960795 + 5441767 * 2 ^ 59
def prefixEnd_5441767 : Nat := 4983230072969 + 3 ^ 40 * 5441767 * 2
def baseEnd_5441767 : Nat := 34496815812040935744275

theorem tailTrace_5441767 : CollatzResearch.WordTrace tailWord_5441767 prefixEnd_5441767 34496815812040935744275 := by
  unfold tailWord_5441767
  simp only [CollatzResearch.WordTrace]
  refine ⟨198477548076415013657003555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132318365384276675771335703 198477548076415013657003555)
  ·
    refine ⟨297716322114622520485505333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198477548076415013657003555 297716322114622520485505333)
    ·
      refine ⟨27910905198245861295516125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 297716322114622520485505333 27910905198245861295516125)
      ·
        refine ⟨10466589449342197985818547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27910905198245861295516125 10466589449342197985818547)
        ·
          refine ⟨15699884174013296978727821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10466589449342197985818547 15699884174013296978727821)
          ·
            refine ⟨5887456565254986367022933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15699884174013296978727821 5887456565254986367022933)
            ·
              refine ⟨34496815812040935744275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5887456565254986367022933 34496815812040935744275)
              ·
                rfl

theorem cell23_5441767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 3, 9].length) (baseStart_5441767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5441767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5441767 prefixEnd_5441767 := by exact prefixLift 5441767
  have htrace : WordTrace (prefixWord ++ tailWord_5441767) baseStart_5441767 baseEnd_5441767 := by
    simpa [prefixWord, tailWord_5441767, baseEnd_5441767] using wordTrace_append hprefix tailTrace_5441767
  have hstable : (prefixWord ++ tailWord_5441767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5441767).length < 2 ^ (prefixWord ++ tailWord_5441767).sum := by decide
  have hdescent : baseEnd_5441767 < baseStart_5441767 := by decide
  rcases family_descends (prefixWord ++ tailWord_5441767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5441778 : List Nat := [3, 2, 1, 3, 2, 3, 1, 1, 3, 2, 2]
def baseStart_5441778 : Nat := 118140960795 + 5441778 * 2 ^ 59
def prefixEnd_5441778 : Nat := 4983230072969 + 3 ^ 40 * 5441778 * 2
def baseEnd_5441778 : Nat := 2794247729062515252248725

theorem tailTrace_5441778 : CollatzResearch.WordTrace tailWord_5441778 prefixEnd_5441778 2794247729062515252248725 := by
  unfold tailWord_5441778
  simp only [CollatzResearch.WordTrace]
  refine ⟨49619487319843790633913497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132318632852916775023769325 49619487319843790633913497)
  ·
    refine ⟨37214615489882842975435123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49619487319843790633913497 37214615489882842975435123)
    ·
      refine ⟨55821923234824264463152685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37214615489882842975435123 55821923234824264463152685)
      ·
        refine ⟨20933221213059099173682257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55821923234824264463152685 20933221213059099173682257)
        ·
          refine ⟨15699915909794324380261693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20933221213059099173682257 15699915909794324380261693)
          ·
            refine ⟨5887468466172871642598135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15699915909794324380261693 5887468466172871642598135)
            ·
              refine ⟨8831202699259307463897203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5887468466172871642598135 8831202699259307463897203)
              ·
                refine ⟨13246804048888961195845805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8831202699259307463897203 13246804048888961195845805)
                ·
                  refine ⟨4967551518333360448442177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13246804048888961195845805 4967551518333360448442177)
                  ·
                    refine ⟨3725663638750020336331633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4967551518333360448442177 3725663638750020336331633)
                    ·
                      refine ⟨2794247729062515252248725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3725663638750020336331633 2794247729062515252248725)
                      ·
                        rfl

theorem cell23_5441778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 3, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 3, 1, 1, 3, 2, 2].length) (baseStart_5441778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5441778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5441778 prefixEnd_5441778 := by exact prefixLift 5441778
  have htrace : WordTrace (prefixWord ++ tailWord_5441778) baseStart_5441778 baseEnd_5441778 := by
    simpa [prefixWord, tailWord_5441778, baseEnd_5441778] using wordTrace_append hprefix tailTrace_5441778
  have hstable : (prefixWord ++ tailWord_5441778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5441778).length < 2 ^ (prefixWord ++ tailWord_5441778).sum := by decide
  have hdescent : baseEnd_5441778 < baseStart_5441778 := by decide
  rcases family_descends (prefixWord ++ tailWord_5441778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5441804 : List Nat := [2, 2, 1, 2, 2, 2, 3, 1, 3, 3, 2]
def baseStart_5441804 : Nat := 118140960795 + 5441804 * 2 ^ 59
def prefixEnd_5441804 : Nat := 4983230072969 + 3 ^ 40 * 5441804 * 2
def baseEnd_5441804 : Nat := 2794261079559532150523605

theorem tailTrace_5441804 : CollatzResearch.WordTrace tailWord_5441804 prefixEnd_5441804 2794261079559532150523605 := by
  unfold tailWord_5441804
  simp only [CollatzResearch.WordTrace]
  refine ⟨99239448788640484488050233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132319265051520645984066977 99239448788640484488050233)
  ·
    refine ⟨74429586591480363366037675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99239448788640484488050233 74429586591480363366037675)
    ·
      refine ⟨111644379887220545049056513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74429586591480363366037675 111644379887220545049056513)
      ·
        refine ⟨83733284915415408786792385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111644379887220545049056513 83733284915415408786792385)
        ·
          refine ⟨62799963686561556590094289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83733284915415408786792385 62799963686561556590094289)
          ·
            refine ⟨47099972764921167442570717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62799963686561556590094289 47099972764921167442570717)
            ·
              refine ⟨17662489786845437790964019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47099972764921167442570717 17662489786845437790964019)
              ·
                refine ⟨26493734680268156686446029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17662489786845437790964019 26493734680268156686446029)
                ·
                  refine ⟨9935150505100558757417261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26493734680268156686446029 9935150505100558757417261)
                  ·
                    refine ⟨3725681439412709534031473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9935150505100558757417261 3725681439412709534031473)
                    ·
                      refine ⟨2794261079559532150523605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3725681439412709534031473 2794261079559532150523605)
                      ·
                        rfl

theorem cell23_5441804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 3, 1, 3, 3, 2].length) (baseStart_5441804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5441804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5441804 prefixEnd_5441804 := by exact prefixLift 5441804
  have htrace : WordTrace (prefixWord ++ tailWord_5441804) baseStart_5441804 baseEnd_5441804 := by
    simpa [prefixWord, tailWord_5441804, baseEnd_5441804] using wordTrace_append hprefix tailTrace_5441804
  have hstable : (prefixWord ++ tailWord_5441804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5441804).length < 2 ^ (prefixWord ++ tailWord_5441804).sum := by decide
  have hdescent : baseEnd_5441804 < baseStart_5441804 := by decide
  rcases family_descends (prefixWord ++ tailWord_5441804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5441844 : List Nat := [2, 5, 1, 1, 1, 3, 1, 1, 2, 6]
def baseStart_5441844 : Nat := 118140960795 + 5441844 * 2 ^ 59
def prefixEnd_5441844 : Nat := 4983230072969 + 3 ^ 40 * 5441844 * 2
def baseEnd_5441844 : Nat := 931427206261903998007807

theorem tailTrace_5441844 : CollatzResearch.WordTrace tailWord_5441844 prefixEnd_5441844 931427206261903998007807 := by
  unfold tailWord_5441844
  simp only [CollatzResearch.WordTrace]
  refine ⟨99240178248568027903778293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132320237664757370538371057 99240178248568027903778293)
  ·
    refine ⟨9303766710803252615979215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 99240178248568027903778293 9303766710803252615979215)
    ·
      refine ⟨13955650066204878923968823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9303766710803252615979215 13955650066204878923968823)
      ·
        refine ⟨20933475099307318385953235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13955650066204878923968823 20933475099307318385953235)
        ·
          refine ⟨31400212648960977578929853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20933475099307318385953235 31400212648960977578929853)
          ·
            refine ⟨11775079743360366592098695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31400212648960977578929853 11775079743360366592098695)
            ·
              refine ⟨17662619615040549888148043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11775079743360366592098695 17662619615040549888148043)
              ·
                refine ⟨26493929422560824832222065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17662619615040549888148043 26493929422560824832222065)
                ·
                  refine ⟨19870447066920618624166549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26493929422560824832222065 19870447066920618624166549)
                  ·
                    refine ⟨931427206261903998007807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19870447066920618624166549 931427206261903998007807)
                    ·
                      rfl

theorem cell23_5441844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 1, 1, 2, 6].length) (baseStart_5441844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5441844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5441844 prefixEnd_5441844 := by exact prefixLift 5441844
  have htrace : WordTrace (prefixWord ++ tailWord_5441844) baseStart_5441844 baseEnd_5441844 := by
    simpa [prefixWord, tailWord_5441844, baseEnd_5441844] using wordTrace_append hprefix tailTrace_5441844
  have hstable : (prefixWord ++ tailWord_5441844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5441844).length < 2 ^ (prefixWord ++ tailWord_5441844).sum := by decide
  have hdescent : baseEnd_5441844 < baseStart_5441844 := by decide
  rcases family_descends (prefixWord ++ tailWord_5441844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5441874 : List Nat := [3, 2, 2, 1, 1, 1, 3, 5, 5]
def baseStart_5441874 : Nat := 118140960795 + 5441874 * 2 ^ 59
def prefixEnd_5441874 : Nat := 4983230072969 + 3 ^ 40 * 5441874 * 2
def baseEnd_5441874 : Nat := 310477447022816319627587

theorem tailTrace_5441874 : CollatzResearch.WordTrace tailWord_5441874 prefixEnd_5441874 310477447022816319627587 := by
  unfold tailWord_5441874
  simp only [CollatzResearch.WordTrace]
  refine ⟨49620362671756842732787169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132320967124684913954099117 49620362671756842732787169)
  ·
    refine ⟨37215272003817632049590377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49620362671756842732787169 37215272003817632049590377)
    ·
      refine ⟨27911454002863224037192783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37215272003817632049590377 27911454002863224037192783)
      ·
        refine ⟨41867181004294836055789175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27911454002863224037192783 41867181004294836055789175)
        ·
          refine ⟨62800771506442254083683763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41867181004294836055789175 62800771506442254083683763)
          ·
            refine ⟨94201157259663381125525645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62800771506442254083683763 94201157259663381125525645)
            ·
              refine ⟨35325433972373767922072117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 94201157259663381125525645 35325433972373767922072117)
              ·
                refine ⟨3311759434910040742694261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 35325433972373767922072117 3311759434910040742694261)
                ·
                  refine ⟨310477447022816319627587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3311759434910040742694261 310477447022816319627587)
                  ·
                    rfl

theorem cell23_5441874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 3, 5, 5].length) (baseStart_5441874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5441874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5441874 prefixEnd_5441874 := by exact prefixLift 5441874
  have htrace : WordTrace (prefixWord ++ tailWord_5441874) baseStart_5441874 baseEnd_5441874 := by
    simpa [prefixWord, tailWord_5441874, baseEnd_5441874] using wordTrace_append hprefix tailTrace_5441874
  have hstable : (prefixWord ++ tailWord_5441874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5441874).length < 2 ^ (prefixWord ++ tailWord_5441874).sum := by decide
  have hdescent : baseEnd_5441874 < baseStart_5441874 := by decide
  rcases family_descends (prefixWord ++ tailWord_5441874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5441887 : List Nat := [1, 1, 2, 3, 1, 2, 2, 4, 2, 5]
def baseStart_5441887 : Nat := 118140960795 + 5441887 * 2 ^ 59
def prefixEnd_5441887 : Nat := 4983230072969 + 3 ^ 40 * 5441887 * 2
def baseEnd_5441887 : Nat := 931434566151285108595241

theorem tailTrace_5441887 : CollatzResearch.WordTrace tailWord_5441887 prefixEnd_5441887 931434566151285108595241 := by
  unfold tailWord_5441887
  simp only [CollatzResearch.WordTrace]
  refine ⟨198481924835980274151371915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132321283223986849434247943 198481924835980274151371915)
  ·
    refine ⟨297722887253970411227057873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198481924835980274151371915 297722887253970411227057873)
    ·
      refine ⟨223292165440477808420293405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 297722887253970411227057873 223292165440477808420293405)
      ·
        refine ⟨83734562040179178157610027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 223292165440477808420293405 83734562040179178157610027)
        ·
          refine ⟨125601843060268767236415041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83734562040179178157610027 125601843060268767236415041)
          ·
            refine ⟨94201382295201575427311281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 125601843060268767236415041 94201382295201575427311281)
            ·
              refine ⟨70651036721401181570483461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 94201382295201575427311281 70651036721401181570483461)
              ·
                refine ⟨13247069385262721544465649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 70651036721401181570483461 13247069385262721544465649)
                ·
                  refine ⟨9935302038947041158349237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13247069385262721544465649 9935302038947041158349237)
                  ·
                    refine ⟨931434566151285108595241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9935302038947041158349237 931434566151285108595241)
                    ·
                      rfl

theorem cell23_5441887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 4, 2, 5].length) (baseStart_5441887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5441887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5441887 prefixEnd_5441887 := by exact prefixLift 5441887
  have htrace : WordTrace (prefixWord ++ tailWord_5441887) baseStart_5441887 baseEnd_5441887 := by
    simpa [prefixWord, tailWord_5441887, baseEnd_5441887] using wordTrace_append hprefix tailTrace_5441887
  have hstable : (prefixWord ++ tailWord_5441887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5441887).length < 2 ^ (prefixWord ++ tailWord_5441887).sum := by decide
  have hdescent : baseEnd_5441887 < baseStart_5441887 := by decide
  rcases family_descends (prefixWord ++ tailWord_5441887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5441907 : List Nat := [1, 1, 1, 2, 2, 1, 2, 4, 4, 1, 4]
def baseStart_5441907 : Nat := 118140960795 + 5441907 * 2 ^ 59
def prefixEnd_5441907 : Nat := 4983230072969 + 3 ^ 40 * 5441907 * 2
def baseEnd_5441907 : Nat := 2794313968066945247535631

theorem tailTrace_5441907 : CollatzResearch.WordTrace tailWord_5441907 prefixEnd_5441907 2794313968066945247535631 := by
  unfold tailWord_5441907
  simp only [CollatzResearch.WordTrace]
  refine ⟨198482654295907817567099975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132321769530605211711399983 198482654295907817567099975)
  ·
    refine ⟨297723981443861726350649963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198482654295907817567099975 297723981443861726350649963)
    ·
      refine ⟨446585972165792589525974945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 297723981443861726350649963 446585972165792589525974945)
      ·
        refine ⟨334939479124344442144481209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 446585972165792589525974945 334939479124344442144481209)
        ·
          refine ⟨251204609343258331608360907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 334939479124344442144481209 251204609343258331608360907)
          ·
            refine ⟨376806914014887497412541361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 251204609343258331608360907 376806914014887497412541361)
            ·
              refine ⟨282605185511165623059406021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 376806914014887497412541361 282605185511165623059406021)
              ·
                refine ⟨52988472283343554323638629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 282605185511165623059406021 52988472283343554323638629)
                ·
                  refine ⟨9935338553126916435682243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 52988472283343554323638629 9935338553126916435682243)
                  ·
                    refine ⟨14903007829690374653523365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9935338553126916435682243 14903007829690374653523365)
                    ·
                      refine ⟨2794313968066945247535631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14903007829690374653523365 2794313968066945247535631)
                      ·
                        rfl

theorem cell23_5441907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 4, 4, 1, 4].length) (baseStart_5441907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5441907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5441907 prefixEnd_5441907 := by exact prefixLift 5441907
  have htrace : WordTrace (prefixWord ++ tailWord_5441907) baseStart_5441907 baseEnd_5441907 := by
    simpa [prefixWord, tailWord_5441907, baseEnd_5441907] using wordTrace_append hprefix tailTrace_5441907
  have hstable : (prefixWord ++ tailWord_5441907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5441907).length < 2 ^ (prefixWord ++ tailWord_5441907).sum := by decide
  have hdescent : baseEnd_5441907 < baseStart_5441907 := by decide
  rcases family_descends (prefixWord ++ tailWord_5441907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5441924 : List Nat := [2, 3, 2, 1, 1, 2, 2, 3, 2, 1, 4]
def baseStart_5441924 : Nat := 118140960795 + 5441924 * 2 ^ 59
def prefixEnd_5441924 : Nat := 4983230072969 + 3 ^ 40 * 5441924 * 2
def baseEnd_5441924 : Nat := 2794322697238071681023053

theorem tailTrace_5441924 : CollatzResearch.WordTrace tailWord_5441924 prefixEnd_5441924 2794322697238071681023053 := by
  unfold tailWord_5441924
  simp only [CollatzResearch.WordTrace]
  refine ⟨99241637168423114735234413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132322182891230819646979217 99241637168423114735234413)
  ·
    refine ⟨37215613938158668025712905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 99241637168423114735234413 37215613938158668025712905)
    ·
      refine ⟨27911710453619001019284679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37215613938158668025712905 27911710453619001019284679)
      ·
        refine ⟨41867565680428501528927019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27911710453619001019284679 41867565680428501528927019)
        ·
          refine ⟨62801348520642752293390529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41867565680428501528927019 62801348520642752293390529)
          ·
            refine ⟨47101011390482064220042897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62801348520642752293390529 47101011390482064220042897)
            ·
              refine ⟨35325758542861548165032173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47101011390482064220042897 35325758542861548165032173)
              ·
                refine ⟨13247159453573080561887065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35325758542861548165032173 13247159453573080561887065)
                ·
                  refine ⟨9935369590179810421415299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13247159453573080561887065 9935369590179810421415299)
                  ·
                    refine ⟨14903054385269715632122949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9935369590179810421415299 14903054385269715632122949)
                    ·
                      refine ⟨2794322697238071681023053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14903054385269715632122949 2794322697238071681023053)
                      ·
                        rfl

theorem cell23_5441924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 2, 3, 2, 1, 4].length) (baseStart_5441924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5441924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5441924 prefixEnd_5441924 := by exact prefixLift 5441924
  have htrace : WordTrace (prefixWord ++ tailWord_5441924) baseStart_5441924 baseEnd_5441924 := by
    simpa [prefixWord, tailWord_5441924, baseEnd_5441924] using wordTrace_append hprefix tailTrace_5441924
  have hstable : (prefixWord ++ tailWord_5441924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5441924).length < 2 ^ (prefixWord ++ tailWord_5441924).sum := by decide
  have hdescent : baseEnd_5441924 < baseStart_5441924 := by decide
  rcases family_descends (prefixWord ++ tailWord_5441924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5441942 : List Nat := [5, 3, 1, 2, 2, 1, 1, 1, 7]
def baseStart_5441942 : Nat := 118140960795 + 5441942 * 2 ^ 59
def prefixEnd_5441942 : Nat := 4983230072969 + 3 ^ 40 * 5441942 * 2
def baseEnd_5441942 : Nat := 310481326654428067844219

theorem tailTrace_5441942 : CollatzResearch.WordTrace tailWord_5441942 prefixEnd_5441942 310481326654428067844219 := by
  unfold tailWord_5441942
  simp only [CollatzResearch.WordTrace]
  refine ⟨12405245678173813659039005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 132322620567187345696416053 12405245678173813659039005)
  ·
    refine ⟨4651967129315180122139627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12405245678173813659039005 4651967129315180122139627)
    ·
      refine ⟨6977950693972770183209441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4651967129315180122139627 6977950693972770183209441)
      ·
        refine ⟨5233463020479577637407081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6977950693972770183209441 5233463020479577637407081)
        ·
          refine ⟨3925097265359683228055311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5233463020479577637407081 3925097265359683228055311)
          ·
            refine ⟨5887645898039524842082967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3925097265359683228055311 5887645898039524842082967)
            ·
              refine ⟨8831468847059287263124451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5887645898039524842082967 8831468847059287263124451)
              ·
                refine ⟨13247203270588930894686677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8831468847059287263124451 13247203270588930894686677)
                ·
                  refine ⟨310481326654428067844219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13247203270588930894686677 310481326654428067844219)
                  ·
                    rfl

theorem cell23_5441942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 2, 1, 1, 1, 7].length) (baseStart_5441942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5441942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5441942 prefixEnd_5441942 := by exact prefixLift 5441942
  have htrace : WordTrace (prefixWord ++ tailWord_5441942) baseStart_5441942 baseEnd_5441942 := by
    simpa [prefixWord, tailWord_5441942, baseEnd_5441942] using wordTrace_append hprefix tailTrace_5441942
  have hstable : (prefixWord ++ tailWord_5441942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5441942).length < 2 ^ (prefixWord ++ tailWord_5441942).sum := by decide
  have hdescent : baseEnd_5441942 < baseStart_5441942 := by decide
  rcases family_descends (prefixWord ++ tailWord_5441942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5442024 : List Nat := [2, 1, 4, 1, 1, 3, 1, 3, 1, 6]
def baseStart_5442024 : Nat := 118140960795 + 5442024 * 2 ^ 59
def prefixEnd_5442024 : Nat := 4983230072969 + 3 ^ 40 * 5442024 * 2
def baseEnd_5442024 : Nat := 931458015101173763257531

theorem tailTrace_5442024 : CollatzResearch.WordTrace tailWord_5442024 prefixEnd_5442024 931458015101173763257531 := by
  unfold tailWord_5442024
  simp only [CollatzResearch.WordTrace]
  refine ⟨99243460818241973274554563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132324614424322631032739417 99243460818241973274554563)
  ·
    refine ⟨148865191227362959911831845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99243460818241973274554563 148865191227362959911831845)
    ·
      refine ⟨27912223355130554983468471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 148865191227362959911831845 27912223355130554983468471)
      ·
        refine ⟨41868335032695832475202707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27912223355130554983468471 41868335032695832475202707)
        ·
          refine ⟨62802502549043748712804061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41868335032695832475202707 62802502549043748712804061)
          ·
            refine ⟨23550938455891405767301523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62802502549043748712804061 23550938455891405767301523)
            ·
              refine ⟨35326407683837108650952285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23550938455891405767301523 35326407683837108650952285)
              ·
                refine ⟨13247402881438915744107107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35326407683837108650952285 13247402881438915744107107)
                ·
                  refine ⟨19871104322158373616160661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13247402881438915744107107 19871104322158373616160661)
                  ·
                    refine ⟨931458015101173763257531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19871104322158373616160661 931458015101173763257531)
                    ·
                      rfl

theorem cell23_5442024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 1, 3, 1, 6].length) (baseStart_5442024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5442024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5442024 prefixEnd_5442024 := by exact prefixLift 5442024
  have htrace : WordTrace (prefixWord ++ tailWord_5442024) baseStart_5442024 baseEnd_5442024 := by
    simpa [prefixWord, tailWord_5442024, baseEnd_5442024] using wordTrace_append hprefix tailTrace_5442024
  have hstable : (prefixWord ++ tailWord_5442024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5442024).length < 2 ^ (prefixWord ++ tailWord_5442024).sum := by decide
  have hdescent : baseEnd_5442024 < baseStart_5442024 := by decide
  rcases family_descends (prefixWord ++ tailWord_5442024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5442051 : List Nat := [1, 1, 1, 3, 2, 1, 5, 3, 1, 2, 3]
def baseStart_5442051 : Nat := 118140960795 + 5442051 * 2 ^ 59
def prefixEnd_5442051 : Nat := 4983230072969 + 3 ^ 40 * 5442051 * 2
def baseEnd_5442051 : Nat := 2794387909281192684134969

theorem tailTrace_5442051 : CollatzResearch.WordTrace tailWord_5442051 prefixEnd_5442051 2794387909281192684134969 := by
  unfold tailWord_5442051
  simp only [CollatzResearch.WordTrace]
  refine ⟨198487906407386130160342007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132325270938257420106894671 198487906407386130160342007)
  ·
    refine ⟨297731859611079195240513011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198487906407386130160342007 297731859611079195240513011)
    ·
      refine ⟨446597789416618792860769517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 297731859611079195240513011 446597789416618792860769517)
      ·
        refine ⟨167474171031232047322788569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 446597789416618792860769517 167474171031232047322788569)
        ·
          refine ⟨125605628273424035492091427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 167474171031232047322788569 125605628273424035492091427)
          ·
            refine ⟨188408442410136053238137141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 125605628273424035492091427 188408442410136053238137141)
            ·
              refine ⟨17663291475950254991075357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 188408442410136053238137141 17663291475950254991075357)
              ·
                refine ⟨6623734303481345621653259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17663291475950254991075357 6623734303481345621653259)
                ·
                  refine ⟨9935601455222018432479889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6623734303481345621653259 9935601455222018432479889)
                  ·
                    refine ⟨7451701091416513824359917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9935601455222018432479889 7451701091416513824359917)
                    ·
                      refine ⟨2794387909281192684134969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7451701091416513824359917 2794387909281192684134969)
                      ·
                        rfl

theorem cell23_5442051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 5, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 5, 3, 1, 2, 3].length) (baseStart_5442051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5442051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5442051 prefixEnd_5442051 := by exact prefixLift 5442051
  have htrace : WordTrace (prefixWord ++ tailWord_5442051) baseStart_5442051 baseEnd_5442051 := by
    simpa [prefixWord, tailWord_5442051, baseEnd_5442051] using wordTrace_append hprefix tailTrace_5442051
  have hstable : (prefixWord ++ tailWord_5442051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5442051).length < 2 ^ (prefixWord ++ tailWord_5442051).sum := by decide
  have hdescent : baseEnd_5442051 < baseStart_5442051 := by decide
  rcases family_descends (prefixWord ++ tailWord_5442051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5442068 : List Nat := [2, 4, 3, 1, 1, 2, 1, 2, 1, 1, 5]
def baseStart_5442068 : Nat := 118140960795 + 5442068 * 2 ^ 59
def prefixEnd_5442068 : Nat := 4983230072969 + 3 ^ 40 * 5442068 * 2
def baseEnd_5442068 : Nat := 2794396638452319117622391

theorem tailTrace_5442068 : CollatzResearch.WordTrace tailWord_5442068 prefixEnd_5442068 2794396638452319117622391 := by
  unfold tailWord_5442068
  simp only [CollatzResearch.WordTrace]
  refine ⟨99244263224162271031855429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132325684298883028042473905 99244263224162271031855429)
  ·
    refine ⟨18608299354530425818472893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 99244263224162271031855429 18608299354530425818472893)
    ·
      refine ⟨6978112257948909681927335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18608299354530425818472893 6978112257948909681927335)
      ·
        refine ⟨10467168386923364522891003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6978112257948909681927335 10467168386923364522891003)
        ·
          refine ⟨15700752580385046784336505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10467168386923364522891003 15700752580385046784336505)
          ·
            refine ⟨11775564435288785088252379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15700752580385046784336505 11775564435288785088252379)
            ·
              refine ⟨17663346652933177632378569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11775564435288785088252379 17663346652933177632378569)
              ·
                refine ⟨13247509989699883224283927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17663346652933177632378569 13247509989699883224283927)
                ·
                  refine ⟨19871264984549824836425891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13247509989699883224283927 19871264984549824836425891)
                  ·
                    refine ⟨29806897476824737254638837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19871264984549824836425891 29806897476824737254638837)
                    ·
                      refine ⟨2794396638452319117622391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29806897476824737254638837 2794396638452319117622391)
                      ·
                        rfl

theorem cell23_5442068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 1, 2, 1, 1, 5].length) (baseStart_5442068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5442068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5442068 prefixEnd_5442068 := by exact prefixLift 5442068
  have htrace : WordTrace (prefixWord ++ tailWord_5442068) baseStart_5442068 baseEnd_5442068 := by
    simpa [prefixWord, tailWord_5442068, baseEnd_5442068] using wordTrace_append hprefix tailTrace_5442068
  have hstable : (prefixWord ++ tailWord_5442068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5442068).length < 2 ^ (prefixWord ++ tailWord_5442068).sum := by decide
  have hdescent : baseEnd_5442068 < baseStart_5442068 := by decide
  rcases family_descends (prefixWord ++ tailWord_5442068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5442088 : List Nat := [2, 1, 5, 2, 1, 3, 2, 7]
def baseStart_5442088 : Nat := 118140960795 + 5442088 * 2 ^ 59
def prefixEnd_5442088 : Nat := 4983230072969 + 3 ^ 40 * 5442088 * 2
def baseEnd_5442088 : Nat := 103496552150570705161937

theorem tailTrace_5442088 : CollatzResearch.WordTrace tailWord_5442088 prefixEnd_5442088 103496552150570705161937 := by
  unfold tailWord_5442088
  simp only [CollatzResearch.WordTrace]
  refine ⟨99244627954126042739719459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132326170605501390319625945 99244627954126042739719459)
  ·
    refine ⟨148866941931189064109579189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99244627954126042739719459 148866941931189064109579189)
    ·
      refine ⟨13956275806048974760273049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 148866941931189064109579189 13956275806048974760273049)
      ·
        refine ⟨10467206854536731070204787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13956275806048974760273049 10467206854536731070204787)
        ·
          refine ⟨15700810281805096605307181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10467206854536731070204787 15700810281805096605307181)
          ·
            refine ⟨5887803855676911226990193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15700810281805096605307181 5887803855676911226990193)
            ·
              refine ⟨4415852891757683420242645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5887803855676911226990193 4415852891757683420242645)
              ·
                refine ⟨103496552150570705161937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4415852891757683420242645 103496552150570705161937)
                ·
                  rfl

theorem cell23_5442088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 3, 2, 7].length) (baseStart_5442088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5442088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5442088 prefixEnd_5442088 := by exact prefixLift 5442088
  have htrace : WordTrace (prefixWord ++ tailWord_5442088) baseStart_5442088 baseEnd_5442088 := by
    simpa [prefixWord, tailWord_5442088, baseEnd_5442088] using wordTrace_append hprefix tailTrace_5442088
  have hstable : (prefixWord ++ tailWord_5442088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5442088).length < 2 ^ (prefixWord ++ tailWord_5442088).sum := by decide
  have hdescent : baseEnd_5442088 < baseStart_5442088 := by decide
  rcases family_descends (prefixWord ++ tailWord_5442088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5442091 : List Nat := [1, 1, 1, 1, 2, 1, 3, 5, 3, 3, 2]
def baseStart_5442091 : Nat := 118140960795 + 5442091 * 2 ^ 59
def prefixEnd_5442091 : Nat := 4983230072969 + 3 ^ 40 * 5442091 * 2
def baseEnd_5442091 : Nat := 2794408448507372527634785

theorem tailTrace_5442091 : CollatzResearch.WordTrace tailWord_5442091 prefixEnd_5442091 2794408448507372527634785 := by
  unfold tailWord_5442091
  simp only [CollatzResearch.WordTrace]
  refine ⟨198489365327241216991798127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132326243551494144661198751 198489365327241216991798127)
  ·
    refine ⟨297734047990861825487697191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198489365327241216991798127 297734047990861825487697191)
    ·
      refine ⟨446601071986292738231545787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 297734047990861825487697191 446601071986292738231545787)
      ·
        refine ⟨669901607979439107347318681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 446601071986292738231545787 669901607979439107347318681)
        ·
          refine ⟨502426205984579330510489011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 669901607979439107347318681 502426205984579330510489011)
          ·
            refine ⟨753639308976868995765733517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 502426205984579330510489011 753639308976868995765733517)
            ·
              refine ⟨282614740866325873412150069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 753639308976868995765733517 282614740866325873412150069)
              ·
                refine ⟨26495131956218050632389069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 282614740866325873412150069 26495131956218050632389069)
                ·
                  refine ⟨9935674483581768987145901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26495131956218050632389069 9935674483581768987145901)
                  ·
                    refine ⟨3725877931343163370179713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9935674483581768987145901 3725877931343163370179713)
                    ·
                      refine ⟨2794408448507372527634785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3725877931343163370179713 2794408448507372527634785)
                      ·
                        rfl

theorem cell23_5442091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 5, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 5, 3, 3, 2].length) (baseStart_5442091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5442091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5442091 prefixEnd_5442091 := by exact prefixLift 5442091
  have htrace : WordTrace (prefixWord ++ tailWord_5442091) baseStart_5442091 baseEnd_5442091 := by
    simpa [prefixWord, tailWord_5442091, baseEnd_5442091] using wordTrace_append hprefix tailTrace_5442091
  have hstable : (prefixWord ++ tailWord_5442091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5442091).length < 2 ^ (prefixWord ++ tailWord_5442091).sum := by decide
  have hdescent : baseEnd_5442091 < baseStart_5442091 := by decide
  rcases family_descends (prefixWord ++ tailWord_5442091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5442093 : List Nat := [1, 5, 4, 1, 2, 1, 1, 3, 1, 1, 3]
def baseStart_5442093 : Nat := 118140960795 + 5442093 * 2 ^ 59
def prefixEnd_5442093 : Nat := 4983230072969 + 3 ^ 40 * 5442093 * 2
def baseEnd_5442093 : Nat := 2794409475468681519809777

theorem tailTrace_5442093 : CollatzResearch.WordTrace tailWord_5442093 prefixEnd_5442093 2794409475468681519809777 := by
  unfold tailWord_5442093
  simp only [CollatzResearch.WordTrace]
  refine ⟨198489438273233971333370933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132326292182155980888913955 198489438273233971333370933)
  ·
    refine ⟨18608384838115684812503525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 198489438273233971333370933 18608384838115684812503525)
    ·
      refine ⟨3489072157146690902344411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18608384838115684812503525 3489072157146690902344411)
      ·
        refine ⟨5233608235720036353516617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3489072157146690902344411 5233608235720036353516617)
        ·
          refine ⟨3925206176790027265137463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5233608235720036353516617 3925206176790027265137463)
          ·
            refine ⟨5887809265185040897706195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3925206176790027265137463 5887809265185040897706195)
            ·
              refine ⟨8831713897777561346559293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5887809265185040897706195 8831713897777561346559293)
              ·
                refine ⟨3311892711666585504959735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8831713897777561346559293 3311892711666585504959735)
                ·
                  refine ⟨4967839067499878257439603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3311892711666585504959735 4967839067499878257439603)
                  ·
                    refine ⟨7451758601249817386159405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4967839067499878257439603 7451758601249817386159405)
                    ·
                      refine ⟨2794409475468681519809777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7451758601249817386159405 2794409475468681519809777)
                      ·
                        rfl

theorem cell23_5442093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 2, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 2, 1, 1, 3, 1, 1, 3].length) (baseStart_5442093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5442093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5442093 prefixEnd_5442093 := by exact prefixLift 5442093
  have htrace : WordTrace (prefixWord ++ tailWord_5442093) baseStart_5442093 baseEnd_5442093 := by
    simpa [prefixWord, tailWord_5442093, baseEnd_5442093] using wordTrace_append hprefix tailTrace_5442093
  have hstable : (prefixWord ++ tailWord_5442093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5442093).length < 2 ^ (prefixWord ++ tailWord_5442093).sum := by decide
  have hdescent : baseEnd_5442093 < baseStart_5442093 := by decide
  rcases family_descends (prefixWord ++ tailWord_5442093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5442116 : List Nat := [2, 3, 5, 1, 1, 2, 1, 1, 3, 2, 2]
def baseStart_5442116 : Nat := 118140960795 + 5442116 * 2 ^ 59
def prefixEnd_5442116 : Nat := 4983230072969 + 3 ^ 40 * 5442116 * 2
def baseEnd_5442116 : Nat := 2794421285523734929822171

theorem tailTrace_5442116 : CollatzResearch.WordTrace tailWord_5442116 prefixEnd_5442116 2794421285523734929822171 := by
  unfold tailWord_5442116
  simp only [CollatzResearch.WordTrace]
  refine ⟨99245138576075323130729101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132326851434767097507638801 99245138576075323130729101)
  ·
    refine ⟨37216926966028246174023413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 99245138576075323130729101 37216926966028246174023413)
    ·
      refine ⟨3489086903065148078814695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 37216926966028246174023413 3489086903065148078814695)
      ·
        refine ⟨5233630354597722118222043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3489086903065148078814695 5233630354597722118222043)
        ·
          refine ⟨7850445531896583177333065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5233630354597722118222043 7850445531896583177333065)
          ·
            refine ⟨5887834148922437382999799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7850445531896583177333065 5887834148922437382999799)
            ·
              refine ⟨8831751223383656074499699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5887834148922437382999799 8831751223383656074499699)
              ·
                refine ⟨13247626835075484111749549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8831751223383656074499699 13247626835075484111749549)
                ·
                  refine ⟨4967860063153306541906081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13247626835075484111749549 4967860063153306541906081)
                  ·
                    refine ⟨3725895047364979906429561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4967860063153306541906081 3725895047364979906429561)
                    ·
                      refine ⟨2794421285523734929822171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3725895047364979906429561 2794421285523734929822171)
                      ·
                        rfl

theorem cell23_5442116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 2, 1, 1, 3, 2, 2].length) (baseStart_5442116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5442116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5442116 prefixEnd_5442116 := by exact prefixLift 5442116
  have htrace : WordTrace (prefixWord ++ tailWord_5442116) baseStart_5442116 baseEnd_5442116 := by
    simpa [prefixWord, tailWord_5442116, baseEnd_5442116] using wordTrace_append hprefix tailTrace_5442116
  have hstable : (prefixWord ++ tailWord_5442116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5442116).length < 2 ^ (prefixWord ++ tailWord_5442116).sum := by decide
  have hdescent : baseEnd_5442116 < baseStart_5442116 := by decide
  rcases family_descends (prefixWord ++ tailWord_5442116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5442124 : List Nat := [2, 2, 1, 3, 1, 2, 1, 2, 1, 3, 5]
def baseStart_5442124 : Nat := 118140960795 + 5442124 * 2 ^ 59
def prefixEnd_5442124 : Nat := 4983230072969 + 3 ^ 40 * 5442124 * 2
def baseEnd_5442124 : Nat := 2794425393368970898522133

theorem tailTrace_5442124 : CollatzResearch.WordTrace tailWord_5442124 prefixEnd_5442124 2794425393368970898522133 := by
  unfold tailWord_5442124
  simp only [CollatzResearch.WordTrace]
  refine ⟨99245284468060831813874713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132327045957414442418499617 99245284468060831813874713)
  ·
    refine ⟨74433963351045623860406035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99245284468060831813874713 74433963351045623860406035)
    ·
      refine ⟨111650945026568435790609053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74433963351045623860406035 111650945026568435790609053)
      ·
        refine ⟨41869104384963163421478395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 111650945026568435790609053 41869104384963163421478395)
        ·
          refine ⟨62803656577444745132217593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41869104384963163421478395 62803656577444745132217593)
          ·
            refine ⟨47102742433083558849163195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62803656577444745132217593 47102742433083558849163195)
            ·
              refine ⟨70654113649625338273744793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47102742433083558849163195 70654113649625338273744793)
              ·
                refine ⟨52990585237219003705308595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 70654113649625338273744793 52990585237219003705308595)
                ·
                  refine ⟨79485877855828505557962893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52990585237219003705308595 79485877855828505557962893)
                  ·
                    refine ⟨29807204195935689584236085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 79485877855828505557962893 29807204195935689584236085)
                    ·
                      refine ⟨2794425393368970898522133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29807204195935689584236085 2794425393368970898522133)
                      ·
                        rfl

theorem cell23_5442124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 2, 1, 3, 5].length) (baseStart_5442124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5442124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5442124 prefixEnd_5442124 := by exact prefixLift 5442124
  have htrace : WordTrace (prefixWord ++ tailWord_5442124) baseStart_5442124 baseEnd_5442124 := by
    simpa [prefixWord, tailWord_5442124, baseEnd_5442124] using wordTrace_append hprefix tailTrace_5442124
  have hstable : (prefixWord ++ tailWord_5442124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5442124).length < 2 ^ (prefixWord ++ tailWord_5442124).sum := by decide
  have hdescent : baseEnd_5442124 < baseStart_5442124 := by decide
  rcases family_descends (prefixWord ++ tailWord_5442124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5442132 : List Nat := [2, 4, 1, 1, 1, 5, 2, 1, 2, 1, 3]
def baseStart_5442132 : Nat := 118140960795 + 5442132 * 2 ^ 59
def prefixEnd_5442132 : Nat := 4983230072969 + 3 ^ 40 * 5442132 * 2
def baseEnd_5442132 : Nat := 2794429501214206867222097

theorem tailTrace_5442132 : CollatzResearch.WordTrace tailWord_5442132 prefixEnd_5442132 2794429501214206867222097 := by
  unfold tailWord_5442132
  simp only [CollatzResearch.WordTrace]
  refine ⟨99245430360046340497020325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132327240480061787329360433 99245430360046340497020325)
  ·
    refine ⟨18608518192508688843191311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 99245430360046340497020325 18608518192508688843191311)
    ·
      refine ⟨27912777288763033264786967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18608518192508688843191311 27912777288763033264786967)
      ·
        refine ⟨41869165933144549897180451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27912777288763033264786967 41869165933144549897180451)
        ·
          refine ⟨62803748899716824845770677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41869165933144549897180451 62803748899716824845770677)
          ·
            refine ⟨5887851459348452329291001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 62803748899716824845770677 5887851459348452329291001)
            ·
              refine ⟨4415888594511339246968251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5887851459348452329291001 4415888594511339246968251)
              ·
                refine ⟨6623832891767008870452377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4415888594511339246968251 6623832891767008870452377)
                ·
                  refine ⟨4967874668825256652839283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6623832891767008870452377 4967874668825256652839283)
                  ·
                    refine ⟨7451812003237884979258925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4967874668825256652839283 7451812003237884979258925)
                    ·
                      refine ⟨2794429501214206867222097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7451812003237884979258925 2794429501214206867222097)
                      ·
                        rfl

theorem cell23_5442132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 5, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 5, 2, 1, 2, 1, 3].length) (baseStart_5442132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5442132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5442132 prefixEnd_5442132 := by exact prefixLift 5442132
  have htrace : WordTrace (prefixWord ++ tailWord_5442132) baseStart_5442132 baseEnd_5442132 := by
    simpa [prefixWord, tailWord_5442132, baseEnd_5442132] using wordTrace_append hprefix tailTrace_5442132
  have hstable : (prefixWord ++ tailWord_5442132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5442132).length < 2 ^ (prefixWord ++ tailWord_5442132).sum := by decide
  have hdescent : baseEnd_5442132 < baseStart_5442132 := by decide
  rcases family_descends (prefixWord ++ tailWord_5442132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5442144 : List Nat := [2, 1, 1, 3, 2, 1, 2, 4, 7]
def baseStart_5442144 : Nat := 118140960795 + 5442144 * 2 ^ 59
def prefixEnd_5442144 : Nat := 4983230072969 + 3 ^ 40 * 5442144 * 2
def baseEnd_5442144 : Nat := 310492851442451202252449

theorem tailTrace_5442144 : CollatzResearch.WordTrace tailWord_5442144 prefixEnd_5442144 310492851442451202252449 := by
  unfold tailWord_5442144
  simp only [CollatzResearch.WordTrace]
  refine ⟨99245649198024603521738743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132327532264032804695651657 99245649198024603521738743)
  ·
    refine ⟨148868473797036905282608115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99245649198024603521738743 148868473797036905282608115)
    ·
      refine ⟨223302710695555357923912173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148868473797036905282608115 223302710695555357923912173)
      ·
        refine ⟨83738516510833259221467065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 223302710695555357923912173 83738516510833259221467065)
        ·
          refine ⟨62803887383124944416100299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83738516510833259221467065 62803887383124944416100299)
          ·
            refine ⟨94205831074687416624150449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62803887383124944416100299 94205831074687416624150449)
            ·
              refine ⟨70654373306015562468112837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 94205831074687416624150449 70654373306015562468112837)
              ·
                refine ⟨13247694994877917962771157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 70654373306015562468112837 13247694994877917962771157)
                ·
                  refine ⟨310492851442451202252449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13247694994877917962771157 310492851442451202252449)
                  ·
                    rfl

theorem cell23_5442144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 4, 7].length) (baseStart_5442144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5442144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5442144 prefixEnd_5442144 := by exact prefixLift 5442144
  have htrace : WordTrace (prefixWord ++ tailWord_5442144) baseStart_5442144 baseEnd_5442144 := by
    simpa [prefixWord, tailWord_5442144, baseEnd_5442144] using wordTrace_append hprefix tailTrace_5442144
  have hstable : (prefixWord ++ tailWord_5442144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5442144).length < 2 ^ (prefixWord ++ tailWord_5442144).sum := by decide
  have hdescent : baseEnd_5442144 < baseStart_5442144 := by decide
  rcases family_descends (prefixWord ++ tailWord_5442144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5442211 : List Nat := [1, 1, 1, 4, 1, 1, 2, 5, 2, 1, 4]
def baseStart_5442211 : Nat := 118140960795 + 5442211 * 2 ^ 59
def prefixEnd_5442211 : Nat := 4983230072969 + 3 ^ 40 * 5442211 * 2
def baseEnd_5442211 : Nat := 2794470066185912058134233

theorem tailTrace_5442211 : CollatzResearch.WordTrace tailWord_5442211 prefixEnd_5442211 2794470066185912058134233 := by
  unfold tailWord_5442211
  simp only [CollatzResearch.WordTrace]
  refine ⟨198493742086806477486166487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132329161391204318324110991 198493742086806477486166487)
  ·
    refine ⟨297740613130209716229249731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198493742086806477486166487 297740613130209716229249731)
    ·
      refine ⟨446610919695314574343874597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 297740613130209716229249731 446610919695314574343874597)
      ·
        refine ⟨83739547442871482689476487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 446610919695314574343874597 83739547442871482689476487)
        ·
          refine ⟨125609321164307224034214731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83739547442871482689476487 125609321164307224034214731)
          ·
            refine ⟨188413981746460836051322097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 125609321164307224034214731 188413981746460836051322097)
            ·
              refine ⟨141310486309845627038491573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 188413981746460836051322097 141310486309845627038491573)
              ·
                refine ⟨13247858091548027534858585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 141310486309845627038491573 13247858091548027534858585)
                ·
                  refine ⟨9935893568661020651143939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13247858091548027534858585 9935893568661020651143939)
                  ·
                    refine ⟨14903840352991530976715909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9935893568661020651143939 14903840352991530976715909)
                    ·
                      refine ⟨2794470066185912058134233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14903840352991530976715909 2794470066185912058134233)
                      ·
                        rfl

theorem cell23_5442211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 5, 2, 1, 4].length) (baseStart_5442211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5442211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5442211 prefixEnd_5442211 := by exact prefixLift 5442211
  have htrace : WordTrace (prefixWord ++ tailWord_5442211) baseStart_5442211 baseEnd_5442211 := by
    simpa [prefixWord, tailWord_5442211, baseEnd_5442211] using wordTrace_append hprefix tailTrace_5442211
  have hstable : (prefixWord ++ tailWord_5442211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5442211).length < 2 ^ (prefixWord ++ tailWord_5442211).sum := by decide
  have hdescent : baseEnd_5442211 < baseStart_5442211 := by decide
  rcases family_descends (prefixWord ++ tailWord_5442211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5442268 : List Nat := [2, 2, 5, 1, 1, 1, 1, 2, 8]
def baseStart_5442268 : Nat := 118140960795 + 5442268 * 2 ^ 59
def prefixEnd_5442268 : Nat := 4983230072969 + 3 ^ 40 * 5442268 * 2
def baseEnd_5442268 : Nat := 310499926064802037235719

theorem tailTrace_5442268 : CollatzResearch.WordTrace tailWord_5442268 prefixEnd_5442268 310499926064802037235719 := by
  unfold tailWord_5442268
  simp only [CollatzResearch.WordTrace]
  refine ⟨99247910523799988110495729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132330547365066650813994305 99247910523799988110495729)
  ·
    refine ⟨74435932892849991082871797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99247910523799988110495729 74435932892849991082871797)
    ·
      refine ⟨6978368708704686664019231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 74435932892849991082871797 6978368708704686664019231)
      ·
        refine ⟨10467553063057029996028847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6978368708704686664019231 10467553063057029996028847)
        ·
          refine ⟨15701329594585544994043271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10467553063057029996028847 15701329594585544994043271)
          ·
            refine ⟨23551994391878317491064907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15701329594585544994043271 23551994391878317491064907)
            ·
              refine ⟨35327991587817476236597361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23551994391878317491064907 35327991587817476236597361)
              ·
                refine ⟨26495993690863107177448021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35327991587817476236597361 26495993690863107177448021)
                ·
                  refine ⟨310499926064802037235719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 26495993690863107177448021 310499926064802037235719)
                  ·
                    rfl

theorem cell23_5442268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 1, 2, 8].length) (baseStart_5442268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5442268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5442268 prefixEnd_5442268 := by exact prefixLift 5442268
  have htrace : WordTrace (prefixWord ++ tailWord_5442268) baseStart_5442268 baseEnd_5442268 := by
    simpa [prefixWord, tailWord_5442268, baseEnd_5442268] using wordTrace_append hprefix tailTrace_5442268
  have hstable : (prefixWord ++ tailWord_5442268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5442268).length < 2 ^ (prefixWord ++ tailWord_5442268).sum := by decide
  have hdescent : baseEnd_5442268 < baseStart_5442268 := by decide
  rcases family_descends (prefixWord ++ tailWord_5442268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5442302 : List Nat := [4, 2, 2, 1, 2, 3, 2, 1, 6]
def baseStart_5442302 : Nat := 118140960795 + 5442302 * 2 ^ 59
def prefixEnd_5442302 : Nat := 4983230072969 + 3 ^ 40 * 5442302 * 2
def baseEnd_5442302 : Nat := 310501865880607911344035

theorem tailTrace_5442302 : CollatzResearch.WordTrace tailWord_5442302 prefixEnd_5442302 310501865880607911344035 := by
  unfold tailWord_5442302
  simp only [CollatzResearch.WordTrace]
  refine ⟨24812132641184600003466145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 132331374086317866685152773 24812132641184600003466145)
  ·
    refine ⟨18609099480888450002599609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24812132641184600003466145 18609099480888450002599609)
    ·
      refine ⟨13956824610666337501949707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18609099480888450002599609 13956824610666337501949707)
      ·
        refine ⟨20935236915999506252924561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13956824610666337501949707 20935236915999506252924561)
        ·
          refine ⟨15701427686999629689693421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20935236915999506252924561 15701427686999629689693421)
          ·
            refine ⟨5888035382624861133635033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15701427686999629689693421 5888035382624861133635033)
            ·
              refine ⟨4416026536968645850226275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5888035382624861133635033 4416026536968645850226275)
              ·
                refine ⟨6624039805452968775339413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4416026536968645850226275 6624039805452968775339413)
                ·
                  refine ⟨310501865880607911344035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6624039805452968775339413 310501865880607911344035)
                  ·
                    rfl

theorem cell23_5442302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 3, 2, 1, 6].length) (baseStart_5442302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5442302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5442302 prefixEnd_5442302 := by exact prefixLift 5442302
  have htrace : WordTrace (prefixWord ++ tailWord_5442302) baseStart_5442302 baseEnd_5442302 := by
    simpa [prefixWord, tailWord_5442302, baseEnd_5442302] using wordTrace_append hprefix tailTrace_5442302
  have hstable : (prefixWord ++ tailWord_5442302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5442302).length < 2 ^ (prefixWord ++ tailWord_5442302).sum := by decide
  have hdescent : baseEnd_5442302 < baseStart_5442302 := by decide
  rcases family_descends (prefixWord ++ tailWord_5442302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5442321 : List Nat := [1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 5]
def baseStart_5442321 : Nat := 118140960795 + 5442321 * 2 ^ 59
def prefixEnd_5442321 : Nat := 4983230072969 + 3 ^ 40 * 5442321 * 2
def baseEnd_5442321 : Nat := 2794526549057906627758727

theorem tailTrace_5442321 : CollatzResearch.WordTrace tailWord_5442321 prefixEnd_5442321 2794526549057906627758727 := by
  unfold tailWord_5442321
  simp only [CollatzResearch.WordTrace]
  refine ⟨198497754116407966272670817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132331836077605310848447211 198497754116407966272670817)
  ·
    refine ⟨148873315587305974704503113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 198497754116407966272670817 148873315587305974704503113)
    ·
      refine ⟨111654986690479481028377335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 148873315587305974704503113 111654986690479481028377335)
      ·
        refine ⟨167482480035719221542566003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111654986690479481028377335 167482480035719221542566003)
        ·
          refine ⟨251223720053578832313849005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 167482480035719221542566003 251223720053578832313849005)
          ·
            refine ⟨94208895020092062117693377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 251223720053578832313849005 94208895020092062117693377)
            ·
              refine ⟨70656671265069046588270033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 94208895020092062117693377 70656671265069046588270033)
              ·
                refine ⟨52992503448801784941202525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 70656671265069046588270033 52992503448801784941202525)
                ·
                  refine ⟨19872188793300669352950947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 52992503448801784941202525 19872188793300669352950947)
                  ·
                    refine ⟨29808283189951004029426421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19872188793300669352950947 29808283189951004029426421)
                    ·
                      refine ⟨2794526549057906627758727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29808283189951004029426421 2794526549057906627758727)
                      ·
                        rfl

theorem cell23_5442321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 5].length) (baseStart_5442321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5442321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5442321 prefixEnd_5442321 := by exact prefixLift 5442321
  have htrace : WordTrace (prefixWord ++ tailWord_5442321) baseStart_5442321 baseEnd_5442321 := by
    simpa [prefixWord, tailWord_5442321, baseEnd_5442321] using wordTrace_append hprefix tailTrace_5442321
  have hstable : (prefixWord ++ tailWord_5442321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5442321).length < 2 ^ (prefixWord ++ tailWord_5442321).sum := by decide
  have hdescent : baseEnd_5442321 < baseStart_5442321 := by decide
  rcases family_descends (prefixWord ++ tailWord_5442321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5442346 : List Nat := [3, 1, 4, 3, 1, 1, 1, 4, 1, 1, 3]
def baseStart_5442346 : Nat := 118140960795 + 5442346 * 2 ^ 59
def prefixEnd_5442346 : Nat := 4983230072969 + 3 ^ 40 * 5442346 * 2
def baseEnd_5442346 : Nat := 2794539386074269029946113

theorem tailTrace_5442346 : CollatzResearch.WordTrace tailWord_5442346 prefixEnd_5442346 2794539386074269029946113 := by
  unfold tailWord_5442346
  simp only [CollatzResearch.WordTrace]
  refine ⟨49624666485329348885582723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132332443960878263694887261 49624666485329348885582723)
  ·
    refine ⟨74436999727994023328374085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49624666485329348885582723 74436999727994023328374085)
    ·
      refine ⟨13956937448998879374070141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 74436999727994023328374085 13956937448998879374070141)
      ·
        refine ⟨5233851543374579765276303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13956937448998879374070141 5233851543374579765276303)
        ·
          refine ⟨7850777315061869647914455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5233851543374579765276303 7850777315061869647914455)
          ·
            refine ⟨11776165972592804471871683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7850777315061869647914455 11776165972592804471871683)
            ·
              refine ⟨17664248958889206707807525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11776165972592804471871683 17664248958889206707807525)
              ·
                refine ⟨3312046679791726257713911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17664248958889206707807525 3312046679791726257713911)
                ·
                  refine ⟨4968070019687589386570867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3312046679791726257713911 4968070019687589386570867)
                  ·
                    refine ⟨7452105029531384079856301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4968070019687589386570867 7452105029531384079856301)
                    ·
                      refine ⟨2794539386074269029946113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7452105029531384079856301 2794539386074269029946113)
                      ·
                        rfl

theorem cell23_5442346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 1, 4, 1, 1, 3].length) (baseStart_5442346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5442346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5442346 prefixEnd_5442346 := by exact prefixLift 5442346
  have htrace : WordTrace (prefixWord ++ tailWord_5442346) baseStart_5442346 baseEnd_5442346 := by
    simpa [prefixWord, tailWord_5442346, baseEnd_5442346] using wordTrace_append hprefix tailTrace_5442346
  have hstable : (prefixWord ++ tailWord_5442346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5442346).length < 2 ^ (prefixWord ++ tailWord_5442346).sum := by decide
  have hdescent : baseEnd_5442346 < baseStart_5442346 := by decide
  rcases family_descends (prefixWord ++ tailWord_5442346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5442371 : List Nat := [1, 1, 1, 3, 1, 4, 1, 2, 2, 7]
def baseStart_5442371 : Nat := 118140960795 + 5442371 * 2 ^ 59
def prefixEnd_5442371 : Nat := 4983230072969 + 3 ^ 40 * 5442371 * 2
def baseEnd_5442371 : Nat := 931517407696877144044499

theorem tailTrace_5442371 : CollatzResearch.WordTrace tailWord_5442371 prefixEnd_5442371 931517407696877144044499 := by
  unfold tailWord_5442371
  simp only [CollatzResearch.WordTrace]
  refine ⟨198499577766226824811990967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132333051844151216541327311 198499577766226824811990967)
  ·
    refine ⟨297749366649340237217986451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198499577766226824811990967 297749366649340237217986451)
    ·
      refine ⟨446624049974010355826979677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 297749366649340237217986451 446624049974010355826979677)
      ·
        refine ⟨167484018740253883435117379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 446624049974010355826979677 167484018740253883435117379)
        ·
          refine ⟨251226028110380825152676069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 167484018740253883435117379 251226028110380825152676069)
          ·
            refine ⟨47104880270696404716126763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 251226028110380825152676069 47104880270696404716126763)
            ·
              refine ⟨70657320406044607074190145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47104880270696404716126763 70657320406044607074190145)
              ·
                refine ⟨52992990304533455305642609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 70657320406044607074190145 52992990304533455305642609)
                ·
                  refine ⟨39744742728400091479231957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 52992990304533455305642609 39744742728400091479231957)
                  ·
                    refine ⟨931517407696877144044499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 39744742728400091479231957 931517407696877144044499)
                    ·
                      rfl

theorem cell23_5442371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 2, 2, 7].length) (baseStart_5442371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5442371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5442371 prefixEnd_5442371 := by exact prefixLift 5442371
  have htrace : WordTrace (prefixWord ++ tailWord_5442371) baseStart_5442371 baseEnd_5442371 := by
    simpa [prefixWord, tailWord_5442371, baseEnd_5442371] using wordTrace_append hprefix tailTrace_5442371
  have hstable : (prefixWord ++ tailWord_5442371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5442371).length < 2 ^ (prefixWord ++ tailWord_5442371).sum := by decide
  have hdescent : baseEnd_5442371 < baseStart_5442371 := by decide
  rcases family_descends (prefixWord ++ tailWord_5442371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5442418 : List Nat := [3, 2, 1, 2, 1, 1, 4, 1, 2, 6]
def baseStart_5442418 : Nat := 118140960795 + 5442418 * 2 ^ 59
def prefixEnd_5442418 : Nat := 4983230072969 + 3 ^ 40 * 5442418 * 2
def baseEnd_5442418 : Nat := 931525452227130916081927

theorem tailTrace_5442418 : CollatzResearch.WordTrace tailWord_5442418 prefixEnd_5442418 931525452227130916081927 := by
  unfold tailWord_5442418
  simp only [CollatzResearch.WordTrace]
  refine ⟨49625322999264137959737977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132334194664704367892634605 49625322999264137959737977)
  ·
    refine ⟨37218992249448103469803483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49625322999264137959737977 37218992249448103469803483)
    ·
      refine ⟨55828488374172155204705225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37218992249448103469803483 55828488374172155204705225)
      ·
        refine ⟨41871366280629116403528919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55828488374172155204705225 41871366280629116403528919)
        ·
          refine ⟨62807049420943674605293379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41871366280629116403528919 62807049420943674605293379)
          ·
            refine ⟨94210574131415511907940069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62807049420943674605293379 94210574131415511907940069)
            ·
              refine ⟨17664482649640408482738763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 94210574131415511907940069 17664482649640408482738763)
              ·
                refine ⟨26496723974460612724108145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17664482649640408482738763 26496723974460612724108145)
                ·
                  refine ⟨19872542980845459543081109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26496723974460612724108145 19872542980845459543081109)
                  ·
                    refine ⟨931525452227130916081927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19872542980845459543081109 931525452227130916081927)
                    ·
                      rfl

theorem cell23_5442418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 4, 1, 2, 6].length) (baseStart_5442418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5442418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5442418 prefixEnd_5442418 := by exact prefixLift 5442418
  have htrace : WordTrace (prefixWord ++ tailWord_5442418) baseStart_5442418 baseEnd_5442418 := by
    simpa [prefixWord, tailWord_5442418, baseEnd_5442418] using wordTrace_append hprefix tailTrace_5442418
  have hstable : (prefixWord ++ tailWord_5442418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5442418).length < 2 ^ (prefixWord ++ tailWord_5442418).sum := by decide
  have hdescent : baseEnd_5442418 < baseStart_5442418 := by decide
  rcases family_descends (prefixWord ++ tailWord_5442418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5442428 : List Nat := [2, 2, 2, 1, 1, 1, 1, 4, 2, 4, 3]
def baseStart_5442428 : Nat := 118140960795 + 5442428 * 2 ^ 59
def prefixEnd_5442428 : Nat := 4983230072969 + 3 ^ 40 * 5442428 * 2
def baseEnd_5442428 : Nat := 2794581491487937709120735

theorem tailTrace_5442428 : CollatzResearch.WordTrace tailWord_5442428 prefixEnd_5442428 2794581491487937709120735 := by
  unfold tailWord_5442428
  simp only [CollatzResearch.WordTrace]
  refine ⟨99250828363510161773407969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132334437818013549031210625 99250828363510161773407969)
  ·
    refine ⟨74438121272632621330055977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99250828363510161773407969 74438121272632621330055977)
    ·
      refine ⟨55828590954474465997541983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74438121272632621330055977 55828590954474465997541983)
      ·
        refine ⟨83742886431711698996312975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55828590954474465997541983 83742886431711698996312975)
        ·
          refine ⟨125614329647567548494469463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83742886431711698996312975 125614329647567548494469463)
          ·
            refine ⟨188421494471351322741704195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 125614329647567548494469463 188421494471351322741704195)
            ·
              refine ⟨282632241707026984112556293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 188421494471351322741704195 282632241707026984112556293)
              ·
                refine ⟨52993545320067559521104305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 282632241707026984112556293 52993545320067559521104305)
                ·
                  refine ⟨39745158990050669640828229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 52993545320067559521104305 39745158990050669640828229)
                  ·
                    refine ⟨7452217310634500557655293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 39745158990050669640828229 7452217310634500557655293)
                    ·
                      refine ⟨2794581491487937709120735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7452217310634500557655293 2794581491487937709120735)
                      ·
                        rfl

theorem cell23_5442428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 4, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 4, 2, 4, 3].length) (baseStart_5442428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5442428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5442428 prefixEnd_5442428 := by exact prefixLift 5442428
  have htrace : WordTrace (prefixWord ++ tailWord_5442428) baseStart_5442428 baseEnd_5442428 := by
    simpa [prefixWord, tailWord_5442428, baseEnd_5442428] using wordTrace_append hprefix tailTrace_5442428
  have hstable : (prefixWord ++ tailWord_5442428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5442428).length < 2 ^ (prefixWord ++ tailWord_5442428).sum := by decide
  have hdescent : baseEnd_5442428 < baseStart_5442428 := by decide
  rcases family_descends (prefixWord ++ tailWord_5442428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5442465 : List Nat := [1, 2, 3, 4, 1, 1, 3, 1, 7]
def baseStart_5442465 : Nat := 118140960795 + 5442465 * 2 ^ 59
def prefixEnd_5442465 : Nat := 4983230072969 + 3 ^ 40 * 5442465 * 2
def baseEnd_5442465 : Nat := 310511165585794896039785

theorem tailTrace_5442465 : CollatzResearch.WordTrace tailWord_5442465 prefixEnd_5442465 310511165585794896039785 := by
  unfold tailWord_5442465
  simp only [CollatzResearch.WordTrace]
  refine ⟨198503006227886278865912849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132335337485257519243941899 198503006227886278865912849)
  ·
    refine ⟨148877254670914709149434637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 198503006227886278865912849 148877254670914709149434637)
    ·
      refine ⟨55828970501593015931037989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 148877254670914709149434637 55828970501593015931037989)
      ·
        refine ⟨10467931969048690487069623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 55828970501593015931037989 10467931969048690487069623)
        ·
          refine ⟨15701897953573035730604435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10467931969048690487069623 15701897953573035730604435)
          ·
            refine ⟨23552846930359553595906653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15701897953573035730604435 23552846930359553595906653)
            ·
              refine ⟨8832317598884832598464995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23552846930359553595906653 8832317598884832598464995)
              ·
                refine ⟨13248476398327248897697493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8832317598884832598464995 13248476398327248897697493)
                ·
                  refine ⟨310511165585794896039785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13248476398327248897697493 310511165585794896039785)
                  ·
                    rfl

theorem cell23_5442465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 3, 1, 7].length) (baseStart_5442465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5442465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5442465 prefixEnd_5442465 := by exact prefixLift 5442465
  have htrace : WordTrace (prefixWord ++ tailWord_5442465) baseStart_5442465 baseEnd_5442465 := by
    simpa [prefixWord, tailWord_5442465, baseEnd_5442465] using wordTrace_append hprefix tailTrace_5442465
  have hstable : (prefixWord ++ tailWord_5442465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5442465).length < 2 ^ (prefixWord ++ tailWord_5442465).sum := by decide
  have hdescent : baseEnd_5442465 < baseStart_5442465 := by decide
  rcases family_descends (prefixWord ++ tailWord_5442465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5442528 : List Nat := [2, 1, 1, 3, 1, 1, 1, 1, 4, 4, 4]
def baseStart_5442528 : Nat := 118140960795 + 5442528 * 2 ^ 59
def prefixEnd_5442528 : Nat := 4983230072969 + 3 ^ 40 * 5442528 * 2
def baseEnd_5442528 : Nat := 2794632839553387317870275

theorem tailTrace_5442528 : CollatzResearch.WordTrace tailWord_5442528 prefixEnd_5442528 2794632839553387317870275 := by
  unfold tailWord_5442528
  simp only [CollatzResearch.WordTrace]
  refine ⟨99252652013329020312728119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132336869351105360416970825 99252652013329020312728119)
  ·
    refine ⟨148878978019993530469092179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99252652013329020312728119 148878978019993530469092179)
    ·
      refine ⟨223318467029990295703638269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148878978019993530469092179 223318467029990295703638269)
      ·
        refine ⟨83744425136246360888864351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 223318467029990295703638269 83744425136246360888864351)
        ·
          refine ⟨125616637704369541333296527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83744425136246360888864351 125616637704369541333296527)
          ·
            refine ⟨188424956556554311999944791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 125616637704369541333296527 188424956556554311999944791)
            ·
              refine ⟨282637434834831467999917187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 188424956556554311999944791 282637434834831467999917187)
              ·
                refine ⟨423956152252247201999875781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 282637434834831467999917187 423956152252247201999875781)
                ·
                  refine ⟨79491778547296350374976709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 423956152252247201999875781 79491778547296350374976709)
                  ·
                    refine ⟨14904708477618065695308133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 79491778547296350374976709 14904708477618065695308133)
                    ·
                      refine ⟨2794632839553387317870275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14904708477618065695308133 2794632839553387317870275)
                      ·
                        rfl

theorem cell23_5442528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 1, 4, 4, 4].length) (baseStart_5442528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5442528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5442528 prefixEnd_5442528 := by exact prefixLift 5442528
  have htrace : WordTrace (prefixWord ++ tailWord_5442528) baseStart_5442528 baseEnd_5442528 := by
    simpa [prefixWord, tailWord_5442528, baseEnd_5442528] using wordTrace_append hprefix tailTrace_5442528
  have hstable : (prefixWord ++ tailWord_5442528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5442528).length < 2 ^ (prefixWord ++ tailWord_5442528).sum := by decide
  have hdescent : baseEnd_5442528 < baseStart_5442528 := by decide
  rcases family_descends (prefixWord ++ tailWord_5442528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5442546 : List Nat := [3, 2, 1, 5, 2, 1, 1, 1, 2, 5]
def baseStart_5442546 : Nat := 118140960795 + 5442546 * 2 ^ 59
def prefixEnd_5442546 : Nat := 4983230072969 + 3 ^ 40 * 5442546 * 2
def baseEnd_5442546 : Nat := 931547360735056082481731

theorem tailTrace_5442546 : CollatzResearch.WordTrace tailWord_5442546 prefixEnd_5442546 931547360735056082481731 := by
  unfold tailWord_5442546
  simp only [CollatzResearch.WordTrace]
  refine ⟨49626490135148207424902873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132337307027061886466407661 49626490135148207424902873)
  ·
    refine ⟨37219867601361155568677155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49626490135148207424902873 37219867601361155568677155)
    ·
      refine ⟨55829801402041733353015733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37219867601361155568677155 55829801402041733353015733)
      ·
        refine ⟨5234043881441412501845225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 55829801402041733353015733 5234043881441412501845225)
        ·
          refine ⟨3925532911081059376383919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5234043881441412501845225 3925532911081059376383919)
          ·
            refine ⟨5888299366621589064575879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3925532911081059376383919 5888299366621589064575879)
            ·
              refine ⟨8832449049932383596863819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5888299366621589064575879 8832449049932383596863819)
              ·
                refine ⟨13248673574898575395295729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8832449049932383596863819 13248673574898575395295729)
                ·
                  refine ⟨9936505181173931546471797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13248673574898575395295729 9936505181173931546471797)
                  ·
                    refine ⟨931547360735056082481731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9936505181173931546471797 931547360735056082481731)
                    ·
                      rfl

theorem cell23_5442546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 2, 1, 1, 1, 2, 5].length) (baseStart_5442546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5442546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5442546 prefixEnd_5442546 := by exact prefixLift 5442546
  have htrace : WordTrace (prefixWord ++ tailWord_5442546) baseStart_5442546 baseEnd_5442546 := by
    simpa [prefixWord, tailWord_5442546, baseEnd_5442546] using wordTrace_append hprefix tailTrace_5442546
  have hstable : (prefixWord ++ tailWord_5442546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5442546).length < 2 ^ (prefixWord ++ tailWord_5442546).sum := by decide
  have hdescent : baseEnd_5442546 < baseStart_5442546 := by decide
  rcases family_descends (prefixWord ++ tailWord_5442546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5442549 : List Nat := [1, 3, 5, 2, 1, 1, 1, 1, 1, 3, 4]
def baseStart_5442549 : Nat := 118140960795 + 5442549 * 2 ^ 59
def prefixEnd_5442549 : Nat := 4983230072969 + 3 ^ 40 * 5442549 * 2
def baseEnd_5442549 : Nat := 2794643622647131735707679

theorem tailTrace_5442549 : CollatzResearch.WordTrace tailWord_5442549 prefixEnd_5442549 2794643622647131735707679 := by
  unfold tailWord_5442549
  simp only [CollatzResearch.WordTrace]
  refine ⟨198506069959581961211970701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132337379973054640807980467 198506069959581961211970701)
  ·
    refine ⟨74439776234843235454489013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 198506069959581961211970701 74439776234843235454489013)
    ·
      refine ⟨6978729022016553323858345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 74439776234843235454489013 6978729022016553323858345)
      ·
        refine ⟨5234046766512414992893759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6978729022016553323858345 5234046766512414992893759)
        ·
          refine ⟨7851070149768622489340639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5234046766512414992893759 7851070149768622489340639)
          ·
            refine ⟨11776605224652933734010959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7851070149768622489340639 11776605224652933734010959)
            ·
              refine ⟨17664907836979400601016439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11776605224652933734010959 17664907836979400601016439)
              ·
                refine ⟨26497361755469100901524659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17664907836979400601016439 26497361755469100901524659)
                ·
                  refine ⟨39746042633203651352286989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26497361755469100901524659 39746042633203651352286989)
                  ·
                    refine ⟨14904765987451369257107621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 39746042633203651352286989 14904765987451369257107621)
                    ·
                      refine ⟨2794643622647131735707679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14904765987451369257107621 2794643622647131735707679)
                      ·
                        rfl

theorem cell23_5442549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 1, 1, 1, 3, 4].length) (baseStart_5442549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5442549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5442549 prefixEnd_5442549 := by exact prefixLift 5442549
  have htrace : WordTrace (prefixWord ++ tailWord_5442549) baseStart_5442549 baseEnd_5442549 := by
    simpa [prefixWord, tailWord_5442549, baseEnd_5442549] using wordTrace_append hprefix tailTrace_5442549
  have hstable : (prefixWord ++ tailWord_5442549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5442549).length < 2 ^ (prefixWord ++ tailWord_5442549).sum := by decide
  have hdescent : baseEnd_5442549 < baseStart_5442549 := by decide
  rcases family_descends (prefixWord ++ tailWord_5442549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5442572 : List Nat := [2, 2, 1, 2, 3, 4, 1, 2, 6]
def baseStart_5442572 : Nat := 118140960795 + 5442572 * 2 ^ 59
def prefixEnd_5442572 : Nat := 4983230072969 + 3 ^ 40 * 5442572 * 2
def baseEnd_5442572 : Nat := 310517270300242793968897

theorem tailTrace_5442572 : CollatzResearch.WordTrace tailWord_5442572 prefixEnd_5442572 310517270300242793968897 := by
  unfold tailWord_5442572
  simp only [CollatzResearch.WordTrace]
  refine ⟨99253454419249318070028985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132337939225665757426705313 99253454419249318070028985)
  ·
    refine ⟨74440090814436988552521739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99253454419249318070028985 74440090814436988552521739)
    ·
      refine ⟨111660136221655482828782609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74440090814436988552521739 111660136221655482828782609)
      ·
        refine ⟨83745102166241612121586957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111660136221655482828782609 83745102166241612121586957)
        ·
          refine ⟨31404413312340604545595109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 83745102166241612121586957 31404413312340604545595109)
          ·
            refine ⟨5888327496063863352299083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31404413312340604545595109 5888327496063863352299083)
            ·
              refine ⟨8832491244095795028448625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5888327496063863352299083 8832491244095795028448625)
              ·
                refine ⟨6624368433071846271336469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8832491244095795028448625 6624368433071846271336469)
                ·
                  refine ⟨310517270300242793968897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6624368433071846271336469 310517270300242793968897)
                  ·
                    rfl

theorem cell23_5442572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 4, 1, 2, 6].length) (baseStart_5442572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5442572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5442572 prefixEnd_5442572 := by exact prefixLift 5442572
  have htrace : WordTrace (prefixWord ++ tailWord_5442572) baseStart_5442572 baseEnd_5442572 := by
    simpa [prefixWord, tailWord_5442572, baseEnd_5442572] using wordTrace_append hprefix tailTrace_5442572
  have hstable : (prefixWord ++ tailWord_5442572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5442572).length < 2 ^ (prefixWord ++ tailWord_5442572).sum := by decide
  have hdescent : baseEnd_5442572 < baseStart_5442572 := by decide
  rcases family_descends (prefixWord ++ tailWord_5442572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5442575 : List Nat := [1, 1, 2, 1, 1, 1, 2, 1, 2, 9, 2]
def baseStart_5442575 : Nat := 118140960795 + 5442575 * 2 ^ 59
def prefixEnd_5442575 : Nat := 4983230072969 + 3 ^ 40 * 5442575 * 2
def baseEnd_5442575 : Nat := 2794656973144148633982559

theorem tailTrace_5442575 : CollatzResearch.WordTrace tailWord_5442575 prefixEnd_5442575 2794656973144148633982559 := by
  unfold tailWord_5442575
  simp only [CollatzResearch.WordTrace]
  refine ⟨198507018257487767652417179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132338012171658511768278119 198507018257487767652417179)
  ·
    refine ⟨297760527386231651478625769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198507018257487767652417179 297760527386231651478625769)
    ·
      refine ⟨223320395539673738608969327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 297760527386231651478625769 223320395539673738608969327)
      ·
        refine ⟨334980593309510607913453991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 223320395539673738608969327 334980593309510607913453991)
        ·
          refine ⟨502470889964265911870180987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 334980593309510607913453991 502470889964265911870180987)
          ·
            refine ⟨753706334946398867805271481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 502470889964265911870180987 753706334946398867805271481)
            ·
              refine ⟨565279751209799150853953611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 753706334946398867805271481 565279751209799150853953611)
              ·
                refine ⟨847919626814698726280930417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 565279751209799150853953611 847919626814698726280930417)
                ·
                  refine ⟨635939720111024044710697813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 847919626814698726280930417 635939720111024044710697813)
                  ·
                    refine ⟨3726209297525531511976745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 635939720111024044710697813 3726209297525531511976745)
                    ·
                      refine ⟨2794656973144148633982559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3726209297525531511976745 2794656973144148633982559)
                      ·
                        rfl

theorem cell23_5442575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 1, 2, 9, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 1, 2, 9, 2].length) (baseStart_5442575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5442575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5442575 prefixEnd_5442575 := by exact prefixLift 5442575
  have htrace : WordTrace (prefixWord ++ tailWord_5442575) baseStart_5442575 baseEnd_5442575 := by
    simpa [prefixWord, tailWord_5442575, baseEnd_5442575] using wordTrace_append hprefix tailTrace_5442575
  have hstable : (prefixWord ++ tailWord_5442575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5442575).length < 2 ^ (prefixWord ++ tailWord_5442575).sum := by decide
  have hdescent : baseEnd_5442575 < baseStart_5442575 := by decide
  rcases family_descends (prefixWord ++ tailWord_5442575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5442589 : List Nat := [1, 4, 2, 2, 3, 1, 3, 1, 6]
def baseStart_5442589 : Nat := 118140960795 + 5442589 * 2 ^ 59
def prefixEnd_5442589 : Nat := 4983230072969 + 3 ^ 40 * 5442589 * 2
def baseEnd_5442589 : Nat := 310518240208145731023055

theorem tailTrace_5442589 : CollatzResearch.WordTrace tailWord_5442589 prefixEnd_5442589 310518240208145731023055 := by
  unfold tailWord_5442589
  simp only [CollatzResearch.WordTrace]
  refine ⟨198507528879437048043426821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132338352586291365362284547 198507528879437048043426821)
  ·
    refine ⟨37220161664894446508142529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 198507528879437048043426821 37220161664894446508142529)
    ·
      refine ⟨27915121248670834881106897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37220161664894446508142529 27915121248670834881106897)
      ·
        refine ⟨20936340936503126160830173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27915121248670834881106897 20936340936503126160830173)
        ·
          refine ⟨7851127851188672310311315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20936340936503126160830173 7851127851188672310311315)
          ·
            refine ⟨11776691776783008465466973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7851127851188672310311315 11776691776783008465466973)
            ·
              refine ⟨4416259416293628174550115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11776691776783008465466973 4416259416293628174550115)
              ·
                refine ⟨6624389124440442261825173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4416259416293628174550115 6624389124440442261825173)
                ·
                  refine ⟨310518240208145731023055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6624389124440442261825173 310518240208145731023055)
                  ·
                    rfl

theorem cell23_5442589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 3, 1, 6].length) (baseStart_5442589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5442589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5442589 prefixEnd_5442589 := by exact prefixLift 5442589
  have htrace : WordTrace (prefixWord ++ tailWord_5442589) baseStart_5442589 baseEnd_5442589 := by
    simpa [prefixWord, tailWord_5442589, baseEnd_5442589] using wordTrace_append hprefix tailTrace_5442589
  have hstable : (prefixWord ++ tailWord_5442589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5442589).length < 2 ^ (prefixWord ++ tailWord_5442589).sum := by decide
  have hdescent : baseEnd_5442589 < baseStart_5442589 := by decide
  rcases family_descends (prefixWord ++ tailWord_5442589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5442616 : List Nat := [2, 1, 2, 1, 5, 1, 3, 3, 1, 1, 3]
def baseStart_5442616 : Nat := 118140960795 + 5442616 * 2 ^ 59
def prefixEnd_5442616 : Nat := 4983230072969 + 3 ^ 40 * 5442616 * 2
def baseEnd_5442616 : Nat := 2794678025850982973569871

theorem tailTrace_5442616 : CollatzResearch.WordTrace tailWord_5442616 prefixEnd_5442616 2794678025850982973569871 := by
  unfold tailWord_5442616
  simp only [CollatzResearch.WordTrace]
  refine ⟨99254256825169615827329851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132339009100226154436439801 99254256825169615827329851)
  ·
    refine ⟨148881385237754423740994777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99254256825169615827329851 148881385237754423740994777)
    ·
      refine ⟨111661038928315817805746083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 148881385237754423740994777 111661038928315817805746083)
      ·
        refine ⟨167491558392473726708619125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111661038928315817805746083 167491558392473726708619125)
        ·
          refine ⟨15702333599294411878933043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 167491558392473726708619125 15702333599294411878933043)
          ·
            refine ⟨23553500398941617818399565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15702333599294411878933043 23553500398941617818399565)
            ·
              refine ⟨8832562649603106681899837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23553500398941617818399565 8832562649603106681899837)
              ·
                refine ⟨3312210993601165005712439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8832562649603106681899837 3312210993601165005712439)
                ·
                  refine ⟨4968316490401747508568659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3312210993601165005712439 4968316490401747508568659)
                  ·
                    refine ⟨7452474735602621262852989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4968316490401747508568659 7452474735602621262852989)
                    ·
                      refine ⟨2794678025850982973569871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7452474735602621262852989 2794678025850982973569871)
                      ·
                        rfl

theorem cell23_5442616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 3, 3, 1, 1, 3].length) (baseStart_5442616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5442616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5442616 prefixEnd_5442616 := by exact prefixLift 5442616
  have htrace : WordTrace (prefixWord ++ tailWord_5442616) baseStart_5442616 baseEnd_5442616 := by
    simpa [prefixWord, tailWord_5442616, baseEnd_5442616] using wordTrace_append hprefix tailTrace_5442616
  have hstable : (prefixWord ++ tailWord_5442616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5442616).length < 2 ^ (prefixWord ++ tailWord_5442616).sum := by decide
  have hdescent : baseEnd_5442616 < baseStart_5442616 := by decide
  rcases family_descends (prefixWord ++ tailWord_5442616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5442632 : List Nat := [2, 1, 3, 1, 1, 1, 4, 4, 2, 4]
def baseStart_5442632 : Nat := 118140960795 + 5442632 * 2 ^ 59
def prefixEnd_5442632 : Nat := 4983230072969 + 3 ^ 40 * 5442632 * 2
def baseEnd_5442632 : Nat := 931562080513818303656599

theorem tailTrace_5442632 : CollatzResearch.WordTrace tailWord_5442632 prefixEnd_5442632 931562080513818303656599 := by
  unfold tailWord_5442632
  simp only [CollatzResearch.WordTrace]
  refine ⟨99254548609140633193621075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132339398145520844258161433 99254548609140633193621075)
  ·
    refine ⟨148881822913710949790431613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99254548609140633193621075 148881822913710949790431613)
    ·
      refine ⟨55830683592641606171411855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 148881822913710949790431613 55830683592641606171411855)
      ·
        refine ⟨83746025388962409257117783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55830683592641606171411855 83746025388962409257117783)
        ·
          refine ⟨125619038083443613885676675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83746025388962409257117783 125619038083443613885676675)
          ·
            refine ⟨188428557125165420828515013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 125619038083443613885676675 188428557125165420828515013)
            ·
              refine ⟨35330354460968516405346565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 188428557125165420828515013 35330354460968516405346565)
              ·
                refine ⟨6624441461431596826002481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35330354460968516405346565 6624441461431596826002481)
                ·
                  refine ⟨4968331096073697619501861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6624441461431596826002481 4968331096073697619501861)
                  ·
                    refine ⟨931562080513818303656599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4968331096073697619501861 931562080513818303656599)
                    ·
                      rfl

theorem cell23_5442632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 4, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 4, 4, 2, 4].length) (baseStart_5442632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5442632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5442632 prefixEnd_5442632 := by exact prefixLift 5442632
  have htrace : WordTrace (prefixWord ++ tailWord_5442632) baseStart_5442632 baseEnd_5442632 := by
    simpa [prefixWord, tailWord_5442632, baseEnd_5442632] using wordTrace_append hprefix tailTrace_5442632
  have hstable : (prefixWord ++ tailWord_5442632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5442632).length < 2 ^ (prefixWord ++ tailWord_5442632).sum := by decide
  have hdescent : baseEnd_5442632 < baseStart_5442632 := by decide
  rcases family_descends (prefixWord ++ tailWord_5442632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5442642 : List Nat := [3, 2, 2, 1, 3, 1, 2, 2, 1, 1, 5]
def baseStart_5442642 : Nat := 118140960795 + 5442642 * 2 ^ 59
def prefixEnd_5442642 : Nat := 4983230072969 + 3 ^ 40 * 5442642 * 2
def baseEnd_5442642 : Nat := 2794691376347999871844751

theorem tailTrace_5442642 : CollatzResearch.WordTrace tailWord_5442642 prefixEnd_5442642 2794691376347999871844751 := by
  unfold tailWord_5442642
  simp only [CollatzResearch.WordTrace]
  refine ⟨49627365487061259523776545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132339641298830025396737453 49627365487061259523776545)
  ·
    refine ⟨37220524115295944642832409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49627365487061259523776545 37220524115295944642832409)
    ·
      refine ⟨27915393086471958482124307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37220524115295944642832409 27915393086471958482124307)
      ·
        refine ⟨41873089629707937723186461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27915393086471958482124307 41873089629707937723186461)
        ·
          refine ⟨15702408611140476646194923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41873089629707937723186461 15702408611140476646194923)
          ·
            refine ⟨23553612916710714969292385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15702408611140476646194923 23553612916710714969292385)
            ·
              refine ⟨17665209687533036226969289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23553612916710714969292385 17665209687533036226969289)
              ·
                refine ⟨13248907265649777170226967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17665209687533036226969289 13248907265649777170226967)
                ·
                  refine ⟨19873360898474665755340451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13248907265649777170226967 19873360898474665755340451)
                  ·
                    refine ⟨29810041347711998633010677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19873360898474665755340451 29810041347711998633010677)
                    ·
                      refine ⟨2794691376347999871844751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29810041347711998633010677 2794691376347999871844751)
                      ·
                        rfl

theorem cell23_5442642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 2, 2, 1, 1, 5].length) (baseStart_5442642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5442642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5442642 prefixEnd_5442642 := by exact prefixLift 5442642
  have htrace : WordTrace (prefixWord ++ tailWord_5442642) baseStart_5442642 baseEnd_5442642 := by
    simpa [prefixWord, tailWord_5442642, baseEnd_5442642] using wordTrace_append hprefix tailTrace_5442642
  have hstable : (prefixWord ++ tailWord_5442642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5442642).length < 2 ^ (prefixWord ++ tailWord_5442642).sum := by decide
  have hdescent : baseEnd_5442642 < baseStart_5442642 := by decide
  rcases family_descends (prefixWord ++ tailWord_5442642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5442645 : List Nat := [1, 3, 2, 2, 1, 2, 4, 8]
def baseStart_5442645 : Nat := 118140960795 + 5442645 * 2 ^ 59
def prefixEnd_5442645 : Nat := 4983230072969 + 3 ^ 40 * 5442645 * 2
def baseEnd_5442645 : Nat := 103507145066294939263231

theorem tailTrace_5442645 : CollatzResearch.WordTrace tailWord_5442645 prefixEnd_5442645 103507145066294939263231 := by
  unfold tailWord_5442645
  simp only [CollatzResearch.WordTrace]
  refine ⟨198509571367234169607465389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132339714244822779738310259 198509571367234169607465389)
  ·
    refine ⟨74441089262712813602799521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 198509571367234169607465389 74441089262712813602799521)
    ·
      refine ⟨55830816947034610202099641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74441089262712813602799521 55830816947034610202099641)
      ·
        refine ⟨41873112710275957651574731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55830816947034610202099641 41873112710275957651574731)
        ·
          refine ⟨62809669065413936477362097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41873112710275957651574731 62809669065413936477362097)
          ·
            refine ⟨47107251799060452358021573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62809669065413936477362097 47107251799060452358021573)
            ·
              refine ⟨8832609712323834817129045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 47107251799060452358021573 8832609712323834817129045)
              ·
                refine ⟨103507145066294939263231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8832609712323834817129045 103507145066294939263231)
                ·
                  rfl

theorem cell23_5442645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 4, 8].length) (baseStart_5442645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5442645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5442645 prefixEnd_5442645 := by exact prefixLift 5442645
  have htrace : WordTrace (prefixWord ++ tailWord_5442645) baseStart_5442645 baseEnd_5442645 := by
    simpa [prefixWord, tailWord_5442645, baseEnd_5442645] using wordTrace_append hprefix tailTrace_5442645
  have hstable : (prefixWord ++ tailWord_5442645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5442645).length < 2 ^ (prefixWord ++ tailWord_5442645).sum := by decide
  have hdescent : baseEnd_5442645 < baseStart_5442645 := by decide
  rcases family_descends (prefixWord ++ tailWord_5442645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5442652 : List Nat := [2, 2, 4, 1, 1, 1, 2, 3, 1, 2, 4]
def baseStart_5442652 : Nat := 118140960795 + 5442652 * 2 ^ 59
def prefixEnd_5442652 : Nat := 4983230072969 + 3 ^ 40 * 5442652 * 2
def baseEnd_5442652 : Nat := 2794696511154544832719705

theorem tailTrace_5442652 : CollatzResearch.WordTrace tailWord_5442652 prefixEnd_5442652 2794696511154544832719705 := by
  unfold tailWord_5442652
  simp only [CollatzResearch.WordTrace]
  refine ⟨99254913339104404901485105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132339884452139206535313473 99254913339104404901485105)
  ·
    refine ⟨74441185004328303676113829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99254913339104404901485105 74441185004328303676113829)
    ·
      refine ⟨13957722188311556939271343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 74441185004328303676113829 13957722188311556939271343)
      ·
        refine ⟨20936583282467335408907015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13957722188311556939271343 20936583282467335408907015)
        ·
          refine ⟨31404874923701003113360523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20936583282467335408907015 31404874923701003113360523)
          ·
            refine ⟨47107312385551504670040785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31404874923701003113360523 47107312385551504670040785)
            ·
              refine ⟨35330484289163628502530589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47107312385551504670040785 35330484289163628502530589)
              ·
                refine ⟨13248931608436360688448971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35330484289163628502530589 13248931608436360688448971)
                ·
                  refine ⟨19873397412654541032673457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13248931608436360688448971 19873397412654541032673457)
                  ·
                    refine ⟨14905048059490905774505093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19873397412654541032673457 14905048059490905774505093)
                    ·
                      refine ⟨2794696511154544832719705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14905048059490905774505093 2794696511154544832719705)
                      ·
                        rfl

theorem cell23_5442652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 2, 3, 1, 2, 4].length) (baseStart_5442652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5442652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5442652 prefixEnd_5442652 := by exact prefixLift 5442652
  have htrace : WordTrace (prefixWord ++ tailWord_5442652) baseStart_5442652 baseEnd_5442652 := by
    simpa [prefixWord, tailWord_5442652, baseEnd_5442652] using wordTrace_append hprefix tailTrace_5442652
  have hstable : (prefixWord ++ tailWord_5442652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5442652).length < 2 ^ (prefixWord ++ tailWord_5442652).sum := by decide
  have hdescent : baseEnd_5442652 < baseStart_5442652 := by decide
  rcases family_descends (prefixWord ++ tailWord_5442652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5442653 : List Nat := [1, 4, 4, 1, 3, 1, 1, 2, 1, 5]
def baseStart_5442653 : Nat := 118140960795 + 5442653 * 2 ^ 59
def prefixEnd_5442653 : Nat := 4983230072969 + 3 ^ 40 * 5442653 * 2
def baseEnd_5442653 : Nat := 931565674878399776269067

theorem tailTrace_5442653 : CollatzResearch.WordTrace tailWord_5442653 prefixEnd_5442653 931565674878399776269067 := by
  unfold tailWord_5442653
  simp only [CollatzResearch.WordTrace]
  refine ⟨198509863151205186973756613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132339908767470124649171075 198509863151205186973756613)
  ·
    refine ⟨37220599340850972557579365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 198509863151205186973756613 37220599340850972557579365)
    ·
      refine ⟨6978862376409557354546131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 37220599340850972557579365 6978862376409557354546131)
      ·
        refine ⟨10468293564614336031819197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6978862376409557354546131 10468293564614336031819197)
        ·
          refine ⟨3925610086730376011932199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10468293564614336031819197 3925610086730376011932199)
          ·
            refine ⟨5888415130095564017898299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3925610086730376011932199 5888415130095564017898299)
            ·
              refine ⟨8832622695143346026847449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5888415130095564017898299 8832622695143346026847449)
              ·
                refine ⟨6624467021357509520135587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8832622695143346026847449 6624467021357509520135587)
                ·
                  refine ⟨9936700532036264280203381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6624467021357509520135587 9936700532036264280203381)
                  ·
                    refine ⟨931565674878399776269067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9936700532036264280203381 931565674878399776269067)
                    ·
                      rfl

theorem cell23_5442653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 3, 1, 1, 2, 1, 5].length) (baseStart_5442653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5442653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5442653 prefixEnd_5442653 := by exact prefixLift 5442653
  have htrace : WordTrace (prefixWord ++ tailWord_5442653) baseStart_5442653 baseEnd_5442653 := by
    simpa [prefixWord, tailWord_5442653, baseEnd_5442653] using wordTrace_append hprefix tailTrace_5442653
  have hstable : (prefixWord ++ tailWord_5442653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5442653).length < 2 ^ (prefixWord ++ tailWord_5442653).sum := by decide
  have hdescent : baseEnd_5442653 < baseStart_5442653 := by decide
  rcases family_descends (prefixWord ++ tailWord_5442653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5442672 : List Nat := [2, 1, 1, 1, 5, 1, 3, 2, 1, 3, 3]
def baseStart_5442672 : Nat := 118140960795 + 5442672 * 2 ^ 59
def prefixEnd_5442672 : Nat := 4983230072969 + 3 ^ 40 * 5442672 * 2
def baseEnd_5442672 : Nat := 2794706780767634754469613

theorem tailTrace_5442672 : CollatzResearch.WordTrace tailWord_5442672 prefixEnd_5442672 2794706780767634754469613 := by
  unfold tailWord_5442672
  simp only [CollatzResearch.WordTrace]
  refine ⟨99255278069068176609349135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132340370758757568812465513 99255278069068176609349135)
  ·
    refine ⟨148882917103602264914023703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99255278069068176609349135 148882917103602264914023703)
    ·
      refine ⟨223324375655403397371035555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148882917103602264914023703 223324375655403397371035555)
      ·
        refine ⟨334986563483105096056553333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 223324375655403397371035555 334986563483105096056553333)
        ·
          refine ⟨31404990326541102755301875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 334986563483105096056553333 31404990326541102755301875)
          ·
            refine ⟨47107485489811654132952813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31404990326541102755301875 47107485489811654132952813)
            ·
              refine ⟨17665307058679370299857305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47107485489811654132952813 17665307058679370299857305)
              ·
                refine ⟨13248980294009527724892979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17665307058679370299857305 13248980294009527724892979)
                ·
                  refine ⟨19873470441014291587339469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13248980294009527724892979 19873470441014291587339469)
                  ·
                    refine ⟨7452551415380359345252301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19873470441014291587339469 7452551415380359345252301)
                    ·
                      refine ⟨2794706780767634754469613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7452551415380359345252301 2794706780767634754469613)
                      ·
                        rfl

theorem cell23_5442672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 3, 2, 1, 3, 3].length) (baseStart_5442672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5442672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5442672 prefixEnd_5442672 := by exact prefixLift 5442672
  have htrace : WordTrace (prefixWord ++ tailWord_5442672) baseStart_5442672 baseEnd_5442672 := by
    simpa [prefixWord, tailWord_5442672, baseEnd_5442672] using wordTrace_append hprefix tailTrace_5442672
  have hstable : (prefixWord ++ tailWord_5442672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5442672).length < 2 ^ (prefixWord ++ tailWord_5442672).sum := by decide
  have hdescent : baseEnd_5442672 < baseStart_5442672 := by decide
  rcases family_descends (prefixWord ++ tailWord_5442672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5442706 : List Nat := [3, 2, 3, 1, 1, 2, 2, 3, 2, 1, 3]
def baseStart_5442706 : Nat := 118140960795 + 5442706 * 2 ^ 59
def prefixEnd_5442706 : Nat := 4983230072969 + 3 ^ 40 * 5442706 * 2
def baseEnd_5442706 : Nat := 2794724239109887621444457

theorem tailTrace_5442706 : CollatzResearch.WordTrace tailWord_5442706 prefixEnd_5442706 2794724239109887621444457 := by
  unfold tailWord_5442706
  simp only [CollatzResearch.WordTrace]
  refine ⟨49627949055003294256358993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132341197480008784683623981 49627949055003294256358993)
  ·
    refine ⟨37220961791252470692269245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49627949055003294256358993 37220961791252470692269245)
    ·
      refine ⟨13957860671719676509600967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37220961791252470692269245 13957860671719676509600967)
      ·
        refine ⟨20936791007579514764401451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13957860671719676509600967 20936791007579514764401451)
        ·
          refine ⟨31405186511369272146602177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20936791007579514764401451 31405186511369272146602177)
          ·
            refine ⟨23553889883526954109951633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31405186511369272146602177 23553889883526954109951633)
            ·
              refine ⟨17665417412645215582463725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23553889883526954109951633 17665417412645215582463725)
              ·
                refine ⟨6624531529741955843423897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17665417412645215582463725 6624531529741955843423897)
                ·
                  refine ⟨4968398647306466882567923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6624531529741955843423897 4968398647306466882567923)
                  ·
                    refine ⟨7452597970959700323851885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4968398647306466882567923 7452597970959700323851885)
                    ·
                      refine ⟨2794724239109887621444457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7452597970959700323851885 2794724239109887621444457)
                      ·
                        rfl

theorem cell23_5442706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 2, 3, 2, 1, 3].length) (baseStart_5442706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5442706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5442706 prefixEnd_5442706 := by exact prefixLift 5442706
  have htrace : WordTrace (prefixWord ++ tailWord_5442706) baseStart_5442706 baseEnd_5442706 := by
    simpa [prefixWord, tailWord_5442706, baseEnd_5442706] using wordTrace_append hprefix tailTrace_5442706
  have hstable : (prefixWord ++ tailWord_5442706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5442706).length < 2 ^ (prefixWord ++ tailWord_5442706).sum := by decide
  have hdescent : baseEnd_5442706 < baseStart_5442706 := by decide
  rcases family_descends (prefixWord ++ tailWord_5442706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5442733 : List Nat := [1, 5, 2, 1, 3, 1, 1, 3, 1, 3, 2]
def baseStart_5442733 : Nat := 118140960795 + 5442733 * 2 ^ 59
def prefixEnd_5442733 : Nat := 4983230072969 + 3 ^ 40 * 5442733 * 2
def baseEnd_5442733 : Nat := 2794738103087559015806833

theorem tailTrace_5442733 : CollatzResearch.WordTrace tailWord_5442733 prefixEnd_5442733 2794738103087559015806833 := by
  unfold tailWord_5442733
  simp only [CollatzResearch.WordTrace]
  refine ⟨198512780990915360636668853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132341853993943573757779235 198512780990915360636668853)
  ·
    refine ⟨18610573217898315059687705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 198512780990915360636668853 18610573217898315059687705)
    ·
      refine ⟨13957929913423736294765779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18610573217898315059687705 13957929913423736294765779)
      ·
        refine ⟨20936894870135604442148669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13957929913423736294765779 20936894870135604442148669)
        ·
          refine ⟨7851335576300851665805751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20936894870135604442148669 7851335576300851665805751)
          ·
            refine ⟨11777003364451277498708627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7851335576300851665805751 11777003364451277498708627)
            ·
              refine ⟨17665505046676916248062941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11777003364451277498708627 17665505046676916248062941)
              ·
                refine ⟨6624564392503843593023603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17665505046676916248062941 6624564392503843593023603)
                ·
                  refine ⟨9936846588755765389535405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6624564392503843593023603 9936846588755765389535405)
                  ·
                    refine ⟨3726317470783412021075777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9936846588755765389535405 3726317470783412021075777)
                    ·
                      refine ⟨2794738103087559015806833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3726317470783412021075777 2794738103087559015806833)
                      ·
                        rfl

theorem cell23_5442733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 1, 3, 1, 3, 2].length) (baseStart_5442733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5442733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5442733 prefixEnd_5442733 := by exact prefixLift 5442733
  have htrace : WordTrace (prefixWord ++ tailWord_5442733) baseStart_5442733 baseEnd_5442733 := by
    simpa [prefixWord, tailWord_5442733, baseEnd_5442733] using wordTrace_append hprefix tailTrace_5442733
  have hstable : (prefixWord ++ tailWord_5442733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5442733).length < 2 ^ (prefixWord ++ tailWord_5442733).sum := by decide
  have hdescent : baseEnd_5442733 < baseStart_5442733 := by decide
  rcases family_descends (prefixWord ++ tailWord_5442733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5442792 : List Nat := [2, 1, 4, 1, 2, 1, 2, 2, 1, 2, 5]
def baseStart_5442792 : Nat := 118140960795 + 5442792 * 2 ^ 59
def prefixEnd_5442792 : Nat := 4983230072969 + 3 ^ 40 * 5442792 * 2
def baseEnd_5442792 : Nat := 2794768398446174284969061

theorem tailTrace_5442792 : CollatzResearch.WordTrace tailWord_5442792 prefixEnd_5442792 2794768398446174284969061 := by
  unfold tailWord_5442792
  simp only [CollatzResearch.WordTrace]
  refine ⟨99257466448850806856533315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132343288598467742475377753 99257466448850806856533315)
  ·
    refine ⟨148886199673276210284799973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99257466448850806856533315 148886199673276210284799973)
    ·
      refine ⟨27916162438739289428399995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 148886199673276210284799973 27916162438739289428399995)
      ·
        refine ⟨41874243658108934142599993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27916162438739289428399995 41874243658108934142599993)
        ·
          refine ⟨31405682743581700606949995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41874243658108934142599993 31405682743581700606949995)
          ·
            refine ⟨47108524115372550910424993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31405682743581700606949995 47108524115372550910424993)
            ·
              refine ⟨35331393086529413182818745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47108524115372550910424993 35331393086529413182818745)
              ·
                refine ⟨26498544814897059887114059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35331393086529413182818745 26498544814897059887114059)
                ·
                  refine ⟨39747817222345589830671089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26498544814897059887114059 39747817222345589830671089)
                  ·
                    refine ⟨29810862916759192373003317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 39747817222345589830671089 29810862916759192373003317)
                    ·
                      refine ⟨2794768398446174284969061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29810862916759192373003317 2794768398446174284969061)
                      ·
                        rfl

theorem cell23_5442792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 2, 2, 1, 2, 5].length) (baseStart_5442792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5442792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5442792 prefixEnd_5442792 := by exact prefixLift 5442792
  have htrace : WordTrace (prefixWord ++ tailWord_5442792) baseStart_5442792 baseEnd_5442792 := by
    simpa [prefixWord, tailWord_5442792, baseEnd_5442792] using wordTrace_append hprefix tailTrace_5442792
  have hstable : (prefixWord ++ tailWord_5442792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5442792).length < 2 ^ (prefixWord ++ tailWord_5442792).sum := by decide
  have hdescent : baseEnd_5442792 < baseStart_5442792 := by decide
  rcases family_descends (prefixWord ++ tailWord_5442792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5442799 : List Nat := [1, 1, 2, 1, 7, 1, 1, 2, 2, 5]
def baseStart_5442799 : Nat := 118140960795 + 5442799 * 2 ^ 59
def prefixEnd_5442799 : Nat := 4983230072969 + 3 ^ 40 * 5442799 * 2
def baseEnd_5442799 : Nat := 931590664270251919193843

theorem tailTrace_5442799 : CollatzResearch.WordTrace tailWord_5442799 prefixEnd_5442799 931590664270251919193843 := by
  unfold tailWord_5442799
  simp only [CollatzResearch.WordTrace]
  refine ⟨198515188208676253908571451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132343458805784169272380967 198515188208676253908571451)
  ·
    refine ⟨297772782313014380862857177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198515188208676253908571451 297772782313014380862857177)
    ·
      refine ⟨223329586734760785647142883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 297772782313014380862857177 223329586734760785647142883)
      ·
        refine ⟨334994380102141178470714325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 223329586734760785647142883 334994380102141178470714325)
        ·
          refine ⟨7851430783643933870407367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 334994380102141178470714325 7851430783643933870407367)
          ·
            refine ⟨11777146175465900805611051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7851430783643933870407367 11777146175465900805611051)
            ·
              refine ⟨17665719263198851208416577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11777146175465900805611051 17665719263198851208416577)
              ·
                refine ⟨13249289447399138406312433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17665719263198851208416577 13249289447399138406312433)
                ·
                  refine ⟨9936967085549353804734325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13249289447399138406312433 9936967085549353804734325)
                  ·
                    refine ⟨931590664270251919193843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9936967085549353804734325 931590664270251919193843)
                    ·
                      rfl

theorem cell23_5442799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 1, 2, 2, 5].length) (baseStart_5442799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5442799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5442799 prefixEnd_5442799 := by exact prefixLift 5442799
  have htrace : WordTrace (prefixWord ++ tailWord_5442799) baseStart_5442799 baseEnd_5442799 := by
    simpa [prefixWord, tailWord_5442799, baseEnd_5442799] using wordTrace_append hprefix tailTrace_5442799
  have hstable : (prefixWord ++ tailWord_5442799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5442799).length < 2 ^ (prefixWord ++ tailWord_5442799).sum := by decide
  have hdescent : baseEnd_5442799 < baseStart_5442799 := by decide
  rcases family_descends (prefixWord ++ tailWord_5442799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5442856 : List Nat := [2, 1, 5, 1, 2, 1, 2, 2, 2, 2, 3]
def baseStart_5442856 : Nat := 118140960795 + 5442856 * 2 ^ 59
def prefixEnd_5442856 : Nat := 4983230072969 + 3 ^ 40 * 5442856 * 2
def baseEnd_5442856 : Nat := 2794801261208062034568767

theorem tailTrace_5442856 : CollatzResearch.WordTrace tailWord_5442856 prefixEnd_5442856 2794801261208062034568767 := by
  unfold tailWord_5442856
  simp only [CollatzResearch.WordTrace]
  refine ⟨99258633584734876321698211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132344844779646501762264281 99258633584734876321698211)
  ·
    refine ⟨148887950377102314482547317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99258633584734876321698211 148887950377102314482547317)
    ·
      refine ⟨13958245347853341982738811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 148887950377102314482547317 13958245347853341982738811)
      ·
        refine ⟨20937368021780012974108217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13958245347853341982738811 20937368021780012974108217)
        ·
          refine ⟨15703026016335009730581163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20937368021780012974108217 15703026016335009730581163)
          ·
            refine ⟨23554539024502514595871745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15703026016335009730581163 23554539024502514595871745)
            ·
              refine ⟨17665904268376885946903809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23554539024502514595871745 17665904268376885946903809)
              ·
                refine ⟨13249428201282664460177857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17665904268376885946903809 13249428201282664460177857)
                ·
                  refine ⟨9937071150961998345133393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13249428201282664460177857 9937071150961998345133393)
                  ·
                    refine ⟨7452803363221498758850045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9937071150961998345133393 7452803363221498758850045)
                    ·
                      refine ⟨2794801261208062034568767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7452803363221498758850045 2794801261208062034568767)
                      ·
                        rfl

theorem cell23_5442856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 2, 2, 2, 2, 3].length) (baseStart_5442856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5442856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5442856 prefixEnd_5442856 := by exact prefixLift 5442856
  have htrace : WordTrace (prefixWord ++ tailWord_5442856) baseStart_5442856 baseEnd_5442856 := by
    simpa [prefixWord, tailWord_5442856, baseEnd_5442856] using wordTrace_append hprefix tailTrace_5442856
  have hstable : (prefixWord ++ tailWord_5442856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5442856).length < 2 ^ (prefixWord ++ tailWord_5442856).sum := by decide
  have hdescent : baseEnd_5442856 < baseStart_5442856 := by decide
  rcases family_descends (prefixWord ++ tailWord_5442856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5442870 : List Nat := [5, 1, 2, 3, 1, 1, 1, 1, 2, 4, 2]
def baseStart_5442870 : Nat := 118140960795 + 5442870 * 2 ^ 59
def prefixEnd_5442870 : Nat := 4983230072969 + 3 ^ 40 * 5442870 * 2
def baseEnd_5442870 : Nat := 2794808449937224979793703

theorem tailTrace_5442870 : CollatzResearch.WordTrace tailWord_5442870 prefixEnd_5442870 2794808449937224979793703 := by
  unfold tailWord_5442870
  simp only [CollatzResearch.WordTrace]
  refine ⟨12407361111963689564650379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 132345185194279355356270709 12407361111963689564650379)
  ·
    refine ⟨18611041667945534346975569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12407361111963689564650379 18611041667945534346975569)
    ·
      refine ⟨13958281250959150760231677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18611041667945534346975569 13958281250959150760231677)
      ·
        refine ⟨5234355469109681535086879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13958281250959150760231677 5234355469109681535086879)
        ·
          refine ⟨7851533203664522302630319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5234355469109681535086879 7851533203664522302630319)
          ·
            refine ⟨11777299805496783453945479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7851533203664522302630319 11777299805496783453945479)
            ·
              refine ⟨17665949708245175180918219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11777299805496783453945479 17665949708245175180918219)
              ·
                refine ⟨26498924562367762771377329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17665949708245175180918219 26498924562367762771377329)
                ·
                  refine ⟨19874193421775822078532997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26498924562367762771377329 19874193421775822078532997)
                  ·
                    refine ⟨3726411266582966639724937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19874193421775822078532997 3726411266582966639724937)
                    ·
                      refine ⟨2794808449937224979793703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3726411266582966639724937 2794808449937224979793703)
                      ·
                        rfl

theorem cell23_5442870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 1, 1, 2, 4, 2].length) (baseStart_5442870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5442870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5442870 prefixEnd_5442870 := by exact prefixLift 5442870
  have htrace : WordTrace (prefixWord ++ tailWord_5442870) baseStart_5442870 baseEnd_5442870 := by
    simpa [prefixWord, tailWord_5442870, baseEnd_5442870] using wordTrace_append hprefix tailTrace_5442870
  have hstable : (prefixWord ++ tailWord_5442870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5442870).length < 2 ^ (prefixWord ++ tailWord_5442870).sum := by decide
  have hdescent : baseEnd_5442870 < baseStart_5442870 := by decide
  rcases family_descends (prefixWord ++ tailWord_5442870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5442903 : List Nat := [1, 1, 3, 2, 3, 2, 1, 5, 1, 1, 3]
def baseStart_5442903 : Nat := 118140960795 + 5442903 * 2 ^ 59
def prefixEnd_5442903 : Nat := 4983230072969 + 3 ^ 40 * 5442903 * 2
def baseEnd_5442903 : Nat := 2794825394798823350681051

theorem tailTrace_5442903 : CollatzResearch.WordTrace tailWord_5442903 prefixEnd_5442903 2794825394798823350681051 := by
  unfold tailWord_5442903
  simp only [CollatzResearch.WordTrace]
  refine ⟨198518981400299479670357363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132345987600199653113571575 198518981400299479670357363)
  ·
    refine ⟨297778472100449219505536045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198518981400299479670357363 297778472100449219505536045)
    ·
      refine ⟨111666927037668457314576017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 297778472100449219505536045 111666927037668457314576017)
      ·
        refine ⟨83750195278251342985932013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111666927037668457314576017 83750195278251342985932013)
        ·
          refine ⟨31406323229344253619724505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 83750195278251342985932013 31406323229344253619724505)
          ·
            refine ⟨23554742422008190214793379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31406323229344253619724505 23554742422008190214793379)
            ·
              refine ⟨35332113633012285322190069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23554742422008190214793379 35332113633012285322190069)
              ·
                refine ⟨3312385653094901748955319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 35332113633012285322190069 3312385653094901748955319)
                ·
                  refine ⟨4968578479642352623432979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3312385653094901748955319 4968578479642352623432979)
                  ·
                    refine ⟨7452867719463528935149469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4968578479642352623432979 7452867719463528935149469)
                    ·
                      refine ⟨2794825394798823350681051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7452867719463528935149469 2794825394798823350681051)
                      ·
                        rfl

theorem cell23_5442903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 1, 5, 1, 1, 3].length) (baseStart_5442903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5442903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5442903 prefixEnd_5442903 := by exact prefixLift 5442903
  have htrace : WordTrace (prefixWord ++ tailWord_5442903) baseStart_5442903 baseEnd_5442903 := by
    simpa [prefixWord, tailWord_5442903, baseEnd_5442903] using wordTrace_append hprefix tailTrace_5442903
  have hstable : (prefixWord ++ tailWord_5442903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5442903).length < 2 ^ (prefixWord ++ tailWord_5442903).sum := by decide
  have hdescent : baseEnd_5442903 < baseStart_5442903 := by decide
  rcases family_descends (prefixWord ++ tailWord_5442903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5442906 : List Nat := [3, 1, 1, 2, 1, 2, 6, 1, 1, 5]
def baseStart_5442906 : Nat := 118140960795 + 5442906 * 2 ^ 59
def prefixEnd_5442906 : Nat := 4983230072969 + 3 ^ 40 * 5442906 * 2
def baseEnd_5442906 : Nat := 931608978413595612981179

theorem tailTrace_5442906 : CollatzResearch.WordTrace tailWord_5442906 prefixEnd_5442906 931608978413595612981179 := by
  unfold tailWord_5442906
  simp only [CollatzResearch.WordTrace]
  refine ⟨49629772704822152795679143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132346060546192407455144381 49629772704822152795679143)
  ·
    refine ⟨74444659057233229193518715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49629772704822152795679143 74444659057233229193518715)
    ·
      refine ⟨111666988585849843790278073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74444659057233229193518715 111666988585849843790278073)
      ·
        refine ⟨83750241439387382842708555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111666988585849843790278073 83750241439387382842708555)
        ·
          refine ⟨125625362159081074264062833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83750241439387382842708555 125625362159081074264062833)
          ·
            refine ⟨94219021619310805698047125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 125625362159081074264062833 94219021619310805698047125)
            ·
              refine ⟨4416516638405194017095959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 94219021619310805698047125 4416516638405194017095959)
              ·
                refine ⟨6624774957607791025643939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4416516638405194017095959 6624774957607791025643939)
                ·
                  refine ⟨9937162436411686538465909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6624774957607791025643939 9937162436411686538465909)
                  ·
                    refine ⟨931608978413595612981179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9937162436411686538465909 931608978413595612981179)
                    ·
                      rfl

theorem cell23_5442906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 6, 1, 1, 5].length) (baseStart_5442906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5442906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5442906 prefixEnd_5442906 := by exact prefixLift 5442906
  have htrace : WordTrace (prefixWord ++ tailWord_5442906) baseStart_5442906 baseEnd_5442906 := by
    simpa [prefixWord, tailWord_5442906, baseEnd_5442906] using wordTrace_append hprefix tailTrace_5442906
  have hstable : (prefixWord ++ tailWord_5442906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5442906).length < 2 ^ (prefixWord ++ tailWord_5442906).sum := by decide
  have hdescent : baseEnd_5442906 < baseStart_5442906 := by decide
  rcases family_descends (prefixWord ++ tailWord_5442906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5442929 : List Nat := [1, 2, 2, 2, 1, 2, 2, 1, 5, 2, 3]
def baseStart_5442929 : Nat := 118140960795 + 5442929 * 2 ^ 59
def prefixEnd_5442929 : Nat := 4983230072969 + 3 ^ 40 * 5442929 * 2
def baseEnd_5442929 : Nat := 2794838745295840248955931

theorem tailTrace_5442929 : CollatzResearch.WordTrace tailWord_5442929 prefixEnd_5442929 2794838745295840248955931 := by
  unfold tailWord_5442929
  simp only [CollatzResearch.WordTrace]
  refine ⟨198519929698205286110803841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132346619798803524073869227 198519929698205286110803841)
  ·
    refine ⟨148889947273653964583102881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 198519929698205286110803841 148889947273653964583102881)
    ·
      refine ⟨111667460455240473437327161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 148889947273653964583102881 111667460455240473437327161)
      ·
        refine ⟨83750595341430355077995371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111667460455240473437327161 83750595341430355077995371)
        ·
          refine ⟨125625893012145532616993057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83750595341430355077995371 125625893012145532616993057)
          ·
            refine ⟨94219419759109149462744793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 125625893012145532616993057 94219419759109149462744793)
            ·
              refine ⟨70664564819331862097058595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 94219419759109149462744793 70664564819331862097058595)
              ·
                refine ⟨105996847228997793145587893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70664564819331862097058595 105996847228997793145587893)
                ·
                  refine ⟨9937204427718543107398865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 105996847228997793145587893 9937204427718543107398865)
                  ·
                    refine ⟨7452903320788907330549149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9937204427718543107398865 7452903320788907330549149)
                    ·
                      refine ⟨2794838745295840248955931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7452903320788907330549149 2794838745295840248955931)
                      ·
                        rfl

theorem cell23_5442929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 1, 5, 2, 3].length) (baseStart_5442929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5442929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5442929 prefixEnd_5442929 := by exact prefixLift 5442929
  have htrace : WordTrace (prefixWord ++ tailWord_5442929) baseStart_5442929 baseEnd_5442929 := by
    simpa [prefixWord, tailWord_5442929, baseEnd_5442929] using wordTrace_append hprefix tailTrace_5442929
  have hstable : (prefixWord ++ tailWord_5442929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5442929).length < 2 ^ (prefixWord ++ tailWord_5442929).sum := by decide
  have hdescent : baseEnd_5442929 < baseStart_5442929 := by decide
  rcases family_descends (prefixWord ++ tailWord_5442929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5442949 : List Nat := [1, 3, 1, 1, 3, 1, 6, 7]
def baseStart_5442949 : Nat := 118140960795 + 5442949 * 2 ^ 59
def prefixEnd_5442949 : Nat := 4983230072969 + 3 ^ 40 * 5442949 * 2
def baseEnd_5442949 : Nat := 103512926478108524840957

theorem tailTrace_5442949 : CollatzResearch.WordTrace tailWord_5442949 prefixEnd_5442949 103512926478108524840957 := by
  unfold tailWord_5442949
  simp only [CollatzResearch.WordTrace]
  refine ⟨198520659158132829526531901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132347106105421886351021267 198520659158132829526531901)
  ·
    refine ⟨74445247184299811072449463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 198520659158132829526531901 74445247184299811072449463)
    ·
      refine ⟨111667870776449716608674195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74445247184299811072449463 111667870776449716608674195)
      ·
        refine ⟨167501806164674574913011293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111667870776449716608674195 167501806164674574913011293)
        ·
          refine ⟨62813177311752965592379235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 167501806164674574913011293 62813177311752965592379235)
          ·
            refine ⟨94219765967629448388568853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62813177311752965592379235 94219765967629448388568853)
            ·
              refine ⟨4416551529732630393214165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 94219765967629448388568853 4416551529732630393214165)
              ·
                refine ⟨103512926478108524840957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4416551529732630393214165 103512926478108524840957)
                ·
                  rfl

theorem cell23_5442949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 6, 7].length) (baseStart_5442949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5442949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5442949 prefixEnd_5442949 := by exact prefixLift 5442949
  have htrace : WordTrace (prefixWord ++ tailWord_5442949) baseStart_5442949 baseEnd_5442949 := by
    simpa [prefixWord, tailWord_5442949, baseEnd_5442949] using wordTrace_append hprefix tailTrace_5442949
  have hstable : (prefixWord ++ tailWord_5442949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5442949).length < 2 ^ (prefixWord ++ tailWord_5442949).sum := by decide
  have hdescent : baseEnd_5442949 < baseStart_5442949 := by decide
  rcases family_descends (prefixWord ++ tailWord_5442949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5442976 : List Nat := [2, 1, 1, 4, 1, 2, 1, 3, 4, 1, 3]
def baseStart_5442976 : Nat := 118140960795 + 5442976 * 2 ^ 59
def prefixEnd_5442976 : Nat := 4983230072969 + 3 ^ 40 * 5442976 * 2
def baseEnd_5442976 : Nat := 2794862878886601565068215

theorem tailTrace_5442976 : CollatzResearch.WordTrace tailWord_5442976 prefixEnd_5442976 2794862878886601565068215 := by
  unfold tailWord_5442976
  simp only [CollatzResearch.WordTrace]
  refine ⟨99260821964517506568882391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132347762619356675425176521 99260821964517506568882391)
  ·
    refine ⟨148891232946776259853323587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99260821964517506568882391 148891232946776259853323587)
    ·
      refine ⟨223336849420164389779985381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148891232946776259853323587 223336849420164389779985381)
      ·
        refine ⟨41875659266280823083747259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 223336849420164389779985381 41875659266280823083747259)
        ·
          refine ⟨62813488899421234625620889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41875659266280823083747259 62813488899421234625620889)
          ·
            refine ⟨47110116674565925969215667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62813488899421234625620889 47110116674565925969215667)
            ·
              refine ⟨70665175011848888953823501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47110116674565925969215667 70665175011848888953823501)
              ·
                refine ⟨26499440629443333357683813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 70665175011848888953823501 26499440629443333357683813)
                ·
                  refine ⟨4968645118020625004565715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26499440629443333357683813 4968645118020625004565715)
                  ·
                    refine ⟨7452967677030937506848573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4968645118020625004565715 7452967677030937506848573)
                    ·
                      refine ⟨2794862878886601565068215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7452967677030937506848573 2794862878886601565068215)
                      ·
                        rfl

theorem cell23_5442976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 3, 4, 1, 3].length) (baseStart_5442976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5442976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5442976 prefixEnd_5442976 := by exact prefixLift 5442976
  have htrace : WordTrace (prefixWord ++ tailWord_5442976) baseStart_5442976 baseEnd_5442976 := by
    simpa [prefixWord, tailWord_5442976, baseEnd_5442976] using wordTrace_append hprefix tailTrace_5442976
  have hstable : (prefixWord ++ tailWord_5442976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5442976).length < 2 ^ (prefixWord ++ tailWord_5442976).sum := by decide
  have hdescent : baseEnd_5442976 < baseStart_5442976 := by decide
  rcases family_descends (prefixWord ++ tailWord_5442976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5442993 : List Nat := [1, 2, 2, 4, 1, 1, 3, 3, 2, 1, 3]
def baseStart_5442993 : Nat := 118140960795 + 5442993 * 2 ^ 59
def prefixEnd_5442993 : Nat := 4983230072969 + 3 ^ 40 * 5442993 * 2
def baseEnd_5442993 : Nat := 2794871608057727998555637

theorem tailTrace_5442993 : CollatzResearch.WordTrace tailWord_5442993 prefixEnd_5442993 2794871608057727998555637 := by
  unfold tailWord_5442993
  simp only [CollatzResearch.WordTrace]
  refine ⟨198522263969973425041133633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132348175979982283360755755 198522263969973425041133633)
  ·
    refine ⟨148891697977480068780850225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 198522263969973425041133633 148891697977480068780850225)
    ·
      refine ⟨111668773483110051585637669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 148891697977480068780850225 111668773483110051585637669)
      ·
        refine ⟨20937895028083134672307063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 111668773483110051585637669 20937895028083134672307063)
        ·
          refine ⟨31406842542124702008460595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20937895028083134672307063 31406842542124702008460595)
          ·
            refine ⟨47110263813187053012690893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31406842542124702008460595 47110263813187053012690893)
            ·
              refine ⟨17666348929945144879759085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47110263813187053012690893 17666348929945144879759085)
              ·
                refine ⟨6624880848729429329909657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17666348929945144879759085 6624880848729429329909657)
                ·
                  refine ⟨4968660636547071997432243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6624880848729429329909657 4968660636547071997432243)
                  ·
                    refine ⟨7452990954820607996148365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4968660636547071997432243 7452990954820607996148365)
                    ·
                      refine ⟨2794871608057727998555637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7452990954820607996148365 2794871608057727998555637)
                      ·
                        rfl

theorem cell23_5442993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 3, 3, 2, 1, 3].length) (baseStart_5442993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5442993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5442993 prefixEnd_5442993 := by exact prefixLift 5442993
  have htrace : WordTrace (prefixWord ++ tailWord_5442993) baseStart_5442993 baseEnd_5442993 := by
    simpa [prefixWord, tailWord_5442993, baseEnd_5442993] using wordTrace_append hprefix tailTrace_5442993
  have hstable : (prefixWord ++ tailWord_5442993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5442993).length < 2 ^ (prefixWord ++ tailWord_5442993).sum := by decide
  have hdescent : baseEnd_5442993 < baseStart_5442993 := by decide
  rcases family_descends (prefixWord ++ tailWord_5442993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5443019 : List Nat := [1, 1, 1, 1, 3, 3, 4, 1, 2, 1, 5]
def baseStart_5443019 : Nat := 118140960795 + 5443019 * 2 ^ 59
def prefixEnd_5443019 : Nat := 4983230072969 + 3 ^ 40 * 5443019 * 2
def baseEnd_5443019 : Nat := 2794884958554744896830517

theorem tailTrace_5443019 : CollatzResearch.WordTrace tailWord_5443019 prefixEnd_5443019 2794884958554744896830517 := by
  unfold tailWord_5443019
  simp only [CollatzResearch.WordTrace]
  refine ⟨198523212267879231481580111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132348808178586154321053407 198523212267879231481580111)
  ·
    refine ⟨297784818401818847222370167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198523212267879231481580111 297784818401818847222370167)
    ·
      refine ⟨446677227602728270833555251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 297784818401818847222370167 446677227602728270833555251)
      ·
        refine ⟨670015841404092406250332877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 446677227602728270833555251 670015841404092406250332877)
        ·
          refine ⟨251255940526534652343874829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 670015841404092406250332877 251255940526534652343874829)
          ·
            refine ⟨94220977697450494628953061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 251255940526534652343874829 94220977697450494628953061)
            ·
              refine ⟨17666433318271967742928699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 94220977697450494628953061 17666433318271967742928699)
              ·
                refine ⟨26499649977407951614393049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17666433318271967742928699 26499649977407951614393049)
                ·
                  refine ⟨19874737483055963710794787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26499649977407951614393049 19874737483055963710794787)
                  ·
                    refine ⟨29812106224583945566192181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19874737483055963710794787 29812106224583945566192181)
                    ·
                      refine ⟨2794884958554744896830517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29812106224583945566192181 2794884958554744896830517)
                      ·
                        rfl

theorem cell23_5443019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 4, 1, 2, 1, 5].length) (baseStart_5443019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5443019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5443019 prefixEnd_5443019 := by exact prefixLift 5443019
  have htrace : WordTrace (prefixWord ++ tailWord_5443019) baseStart_5443019 baseEnd_5443019 := by
    simpa [prefixWord, tailWord_5443019, baseEnd_5443019] using wordTrace_append hprefix tailTrace_5443019
  have hstable : (prefixWord ++ tailWord_5443019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5443019).length < 2 ^ (prefixWord ++ tailWord_5443019).sum := by decide
  have hdescent : baseEnd_5443019 < baseStart_5443019 := by decide
  rcases family_descends (prefixWord ++ tailWord_5443019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5443039 : List Nat := [1, 1, 2, 3, 3, 1, 2, 3, 7]
def baseStart_5443039 : Nat := 118140960795 + 5443039 * 2 ^ 59
def prefixEnd_5443039 : Nat := 4983230072969 + 3 ^ 40 * 5443039 * 2
def baseEnd_5443039 : Nat := 310543914240870535397825

theorem tailTrace_5443039 : CollatzResearch.WordTrace tailWord_5443039 prefixEnd_5443039 310543914240870535397825 := by
  unfold tailWord_5443039
  simp only [CollatzResearch.WordTrace]
  refine ⟨198523941727806774897308171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132349294485204516598205447 198523941727806774897308171)
  ·
    refine ⟨297785912591710162345962257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198523941727806774897308171 297785912591710162345962257)
    ·
      refine ⟨223339434443782621759471693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 297785912591710162345962257 223339434443782621759471693)
      ·
        refine ⟨83752287916418483159801885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 223339434443782621759471693 83752287916418483159801885)
        ·
          refine ⟨31407107968656931184925707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 83752287916418483159801885 31407107968656931184925707)
          ·
            refine ⟨47110661952985396777388561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31407107968656931184925707 47110661952985396777388561)
            ·
              refine ⟨35332996464739047583041421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47110661952985396777388561 35332996464739047583041421)
              ·
                refine ⟨13249873674277142843640533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35332996464739047583041421 13249873674277142843640533)
                ·
                  refine ⟨310543914240870535397825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13249873674277142843640533 310543914240870535397825)
                  ·
                    rfl

theorem cell23_5443039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 2, 3, 7].length) (baseStart_5443039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5443039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5443039 prefixEnd_5443039 := by exact prefixLift 5443039
  have htrace : WordTrace (prefixWord ++ tailWord_5443039) baseStart_5443039 baseEnd_5443039 := by
    simpa [prefixWord, tailWord_5443039, baseEnd_5443039] using wordTrace_append hprefix tailTrace_5443039
  have hstable : (prefixWord ++ tailWord_5443039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5443039).length < 2 ^ (prefixWord ++ tailWord_5443039).sum := by decide
  have hdescent : baseEnd_5443039 < baseStart_5443039 := by decide
  rcases family_descends (prefixWord ++ tailWord_5443039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5443050 : List Nat := [3, 1, 3, 1, 4, 1, 2, 1, 1, 4, 2]
def baseStart_5443050 : Nat := 118140960795 + 5443050 * 2 ^ 59
def prefixEnd_5443050 : Nat := 4983230072969 + 3 ^ 40 * 5443050 * 2
def baseEnd_5443050 : Nat := 2794900876455034275542875

theorem tailTrace_5443050 : CollatzResearch.WordTrace tailWord_5443050 prefixEnd_5443050 2794900876455034275542875 := by
  unfold tailWord_5443050
  simp only [CollatzResearch.WordTrace]
  refine ⟨49631085732691730943989651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132349561953844615850639069 49631085732691730943989651)
  ·
    refine ⟨74446628599037596415984477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49631085732691730943989651 74446628599037596415984477)
    ·
      refine ⟨27917485724639098655994179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74446628599037596415984477 27917485724639098655994179)
      ·
        refine ⟨41876228586958647983991269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27917485724639098655994179 41876228586958647983991269)
        ·
          refine ⟨7851792860054746496998363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 41876228586958647983991269 7851792860054746496998363)
          ·
            refine ⟨11777689290082119745497545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7851792860054746496998363 11777689290082119745497545)
            ·
              refine ⟨8833266967561589809123159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11777689290082119745497545 8833266967561589809123159)
              ·
                refine ⟨13249900451342384713684739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8833266967561589809123159 13249900451342384713684739)
                ·
                  refine ⟨19874850677013577070527109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13249900451342384713684739 19874850677013577070527109)
                  ·
                    refine ⟨3726534501940045700723833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19874850677013577070527109 3726534501940045700723833)
                    ·
                      refine ⟨2794900876455034275542875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3726534501940045700723833 2794900876455034275542875)
                      ·
                        rfl

theorem cell23_5443050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 2, 1, 1, 4, 2].length) (baseStart_5443050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5443050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5443050 prefixEnd_5443050 := by exact prefixLift 5443050
  have htrace : WordTrace (prefixWord ++ tailWord_5443050) baseStart_5443050 baseEnd_5443050 := by
    simpa [prefixWord, tailWord_5443050, baseEnd_5443050] using wordTrace_append hprefix tailTrace_5443050
  have hstable : (prefixWord ++ tailWord_5443050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5443050).length < 2 ^ (prefixWord ++ tailWord_5443050).sum := by decide
  have hdescent : baseEnd_5443050 < baseStart_5443050 := by decide
  rcases family_descends (prefixWord ++ tailWord_5443050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5443078 : List Nat := [6, 2, 1, 1, 3, 1, 1, 2, 2, 1, 3]
def baseStart_5443078 : Nat := 118140960795 + 5443078 * 2 ^ 59
def prefixEnd_5443078 : Nat := 4983230072969 + 3 ^ 40 * 5443078 * 2
def baseEnd_5443078 : Nat := 2794915253913360165992747

theorem tailTrace_5443078 : CollatzResearch.WordTrace tailWord_5443078 prefixEnd_5443078 2794915253913360165992747 := by
  unfold tailWord_5443078
  simp only [CollatzResearch.WordTrace]
  refine ⟨6203917630458296392436809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 132350242783110323038651925 6203917630458296392436809)
  ·
    refine ⟨4652938222843722294327607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6203917630458296392436809 4652938222843722294327607)
    ·
      refine ⟨6979407334265583441491411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4652938222843722294327607 6979407334265583441491411)
      ·
        refine ⟨10469111001398375162237117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6979407334265583441491411 10469111001398375162237117)
        ·
          refine ⟨3925916625524390685838919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10469111001398375162237117 3925916625524390685838919)
          ·
            refine ⟨5888874938286586028758379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3925916625524390685838919 5888874938286586028758379)
            ·
              refine ⟨8833312407429879043137569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5888874938286586028758379 8833312407429879043137569)
              ·
                refine ⟨6624984305572409282353177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8833312407429879043137569 6624984305572409282353177)
                ·
                  refine ⟨4968738229179306961764883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6624984305572409282353177 4968738229179306961764883)
                  ·
                    refine ⟨7453107343768960442647325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4968738229179306961764883 7453107343768960442647325)
                    ·
                      refine ⟨2794915253913360165992747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7453107343768960442647325 2794915253913360165992747)
                      ·
                        rfl

theorem cell23_5443078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 3, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 3, 1, 1, 2, 2, 1, 3].length) (baseStart_5443078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5443078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5443078 prefixEnd_5443078 := by exact prefixLift 5443078
  have htrace : WordTrace (prefixWord ++ tailWord_5443078) baseStart_5443078 baseEnd_5443078 := by
    simpa [prefixWord, tailWord_5443078, baseEnd_5443078] using wordTrace_append hprefix tailTrace_5443078
  have hstable : (prefixWord ++ tailWord_5443078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5443078).length < 2 ^ (prefixWord ++ tailWord_5443078).sum := by decide
  have hdescent : baseEnd_5443078 < baseStart_5443078 := by decide
  rcases family_descends (prefixWord ++ tailWord_5443078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5443084 : List Nat := [2, 2, 1, 2, 6, 1, 1, 2, 2, 2, 2]
def baseStart_5443084 : Nat := 118140960795 + 5443084 * 2 ^ 59
def prefixEnd_5443084 : Nat := 4983230072969 + 3 ^ 40 * 5443084 * 2
def baseEnd_5443084 : Nat := 2794918334797287142517719

theorem tailTrace_5443084 : CollatzResearch.WordTrace tailWord_5443084 prefixEnd_5443084 2794918334797287142517719 := by
  unfold tailWord_5443084
  simp only [CollatzResearch.WordTrace]
  refine ⟨99262791506321873791348153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132350388675095831721797537 99262791506321873791348153)
  ·
    refine ⟨74447093629741405343511115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99262791506321873791348153 74447093629741405343511115)
    ·
      refine ⟨111670640444612108015266673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74447093629741405343511115 111670640444612108015266673)
      ·
        refine ⟨83752980333459081011450005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111670640444612108015266673 83752980333459081011450005)
        ·
          refine ⟨3925920953130894422411719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 83752980333459081011450005 3925920953130894422411719)
          ·
            refine ⟨5888881429696341633617579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3925920953130894422411719 5888881429696341633617579)
            ·
              refine ⟨8833322144544512450426369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5888881429696341633617579 8833322144544512450426369)
              ·
                refine ⟨6624991608408384337819777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8833322144544512450426369 6624991608408384337819777)
                ·
                  refine ⟨4968743706306288253364833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6624991608408384337819777 4968743706306288253364833)
                  ·
                    refine ⟨3726557779729716190023625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4968743706306288253364833 3726557779729716190023625)
                    ·
                      refine ⟨2794918334797287142517719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3726557779729716190023625 2794918334797287142517719)
                      ·
                        rfl

theorem cell23_5443084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 6, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 6, 1, 1, 2, 2, 2, 2].length) (baseStart_5443084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5443084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5443084 prefixEnd_5443084 := by exact prefixLift 5443084
  have htrace : WordTrace (prefixWord ++ tailWord_5443084) baseStart_5443084 baseEnd_5443084 := by
    simpa [prefixWord, tailWord_5443084, baseEnd_5443084] using wordTrace_append hprefix tailTrace_5443084
  have hstable : (prefixWord ++ tailWord_5443084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5443084).length < 2 ^ (prefixWord ++ tailWord_5443084).sum := by decide
  have hdescent : baseEnd_5443084 < baseStart_5443084 := by decide
  rcases family_descends (prefixWord ++ tailWord_5443084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5443106 : List Nat := [3, 3, 1, 1, 1, 1, 3, 2, 1, 3, 4]
def baseStart_5443106 : Nat := 118140960795 + 5443106 * 2 ^ 59
def prefixEnd_5443106 : Nat := 4983230072969 + 3 ^ 40 * 5443106 * 2
def baseEnd_5443106 : Nat := 2794929631371686056442617

theorem tailTrace_5443106 : CollatzResearch.WordTrace tailWord_5443106 prefixEnd_5443106 2794929631371686056442617 := by
  unfold tailWord_5443106
  simp only [CollatzResearch.WordTrace]
  refine ⟨49631596354641011334999293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132350923612376030226664781 49631596354641011334999293)
  ·
    refine ⟨18611848632990379250624735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49631596354641011334999293 18611848632990379250624735)
    ·
      refine ⟨27917772949485568875937103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18611848632990379250624735 27917772949485568875937103)
      ·
        refine ⟨41876659424228353313905655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27917772949485568875937103 41876659424228353313905655)
        ·
          refine ⟨62814989136342529970858483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41876659424228353313905655 62814989136342529970858483)
          ·
            refine ⟨94222483704513794956287725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62814989136342529970858483 94222483704513794956287725)
            ·
              refine ⟨35333431389192673108607897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 94222483704513794956287725 35333431389192673108607897)
              ·
                refine ⟨26500073541894504831455923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35333431389192673108607897 26500073541894504831455923)
                ·
                  refine ⟨39750110312841757247183885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26500073541894504831455923 39750110312841757247183885)
                  ·
                    refine ⟨14906291367315658967693957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 39750110312841757247183885 14906291367315658967693957)
                    ·
                      refine ⟨2794929631371686056442617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14906291367315658967693957 2794929631371686056442617)
                      ·
                        rfl

theorem cell23_5443106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 3, 2, 1, 3, 4].length) (baseStart_5443106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5443106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5443106 prefixEnd_5443106 := by exact prefixLift 5443106
  have htrace : WordTrace (prefixWord ++ tailWord_5443106) baseStart_5443106 baseEnd_5443106 := by
    simpa [prefixWord, tailWord_5443106, baseEnd_5443106] using wordTrace_append hprefix tailTrace_5443106
  have hstable : (prefixWord ++ tailWord_5443106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5443106).length < 2 ^ (prefixWord ++ tailWord_5443106).sum := by decide
  have hdescent : baseEnd_5443106 < baseStart_5443106 := by decide
  rcases family_descends (prefixWord ++ tailWord_5443106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5443146 : List Nat := [3, 1, 2, 1, 1, 3, 2, 4, 6]
def baseStart_5443146 : Nat := 118140960795 + 5443146 * 2 ^ 59
def prefixEnd_5443146 : Nat := 4983230072969 + 3 ^ 40 * 5443146 * 2
def baseEnd_5443146 : Nat := 310550018955318433326937

theorem tailTrace_5443146 : CollatzResearch.WordTrace tailWord_5443146 prefixEnd_5443146 310550018955318433326937 := by
  unfold tailWord_5443146
  simp only [CollatzResearch.WordTrace]
  refine ⟨49631961084604783042863323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132351896225612754780968861 49631961084604783042863323)
  ·
    refine ⟨74447941626907174564294985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49631961084604783042863323 74447941626907174564294985)
    ·
      refine ⟨55835956220180380923221239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74447941626907174564294985 55835956220180380923221239)
      ·
        refine ⟨83753934330270571384831859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55835956220180380923221239 83753934330270571384831859)
        ·
          refine ⟨125630901495405857077247789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83753934330270571384831859 125630901495405857077247789)
          ·
            refine ⟨47111588060777196403967921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 125630901495405857077247789 47111588060777196403967921)
            ·
              refine ⟨35333691045582897302975941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47111588060777196403967921 35333691045582897302975941)
              ·
                refine ⟨6625067071046793244307989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35333691045582897302975941 6625067071046793244307989)
                ·
                  refine ⟨310550018955318433326937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6625067071046793244307989 310550018955318433326937)
                  ·
                    rfl

theorem cell23_5443146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 2, 4, 6].length) (baseStart_5443146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5443146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5443146 prefixEnd_5443146 := by exact prefixLift 5443146
  have htrace : WordTrace (prefixWord ++ tailWord_5443146) baseStart_5443146 baseEnd_5443146 := by
    simpa [prefixWord, tailWord_5443146, baseEnd_5443146] using wordTrace_append hprefix tailTrace_5443146
  have hstable : (prefixWord ++ tailWord_5443146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5443146).length < 2 ^ (prefixWord ++ tailWord_5443146).sum := by decide
  have hdescent : baseEnd_5443146 < baseStart_5443146 := by decide
  rcases family_descends (prefixWord ++ tailWord_5443146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5443207 : List Nat := [1, 1, 4, 2, 1, 4, 1, 4, 1, 1, 3]
def baseStart_5443207 : Nat := 118140960795 + 5443207 * 2 ^ 59
def prefixEnd_5443207 : Nat := 4983230072969 + 3 ^ 40 * 5443207 * 2
def baseEnd_5443207 : Nat := 2794981492917790161279653

theorem tailTrace_5443207 : CollatzResearch.WordTrace tailWord_5443207 prefixEnd_5443207 2794981492917790161279653 := by
  unfold tailWord_5443207
  simp only [CollatzResearch.WordTrace]
  refine ⟨198530069191198139589423875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132353379460798759726282583 198530069191198139589423875)
  ·
    refine ⟨297795103786797209384135813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198530069191198139589423875 297795103786797209384135813)
    ·
      refine ⟨55836581960024476759525465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 297795103786797209384135813 55836581960024476759525465)
      ·
        refine ⟨41877436470018357569644099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55836581960024476759525465 41877436470018357569644099)
        ·
          refine ⟨62816154705027536354466149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41877436470018357569644099 62816154705027536354466149)
          ·
            refine ⟨11778029007192663066462403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 62816154705027536354466149 11778029007192663066462403)
            ·
              refine ⟨17667043510788994599693605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11778029007192663066462403 17667043510788994599693605)
              ·
                refine ⟨3312570658272936487442551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17667043510788994599693605 3312570658272936487442551)
                ·
                  refine ⟨4968855987409404731163827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3312570658272936487442551 4968855987409404731163827)
                  ·
                    refine ⟨7453283981114107096745741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4968855987409404731163827 7453283981114107096745741)
                    ·
                      refine ⟨2794981492917790161279653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7453283981114107096745741 2794981492917790161279653)
                      ·
                        rfl

theorem cell23_5443207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 1, 4, 1, 1, 3].length) (baseStart_5443207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5443207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5443207 prefixEnd_5443207 := by exact prefixLift 5443207
  have htrace : WordTrace (prefixWord ++ tailWord_5443207) baseStart_5443207 baseEnd_5443207 := by
    simpa [prefixWord, tailWord_5443207, baseEnd_5443207] using wordTrace_append hprefix tailTrace_5443207
  have hstable : (prefixWord ++ tailWord_5443207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5443207).length < 2 ^ (prefixWord ++ tailWord_5443207).sum := by decide
  have hdescent : baseEnd_5443207 < baseStart_5443207 := by decide
  rcases family_descends (prefixWord ++ tailWord_5443207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5443216 : List Nat := [2, 1, 1, 1, 1, 1, 3, 6, 1, 1, 5]
def baseStart_5443216 : Nat := 118140960795 + 5443216 * 2 ^ 59
def prefixEnd_5443216 : Nat := 4983230072969 + 3 ^ 40 * 5443216 * 2
def baseEnd_5443216 : Nat := 2794986114243680626067111

theorem tailTrace_5443216 : CollatzResearch.WordTrace tailWord_5443216 prefixEnd_5443216 2794986114243680626067111 := by
  unfold tailWord_5443216
  simp only [CollatzResearch.WordTrace]
  refine ⟨99265198724082767063250751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132353598298777022751001001 99265198724082767063250751)
  ·
    refine ⟨148897798086124150594876127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99265198724082767063250751 148897798086124150594876127)
    ·
      refine ⟨223346697129186225892314191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148897798086124150594876127 223346697129186225892314191)
      ·
        refine ⟨335020045693779338838471287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 223346697129186225892314191 335020045693779338838471287)
        ·
          refine ⟨502530068540669008257706931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 335020045693779338838471287 502530068540669008257706931)
          ·
            refine ⟨753795102811003512386560397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 502530068540669008257706931 753795102811003512386560397)
            ·
              refine ⟨282673163554126317144960149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 753795102811003512386560397 282673163554126317144960149)
              ·
                refine ⟨13250304541599671116170007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 282673163554126317144960149 13250304541599671116170007)
                ·
                  refine ⟨19875456812399506674255011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13250304541599671116170007 19875456812399506674255011)
                  ·
                    refine ⟨29813185218599260011382517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19875456812399506674255011 29813185218599260011382517)
                    ·
                      refine ⟨2794986114243680626067111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29813185218599260011382517 2794986114243680626067111)
                      ·
                        rfl

theorem cell23_5443216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 6, 1, 1, 5].length) (baseStart_5443216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5443216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5443216 prefixEnd_5443216 := by exact prefixLift 5443216
  have htrace : WordTrace (prefixWord ++ tailWord_5443216) baseStart_5443216 baseEnd_5443216 := by
    simpa [prefixWord, tailWord_5443216, baseEnd_5443216] using wordTrace_append hprefix tailTrace_5443216
  have hstable : (prefixWord ++ tailWord_5443216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5443216).length < 2 ^ (prefixWord ++ tailWord_5443216).sum := by decide
  have hdescent : baseEnd_5443216 < baseStart_5443216 := by decide
  rcases family_descends (prefixWord ++ tailWord_5443216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5443223 : List Nat := [1, 1, 3, 3, 2, 3, 2, 1, 1, 6]
def baseStart_5443223 : Nat := 118140960795 + 5443223 * 2 ^ 59
def prefixEnd_5443223 : Nat := 4983230072969 + 3 ^ 40 * 5443223 * 2
def baseEnd_5443223 : Nat := 931663236202754032893193

theorem tailTrace_5443223 : CollatzResearch.WordTrace tailWord_5443223 prefixEnd_5443223 931663236202754032893193 := by
  unfold tailWord_5443223
  simp only [CollatzResearch.WordTrace]
  refine ⟨198530652759140174322006323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132353768506093449548004215 198530652759140174322006323)
  ·
    refine ⟨297795979138710261483009485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198530652759140174322006323 297795979138710261483009485)
    ·
      refine ⟨111673492177016348056128557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 297795979138710261483009485 111673492177016348056128557)
      ·
        refine ⟨41877559566381130521048209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 111673492177016348056128557 41877559566381130521048209)
        ·
          refine ⟨31408169674785847890786157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41877559566381130521048209 31408169674785847890786157)
          ·
            refine ⟨11778063628044692959044809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31408169674785847890786157 11778063628044692959044809)
            ·
              refine ⟨8833547721033519719283607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11778063628044692959044809 8833547721033519719283607)
              ·
                refine ⟨13250321581550279578925411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8833547721033519719283607 13250321581550279578925411)
                ·
                  refine ⟨19875482372325419368388117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13250321581550279578925411 19875482372325419368388117)
                  ·
                    refine ⟨931663236202754032893193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19875482372325419368388117 931663236202754032893193)
                    ·
                      rfl

theorem cell23_5443223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 2, 1, 1, 6].length) (baseStart_5443223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5443223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5443223 prefixEnd_5443223 := by exact prefixLift 5443223
  have htrace : WordTrace (prefixWord ++ tailWord_5443223) baseStart_5443223 baseEnd_5443223 := by
    simpa [prefixWord, tailWord_5443223, baseEnd_5443223] using wordTrace_append hprefix tailTrace_5443223
  have hstable : (prefixWord ++ tailWord_5443223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5443223).length < 2 ^ (prefixWord ++ tailWord_5443223).sum := by decide
  have hdescent : baseEnd_5443223 < baseStart_5443223 := by decide
  rcases family_descends (prefixWord ++ tailWord_5443223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5443230 : List Nat := [4, 3, 1, 1, 1, 2, 2, 1, 3, 1, 4]
def baseStart_5443230 : Nat := 118140960795 + 5443230 * 2 ^ 59
def prefixEnd_5443230 : Nat := 4983230072969 + 3 ^ 40 * 5443230 * 2
def baseEnd_5443230 : Nat := 2794993302972843571292047

theorem tailTrace_5443230 : CollatzResearch.WordTrace tailWord_5443230 prefixEnd_5443230 2794993302972843571292047 := by
  unfold tailWord_5443230
  simp only [CollatzResearch.WordTrace]
  refine ⟨24816363508764351814688893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 132353938713409876345007429 24816363508764351814688893)
  ·
    refine ⟨9306136315786631930508335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24816363508764351814688893 9306136315786631930508335)
    ·
      refine ⟨13959204473679947895762503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9306136315786631930508335 13959204473679947895762503)
      ·
        refine ⟨20938806710519921843643755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13959204473679947895762503 20938806710519921843643755)
        ·
          refine ⟨31408210065779882765465633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20938806710519921843643755 31408210065779882765465633)
          ·
            refine ⟨23556157549334912074099225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31408210065779882765465633 23556157549334912074099225)
            ·
              refine ⟨17667118162001184055574419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23556157549334912074099225 17667118162001184055574419)
              ·
                refine ⟨26500677243001776083361629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17667118162001184055574419 26500677243001776083361629)
                ·
                  refine ⟨9937753966125666031260611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26500677243001776083361629 9937753966125666031260611)
                  ·
                    refine ⟨14906630949188499046890917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9937753966125666031260611 14906630949188499046890917)
                    ·
                      refine ⟨2794993302972843571292047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14906630949188499046890917 2794993302972843571292047)
                      ·
                        rfl

theorem cell23_5443230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 2, 1, 3, 1, 4].length) (baseStart_5443230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5443230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5443230 prefixEnd_5443230 := by exact prefixLift 5443230
  have htrace : WordTrace (prefixWord ++ tailWord_5443230) baseStart_5443230 baseEnd_5443230 := by
    simpa [prefixWord, tailWord_5443230, baseEnd_5443230] using wordTrace_append hprefix tailTrace_5443230
  have hstable : (prefixWord ++ tailWord_5443230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5443230).length < 2 ^ (prefixWord ++ tailWord_5443230).sum := by decide
  have hdescent : baseEnd_5443230 < baseStart_5443230 := by decide
  rcases family_descends (prefixWord ++ tailWord_5443230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5443253 : List Nat := [1, 3, 3, 3, 2, 1, 10]
def baseStart_5443253 : Nat := 118140960795 + 5443253 * 2 ^ 59
def prefixEnd_5443253 : Nat := 4983230072969 + 3 ^ 40 * 5443253 * 2
def baseEnd_5443253 : Nat := 34506235963307370139561

theorem tailTrace_5443253 : CollatzResearch.WordTrace tailWord_5443253 prefixEnd_5443253 34506235963307370139561 := by
  unfold tailWord_5443253
  simp only [CollatzResearch.WordTrace]
  refine ⟨198531746949031489445598413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132354497966020992963732275 198531746949031489445598413)
  ·
    refine ⟨74449405105886808542099405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 198531746949031489445598413 74449405105886808542099405)
    ·
      refine ⟨27918526914707553203287277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74449405105886808542099405 27918526914707553203287277)
      ·
        refine ⟨10469447593015332451232729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27918526914707553203287277 10469447593015332451232729)
        ·
          refine ⟨7852085694761499338424547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10469447593015332451232729 7852085694761499338424547)
          ·
            refine ⟨11778128542142249007636821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7852085694761499338424547 11778128542142249007636821)
            ·
              refine ⟨34506235963307370139561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 11778128542142249007636821 34506235963307370139561)
              ·
                rfl

theorem cell23_5443253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 10].length) (baseStart_5443253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5443253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5443253 prefixEnd_5443253 := by exact prefixLift 5443253
  have htrace : WordTrace (prefixWord ++ tailWord_5443253) baseStart_5443253 baseEnd_5443253 := by
    simpa [prefixWord, tailWord_5443253, baseEnd_5443253] using wordTrace_append hprefix tailTrace_5443253
  have hstable : (prefixWord ++ tailWord_5443253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5443253).length < 2 ^ (prefixWord ++ tailWord_5443253).sum := by decide
  have hdescent : baseEnd_5443253 < baseStart_5443253 := by decide
  rcases family_descends (prefixWord ++ tailWord_5443253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5443277 : List Nat := [1, 6, 2, 1, 1, 1, 3, 1, 1, 2, 4]
def baseStart_5443277 : Nat := 118140960795 + 5443277 * 2 ^ 59
def prefixEnd_5443277 : Nat := 4983230072969 + 3 ^ 40 * 5443277 * 2
def baseEnd_5443277 : Nat := 2795017436563604887404331

theorem tailTrace_5443277 : CollatzResearch.WordTrace tailWord_5443277 prefixEnd_5443277 2795017436563604887404331 := by
  unfold tailWord_5443277
  simp only [CollatzResearch.WordTrace]
  refine ⟨198532622300944541544472085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132355081533963027696314723 198532622300944541544472085)
  ·
    refine ⟨9306216670356775384897129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 198532622300944541544472085 9306216670356775384897129)
    ·
      refine ⟨6979662502767581538672847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9306216670356775384897129 6979662502767581538672847)
      ·
        refine ⟨10469493754151372308009271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6979662502767581538672847 10469493754151372308009271)
        ·
          refine ⟨15704240631227058462013907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10469493754151372308009271 15704240631227058462013907)
          ·
            refine ⟨23556360946840587693020861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15704240631227058462013907 23556360946840587693020861)
            ·
              refine ⟨8833635355065220384882823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23556360946840587693020861 8833635355065220384882823)
              ·
                refine ⟨13250453032597830577324235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8833635355065220384882823 13250453032597830577324235)
                ·
                  refine ⟨19875679548896745865986353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13250453032597830577324235 19875679548896745865986353)
                  ·
                    refine ⟨14906759661672559399489765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19875679548896745865986353 14906759661672559399489765)
                    ·
                      refine ⟨2795017436563604887404331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14906759661672559399489765 2795017436563604887404331)
                      ·
                        rfl

theorem cell23_5443277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 3, 1, 1, 2, 4].length) (baseStart_5443277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5443277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5443277 prefixEnd_5443277 := by exact prefixLift 5443277
  have htrace : WordTrace (prefixWord ++ tailWord_5443277) baseStart_5443277 baseEnd_5443277 := by
    simpa [prefixWord, tailWord_5443277, baseEnd_5443277] using wordTrace_append hprefix tailTrace_5443277
  have hstable : (prefixWord ++ tailWord_5443277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5443277).length < 2 ^ (prefixWord ++ tailWord_5443277).sum := by decide
  have hdescent : baseEnd_5443277 < baseStart_5443277 := by decide
  rcases family_descends (prefixWord ++ tailWord_5443277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5443296 : List Nat := [2, 1, 1, 3, 1, 2, 2, 2, 1, 8]
def baseStart_5443296 : Nat := 118140960795 + 5443296 * 2 ^ 59
def prefixEnd_5443296 : Nat := 4983230072969 + 3 ^ 40 * 5443296 * 2
def baseEnd_5443296 : Nat := 931675730898680104355581

theorem tailTrace_5443296 : CollatzResearch.WordTrace tailWord_5443296 prefixEnd_5443296 931675730898680104355581 := by
  unfold tailWord_5443296
  simp only [CollatzResearch.WordTrace]
  refine ⟨99266657643937853894706871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132355543525250471859609161 99266657643937853894706871)
  ·
    refine ⟨148899986465906780842060307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99266657643937853894706871 148899986465906780842060307)
    ·
      refine ⟨223349979698860171263090461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148899986465906780842060307 223349979698860171263090461)
      ·
        refine ⟨83756242387072564223658923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 223349979698860171263090461 83756242387072564223658923)
        ·
          refine ⟨125634363580608846335488385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83756242387072564223658923 125634363580608846335488385)
          ·
            refine ⟨94225772685456634751616289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 125634363580608846335488385 94225772685456634751616289)
            ·
              refine ⟨70669329514092476063712217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 94225772685456634751616289 70669329514092476063712217)
              ·
                refine ⟨53001997135569357047784163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 70669329514092476063712217 53001997135569357047784163)
                ·
                  refine ⟨79502995703354035571676245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53001997135569357047784163 79502995703354035571676245)
                  ·
                    refine ⟨931675730898680104355581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 79502995703354035571676245 931675730898680104355581)
                    ·
                      rfl

theorem cell23_5443296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 2, 1, 8].length) (baseStart_5443296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5443296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5443296 prefixEnd_5443296 := by exact prefixLift 5443296
  have htrace : WordTrace (prefixWord ++ tailWord_5443296) baseStart_5443296 baseEnd_5443296 := by
    simpa [prefixWord, tailWord_5443296, baseEnd_5443296] using wordTrace_append hprefix tailTrace_5443296
  have hstable : (prefixWord ++ tailWord_5443296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5443296).length < 2 ^ (prefixWord ++ tailWord_5443296).sum := by decide
  have hdescent : baseEnd_5443296 < baseStart_5443296 := by decide
  rcases family_descends (prefixWord ++ tailWord_5443296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5443360 : List Nat := [2, 1, 1, 5, 1, 1, 2, 5, 5]
def baseStart_5443360 : Nat := 118140960795 + 5443360 * 2 ^ 59
def prefixEnd_5443360 : Nat := 4983230072969 + 3 ^ 40 * 5443360 * 2
def baseEnd_5443360 : Nat := 310562228384214229185161

theorem tailTrace_5443360 : CollatzResearch.WordTrace tailWord_5443360 prefixEnd_5443360 310562228384214229185161 := by
  unfold tailWord_5443360
  simp only [CollatzResearch.WordTrace]
  refine ⟨99267824779821923359871767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132357099706429231146495689 99267824779821923359871767)
  ·
    refine ⟨148901737169732885039807651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99267824779821923359871767 148901737169732885039807651)
    ·
      refine ⟨223352605754599327559711477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148901737169732885039807651 223352605754599327559711477)
      ·
        refine ⟨20939306789493686958722951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 223352605754599327559711477 20939306789493686958722951)
        ·
          refine ⟨31408960184240530438084427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20939306789493686958722951 31408960184240530438084427)
          ·
            refine ⟨47113440276360795657126641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31408960184240530438084427 47113440276360795657126641)
            ·
              refine ⟨35335080207270596742844981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47113440276360795657126641 35335080207270596742844981)
              ·
                refine ⟨3312663769431618444641717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 35335080207270596742844981 3312663769431618444641717)
                ·
                  refine ⟨310562228384214229185161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3312663769431618444641717 310562228384214229185161)
                  ·
                    rfl

theorem cell23_5443360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 2, 5, 5].length) (baseStart_5443360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5443360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5443360 prefixEnd_5443360 := by exact prefixLift 5443360
  have htrace : WordTrace (prefixWord ++ tailWord_5443360) baseStart_5443360 baseEnd_5443360 := by
    simpa [prefixWord, tailWord_5443360, baseEnd_5443360] using wordTrace_append hprefix tailTrace_5443360
  have hstable : (prefixWord ++ tailWord_5443360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5443360).length < 2 ^ (prefixWord ++ tailWord_5443360).sum := by decide
  have hdescent : baseEnd_5443360 < baseStart_5443360 := by decide
  rcases family_descends (prefixWord ++ tailWord_5443360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5443377 : List Nat := [1, 2, 2, 3, 2, 2, 4, 2, 5]
def baseStart_5443377 : Nat := 118140960795 + 5443377 * 2 ^ 59
def prefixEnd_5443377 : Nat := 4983230072969 + 3 ^ 40 * 5443377 * 2
def baseEnd_5443377 : Nat := 310563198292117166239319

theorem tailTrace_5443377 : CollatzResearch.WordTrace tailWord_5443377 prefixEnd_5443377 310563198292117166239319 := by
  unfold tailWord_5443377
  simp only [CollatzResearch.WordTrace]
  refine ⟨198536269600582258623112385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132357513067054839082074923 198536269600582258623112385)
  ·
    refine ⟨148902202200436693967334289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 198536269600582258623112385 148902202200436693967334289)
    ·
      refine ⟨111676651650327520475500717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 148902202200436693967334289 111676651650327520475500717)
      ·
        refine ⟨41878744368872820178312769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 111676651650327520475500717 41878744368872820178312769)
        ·
          refine ⟨31409058276654615133734577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41878744368872820178312769 31409058276654615133734577)
          ·
            refine ⟨23556793707490961350300933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31409058276654615133734577 23556793707490961350300933)
            ·
              refine ⟨4416898820154555253181425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23556793707490961350300933 4416898820154555253181425)
              ·
                refine ⟨3312674115115916439886069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4416898820154555253181425 3312674115115916439886069)
                ·
                  refine ⟨310563198292117166239319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3312674115115916439886069 310563198292117166239319)
                  ·
                    rfl

theorem cell23_5443377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 4, 2, 5].length) (baseStart_5443377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5443377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5443377 prefixEnd_5443377 := by exact prefixLift 5443377
  have htrace : WordTrace (prefixWord ++ tailWord_5443377) baseStart_5443377 baseEnd_5443377 := by
    simpa [prefixWord, tailWord_5443377, baseEnd_5443377] using wordTrace_append hprefix tailTrace_5443377
  have hstable : (prefixWord ++ tailWord_5443377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5443377).length < 2 ^ (prefixWord ++ tailWord_5443377).sum := by decide
  have hdescent : baseEnd_5443377 < baseStart_5443377 := by decide
  rcases family_descends (prefixWord ++ tailWord_5443377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5443410 : List Nat := [3, 2, 2, 1, 1, 4, 1, 1, 1, 3, 4]
def baseStart_5443410 : Nat := 118140960795 + 5443410 * 2 ^ 59
def prefixEnd_5443410 : Nat := 4983230072969 + 3 ^ 40 * 5443410 * 2
def baseEnd_5443410 : Nat := 2795085729490652867041219

theorem tailTrace_5443410 : CollatzResearch.WordTrace tailWord_5443410 prefixEnd_5443410 2795085729490652867041219 := by
  unfold tailWord_5443410
  simp only [CollatzResearch.WordTrace]
  refine ⟨49634368302365676314765921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132358315472975136839375789 49634368302365676314765921)
  ·
    refine ⟨37225776226774257236074441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49634368302365676314765921 37225776226774257236074441)
    ·
      refine ⟨27919332170080692927055831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37225776226774257236074441 27919332170080692927055831)
      ·
        refine ⟨41878998255121039390583747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27919332170080692927055831 41878998255121039390583747)
        ·
          refine ⟨62818497382681559085875621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41878998255121039390583747 62818497382681559085875621)
          ·
            refine ⟨11778468259252792328601679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 62818497382681559085875621 11778468259252792328601679)
            ·
              refine ⟨17667702388879188492902519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11778468259252792328601679 17667702388879188492902519)
              ·
                refine ⟨26501553583318782739353779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17667702388879188492902519 26501553583318782739353779)
                ·
                  refine ⟨39752330374978174109030669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26501553583318782739353779 39752330374978174109030669)
                  ·
                    refine ⟨14907123890616815290886501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 39752330374978174109030669 14907123890616815290886501)
                    ·
                      refine ⟨2795085729490652867041219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14907123890616815290886501 2795085729490652867041219)
                      ·
                        rfl

theorem cell23_5443410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 1, 1, 1, 3, 4].length) (baseStart_5443410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5443410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5443410 prefixEnd_5443410 := by exact prefixLift 5443410
  have htrace : WordTrace (prefixWord ++ tailWord_5443410) baseStart_5443410 baseEnd_5443410 := by
    simpa [prefixWord, tailWord_5443410, baseEnd_5443410] using wordTrace_append hprefix tailTrace_5443410
  have hstable : (prefixWord ++ tailWord_5443410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5443410).length < 2 ^ (prefixWord ++ tailWord_5443410).sum := by decide
  have hdescent : baseEnd_5443410 < baseStart_5443410 := by decide
  rcases family_descends (prefixWord ++ tailWord_5443410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5443423 : List Nat := [1, 1, 2, 3, 1, 4, 1, 1, 2, 1, 6]
def baseStart_5443423 : Nat := 118140960795 + 5443423 * 2 ^ 59
def prefixEnd_5443423 : Nat := 4983230072969 + 3 ^ 40 * 5443423 * 2
def baseEnd_5443423 : Nat := 2795092404739161316178659

theorem tailTrace_5443423 : CollatzResearch.WordTrace tailWord_5443423 prefixEnd_5443423 2795092404739161316178659 := by
  unfold tailWord_5443423
  simp only [CollatzResearch.WordTrace]
  refine ⟨198537947358415608479286923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132358631572277072319524615 198537947358415608479286923)
  ·
    refine ⟨297806921037623412718930385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198537947358415608479286923 297806921037623412718930385)
    ·
      refine ⟨223355190778217559539197789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 297806921037623412718930385 223355190778217559539197789)
      ·
        refine ⟨83758196541831584827199171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 223355190778217559539197789 83758196541831584827199171)
        ·
          refine ⟨125637294812747377240798757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83758196541831584827199171 125637294812747377240798757)
          ·
            refine ⟨23556992777390133232649767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 125637294812747377240798757 23556992777390133232649767)
            ·
              refine ⟨35335489166085199848974651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23556992777390133232649767 35335489166085199848974651)
              ·
                refine ⟨53003233749127799773461977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35335489166085199848974651 53003233749127799773461977)
                ·
                  refine ⟨39752425311845849830096483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 53003233749127799773461977 39752425311845849830096483)
                  ·
                    refine ⟨59628637967768774745144725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 39752425311845849830096483 59628637967768774745144725)
                    ·
                      refine ⟨2795092404739161316178659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 59628637967768774745144725 2795092404739161316178659)
                      ·
                        rfl

theorem cell23_5443423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 1, 1, 2, 1, 6].length) (baseStart_5443423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5443423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5443423 prefixEnd_5443423 := by exact prefixLift 5443423
  have htrace : WordTrace (prefixWord ++ tailWord_5443423) baseStart_5443423 baseEnd_5443423 := by
    simpa [prefixWord, tailWord_5443423, baseEnd_5443423] using wordTrace_append hprefix tailTrace_5443423
  have hstable : (prefixWord ++ tailWord_5443423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5443423).length < 2 ^ (prefixWord ++ tailWord_5443423).sum := by decide
  have hdescent : baseEnd_5443423 < baseStart_5443423 := by decide
  rcases family_descends (prefixWord ++ tailWord_5443423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5443453 : List Nat := [1, 4, 1, 1, 2, 1, 1, 1, 3, 2, 6]
def baseStart_5443453 : Nat := 118140960795 + 5443453 * 2 ^ 59
def prefixEnd_5443453 : Nat := 4983230072969 + 3 ^ 40 * 5443453 * 2
def baseEnd_5443453 : Nat := 2795107809158796198803521

theorem tailTrace_5443453 : CollatzResearch.WordTrace tailWord_5443453 prefixEnd_5443453 2795107809158796198803521 := by
  unfold tailWord_5443453
  simp only [CollatzResearch.WordTrace]
  refine ⟨198539041548306923602879013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132359361032204615735252675 198539041548306923602879013)
  ·
    refine ⟨37226070290307548175539815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 198539041548306923602879013 37226070290307548175539815)
    ·
      refine ⟨55839105435461322263309723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37226070290307548175539815 55839105435461322263309723)
      ·
        refine ⟨83758658153191983394964585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55839105435461322263309723 83758658153191983394964585)
        ·
          refine ⟨62818993614893987546223439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83758658153191983394964585 62818993614893987546223439)
          ·
            refine ⟨94228490422340981319335159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62818993614893987546223439 94228490422340981319335159)
            ·
              refine ⟨141342735633511471979002739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 94228490422340981319335159 141342735633511471979002739)
              ·
                refine ⟨212014103450267207968504109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 141342735633511471979002739 212014103450267207968504109)
                ·
                  refine ⟨79505288793850202988189041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 212014103450267207968504109 79505288793850202988189041)
                  ·
                    refine ⟨59628966595387652241141781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 79505288793850202988189041 59628966595387652241141781)
                    ·
                      refine ⟨2795107809158796198803521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 59628966595387652241141781 2795107809158796198803521)
                      ·
                        rfl

theorem cell23_5443453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 1, 3, 2, 6].length) (baseStart_5443453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5443453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5443453 prefixEnd_5443453 := by exact prefixLift 5443453
  have htrace : WordTrace (prefixWord ++ tailWord_5443453) baseStart_5443453 baseEnd_5443453 := by
    simpa [prefixWord, tailWord_5443453, baseEnd_5443453] using wordTrace_append hprefix tailTrace_5443453
  have hstable : (prefixWord ++ tailWord_5443453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5443453).length < 2 ^ (prefixWord ++ tailWord_5443453).sum := by decide
  have hdescent : baseEnd_5443453 < baseStart_5443453 := by decide
  rcases family_descends (prefixWord ++ tailWord_5443453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5443454 : List Nat := [4, 2, 3, 1, 1, 1, 2, 2, 3, 4]
def baseStart_5443454 : Nat := 118140960795 + 5443454 * 2 ^ 59
def prefixEnd_5443454 : Nat := 4983230072969 + 3 ^ 40 * 5443454 * 2
def baseEnd_5443454 : Nat := 931702774213150231630339

theorem tailTrace_5443454 : CollatzResearch.WordTrace tailWord_5443454 prefixEnd_5443454 931702774213150231630339 := by
  unfold tailWord_5443454
  simp only [CollatzResearch.WordTrace]
  refine ⟨24817384752662912596708177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 132359385347535533849110277 24817384752662912596708177)
  ·
    refine ⟨18613038564497184447531133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24817384752662912596708177 18613038564497184447531133)
    ·
      refine ⟨6979889461686444167824175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18613038564497184447531133 6979889461686444167824175)
      ·
        refine ⟨10469834192529666251736263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6979889461686444167824175 10469834192529666251736263)
        ·
          refine ⟨15704751288794499377604395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10469834192529666251736263 15704751288794499377604395)
          ·
            refine ⟨23557126933191749066406593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15704751288794499377604395 23557126933191749066406593)
            ·
              refine ⟨17667845199893811799804945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23557126933191749066406593 17667845199893811799804945)
              ·
                refine ⟨13250883899920358849853709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17667845199893811799804945 13250883899920358849853709)
                ·
                  refine ⟨4969081462470134568695141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13250883899920358849853709 4969081462470134568695141)
                  ·
                    refine ⟨931702774213150231630339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4969081462470134568695141 931702774213150231630339)
                    ·
                      rfl

theorem cell23_5443454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 2, 2, 3, 4].length) (baseStart_5443454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5443454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5443454 prefixEnd_5443454 := by exact prefixLift 5443454
  have htrace : WordTrace (prefixWord ++ tailWord_5443454) baseStart_5443454 baseEnd_5443454 := by
    simpa [prefixWord, tailWord_5443454, baseEnd_5443454] using wordTrace_append hprefix tailTrace_5443454
  have hstable : (prefixWord ++ tailWord_5443454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5443454).length < 2 ^ (prefixWord ++ tailWord_5443454).sum := by decide
  have hdescent : baseEnd_5443454 < baseStart_5443454 := by decide
  rcases family_descends (prefixWord ++ tailWord_5443454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5443517 : List Nat := [1, 4, 1, 2, 3, 2, 1, 1, 3, 1, 4]
def baseStart_5443517 : Nat := 118140960795 + 5443517 * 2 ^ 59
def prefixEnd_5443517 : Nat := 4983230072969 + 3 ^ 40 * 5443517 * 2
def baseEnd_5443517 : Nat := 2795140671920683948403227

theorem tailTrace_5443517 : CollatzResearch.WordTrace tailWord_5443517 prefixEnd_5443517 2795140671920683948403227 := by
  unfold tailWord_5443517
  simp only [CollatzResearch.WordTrace]
  refine ⟨198541375820075062533208805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132360917213383375022139203 198541375820075062533208805)
  ·
    refine ⟨37226507966264074224976651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 198541375820075062533208805 37226507966264074224976651)
    ·
      refine ⟨55839761949396111337464977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37226507966264074224976651 55839761949396111337464977)
      ·
        refine ⟨41879821462047083503098733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55839761949396111337464977 41879821462047083503098733)
        ·
          refine ⟨15704933048267656313662025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41879821462047083503098733 15704933048267656313662025)
          ·
            refine ⟨11778699786200742235246519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15704933048267656313662025 11778699786200742235246519)
            ·
              refine ⟨17668049679301113352869779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11778699786200742235246519 17668049679301113352869779)
              ·
                refine ⟨26502074518951670029304669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17668049679301113352869779 26502074518951670029304669)
                ·
                  refine ⟨9938277944606876260989251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26502074518951670029304669 9938277944606876260989251)
                  ·
                    refine ⟨14907416916910314391483877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9938277944606876260989251 14907416916910314391483877)
                    ·
                      refine ⟨2795140671920683948403227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14907416916910314391483877 2795140671920683948403227)
                      ·
                        rfl

theorem cell23_5443517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 1, 1, 3, 1, 4].length) (baseStart_5443517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5443517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5443517 prefixEnd_5443517 := by exact prefixLift 5443517
  have htrace : WordTrace (prefixWord ++ tailWord_5443517) baseStart_5443517 baseEnd_5443517 := by
    simpa [prefixWord, tailWord_5443517, baseEnd_5443517] using wordTrace_append hprefix tailTrace_5443517
  have hstable : (prefixWord ++ tailWord_5443517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5443517).length < 2 ^ (prefixWord ++ tailWord_5443517).sum := by decide
  have hdescent : baseEnd_5443517 < baseStart_5443517 := by decide
  rcases family_descends (prefixWord ++ tailWord_5443517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5443530 : List Nat := [3, 1, 2, 1, 2, 1, 3, 1, 3, 2, 4]
def baseStart_5443530 : Nat := 118140960795 + 5443530 * 2 ^ 59
def prefixEnd_5443530 : Nat := 4983230072969 + 3 ^ 40 * 5443530 * 2
def baseEnd_5443530 : Nat := 2795147347169192397540667

theorem tailTrace_5443530 : CollatzResearch.WordTrace tailWord_5443530 prefixEnd_5443530 2795147347169192397540667 := by
  unfold tailWord_5443530
  simp only [CollatzResearch.WordTrace]
  refine ⟨49635462492256991438358011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132361233312685310502288029 49635462492256991438358011)
  ·
    refine ⟨74453193738385487157537017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49635462492256991438358011 74453193738385487157537017)
    ·
      refine ⟨55839895303789115368152763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74453193738385487157537017 55839895303789115368152763)
      ·
        refine ⟨83759842955683673052229145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55839895303789115368152763 83759842955683673052229145)
        ·
          refine ⟨62819882216762754789171859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83759842955683673052229145 62819882216762754789171859)
          ·
            refine ⟨94229823325144132183757789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62819882216762754789171859 94229823325144132183757789)
            ·
              refine ⟨35336183746929049568909171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 94229823325144132183757789 35336183746929049568909171)
              ·
                refine ⟨53004275620393574353363757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35336183746929049568909171 53004275620393574353363757)
                ·
                  refine ⟨19876603357647590382511409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 53004275620393574353363757 19876603357647590382511409)
                  ·
                    refine ⟨14907452518235692786883557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19876603357647590382511409 14907452518235692786883557)
                    ·
                      refine ⟨2795147347169192397540667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14907452518235692786883557 2795147347169192397540667)
                      ·
                        rfl

theorem cell23_5443530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 3, 1, 3, 2, 4].length) (baseStart_5443530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5443530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5443530 prefixEnd_5443530 := by exact prefixLift 5443530
  have htrace : WordTrace (prefixWord ++ tailWord_5443530) baseStart_5443530 baseEnd_5443530 := by
    simpa [prefixWord, tailWord_5443530, baseEnd_5443530] using wordTrace_append hprefix tailTrace_5443530
  have hstable : (prefixWord ++ tailWord_5443530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5443530).length < 2 ^ (prefixWord ++ tailWord_5443530).sum := by decide
  have hdescent : baseEnd_5443530 < baseStart_5443530 := by decide
  rcases family_descends (prefixWord ++ tailWord_5443530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5443534 : List Nat := [4, 1, 1, 1, 2, 2, 5, 1, 1, 1, 4]
def baseStart_5443534 : Nat := 118140960795 + 5443534 * 2 ^ 59
def prefixEnd_5443534 : Nat := 4983230072969 + 3 ^ 40 * 5443534 * 2
def baseEnd_5443534 : Nat := 2795149401091810381890649

theorem tailTrace_5443534 : CollatzResearch.WordTrace tailWord_5443534 prefixEnd_5443534 2795149401091810381890649 := by
  unfold tailWord_5443534
  simp only [CollatzResearch.WordTrace]
  refine ⟨24817749482626684304572207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 132361330574008982957718437 24817749482626684304572207)
  ·
    refine ⟨37226624223940026456858311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24817749482626684304572207 37226624223940026456858311)
    ·
      refine ⟨55839936335910039685287467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37226624223940026456858311 55839936335910039685287467)
      ·
        refine ⟨83759904503865059527931201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55839936335910039685287467 83759904503865059527931201)
        ·
          refine ⟨62819928377898794645948401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83759904503865059527931201 62819928377898794645948401)
          ·
            refine ⟨47114946283424095984461301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62819928377898794645948401 47114946283424095984461301)
            ·
              refine ⟨4417026214071008998543247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 47114946283424095984461301 4417026214071008998543247)
              ·
                refine ⟨6625539321106513497814871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4417026214071008998543247 6625539321106513497814871)
                ·
                  refine ⟨9938308981659770246722307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6625539321106513497814871 9938308981659770246722307)
                  ·
                    refine ⟨14907463472489655370083461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9938308981659770246722307 14907463472489655370083461)
                    ·
                      refine ⟨2795149401091810381890649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14907463472489655370083461 2795149401091810381890649)
                      ·
                        rfl

theorem cell23_5443534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 5, 1, 1, 1, 4].length) (baseStart_5443534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5443534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5443534 prefixEnd_5443534 := by exact prefixLift 5443534
  have htrace : WordTrace (prefixWord ++ tailWord_5443534) baseStart_5443534 baseEnd_5443534 := by
    simpa [prefixWord, tailWord_5443534, baseEnd_5443534] using wordTrace_append hprefix tailTrace_5443534
  have hstable : (prefixWord ++ tailWord_5443534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5443534).length < 2 ^ (prefixWord ++ tailWord_5443534).sum := by decide
  have hdescent : baseEnd_5443534 < baseStart_5443534 := by decide
  rcases family_descends (prefixWord ++ tailWord_5443534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5443545 : List Nat := [1, 2, 1, 2, 7, 1, 2, 2, 1, 1, 3]
def baseStart_5443545 : Nat := 118140960795 + 5443545 * 2 ^ 59
def prefixEnd_5443545 : Nat := 4983230072969 + 3 ^ 40 * 5443545 * 2
def baseEnd_5443545 : Nat := 2795155049379009838853099

theorem tailTrace_5443545 : CollatzResearch.WordTrace tailWord_5443545 prefixEnd_5443545 2795155049379009838853099 := by
  unfold tailWord_5443545
  simp only [CollatzResearch.WordTrace]
  refine ⟨198542397063973623315228089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132361598042649082210152059 198542397063973623315228089)
  ·
    refine ⟨148906797797980217486421067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 198542397063973623315228089 148906797797980217486421067)
    ·
      refine ⟨223360196696970326229631601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148906797797980217486421067 223360196696970326229631601)
      ·
        refine ⟨167520147522727744672223701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 223360196696970326229631601 167520147522727744672223701)
        ·
          refine ⟨3926253457563931515755243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 167520147522727744672223701 3926253457563931515755243)
          ·
            refine ⟨5889380186345897273632865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3926253457563931515755243 5889380186345897273632865)
            ·
              refine ⟨4417035139759422955224649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5889380186345897273632865 4417035139759422955224649)
              ·
                refine ⟨3312776354819567216418487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4417035139759422955224649 3312776354819567216418487)
                ·
                  refine ⟨4969164532229350824627731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3312776354819567216418487 4969164532229350824627731)
                  ·
                    refine ⟨7453746798344026236941597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4969164532229350824627731 7453746798344026236941597)
                    ·
                      refine ⟨2795155049379009838853099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7453746798344026236941597 2795155049379009838853099)
                      ·
                        rfl

theorem cell23_5443545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 7, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 7, 1, 2, 2, 1, 1, 3].length) (baseStart_5443545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5443545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5443545 prefixEnd_5443545 := by exact prefixLift 5443545
  have htrace : WordTrace (prefixWord ++ tailWord_5443545) baseStart_5443545 baseEnd_5443545 := by
    simpa [prefixWord, tailWord_5443545, baseEnd_5443545] using wordTrace_append hprefix tailTrace_5443545
  have hstable : (prefixWord ++ tailWord_5443545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5443545).length < 2 ^ (prefixWord ++ tailWord_5443545).sum := by decide
  have hdescent : baseEnd_5443545 < baseStart_5443545 := by decide
  rcases family_descends (prefixWord ++ tailWord_5443545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5443567 : List Nat := [1, 1, 2, 1, 4, 2, 4, 1, 1, 3, 3]
def baseStart_5443567 : Nat := 118140960795 + 5443567 * 2 ^ 59
def prefixEnd_5443567 : Nat := 4983230072969 + 3 ^ 40 * 5443567 * 2
def baseEnd_5443567 : Nat := 2795166345953408752777997

theorem tailTrace_5443567 : CollatzResearch.WordTrace tailWord_5443567 prefixEnd_5443567 2795166345953408752777997 := by
  unfold tailWord_5443567
  simp only [CollatzResearch.WordTrace]
  refine ⟨198543199469893921072528955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132362132979929280715019303 198543199469893921072528955)
  ·
    refine ⟨297814799204840881608793433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198543199469893921072528955 297814799204840881608793433)
    ·
      refine ⟨223361099403630661206595075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 297814799204840881608793433 223361099403630661206595075)
      ·
        refine ⟨335041649105445991809892613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 223361099403630661206595075 335041649105445991809892613)
        ·
          refine ⟨62820309207271123464354865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 335041649105445991809892613 62820309207271123464354865)
          ·
            refine ⟨47115231905453342598266149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62820309207271123464354865 47115231905453342598266149)
            ·
              refine ⟨8834105982272501737174903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 47115231905453342598266149 8834105982272501737174903)
              ·
                refine ⟨13251158973408752605762355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8834105982272501737174903 13251158973408752605762355)
                ·
                  refine ⟨19876738460113128908643533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13251158973408752605762355 19876738460113128908643533)
                  ·
                    refine ⟨7453776922542423340741325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19876738460113128908643533 7453776922542423340741325)
                    ·
                      refine ⟨2795166345953408752777997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7453776922542423340741325 2795166345953408752777997)
                      ·
                        rfl

theorem cell23_5443567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 4, 1, 1, 3, 3].length) (baseStart_5443567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5443567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5443567 prefixEnd_5443567 := by exact prefixLift 5443567
  have htrace : WordTrace (prefixWord ++ tailWord_5443567) baseStart_5443567 baseEnd_5443567 := by
    simpa [prefixWord, tailWord_5443567, baseEnd_5443567] using wordTrace_append hprefix tailTrace_5443567
  have hstable : (prefixWord ++ tailWord_5443567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5443567).length < 2 ^ (prefixWord ++ tailWord_5443567).sum := by decide
  have hdescent : baseEnd_5443567 < baseStart_5443567 := by decide
  rcases family_descends (prefixWord ++ tailWord_5443567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5443574 : List Nat := [5, 1, 1, 1, 4, 1, 3, 7]
def baseStart_5443574 : Nat := 118140960795 + 5443574 * 2 ^ 59
def prefixEnd_5443574 : Nat := 4983230072969 + 3 ^ 40 * 5443574 * 2
def baseEnd_5443574 : Nat := 103524812604370008347795

theorem tailTrace_5443574 : CollatzResearch.WordTrace tailWord_5443574 prefixEnd_5443574 103524812604370008347795 := by
  unfold tailWord_5443574
  simp only [CollatzResearch.WordTrace]
  refine ⟨12408965923804285079252111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 132362303187245707512022517 12408965923804285079252111)
  ·
    refine ⟨18613448885706427618878167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12408965923804285079252111 18613448885706427618878167)
    ·
      refine ⟨27920173328559641428317251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18613448885706427618878167 27920173328559641428317251)
      ·
        refine ⟨41880259992839462142475877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27920173328559641428317251 41880259992839462142475877)
        ·
          refine ⟨7852548748657399151714227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 41880259992839462142475877 7852548748657399151714227)
          ·
            refine ⟨11778823122986098727571341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7852548748657399151714227 11778823122986098727571341)
            ·
              refine ⟨4417058671119787022839253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11778823122986098727571341 4417058671119787022839253)
              ·
                refine ⟨103524812604370008347795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4417058671119787022839253 103524812604370008347795)
                ·
                  rfl

theorem cell23_5443574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 3, 7].length) (baseStart_5443574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5443574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5443574 prefixEnd_5443574 := by exact prefixLift 5443574
  have htrace : WordTrace (prefixWord ++ tailWord_5443574) baseStart_5443574 baseEnd_5443574 := by
    simpa [prefixWord, tailWord_5443574, baseEnd_5443574] using wordTrace_append hprefix tailTrace_5443574
  have hstable : (prefixWord ++ tailWord_5443574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5443574).length < 2 ^ (prefixWord ++ tailWord_5443574).sum := by decide
  have hdescent : baseEnd_5443574 < baseStart_5443574 := by decide
  rcases family_descends (prefixWord ++ tailWord_5443574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5443580 : List Nat := [2, 2, 2, 1, 2, 2, 2, 1, 2, 2, 5]
def baseStart_5443580 : Nat := 118140960795 + 5443580 * 2 ^ 59
def prefixEnd_5443580 : Nat := 4983230072969 + 3 ^ 40 * 5443580 * 2
def baseEnd_5443580 : Nat := 2795173021201917201915437

theorem tailTrace_5443580 : CollatzResearch.WordTrace tailWord_5443580 prefixEnd_5443580 2795173021201917201915437 := by
  unfold tailWord_5443580
  simp only [CollatzResearch.WordTrace]
  refine ⟨99271836809423412146376097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132362449079231216195168129 99271836809423412146376097)
  ·
    refine ⟨74453877607067559109782073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99271836809423412146376097 74453877607067559109782073)
    ·
      refine ⟨55840408205300669332336555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74453877607067559109782073 55840408205300669332336555)
      ·
        refine ⟨83760612307951003998504833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55840408205300669332336555 83760612307951003998504833)
        ·
          refine ⟨62820459230963252998878625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83760612307951003998504833 62820459230963252998878625)
          ·
            refine ⟨47115344423222439749158969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62820459230963252998878625 47115344423222439749158969)
            ·
              refine ⟨35336508317416829811869227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47115344423222439749158969 35336508317416829811869227)
              ·
                refine ⟨53004762476125244717803841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35336508317416829811869227 53004762476125244717803841)
                ·
                  refine ⟨39753571857093933538352881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 53004762476125244717803841 39753571857093933538352881)
                  ·
                    refine ⟨29815178892820450153764661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 39753571857093933538352881 29815178892820450153764661)
                    ·
                      refine ⟨2795173021201917201915437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29815178892820450153764661 2795173021201917201915437)
                      ·
                        rfl

theorem cell23_5443580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 2, 1, 2, 2, 5].length) (baseStart_5443580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5443580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5443580 prefixEnd_5443580 := by exact prefixLift 5443580
  have htrace : WordTrace (prefixWord ++ tailWord_5443580) baseStart_5443580 baseEnd_5443580 := by
    simpa [prefixWord, tailWord_5443580, baseEnd_5443580] using wordTrace_append hprefix tailTrace_5443580
  have hstable : (prefixWord ++ tailWord_5443580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5443580).length < 2 ^ (prefixWord ++ tailWord_5443580).sum := by decide
  have hdescent : baseEnd_5443580 < baseStart_5443580 := by decide
  rcases family_descends (prefixWord ++ tailWord_5443580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5443694 : List Nat := [4, 1, 2, 2, 1, 1, 4, 1, 2, 5]
def baseStart_5443694 : Nat := 118140960795 + 5443694 * 2 ^ 59
def prefixEnd_5443694 : Nat := 4983230072969 + 3 ^ 40 * 5443694 * 2
def baseEnd_5443694 : Nat := 931743852665509918629971

theorem tailTrace_5443694 : CollatzResearch.WordTrace tailWord_5443694 prefixEnd_5443694 931743852665509918629971 := by
  unfold tailWord_5443694
  simp only [CollatzResearch.WordTrace]
  refine ⟨24818478942554227720300267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 132365221026955881174934757 24818478942554227720300267)
  ·
    refine ⟨37227718413831341580450401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24818478942554227720300267 37227718413831341580450401)
    ·
      refine ⟨27920788810373506185337801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37227718413831341580450401 27920788810373506185337801)
      ·
        refine ⟨20940591607780129639003351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27920788810373506185337801 20940591607780129639003351)
        ·
          refine ⟨31410887411670194458505027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20940591607780129639003351 31410887411670194458505027)
          ·
            refine ⟨47116331117505291687757541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31410887411670194458505027 47116331117505291687757541)
            ·
              refine ⟨8834312084532242191454539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 47116331117505291687757541 8834312084532242191454539)
              ·
                refine ⟨13251468126798363287181809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8834312084532242191454539 13251468126798363287181809)
                ·
                  refine ⟨9938601095098772465386357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13251468126798363287181809 9938601095098772465386357)
                  ·
                    refine ⟨931743852665509918629971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9938601095098772465386357 931743852665509918629971)
                    ·
                      rfl

theorem cell23_5443694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 4, 1, 2, 5].length) (baseStart_5443694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5443694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5443694 prefixEnd_5443694 := by exact prefixLift 5443694
  have htrace : WordTrace (prefixWord ++ tailWord_5443694) baseStart_5443694 baseEnd_5443694 := by
    simpa [prefixWord, tailWord_5443694, baseEnd_5443694] using wordTrace_append hprefix tailTrace_5443694
  have hstable : (prefixWord ++ tailWord_5443694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5443694).length < 2 ^ (prefixWord ++ tailWord_5443694).sum := by decide
  have hdescent : baseEnd_5443694 < baseStart_5443694 := by decide
  rcases family_descends (prefixWord ++ tailWord_5443694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5443748 : List Nat := [2, 3, 1, 2, 5, 1, 1, 1, 2, 1, 4]
def baseStart_5443748 : Nat := 118140960795 + 5443748 * 2 ^ 59
def prefixEnd_5443748 : Nat := 4983230072969 + 3 ^ 40 * 5443748 * 2
def baseEnd_5443748 : Nat := 2795259285951872544614665

theorem tailTrace_5443748 : CollatzResearch.WordTrace tailWord_5443748 prefixEnd_5443748 2795259285951872544614665 := by
  unfold tailWord_5443748
  simp only [CollatzResearch.WordTrace]
  refine ⟨99274900541119094492433949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132366534054825459323245265 99274900541119094492433949)
  ·
    refine ⟨37228087702919660434662731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 99274900541119094492433949 37228087702919660434662731)
    ·
      refine ⟨55842131554379490651994097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37228087702919660434662731 55842131554379490651994097)
      ·
        refine ⟨41881598665784617988995573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55842131554379490651994097 41881598665784617988995573)
        ·
          refine ⟨3926399874917307936468335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 41881598665784617988995573 3926399874917307936468335)
          ·
            refine ⟨5889599812375961904702503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3926399874917307936468335 5889599812375961904702503)
            ·
              refine ⟨8834399718563942857053755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5889599812375961904702503 8834399718563942857053755)
              ·
                refine ⟨13251599577845914285580633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8834399718563942857053755 13251599577845914285580633)
                ·
                  refine ⟨9938699683384435714185475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13251599577845914285580633 9938699683384435714185475)
                  ·
                    refine ⟨14908049525076653571278213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9938699683384435714185475 14908049525076653571278213)
                    ·
                      refine ⟨2795259285951872544614665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14908049525076653571278213 2795259285951872544614665)
                      ·
                        rfl

theorem cell23_5443748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 5, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 5, 1, 1, 1, 2, 1, 4].length) (baseStart_5443748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5443748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5443748 prefixEnd_5443748 := by exact prefixLift 5443748
  have htrace : WordTrace (prefixWord ++ tailWord_5443748) baseStart_5443748 baseEnd_5443748 := by
    simpa [prefixWord, tailWord_5443748, baseEnd_5443748] using wordTrace_append hprefix tailTrace_5443748
  have hstable : (prefixWord ++ tailWord_5443748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5443748).length < 2 ^ (prefixWord ++ tailWord_5443748).sum := by decide
  have hdescent : baseEnd_5443748 < baseStart_5443748 := by decide
  rcases family_descends (prefixWord ++ tailWord_5443748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5443751 : List Nat := [1, 1, 6, 2, 2, 1, 1, 1, 1, 4, 3]
def baseStart_5443751 : Nat := 118140960795 + 5443751 * 2 ^ 59
def prefixEnd_5443751 : Nat := 4983230072969 + 3 ^ 40 * 5443751 * 2
def baseEnd_5443751 : Nat := 2795260826393836032877151

theorem tailTrace_5443751 : CollatzResearch.WordTrace tailWord_5443751 prefixEnd_5443751 2795260826393836032877151 := by
  unfold tailWord_5443751
  simp only [CollatzResearch.WordTrace]
  refine ⟨198549910501227320497227107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132366607000818213664818071 198549910501227320497227107)
  ·
    refine ⟨297824865751840980745840661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198549910501227320497227107 297824865751840980745840661)
    ·
      refine ⟨13960540582117545972461281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 297824865751840980745840661 13960540582117545972461281)
      ·
        refine ⟨10470405436588159479345961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13960540582117545972461281 10470405436588159479345961)
        ·
          refine ⟨7852804077441119609509471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10470405436588159479345961 7852804077441119609509471)
          ·
            refine ⟨11779206116161679414264207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7852804077441119609509471 11779206116161679414264207)
            ·
              refine ⟨17668809174242519121396311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11779206116161679414264207 17668809174242519121396311)
              ·
                refine ⟨26503213761363778682094467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17668809174242519121396311 26503213761363778682094467)
                ·
                  refine ⟨39754820642045668023141701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26503213761363778682094467 39754820642045668023141701)
                  ·
                    refine ⟨7454028870383562754339069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 39754820642045668023141701 7454028870383562754339069)
                    ·
                      refine ⟨2795260826393836032877151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7454028870383562754339069 2795260826393836032877151)
                      ·
                        rfl

theorem cell23_5443751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 1, 1, 1, 4, 3].length) (baseStart_5443751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5443751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5443751 prefixEnd_5443751 := by exact prefixLift 5443751
  have htrace : WordTrace (prefixWord ++ tailWord_5443751) baseStart_5443751 baseEnd_5443751 := by
    simpa [prefixWord, tailWord_5443751, baseEnd_5443751] using wordTrace_append hprefix tailTrace_5443751
  have hstable : (prefixWord ++ tailWord_5443751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5443751).length < 2 ^ (prefixWord ++ tailWord_5443751).sum := by decide
  have hdescent : baseEnd_5443751 < baseStart_5443751 := by decide
  rcases family_descends (prefixWord ++ tailWord_5443751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5443788 : List Nat := [2, 2, 1, 6, 1, 1, 3, 1, 6]
def baseStart_5443788 : Nat := 118140960795 + 5443788 * 2 ^ 59
def prefixEnd_5443788 : Nat := 4983230072969 + 3 ^ 40 * 5443788 * 2
def baseEnd_5443788 : Nat := 310586647242005820901609

theorem tailTrace_5443788 : CollatzResearch.WordTrace tailWord_5443788 prefixEnd_5443788 310586647242005820901609 := by
  unfold tailWord_5443788
  simp only [CollatzResearch.WordTrace]
  refine ⟨99275630001046637908162009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132367506668062183877549345 99275630001046637908162009)
  ·
    refine ⟨74456722500784978431121507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99275630001046637908162009 74456722500784978431121507)
    ·
      refine ⟨111685083751177467646682261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74456722500784978431121507 111685083751177467646682261)
      ·
        refine ⟨5235238300836443795938231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 111685083751177467646682261 5235238300836443795938231)
        ·
          refine ⟨7852857451254665693907347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5235238300836443795938231 7852857451254665693907347)
          ·
            refine ⟨11779286176881998540861021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7852857451254665693907347 11779286176881998540861021)
            ·
              refine ⟨4417232316330749452822883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11779286176881998540861021 4417232316330749452822883)
              ·
                refine ⟨6625848474496124179234325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4417232316330749452822883 6625848474496124179234325)
                ·
                  refine ⟨310586647242005820901609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6625848474496124179234325 310586647242005820901609)
                  ·
                    rfl

theorem cell23_5443788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 3, 1, 6].length) (baseStart_5443788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5443788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5443788 prefixEnd_5443788 := by exact prefixLift 5443788
  have htrace : WordTrace (prefixWord ++ tailWord_5443788) baseStart_5443788 baseEnd_5443788 := by
    simpa [prefixWord, tailWord_5443788, baseEnd_5443788] using wordTrace_append hprefix tailTrace_5443788
  have hstable : (prefixWord ++ tailWord_5443788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5443788).length < 2 ^ (prefixWord ++ tailWord_5443788).sum := by decide
  have hdescent : baseEnd_5443788 < baseStart_5443788 := by decide
  rcases family_descends (prefixWord ++ tailWord_5443788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5443807 : List Nat := [1, 1, 2, 3, 2, 1, 1, 1, 5, 1, 5]
def baseStart_5443807 : Nat := 118140960795 + 5443807 * 2 ^ 59
def prefixEnd_5443807 : Nat := 4983230072969 + 3 ^ 40 * 5443807 * 2
def baseEnd_5443807 : Nat := 2795289581310487813776893

theorem tailTrace_5443807 : CollatzResearch.WordTrace tailWord_5443807 prefixEnd_5443807 2795289581310487813776893 := by
  unfold tailWord_5443807
  simp only [CollatzResearch.WordTrace]
  refine ⟨198551952989024442061265675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132367968659349628040843783 198551952989024442061265675)
  ·
    refine ⟨297827929483536663091898513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198551952989024442061265675 297827929483536663091898513)
    ·
      refine ⟨223370947112652497318923885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 297827929483536663091898513 223370947112652497318923885)
      ·
        refine ⟨83764105167244686494596457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 223370947112652497318923885 83764105167244686494596457)
        ·
          refine ⟨62823078875433514870947343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83764105167244686494596457 62823078875433514870947343)
          ·
            refine ⟨94234618313150272306421015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62823078875433514870947343 94234618313150272306421015)
            ·
              refine ⟨141351927469725408459631523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 94234618313150272306421015 141351927469725408459631523)
              ·
                refine ⟨212027891204588112689447285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 141351927469725408459631523 212027891204588112689447285)
                ·
                  refine ⟨19877614800430135564635683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 212027891204588112689447285 19877614800430135564635683)
                  ·
                    refine ⟨29816422200645203346953525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19877614800430135564635683 29816422200645203346953525)
                    ·
                      refine ⟨2795289581310487813776893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29816422200645203346953525 2795289581310487813776893)
                      ·
                        rfl

theorem cell23_5443807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 1, 5, 1, 5].length) (baseStart_5443807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5443807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5443807 prefixEnd_5443807 := by exact prefixLift 5443807
  have htrace : WordTrace (prefixWord ++ tailWord_5443807) baseStart_5443807 baseEnd_5443807 := by
    simpa [prefixWord, tailWord_5443807, baseEnd_5443807] using wordTrace_append hprefix tailTrace_5443807
  have hstable : (prefixWord ++ tailWord_5443807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5443807).length < 2 ^ (prefixWord ++ tailWord_5443807).sum := by decide
  have hdescent : baseEnd_5443807 < baseStart_5443807 := by decide
  rcases family_descends (prefixWord ++ tailWord_5443807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5443815 : List Nat := [1, 1, 5, 3, 1, 1, 3, 3, 1, 1, 3]
def baseStart_5443815 : Nat := 118140960795 + 5443815 * 2 ^ 59
def prefixEnd_5443815 : Nat := 4983230072969 + 3 ^ 40 * 5443815 * 2
def baseEnd_5443815 : Nat := 2795293689155723782476857

theorem tailTrace_5443815 : CollatzResearch.WordTrace tailWord_5443815 prefixEnd_5443815 2795293689155723782476857 := by
  unfold tailWord_5443815
  simp only [CollatzResearch.WordTrace]
  refine ⟨198552244772995459427556899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132368163181996972951704599 198552244772995459427556899)
  ·
    refine ⟨297828367159493189141335349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198552244772995459427556899 297828367159493189141335349)
    ·
      refine ⟨27921409421202486482000189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 297828367159493189141335349 27921409421202486482000189)
      ·
        refine ⟨10470528532950932430750071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27921409421202486482000189 10470528532950932430750071)
        ·
          refine ⟨15705792799426398646125107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10470528532950932430750071 15705792799426398646125107)
          ·
            refine ⟨23558689199139597969187661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15705792799426398646125107 23558689199139597969187661)
            ·
              refine ⟨8834508449677349238445373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23558689199139597969187661 8834508449677349238445373)
              ·
                refine ⟨3312940668629005964417015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8834508449677349238445373 3312940668629005964417015)
                ·
                  refine ⟨4969411002943508946625523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3312940668629005964417015 4969411002943508946625523)
                  ·
                    refine ⟨7454116504415263419938285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4969411002943508946625523 7454116504415263419938285)
                    ·
                      refine ⟨2795293689155723782476857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7454116504415263419938285 2795293689155723782476857)
                      ·
                        rfl

theorem cell23_5443815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 3, 3, 1, 1, 3].length) (baseStart_5443815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5443815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5443815 prefixEnd_5443815 := by exact prefixLift 5443815
  have htrace : WordTrace (prefixWord ++ tailWord_5443815) baseStart_5443815 baseEnd_5443815 := by
    simpa [prefixWord, tailWord_5443815, baseEnd_5443815] using wordTrace_append hprefix tailTrace_5443815
  have hstable : (prefixWord ++ tailWord_5443815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5443815).length < 2 ^ (prefixWord ++ tailWord_5443815).sum := by decide
  have hdescent : baseEnd_5443815 < baseStart_5443815 := by decide
  rcases family_descends (prefixWord ++ tailWord_5443815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5443848 : List Nat := [2, 1, 3, 2, 3, 1, 4, 1, 2, 4]
def baseStart_5443848 : Nat := 118140960795 + 5443848 * 2 ^ 59
def prefixEnd_5443848 : Nat := 4983230072969 + 3 ^ 40 * 5443848 * 2
def baseEnd_5443848 : Nat := 931770211339107384454735

theorem tailTrace_5443848 : CollatzResearch.WordTrace tailWord_5443848 prefixEnd_5443848 931770211339107384454735 := by
  unfold tailWord_5443848
  simp only [CollatzResearch.WordTrace]
  refine ⟨99276724190937953031754099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132368965587917270709005465 99276724190937953031754099)
  ·
    refine ⟨148915086286406929547631149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99276724190937953031754099 148915086286406929547631149)
    ·
      refine ⟨55843157357402598580361681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 148915086286406929547631149 55843157357402598580361681)
      ·
        refine ⟨41882368018051948935271261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55843157357402598580361681 41882368018051948935271261)
        ·
          refine ⟨15705888006769480850726723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41882368018051948935271261 15705888006769480850726723)
          ·
            refine ⟨23558832010154221276090085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15705888006769480850726723 23558832010154221276090085)
            ·
              refine ⟨4417281001903916489266891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23558832010154221276090085 4417281001903916489266891)
              ·
                refine ⟨6625921502855874733900337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4417281001903916489266891 6625921502855874733900337)
                ·
                  refine ⟨4969441127141906050425253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6625921502855874733900337 4969441127141906050425253)
                  ·
                    refine ⟨931770211339107384454735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4969441127141906050425253 931770211339107384454735)
                    ·
                      rfl

theorem cell23_5443848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 4, 1, 2, 4].length) (baseStart_5443848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5443848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5443848 prefixEnd_5443848 := by exact prefixLift 5443848
  have htrace : WordTrace (prefixWord ++ tailWord_5443848) baseStart_5443848 baseEnd_5443848 := by
    simpa [prefixWord, tailWord_5443848, baseEnd_5443848] using wordTrace_append hprefix tailTrace_5443848
  have hstable : (prefixWord ++ tailWord_5443848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5443848).length < 2 ^ (prefixWord ++ tailWord_5443848).sum := by decide
  have hdescent : baseEnd_5443848 < baseStart_5443848 := by decide
  rcases family_descends (prefixWord ++ tailWord_5443848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5443867 : List Nat := [1, 1, 1, 1, 1, 1, 6, 1, 1, 4, 5]
def baseStart_5443867 : Nat := 118140960795 + 5443867 * 2 ^ 59
def prefixEnd_5443867 : Nat := 4983230072969 + 3 ^ 40 * 5443867 * 2
def baseEnd_5443867 : Nat := 2795320390149757579026617

theorem tailTrace_5443867 : CollatzResearch.WordTrace tailWord_5443867 prefixEnd_5443867 2795320390149757579026617 := by
  unfold tailWord_5443867
  simp only [CollatzResearch.WordTrace]
  refine ⟨198554141368807072308449855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132369427579204714872299903 198554141368807072308449855)
  ·
    refine ⟨297831212053210608462674783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198554141368807072308449855 297831212053210608462674783)
    ·
      refine ⟨446746818079815912694012175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 297831212053210608462674783 446746818079815912694012175)
      ·
        refine ⟨670120227119723869041018263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 446746818079815912694012175 670120227119723869041018263)
        ·
          refine ⟨1005180340679585803561527395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 670120227119723869041018263 1005180340679585803561527395)
          ·
            refine ⟨1507770511019378705342291093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1005180340679585803561527395 1507770511019378705342291093)
            ·
              refine ⟨70676742704033376812919895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1507770511019378705342291093 70676742704033376812919895)
              ·
                refine ⟨106015114056050065219379843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70676742704033376812919895 106015114056050065219379843)
                ·
                  refine ⟨159022671084075097829069765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 106015114056050065219379843 159022671084075097829069765)
                  ·
                    refine ⟨29816750828264080842950581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 159022671084075097829069765 29816750828264080842950581)
                    ·
                      refine ⟨2795320390149757579026617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29816750828264080842950581 2795320390149757579026617)
                      ·
                        rfl

theorem cell23_5443867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 1, 1, 4, 5].length) (baseStart_5443867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5443867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5443867 prefixEnd_5443867 := by exact prefixLift 5443867
  have htrace : WordTrace (prefixWord ++ tailWord_5443867) baseStart_5443867 baseEnd_5443867 := by
    simpa [prefixWord, tailWord_5443867, baseEnd_5443867] using wordTrace_append hprefix tailTrace_5443867
  have hstable : (prefixWord ++ tailWord_5443867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5443867).length < 2 ^ (prefixWord ++ tailWord_5443867).sum := by decide
  have hdescent : baseEnd_5443867 < baseStart_5443867 := by decide
  rcases family_descends (prefixWord ++ tailWord_5443867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5443871 : List Nat := [1, 1, 2, 4, 3, 2, 1, 2, 1, 3, 3]
def baseStart_5443871 : Nat := 118140960795 + 5443871 * 2 ^ 59
def prefixEnd_5443871 : Nat := 4983230072969 + 3 ^ 40 * 5443871 * 2
def baseEnd_5443871 : Nat := 2795322444072375563376599

theorem tailTrace_5443871 : CollatzResearch.WordTrace tailWord_5443871 prefixEnd_5443871 2795322444072375563376599 := by
  unfold tailWord_5443871
  simp only [CollatzResearch.WordTrace]
  refine ⟨198554287260792580991595467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132369524840528387327730311 198554287260792580991595467)
  ·
    refine ⟨297831430891188871487393201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198554287260792580991595467 297831430891188871487393201)
    ·
      refine ⟨223373573168391653615544901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 297831430891188871487393201 223373573168391653615544901)
      ·
        refine ⟨41882544969073435052914669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 223373573168391653615544901 41882544969073435052914669)
        ·
          refine ⟨15705954363402538144843001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41882544969073435052914669 15705954363402538144843001)
          ·
            refine ⟨11779465772551903608632251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15705954363402538144843001 11779465772551903608632251)
            ·
              refine ⟨17669198658827855412948377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11779465772551903608632251 17669198658827855412948377)
              ·
                refine ⟨13251898994120891559711283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17669198658827855412948377 13251898994120891559711283)
                ·
                  refine ⟨19877848491181337339566925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13251898994120891559711283 19877848491181337339566925)
                  ·
                    refine ⟨7454193184193001502337597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19877848491181337339566925 7454193184193001502337597)
                    ·
                      refine ⟨2795322444072375563376599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7454193184193001502337597 2795322444072375563376599)
                      ·
                        rfl

theorem cell23_5443871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 1, 2, 1, 3, 3].length) (baseStart_5443871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5443871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5443871 prefixEnd_5443871 := by exact prefixLift 5443871
  have htrace : WordTrace (prefixWord ++ tailWord_5443871) baseStart_5443871 baseEnd_5443871 := by
    simpa [prefixWord, tailWord_5443871, baseEnd_5443871] using wordTrace_append hprefix tailTrace_5443871
  have hstable : (prefixWord ++ tailWord_5443871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5443871).length < 2 ^ (prefixWord ++ tailWord_5443871).sum := by decide
  have hdescent : baseEnd_5443871 < baseStart_5443871 := by decide
  rcases family_descends (prefixWord ++ tailWord_5443871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5443889 : List Nat := [1, 2, 2, 3, 4, 2, 2, 2, 1, 2, 2]
def baseStart_5443889 : Nat := 118140960795 + 5443889 * 2 ^ 59
def prefixEnd_5443889 : Nat := 4983230072969 + 3 ^ 40 * 5443889 * 2
def baseEnd_5443889 : Nat := 2795331686724156492951517

theorem tailTrace_5443889 : CollatzResearch.WordTrace tailWord_5443889 prefixEnd_5443889 2795331686724156492951517 := by
  unfold tailWord_5443889
  simp only [CollatzResearch.WordTrace]
  refine ⟨198554943774727370065750721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132369962516484913377167147 198554943774727370065750721)
  ·
    refine ⟨148916207831045527549313041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 198554943774727370065750721 148916207831045527549313041)
    ·
      refine ⟨111687155873284145661984781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 148916207831045527549313041 111687155873284145661984781)
      ·
        refine ⟨41882683452481554623244293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 111687155873284145661984781 41882683452481554623244293)
        ·
          refine ⟨7853003147340291491858305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 41882683452481554623244293 7853003147340291491858305)
          ·
            refine ⟨5889752360505218618893729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7853003147340291491858305 5889752360505218618893729)
            ·
              refine ⟨4417314270378913964170297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5889752360505218618893729 4417314270378913964170297)
              ·
                refine ⟨3312985702784185473127723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4417314270378913964170297 3312985702784185473127723)
                ·
                  refine ⟨4969478554176278209691585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3312985702784185473127723 4969478554176278209691585)
                  ·
                    refine ⟨3727108915632208657268689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4969478554176278209691585 3727108915632208657268689)
                    ·
                      refine ⟨2795331686724156492951517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3727108915632208657268689 2795331686724156492951517)
                      ·
                        rfl

theorem cell23_5443889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 2, 2, 2, 1, 2, 2].length) (baseStart_5443889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5443889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5443889 prefixEnd_5443889 := by exact prefixLift 5443889
  have htrace : WordTrace (prefixWord ++ tailWord_5443889) baseStart_5443889 baseEnd_5443889 := by
    simpa [prefixWord, tailWord_5443889, baseEnd_5443889] using wordTrace_append hprefix tailTrace_5443889
  have hstable : (prefixWord ++ tailWord_5443889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5443889).length < 2 ^ (prefixWord ++ tailWord_5443889).sum := by decide
  have hdescent : baseEnd_5443889 < baseStart_5443889 := by decide
  rcases family_descends (prefixWord ++ tailWord_5443889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5443932 : List Nat := [2, 2, 4, 3, 1, 1, 1, 3, 1, 3, 2]
def baseStart_5443932 : Nat := 118140960795 + 5443932 * 2 ^ 59
def prefixEnd_5443932 : Nat := 4983230072969 + 3 ^ 40 * 5443932 * 2
def baseEnd_5443932 : Nat := 2795353766392299824713819

theorem tailTrace_5443932 : CollatzResearch.WordTrace tailWord_5443932 prefixEnd_5443932 2795353766392299824713819 := by
  unfold tailWord_5443932
  simp only [CollatzResearch.WordTrace]
  refine ⟨99278256056785794204783025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132371008075714392273044033 99278256056785794204783025)
  ·
    refine ⟨74458692042589345653587269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99278256056785794204783025 74458692042589345653587269)
    ·
      refine ⟨13961004757985502310047613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 74458692042589345653587269 13961004757985502310047613)
      ·
        refine ⟨5235376784244563366267855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13961004757985502310047613 5235376784244563366267855)
        ·
          refine ⟨7853065176366845049401783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5235376784244563366267855 7853065176366845049401783)
          ·
            refine ⟨11779597764550267574102675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7853065176366845049401783 11779597764550267574102675)
            ·
              refine ⟨17669396646825401361154013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11779597764550267574102675 17669396646825401361154013)
              ·
                refine ⟨6626023742559525510432755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17669396646825401361154013 6626023742559525510432755)
                ·
                  refine ⟨9939035613839288265649133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6626023742559525510432755 9939035613839288265649133)
                  ·
                    refine ⟨3727138355189733099618425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9939035613839288265649133 3727138355189733099618425)
                    ·
                      refine ⟨2795353766392299824713819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3727138355189733099618425 2795353766392299824713819)
                      ·
                        rfl

theorem cell23_5443932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 1, 3, 1, 3, 2].length) (baseStart_5443932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5443932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5443932 prefixEnd_5443932 := by exact prefixLift 5443932
  have htrace : WordTrace (prefixWord ++ tailWord_5443932) baseStart_5443932 baseEnd_5443932 := by
    simpa [prefixWord, tailWord_5443932, baseEnd_5443932] using wordTrace_append hprefix tailTrace_5443932
  have hstable : (prefixWord ++ tailWord_5443932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5443932).length < 2 ^ (prefixWord ++ tailWord_5443932).sum := by decide
  have hdescent : baseEnd_5443932 < baseStart_5443932 := by decide
  rcases family_descends (prefixWord ++ tailWord_5443932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5443964 : List Nat := [2, 2, 2, 1, 1, 1, 2, 1, 6, 5]
def baseStart_5443964 : Nat := 118140960795 + 5443964 * 2 ^ 59
def prefixEnd_5443964 : Nat := 4983230072969 + 3 ^ 40 * 5443964 * 2
def baseEnd_5443964 : Nat := 931790065924414566504557

theorem tailTrace_5443964 : CollatzResearch.WordTrace tailWord_5443964 prefixEnd_5443964 931790065924414566504557 := by
  unfold tailWord_5443964
  simp only [CollatzResearch.WordTrace]
  refine ⟨99278839624727828937365473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132371786166303771916487297 99278839624727828937365473)
  ·
    refine ⟨74459129718545871703024105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99278839624727828937365473 74459129718545871703024105)
    ·
      refine ⟨55844347288909403777268079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74459129718545871703024105 55844347288909403777268079)
      ·
        refine ⟨83766520933364105665902119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55844347288909403777268079 83766520933364105665902119)
        ·
          refine ⟨125649781400046158498853179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83766520933364105665902119 125649781400046158498853179)
          ·
            refine ⟨188474672100069237748279769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 125649781400046158498853179 188474672100069237748279769)
            ·
              refine ⟨141356004075051928311209827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 188474672100069237748279769 141356004075051928311209827)
              ·
                refine ⟨212034006112577892466814741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 141356004075051928311209827 212034006112577892466814741)
                ·
                  refine ⟨9939094036527088709381941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 212034006112577892466814741 9939094036527088709381941)
                  ·
                    refine ⟨931790065924414566504557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9939094036527088709381941 931790065924414566504557)
                    ·
                      rfl

theorem cell23_5443964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 1, 6, 5].length) (baseStart_5443964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5443964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5443964 prefixEnd_5443964 := by exact prefixLift 5443964
  have htrace : WordTrace (prefixWord ++ tailWord_5443964) baseStart_5443964 baseEnd_5443964 := by
    simpa [prefixWord, tailWord_5443964, baseEnd_5443964] using wordTrace_append hprefix tailTrace_5443964
  have hstable : (prefixWord ++ tailWord_5443964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5443964).length < 2 ^ (prefixWord ++ tailWord_5443964).sum := by decide
  have hdescent : baseEnd_5443964 < baseStart_5443964 := by decide
  rcases family_descends (prefixWord ++ tailWord_5443964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5443998 : List Nat := [4, 3, 1, 2, 1, 1, 1, 1, 4, 5]
def baseStart_5443998 : Nat := 118140960795 + 5443998 * 2 ^ 59
def prefixEnd_5443998 : Nat := 4983230072969 + 3 ^ 40 * 5443998 * 2
def baseEnd_5443998 : Nat := 931795885371832188829505

theorem tailTrace_5443998 : CollatzResearch.WordTrace tailWord_5443998 prefixEnd_5443998 931795885371832188829505 := by
  unfold tailWord_5443998
  simp only [CollatzResearch.WordTrace]
  refine ⟨24819864916416560210183581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 132372612887554987787645765 24819864916416560210183581)
  ·
    refine ⟨9307449343656210078818843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24819864916416560210183581 9307449343656210078818843)
    ·
      refine ⟨13961174015484315118228265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9307449343656210078818843 13961174015484315118228265)
      ·
        refine ⟨10470880511613236338671199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13961174015484315118228265 10470880511613236338671199)
        ·
          refine ⟨15706320767419854508006799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10470880511613236338671199 15706320767419854508006799)
          ·
            refine ⟨23559481151129781762010199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15706320767419854508006799 23559481151129781762010199)
            ·
              refine ⟨35339221726694672643015299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23559481151129781762010199 35339221726694672643015299)
              ·
                refine ⟨53008832590042008964522949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35339221726694672643015299 53008832590042008964522949)
                ·
                  refine ⟨9939156110632876680848053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 53008832590042008964522949 9939156110632876680848053)
                  ·
                    refine ⟨931795885371832188829505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9939156110632876680848053 931795885371832188829505)
                    ·
                      rfl

theorem cell23_5443998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 1, 1, 4, 5].length) (baseStart_5443998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5443998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5443998 prefixEnd_5443998 := by exact prefixLift 5443998
  have htrace : WordTrace (prefixWord ++ tailWord_5443998) baseStart_5443998 baseEnd_5443998 := by
    simpa [prefixWord, tailWord_5443998, baseEnd_5443998] using wordTrace_append hprefix tailTrace_5443998
  have hstable : (prefixWord ++ tailWord_5443998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5443998).length < 2 ^ (prefixWord ++ tailWord_5443998).sum := by decide
  have hdescent : baseEnd_5443998 < baseStart_5443998 := by decide
  rcases family_descends (prefixWord ++ tailWord_5443998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5444008 : List Nat := [2, 1, 6, 1, 1, 2, 1, 1, 1, 2, 5]
def baseStart_5444008 : Nat := 118140960795 + 5444008 * 2 ^ 59
def prefixEnd_5444008 : Nat := 4983230072969 + 3 ^ 40 * 5444008 * 2
def baseEnd_5444008 : Nat := 2795392790922041527363469

theorem tailTrace_5444008 : CollatzResearch.WordTrace tailWord_5444008 prefixEnd_5444008 2795392790922041527363469 := by
  unfold tailWord_5444008
  simp only [CollatzResearch.WordTrace]
  refine ⟨99279642030648126694666339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132372856040864168926221785 99279642030648126694666339)
  ·
    refine ⟨148919463045972190041999509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99279642030648126694666339 148919463045972190041999509)
    ·
      refine ⟨6980599830279946408218727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 148919463045972190041999509 6980599830279946408218727)
      ·
        refine ⟨10470899745419919612328091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6980599830279946408218727 10470899745419919612328091)
        ·
          refine ⟨15706349618129879418492137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10470899745419919612328091 15706349618129879418492137)
          ·
            refine ⟨11779762213597409563869103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15706349618129879418492137 11779762213597409563869103)
            ·
              refine ⟨17669643320396114345803655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11779762213597409563869103 17669643320396114345803655)
              ·
                refine ⟨26504464980594171518705483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17669643320396114345803655 26504464980594171518705483)
                ·
                  refine ⟨39756697470891257278058225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26504464980594171518705483 39756697470891257278058225)
                  ·
                    refine ⟨29817523103168442958543669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 39756697470891257278058225 29817523103168442958543669)
                    ·
                      refine ⟨2795392790922041527363469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29817523103168442958543669 2795392790922041527363469)
                      ·
                        rfl

theorem cell23_5444008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 1, 1, 1, 2, 5].length) (baseStart_5444008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5444008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5444008 prefixEnd_5444008 := by exact prefixLift 5444008
  have htrace : WordTrace (prefixWord ++ tailWord_5444008) baseStart_5444008 baseEnd_5444008 := by
    simpa [prefixWord, tailWord_5444008, baseEnd_5444008] using wordTrace_append hprefix tailTrace_5444008
  have hstable : (prefixWord ++ tailWord_5444008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5444008).length < 2 ^ (prefixWord ++ tailWord_5444008).sum := by decide
  have hdescent : baseEnd_5444008 < baseStart_5444008 := by decide
  rcases family_descends (prefixWord ++ tailWord_5444008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5444061 : List Nat := [1, 4, 3, 1, 1, 1, 2, 1, 1, 2, 6]
def baseStart_5444061 : Nat := 118140960795 + 5444061 * 2 ^ 59
def prefixEnd_5444061 : Nat := 4983230072969 + 3 ^ 40 * 5444061 * 2
def baseEnd_5444061 : Nat := 2795420005396729820000725

theorem tailTrace_5444061 : CollatzResearch.WordTrace tailWord_5444061 prefixEnd_5444061 2795420005396729820000725 := by
  unfold tailWord_5444061
  simp only [CollatzResearch.WordTrace]
  refine ⟨198561217130104243441012037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132374144753402828960674691 198561217130104243441012037)
  ·
    refine ⟨37230228211894545645189757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 198561217130104243441012037 37230228211894545645189757)
    ·
      refine ⟨13961335579460454616946159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37230228211894545645189757 13961335579460454616946159)
      ·
        refine ⟨20942003369190681925419239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13961335579460454616946159 20942003369190681925419239)
        ·
          refine ⟨31413005053786022888128859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20942003369190681925419239 31413005053786022888128859)
          ·
            refine ⟨47119507580679034332193289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31413005053786022888128859 47119507580679034332193289)
            ·
              refine ⟨35339630685509275749144967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47119507580679034332193289 35339630685509275749144967)
              ·
                refine ⟨53009446028263913623717451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35339630685509275749144967 53009446028263913623717451)
                ·
                  refine ⟨79514169042395870435576177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53009446028263913623717451 79514169042395870435576177)
                  ·
                    refine ⟨59635626781796902826682133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 79514169042395870435576177 59635626781796902826682133)
                    ·
                      refine ⟨2795420005396729820000725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 59635626781796902826682133 2795420005396729820000725)
                      ·
                        rfl

theorem cell23_5444061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 2, 1, 1, 2, 6].length) (baseStart_5444061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5444061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5444061 prefixEnd_5444061 := by exact prefixLift 5444061
  have htrace : WordTrace (prefixWord ++ tailWord_5444061) baseStart_5444061 baseEnd_5444061 := by
    simpa [prefixWord, tailWord_5444061, baseEnd_5444061] using wordTrace_append hprefix tailTrace_5444061
  have hstable : (prefixWord ++ tailWord_5444061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5444061).length < 2 ^ (prefixWord ++ tailWord_5444061).sum := by decide
  have hdescent : baseEnd_5444061 < baseStart_5444061 := by decide
  rcases family_descends (prefixWord ++ tailWord_5444061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5444071 : List Nat := [1, 1, 5, 2, 1, 1, 1, 1, 5, 5]
def baseStart_5444071 : Nat := 118140960795 + 5444071 * 2 ^ 59
def prefixEnd_5444071 : Nat := 4983230072969 + 3 ^ 40 * 5444071 * 2
def baseEnd_5444071 : Nat := 931808380067758260291893

theorem tailTrace_5444071 : CollatzResearch.WordTrace tailWord_5444071 prefixEnd_5444071 931808380067758260291893 := by
  unfold tailWord_5444071
  simp only [CollatzResearch.WordTrace]
  refine ⟨198561581860068015148876067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132374387906712010099250711 198561581860068015148876067)
  ·
    refine ⟨297842372790102022723314101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198561581860068015148876067 297842372790102022723314101)
    ·
      refine ⟨27922722449072064630310697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 297842372790102022723314101 27922722449072064630310697)
      ·
        refine ⟨20942041836804048472733023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27922722449072064630310697 20942041836804048472733023)
        ·
          refine ⟨31413062755206072709099535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20942041836804048472733023 31413062755206072709099535)
          ·
            refine ⟨47119594132809109063649303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31413062755206072709099535 47119594132809109063649303)
            ·
              refine ⟨70679391199213663595473955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47119594132809109063649303 70679391199213663595473955)
              ·
                refine ⟨106019086798820495393210933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70679391199213663595473955 106019086798820495393210933)
                ·
                  refine ⟨9939289387389421443113525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 106019086798820495393210933 9939289387389421443113525)
                  ·
                    refine ⟨931808380067758260291893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9939289387389421443113525 931808380067758260291893)
                    ·
                      rfl

theorem cell23_5444071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 1, 5, 5].length) (baseStart_5444071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5444071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5444071 prefixEnd_5444071 := by exact prefixLift 5444071
  have htrace : WordTrace (prefixWord ++ tailWord_5444071) baseStart_5444071 baseEnd_5444071 := by
    simpa [prefixWord, tailWord_5444071, baseEnd_5444071] using wordTrace_append hprefix tailTrace_5444071
  have hstable : (prefixWord ++ tailWord_5444071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5444071).length < 2 ^ (prefixWord ++ tailWord_5444071).sum := by decide
  have hdescent : baseEnd_5444071 < baseStart_5444071 := by decide
  rcases family_descends (prefixWord ++ tailWord_5444071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5444101 : List Nat := [1, 3, 1, 1, 2, 2, 4, 2, 1, 6]
def baseStart_5444101 : Nat := 118140960795 + 5444101 * 2 ^ 59
def prefixEnd_5444101 : Nat := 4983230072969 + 3 ^ 40 * 5444101 * 2
def baseEnd_5444101 : Nat := 931813514874303221166847

theorem tailTrace_5444101 : CollatzResearch.WordTrace tailWord_5444101 prefixEnd_5444101 931813514874303221166847 := by
  unfold tailWord_5444101
  simp only [CollatzResearch.WordTrace]
  refine ⟨198562676049959330272468157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132375117366639553514978771 198562676049959330272468157)
  ·
    refine ⟨74461003518734748852175559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 198562676049959330272468157 74461003518734748852175559)
    ·
      refine ⟨111691505278102123278263339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74461003518734748852175559 111691505278102123278263339)
      ·
        refine ⟨167537257917153184917395009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111691505278102123278263339 167537257917153184917395009)
        ·
          refine ⟨125652943437864888688046257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 167537257917153184917395009 125652943437864888688046257)
          ·
            refine ⟨94239707578398666516034693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 125652943437864888688046257 94239707578398666516034693)
            ·
              refine ⟨17669945170949749971756505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 94239707578398666516034693 17669945170949749971756505)
              ·
                refine ⟨13252458878212312478817379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17669945170949749971756505 13252458878212312478817379)
                ·
                  refine ⟨19878688317318468718226069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13252458878212312478817379 19878688317318468718226069)
                  ·
                    refine ⟨931813514874303221166847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19878688317318468718226069 931813514874303221166847)
                    ·
                      rfl

theorem cell23_5444101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 4, 2, 1, 6].length) (baseStart_5444101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5444101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5444101 prefixEnd_5444101 := by exact prefixLift 5444101
  have htrace : WordTrace (prefixWord ++ tailWord_5444101) baseStart_5444101 baseEnd_5444101 := by
    simpa [prefixWord, tailWord_5444101, baseEnd_5444101] using wordTrace_append hprefix tailTrace_5444101
  have hstable : (prefixWord ++ tailWord_5444101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5444101).length < 2 ^ (prefixWord ++ tailWord_5444101).sum := by decide
  have hdescent : baseEnd_5444101 < baseStart_5444101 := by decide
  rcases family_descends (prefixWord ++ tailWord_5444101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5444138 : List Nat := [3, 1, 4, 1, 1, 3, 1, 1, 1, 1, 6]
def baseStart_5444138 : Nat := 118140960795 + 5444138 * 2 ^ 59
def prefixEnd_5444138 : Nat := 4983230072969 + 3 ^ 40 * 5444138 * 2
def baseEnd_5444138 : Nat := 2795459543407126018737871

theorem tailTrace_5444138 : CollatzResearch.WordTrace tailWord_5444138 prefixEnd_5444138 2795459543407126018737871 := by
  unfold tailWord_5444138
  simp only [CollatzResearch.WordTrace]
  refine ⟨49641006387706321397891267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132376017033883523727710045 49641006387706321397891267)
  ·
    refine ⟨74461509581559482096836901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49641006387706321397891267 74461509581559482096836901)
    ·
      refine ⟨13961533046542402893156919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 74461509581559482096836901 13961533046542402893156919)
      ·
        refine ⟨20942299569813604339735379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13961533046542402893156919 20942299569813604339735379)
        ·
          refine ⟨31413449354720406509603069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20942299569813604339735379 31413449354720406509603069)
          ·
            refine ⟨11780043508020152441101151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31413449354720406509603069 11780043508020152441101151)
            ·
              refine ⟨17670065262030228661651727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11780043508020152441101151 17670065262030228661651727)
              ·
                refine ⟨26505097893045342992477591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17670065262030228661651727 26505097893045342992477591)
                ·
                  refine ⟨39757646839568014488716387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26505097893045342992477591 39757646839568014488716387)
                  ·
                    refine ⟨59636470259352021733074581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 39757646839568014488716387 59636470259352021733074581)
                    ·
                      refine ⟨2795459543407126018737871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 59636470259352021733074581 2795459543407126018737871)
                      ·
                        rfl

theorem cell23_5444138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 1, 1, 1, 1, 6].length) (baseStart_5444138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5444138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5444138 prefixEnd_5444138 := by exact prefixLift 5444138
  have htrace : WordTrace (prefixWord ++ tailWord_5444138) baseStart_5444138 baseEnd_5444138 := by
    simpa [prefixWord, tailWord_5444138, baseEnd_5444138] using wordTrace_append hprefix tailTrace_5444138
  have hstable : (prefixWord ++ tailWord_5444138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5444138).length < 2 ^ (prefixWord ++ tailWord_5444138).sum := by decide
  have hdescent : baseEnd_5444138 < baseStart_5444138 := by decide
  rcases family_descends (prefixWord ++ tailWord_5444138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5444142 : List Nat := [4, 1, 3, 1, 3, 1, 2, 2, 1, 1, 4]
def baseStart_5444142 : Nat := 118140960795 + 5444142 * 2 ^ 59
def prefixEnd_5444142 : Nat := 4983230072969 + 3 ^ 40 * 5444142 * 2
def baseEnd_5444142 : Nat := 2795461597329744003087853

theorem tailTrace_5444142 : CollatzResearch.WordTrace tailWord_5444142 prefixEnd_5444142 2795461597329744003087853 := by
  unfold tailWord_5444142
  simp only [CollatzResearch.WordTrace]
  refine ⟨24820521430351349284338835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 132376114295207196183140453 24820521430351349284338835)
  ·
    refine ⟨37230782145527023926508253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24820521430351349284338835 37230782145527023926508253)
    ·
      refine ⟨13961543304572633972440595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37230782145527023926508253 13961543304572633972440595)
      ·
        refine ⟨20942314956858950958660893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13961543304572633972440595 20942314956858950958660893)
        ·
          refine ⟨7853368108822106609497835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20942314956858950958660893 7853368108822106609497835)
          ·
            refine ⟨11780052163233159914246753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7853368108822106609497835 11780052163233159914246753)
            ·
              refine ⟨8835039122424869935685065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11780052163233159914246753 8835039122424869935685065)
              ·
                refine ⟨6626279341818652451763799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8835039122424869935685065 6626279341818652451763799)
                ·
                  refine ⟨9939419012727978677645699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6626279341818652451763799 9939419012727978677645699)
                  ·
                    refine ⟨14909128519091968016468549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9939419012727978677645699 14909128519091968016468549)
                    ·
                      refine ⟨2795461597329744003087853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14909128519091968016468549 2795461597329744003087853)
                      ·
                        rfl

theorem cell23_5444142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 2, 2, 1, 1, 4].length) (baseStart_5444142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5444142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5444142 prefixEnd_5444142 := by exact prefixLift 5444142
  have htrace : WordTrace (prefixWord ++ tailWord_5444142) baseStart_5444142 baseEnd_5444142 := by
    simpa [prefixWord, tailWord_5444142, baseEnd_5444142] using wordTrace_append hprefix tailTrace_5444142
  have hstable : (prefixWord ++ tailWord_5444142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5444142).length < 2 ^ (prefixWord ++ tailWord_5444142).sum := by decide
  have hdescent : baseEnd_5444142 < baseStart_5444142 := by decide
  rcases family_descends (prefixWord ++ tailWord_5444142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5444191 : List Nat := [1, 1, 2, 3, 1, 1, 1, 5, 2, 6]
def baseStart_5444191 : Nat := 118140960795 + 5444191 * 2 ^ 59
def prefixEnd_5444191 : Nat := 4983230072969 + 3 ^ 40 * 5444191 * 2
def baseEnd_5444191 : Nat := 931828919293938103791709

theorem tailTrace_5444191 : CollatzResearch.WordTrace tailWord_5444191 prefixEnd_5444191 931828919293938103791709 := by
  unfold tailWord_5444191
  simp only [CollatzResearch.WordTrace]
  refine ⟨198565958619633275643244427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132377305746422183762162951 198565958619633275643244427)
  ·
    refine ⟨297848937929449913464866641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198565958619633275643244427 297848937929449913464866641)
    ·
      refine ⟨223386703447087435098649981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 297848937929449913464866641 223386703447087435098649981)
      ·
        refine ⟨83770013792657788161993743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 223386703447087435098649981 83770013792657788161993743)
        ·
          refine ⟨125655020688986682242990615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83770013792657788161993743 125655020688986682242990615)
          ·
            refine ⟨188482531033480023364485923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 125655020688986682242990615 188482531033480023364485923)
            ·
              refine ⟨282723796550220035046728885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 188482531033480023364485923 282723796550220035046728885)
              ·
                refine ⟨26505355926583128285630833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 282723796550220035046728885 26505355926583128285630833)
                ·
                  refine ⟨19879016944937346214223125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26505355926583128285630833 19879016944937346214223125)
                  ·
                    refine ⟨931828919293938103791709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19879016944937346214223125 931828919293938103791709)
                    ·
                      rfl

theorem cell23_5444191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 5, 2, 6].length) (baseStart_5444191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5444191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5444191 prefixEnd_5444191 := by exact prefixLift 5444191
  have htrace : WordTrace (prefixWord ++ tailWord_5444191) baseStart_5444191 baseEnd_5444191 := by
    simpa [prefixWord, tailWord_5444191, baseEnd_5444191] using wordTrace_append hprefix tailTrace_5444191
  have hstable : (prefixWord ++ tailWord_5444191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5444191).length < 2 ^ (prefixWord ++ tailWord_5444191).sum := by decide
  have hdescent : baseEnd_5444191 < baseStart_5444191 := by decide
  rcases family_descends (prefixWord ++ tailWord_5444191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5444192 : List Nat := [2, 1, 1, 3, 2, 1, 6, 1, 2, 1, 3]
def baseStart_5444192 : Nat := 118140960795 + 5444192 * 2 ^ 59
def prefixEnd_5444192 : Nat := 4983230072969 + 3 ^ 40 * 5444192 * 2
def baseEnd_5444192 : Nat := 2795487271362468807462623

theorem tailTrace_5444192 : CollatzResearch.WordTrace tailWord_5444192 prefixEnd_5444192 2795487271362468807462623 := by
  unfold tailWord_5444192
  simp only [CollatzResearch.WordTrace]
  refine ⟨99282997546314826407015415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132377330061753101876020553 99282997546314826407015415)
  ·
    refine ⟨148924496319472239610523123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99282997546314826407015415 148924496319472239610523123)
    ·
      refine ⟨223386744479208359415784685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148924496319472239610523123 223386744479208359415784685)
      ·
        refine ⟨83770029179703134780919257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 223386744479208359415784685 83770029179703134780919257)
        ·
          refine ⟨62827521884777351085689443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83770029179703134780919257 62827521884777351085689443)
          ·
            refine ⟨94241282827166026628534165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62827521884777351085689443 94241282827166026628534165)
            ·
              refine ⟨4417560132523407498212539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 94241282827166026628534165 4417560132523407498212539)
              ·
                refine ⟨6626340198785111247318809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4417560132523407498212539 6626340198785111247318809)
                ·
                  refine ⟨4969755149088833435489107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6626340198785111247318809 4969755149088833435489107)
                  ·
                    refine ⟨7454632723633250153233661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4969755149088833435489107 7454632723633250153233661)
                    ·
                      refine ⟨2795487271362468807462623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7454632723633250153233661 2795487271362468807462623)
                      ·
                        rfl

theorem cell23_5444192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 6, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 6, 1, 2, 1, 3].length) (baseStart_5444192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5444192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5444192 prefixEnd_5444192 := by exact prefixLift 5444192
  have htrace : WordTrace (prefixWord ++ tailWord_5444192) baseStart_5444192 baseEnd_5444192 := by
    simpa [prefixWord, tailWord_5444192, baseEnd_5444192] using wordTrace_append hprefix tailTrace_5444192
  have hstable : (prefixWord ++ tailWord_5444192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5444192).length < 2 ^ (prefixWord ++ tailWord_5444192).sum := by decide
  have hdescent : baseEnd_5444192 < baseStart_5444192 := by decide
  rcases family_descends (prefixWord ++ tailWord_5444192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5444211 : List Nat := [1, 1, 1, 2, 2, 1, 1, 3, 3, 4, 4]
def baseStart_5444211 : Nat := 118140960795 + 5444211 * 2 ^ 59
def prefixEnd_5444211 : Nat := 4983230072969 + 3 ^ 40 * 5444211 * 2
def baseEnd_5444211 : Nat := 2795497027494904233125035

theorem tailTrace_5444211 : CollatzResearch.WordTrace tailWord_5444211 prefixEnd_5444211 2795497027494904233125035 := by
  unfold tailWord_5444211
  simp only [CollatzResearch.WordTrace]
  refine ⟨198566688079560819058972487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132377792053040546039314991 198566688079560819058972487)
  ·
    refine ⟨297850032119341228588458731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198566688079560819058972487 297850032119341228588458731)
    ·
      refine ⟨446775048179011842882688097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 297850032119341228588458731 446775048179011842882688097)
      ·
        refine ⟨335081286134258882162016073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 446775048179011842882688097 335081286134258882162016073)
        ·
          refine ⟨251310964600694161621512055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 335081286134258882162016073 251310964600694161621512055)
          ·
            refine ⟨376966446901041242432268083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 251310964600694161621512055 376966446901041242432268083)
            ·
              refine ⟨565449670351561863648402125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 376966446901041242432268083 565449670351561863648402125)
              ·
                refine ⟨212043626381835698868150797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 565449670351561863648402125 212043626381835698868150797)
                ·
                  refine ⟨79516359893188387075556549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 212043626381835698868150797 79516359893188387075556549)
                  ·
                    refine ⟨14909317479972822576666853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 79516359893188387075556549 14909317479972822576666853)
                    ·
                      refine ⟨2795497027494904233125035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14909317479972822576666853 2795497027494904233125035)
                      ·
                        rfl

theorem cell23_5444211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 3, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 3, 3, 4, 4].length) (baseStart_5444211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5444211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5444211 prefixEnd_5444211 := by exact prefixLift 5444211
  have htrace : WordTrace (prefixWord ++ tailWord_5444211) baseStart_5444211 baseEnd_5444211 := by
    simpa [prefixWord, tailWord_5444211, baseEnd_5444211] using wordTrace_append hprefix tailTrace_5444211
  have hstable : (prefixWord ++ tailWord_5444211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5444211).length < 2 ^ (prefixWord ++ tailWord_5444211).sum := by decide
  have hdescent : baseEnd_5444211 < baseStart_5444211 := by decide
  rcases family_descends (prefixWord ++ tailWord_5444211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5444215 : List Nat := [1, 1, 3, 1, 1, 3, 2, 1, 6, 2, 2]
def baseStart_5444215 : Nat := 118140960795 + 5444215 * 2 ^ 59
def prefixEnd_5444215 : Nat := 4983230072969 + 3 ^ 40 * 5444215 * 2
def baseEnd_5444215 : Nat := 2795499081417522217475017

theorem tailTrace_5444215 : CollatzResearch.WordTrace tailWord_5444215 prefixEnd_5444215 2795499081417522217475017 := by
  unfold tailWord_5444215
  simp only [CollatzResearch.WordTrace]
  refine ⟨198566833971546327742118099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132377889314364218494745399 198566833971546327742118099)
  ·
    refine ⟨297850250957319491613177149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198566833971546327742118099 297850250957319491613177149)
    ·
      refine ⟨111693844108994809354941431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 297850250957319491613177149 111693844108994809354941431)
      ·
        refine ⟨167540766163492214032412147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111693844108994809354941431 167540766163492214032412147)
        ·
          refine ⟨251311149245238321048618221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 167540766163492214032412147 251311149245238321048618221)
          ·
            refine ⟨94241680966964370393231833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 251311149245238321048618221 94241680966964370393231833)
            ·
              refine ⟨70681260725223277794923875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 94241680966964370393231833 70681260725223277794923875)
              ·
                refine ⟨106021891087834916692385813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70681260725223277794923875 106021891087834916692385813)
                ·
                  refine ⟨4969776144742261719955585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 106021891087834916692385813 4969776144742261719955585)
                  ·
                    refine ⟨3727332108556696289966689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4969776144742261719955585 3727332108556696289966689)
                    ·
                      refine ⟨2795499081417522217475017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3727332108556696289966689 2795499081417522217475017)
                      ·
                        rfl

theorem cell23_5444215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 1, 6, 2, 2].length) (baseStart_5444215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5444215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5444215 prefixEnd_5444215 := by exact prefixLift 5444215
  have htrace : WordTrace (prefixWord ++ tailWord_5444215) baseStart_5444215 baseEnd_5444215 := by
    simpa [prefixWord, tailWord_5444215, baseEnd_5444215] using wordTrace_append hprefix tailTrace_5444215
  have hstable : (prefixWord ++ tailWord_5444215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5444215).length < 2 ^ (prefixWord ++ tailWord_5444215).sum := by decide
  have hdescent : baseEnd_5444215 < baseStart_5444215 := by decide
  rcases family_descends (prefixWord ++ tailWord_5444215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5444238 : List Nat := [4, 1, 1, 3, 1, 1, 2, 3, 7]
def baseStart_5444238 : Nat := 118140960795 + 5444238 * 2 ^ 59
def prefixEnd_5444238 : Nat := 4983230072969 + 3 ^ 40 * 5444238 * 2
def baseEnd_5444238 : Nat := 310612321274730625276379

theorem tailTrace_5444238 : CollatzResearch.WordTrace tailWord_5444238 prefixEnd_5444238 310612321274730625276379 := by
  unfold tailWord_5444238
  simp only [CollatzResearch.WordTrace]
  refine ⟨24820959106307875333775671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 132378448566975335113470245 24820959106307875333775671)
  ·
    refine ⟨37231438659461813000663507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24820959106307875333775671 37231438659461813000663507)
    ·
      refine ⟨55847157989192719500995261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37231438659461813000663507 55847157989192719500995261)
      ·
        refine ⟨20942684245947269812873223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55847157989192719500995261 20942684245947269812873223)
        ·
          refine ⟨31414026368920904719309835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20942684245947269812873223 31414026368920904719309835)
          ·
            refine ⟨47121039553381357078964753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31414026368920904719309835 47121039553381357078964753)
            ·
              refine ⟨35340779665036017809223565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47121039553381357078964753 35340779665036017809223565)
              ·
                refine ⟨13252792374388506678458837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35340779665036017809223565 13252792374388506678458837)
                ·
                  refine ⟨310612321274730625276379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13252792374388506678458837 310612321274730625276379)
                  ·
                    rfl

theorem cell23_5444238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 2, 3, 7].length) (baseStart_5444238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5444238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5444238 prefixEnd_5444238 := by exact prefixLift 5444238
  have htrace : WordTrace (prefixWord ++ tailWord_5444238) baseStart_5444238 baseEnd_5444238 := by
    simpa [prefixWord, tailWord_5444238, baseEnd_5444238] using wordTrace_append hprefix tailTrace_5444238
  have hstable : (prefixWord ++ tailWord_5444238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5444238).length < 2 ^ (prefixWord ++ tailWord_5444238).sum := by decide
  have hdescent : baseEnd_5444238 < baseStart_5444238 := by decide
  rcases family_descends (prefixWord ++ tailWord_5444238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5444305 : List Nat := [1, 2, 2, 1, 2, 3, 1, 3, 2, 4, 2]
def baseStart_5444305 : Nat := 118140960795 + 5444305 * 2 ^ 59
def prefixEnd_5444305 : Nat := 4983230072969 + 3 ^ 40 * 5444305 * 2
def baseEnd_5444305 : Nat := 2795545294676426865349603

theorem tailTrace_5444305 : CollatzResearch.WordTrace tailWord_5444305 prefixEnd_5444305 2795545294676426865349603 := by
  unfold tailWord_5444305
  simp only [CollatzResearch.WordTrace]
  refine ⟨198570116541220273112894369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132380077694146848741929579 198570116541220273112894369)
  ·
    refine ⟨148927587405915204834670777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 198570116541220273112894369 148927587405915204834670777)
    ·
      refine ⟨111695690554436403626003083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 148927587405915204834670777 111695690554436403626003083)
      ·
        refine ⟨167543535831654605439004625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111695690554436403626003083 167543535831654605439004625)
        ·
          refine ⟨125657651873740954079253469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 167543535831654605439004625 125657651873740954079253469)
          ·
            refine ⟨47121619452652857779720051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 125657651873740954079253469 47121619452652857779720051)
            ·
              refine ⟨70682429178979286669580077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47121619452652857779720051 70682429178979286669580077)
              ·
                refine ⟨26505910942117232501092529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 70682429178979286669580077 26505910942117232501092529)
                ·
                  refine ⟨19879433206587924375819397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26505910942117232501092529 19879433206587924375819397)
                  ·
                    refine ⟨3727393726235235820466137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19879433206587924375819397 3727393726235235820466137)
                    ·
                      refine ⟨2795545294676426865349603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3727393726235235820466137 2795545294676426865349603)
                      ·
                        rfl

theorem cell23_5444305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 3, 2, 4, 2].length) (baseStart_5444305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5444305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5444305 prefixEnd_5444305 := by exact prefixLift 5444305
  have htrace : WordTrace (prefixWord ++ tailWord_5444305) baseStart_5444305 baseEnd_5444305 := by
    simpa [prefixWord, tailWord_5444305, baseEnd_5444305] using wordTrace_append hprefix tailTrace_5444305
  have hstable : (prefixWord ++ tailWord_5444305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5444305).length < 2 ^ (prefixWord ++ tailWord_5444305).sum := by decide
  have hdescent : baseEnd_5444305 < baseStart_5444305 := by decide
  rcases family_descends (prefixWord ++ tailWord_5444305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5444325 : List Nat := [1, 3, 1, 4, 1, 2, 2, 1, 1, 4, 3]
def baseStart_5444325 : Nat := 118140960795 + 5444325 * 2 ^ 59
def prefixEnd_5444325 : Nat := 4983230072969 + 3 ^ 40 * 5444325 * 2
def baseEnd_5444325 : Nat := 2795555564289516787099511

theorem tailTrace_5444325 : CollatzResearch.WordTrace tailWord_5444325 prefixEnd_5444325 2795555564289516787099511 := by
  unfold tailWord_5444325
  simp only [CollatzResearch.WordTrace]
  refine ⟨198570846001147816528622429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132380564000765211019081619 198570846001147816528622429)
  ·
    refine ⟨74464067250430431198233411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 198570846001147816528622429 74464067250430431198233411)
    ·
      refine ⟨111696100875645646797350117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74464067250430431198233411 111696100875645646797350117)
      ·
        refine ⟨20943018914183558774503147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 111696100875645646797350117 20943018914183558774503147)
        ·
          refine ⟨31414528371275338161754721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20943018914183558774503147 31414528371275338161754721)
          ·
            refine ⟨23560896278456503621316041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31414528371275338161754721 23560896278456503621316041)
            ·
              refine ⟨17670672208842377715987031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23560896278456503621316041 17670672208842377715987031)
              ·
                refine ⟨26506008313263566573980547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17670672208842377715987031 26506008313263566573980547)
                ·
                  refine ⟨39759012469895349860970821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26506008313263566573980547 39759012469895349860970821)
                  ·
                    refine ⟨7454814838105378098932029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 39759012469895349860970821 7454814838105378098932029)
                    ·
                      refine ⟨2795555564289516787099511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7454814838105378098932029 2795555564289516787099511)
                      ·
                        rfl

theorem cell23_5444325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 2, 1, 1, 4, 3].length) (baseStart_5444325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5444325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5444325 prefixEnd_5444325 := by exact prefixLift 5444325
  have htrace : WordTrace (prefixWord ++ tailWord_5444325) baseStart_5444325 baseEnd_5444325 := by
    simpa [prefixWord, tailWord_5444325, baseEnd_5444325] using wordTrace_append hprefix tailTrace_5444325
  have hstable : (prefixWord ++ tailWord_5444325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5444325).length < 2 ^ (prefixWord ++ tailWord_5444325).sum := by decide
  have hdescent : baseEnd_5444325 < baseStart_5444325 := by decide
  rcases family_descends (prefixWord ++ tailWord_5444325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5444342 : List Nat := [5, 1, 1, 1, 1, 2, 3, 2, 2, 2, 3]
def baseStart_5444342 : Nat := 118140960795 + 5444342 * 2 ^ 59
def prefixEnd_5444342 : Nat := 4983230072969 + 3 ^ 40 * 5444342 * 2
def baseEnd_5444342 : Nat := 2795564293460643220586933

theorem tailTrace_5444342 : CollatzResearch.WordTrace tailWord_5444342 prefixEnd_5444342 2795564293460643220586933 := by
  unfold tailWord_5444342
  simp only [CollatzResearch.WordTrace]
  refine ⟨12410716627630389276999455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 132380977361390818954660853 12410716627630389276999455)
  ·
    refine ⟨18616074941445583915499183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12410716627630389276999455 18616074941445583915499183)
    ·
      refine ⟨27924112412168375873248775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18616074941445583915499183 27924112412168375873248775)
      ·
        refine ⟨41886168618252563809873163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27924112412168375873248775 41886168618252563809873163)
        ·
          refine ⟨62829252927378845714809745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41886168618252563809873163 62829252927378845714809745)
          ·
            refine ⟨47121939695534134286107309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62829252927378845714809745 47121939695534134286107309)
            ·
              refine ⟨17670727385825300357290241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47121939695534134286107309 17670727385825300357290241)
              ·
                refine ⟨13253045539368975267967681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17670727385825300357290241 13253045539368975267967681)
                ·
                  refine ⟨9939784154526731450975761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13253045539368975267967681 9939784154526731450975761)
                  ·
                    refine ⟨7454838115895048588231821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9939784154526731450975761 7454838115895048588231821)
                    ·
                      refine ⟨2795564293460643220586933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7454838115895048588231821 2795564293460643220586933)
                      ·
                        rfl

theorem cell23_5444342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 3, 2, 2, 2, 3].length) (baseStart_5444342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5444342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5444342 prefixEnd_5444342 := by exact prefixLift 5444342
  have htrace : WordTrace (prefixWord ++ tailWord_5444342) baseStart_5444342 baseEnd_5444342 := by
    simpa [prefixWord, tailWord_5444342, baseEnd_5444342] using wordTrace_append hprefix tailTrace_5444342
  have hstable : (prefixWord ++ tailWord_5444342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5444342).length < 2 ^ (prefixWord ++ tailWord_5444342).sum := by decide
  have hdescent : baseEnd_5444342 < baseStart_5444342 := by decide
  rcases family_descends (prefixWord ++ tailWord_5444342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5444349 : List Nat := [1, 4, 1, 1, 1, 1, 7, 2, 1, 4]
def baseStart_5444349 : Nat := 118140960795 + 5444349 * 2 ^ 59
def prefixEnd_5444349 : Nat := 4983230072969 + 3 ^ 40 * 5444349 * 2
def baseEnd_5444349 : Nat := 931855962608408231066467

theorem tailTrace_5444349 : CollatzResearch.WordTrace tailWord_5444349 prefixEnd_5444349 931855962608408231066467 := by
  unfold tailWord_5444349
  simp only [CollatzResearch.WordTrace]
  refine ⟨198571721353060868627496101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132381147568707245751664067 198571721353060868627496101)
  ·
    refine ⟨37232197753698912867655519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 198571721353060868627496101 37232197753698912867655519)
    ·
      refine ⟨55848296630548369301483279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37232197753698912867655519 55848296630548369301483279)
      ·
        refine ⟨83772444945822553952224919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55848296630548369301483279 83772444945822553952224919)
        ·
          refine ⟨125658667418733830928337379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83772444945822553952224919 125658667418733830928337379)
          ·
            refine ⟨188488001128100746392506069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 125658667418733830928337379 188488001128100746392506069)
            ·
              refine ⟨4417687526439861243574361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 188488001128100746392506069 4417687526439861243574361)
              ·
                refine ⟨3313265644829895932680771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4417687526439861243574361 3313265644829895932680771)
                ·
                  refine ⟨4969898467244843899021157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3313265644829895932680771 4969898467244843899021157)
                  ·
                    refine ⟨931855962608408231066467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4969898467244843899021157 931855962608408231066467)
                    ·
                      rfl

theorem cell23_5444349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 7, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 7, 2, 1, 4].length) (baseStart_5444349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5444349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5444349 prefixEnd_5444349 := by exact prefixLift 5444349
  have htrace : WordTrace (prefixWord ++ tailWord_5444349) baseStart_5444349 baseEnd_5444349 := by
    simpa [prefixWord, tailWord_5444349, baseEnd_5444349] using wordTrace_append hprefix tailTrace_5444349
  have hstable : (prefixWord ++ tailWord_5444349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5444349).length < 2 ^ (prefixWord ++ tailWord_5444349).sum := by decide
  have hdescent : baseEnd_5444349 < baseStart_5444349 := by decide
  rcases family_descends (prefixWord ++ tailWord_5444349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5444389 : List Nat := [1, 3, 1, 2, 3, 1, 2, 5, 1, 1, 3]
def baseStart_5444389 : Nat := 118140960795 + 5444389 * 2 ^ 59
def prefixEnd_5444389 : Nat := 4983230072969 + 3 ^ 40 * 5444389 * 2
def baseEnd_5444389 : Nat := 2795588427051404536699217

theorem tailTrace_5444389 : CollatzResearch.WordTrace tailWord_5444389 prefixEnd_5444389 2795588427051404536699217 := by
  unfold tailWord_5444389
  simp only [CollatzResearch.WordTrace]
  refine ⟨198573180272915955458952221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132382120181943970305968147 198573180272915955458952221)
  ·
    refine ⟨74464942602343483297107083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 198573180272915955458952221 74464942602343483297107083)
    ·
      refine ⟨111697413903515224945660625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74464942602343483297107083 111697413903515224945660625)
      ·
        refine ⟨83773060427636418709245469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111697413903515224945660625 83773060427636418709245469)
        ·
          refine ⟨31414897660363657015967051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 83773060427636418709245469 31414897660363657015967051)
          ·
            refine ⟨47122346490545485523950577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31414897660363657015967051 47122346490545485523950577)
            ·
              refine ⟨35341759867909114142962933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47122346490545485523950577 35341759867909114142962933)
              ·
                refine ⟨3313289987616479450902775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 35341759867909114142962933 3313289987616479450902775)
                ·
                  refine ⟨4969934981424719176354163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3313289987616479450902775 4969934981424719176354163)
                  ·
                    refine ⟨7454902472137078764531245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4969934981424719176354163 7454902472137078764531245)
                    ·
                      refine ⟨2795588427051404536699217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7454902472137078764531245 2795588427051404536699217)
                      ·
                        rfl

theorem cell23_5444389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 2, 5, 1, 1, 3].length) (baseStart_5444389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5444389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5444389 prefixEnd_5444389 := by exact prefixLift 5444389
  have htrace : WordTrace (prefixWord ++ tailWord_5444389) baseStart_5444389 baseEnd_5444389 := by
    simpa [prefixWord, tailWord_5444389, baseEnd_5444389] using wordTrace_append hprefix tailTrace_5444389
  have hstable : (prefixWord ++ tailWord_5444389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5444389).length < 2 ^ (prefixWord ++ tailWord_5444389).sum := by decide
  have hdescent : baseEnd_5444389 < baseStart_5444389 := by decide
  rcases family_descends (prefixWord ++ tailWord_5444389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5444425 : List Nat := [1, 2, 1, 1, 2, 5, 1, 3, 1, 2, 4]
def baseStart_5444425 : Nat := 118140960795 + 5444425 * 2 ^ 59
def prefixEnd_5444425 : Nat := 4983230072969 + 3 ^ 40 * 5444425 * 2
def baseEnd_5444425 : Nat := 2795606912354966395849051

theorem tailTrace_5444425 : CollatzResearch.WordTrace tailWord_5444425 prefixEnd_5444425 2795606912354966395849051 := by
  unfold tailWord_5444425
  simp only [CollatzResearch.WordTrace]
  refine ⟨198574493300785533607262729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132382995533857022404841819 198574493300785533607262729)
  ·
    refine ⟨148930869975589150205447047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 198574493300785533607262729 148930869975589150205447047)
    ·
      refine ⟨223396304963383725308170571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148930869975589150205447047 223396304963383725308170571)
      ·
        refine ⟨335094457445075587962255857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 223396304963383725308170571 335094457445075587962255857)
        ·
          refine ⟨251320843083806690971691893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 335094457445075587962255857 251320843083806690971691893)
          ·
            refine ⟨23561329039106877278596115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 251320843083806690971691893 23561329039106877278596115)
            ·
              refine ⟨35341993558660315917894173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23561329039106877278596115 35341993558660315917894173)
              ·
                refine ⟨13253247584497618469210315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35341993558660315917894173 13253247584497618469210315)
                ·
                  refine ⟨19879871376746427703815473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13253247584497618469210315 19879871376746427703815473)
                  ·
                    refine ⟨14909903532559820777861605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19879871376746427703815473 14909903532559820777861605)
                    ·
                      refine ⟨2795606912354966395849051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14909903532559820777861605 2795606912354966395849051)
                      ·
                        rfl

theorem cell23_5444425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 1, 3, 1, 2, 4].length) (baseStart_5444425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5444425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5444425 prefixEnd_5444425 := by exact prefixLift 5444425
  have htrace : WordTrace (prefixWord ++ tailWord_5444425) baseStart_5444425 baseEnd_5444425 := by
    simpa [prefixWord, tailWord_5444425, baseEnd_5444425] using wordTrace_append hprefix tailTrace_5444425
  have hstable : (prefixWord ++ tailWord_5444425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5444425).length < 2 ^ (prefixWord ++ tailWord_5444425).sum := by decide
  have hdescent : baseEnd_5444425 < baseStart_5444425 := by decide
  rcases family_descends (prefixWord ++ tailWord_5444425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5444472 : List Nat := [2, 1, 2, 1, 1, 1, 1, 6, 3, 3, 2]
def baseStart_5444472 : Nat := 118140960795 + 5444472 * 2 ^ 59
def prefixEnd_5444472 : Nat := 4983230072969 + 3 ^ 40 * 5444472 * 2
def baseEnd_5444472 : Nat := 2795631045945727711961335

theorem tailTrace_5444472 : CollatzResearch.WordTrace tailWord_5444472 prefixEnd_5444472 2795631045945727711961335 := by
  unfold tailWord_5444472
  simp only [CollatzResearch.WordTrace]
  refine ⟨99288103765807630317111835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132384138354410173756149113 99288103765807630317111835)
  ·
    refine ⟨148932155648711445475667753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99288103765807630317111835 148932155648711445475667753)
    ·
      refine ⟨111699116736533584106750815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 148932155648711445475667753 111699116736533584106750815)
      ·
        refine ⟨167548675104800376160126223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111699116736533584106750815 167548675104800376160126223)
        ·
          refine ⟨251323012657200564240189335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 167548675104800376160126223 251323012657200564240189335)
          ·
            refine ⟨376984518985800846360284003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 251323012657200564240189335 376984518985800846360284003)
            ·
              refine ⟨565476778478701269540426005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 376984518985800846360284003 565476778478701269540426005)
              ·
                refine ⟨26506723991189122009707469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 565476778478701269540426005 26506723991189122009707469)
                ·
                  refine ⟨9940021496695920753640301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26506723991189122009707469 9940021496695920753640301)
                  ·
                    refine ⟨3727508061260970282615113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9940021496695920753640301 3727508061260970282615113)
                    ·
                      refine ⟨2795631045945727711961335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3727508061260970282615113 2795631045945727711961335)
                      ·
                        rfl

theorem cell23_5444472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 6, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 6, 3, 3, 2].length) (baseStart_5444472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5444472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5444472 prefixEnd_5444472 := by exact prefixLift 5444472
  have htrace : WordTrace (prefixWord ++ tailWord_5444472) baseStart_5444472 baseEnd_5444472 := by
    simpa [prefixWord, tailWord_5444472, baseEnd_5444472] using wordTrace_append hprefix tailTrace_5444472
  have hstable : (prefixWord ++ tailWord_5444472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5444472).length < 2 ^ (prefixWord ++ tailWord_5444472).sum := by decide
  have hdescent : baseEnd_5444472 < baseStart_5444472 := by decide
  rcases family_descends (prefixWord ++ tailWord_5444472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5444489 : List Nat := [1, 2, 1, 1, 5, 2, 1, 4, 1, 3, 2]
def baseStart_5444489 : Nat := 118140960795 + 5444489 * 2 ^ 59
def prefixEnd_5444489 : Nat := 4983230072969 + 3 ^ 40 * 5444489 * 2
def baseEnd_5444489 : Nat := 2795639775116854145448757

theorem tailTrace_5444489 : CollatzResearch.WordTrace tailWord_5444489 prefixEnd_5444489 2795639775116854145448757 := by
  unfold tailWord_5444489
  simp only [CollatzResearch.WordTrace]
  refine ⟨198576827572553672537592521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132384551715035781691728347 198576827572553672537592521)
  ·
    refine ⟨148932620679415254403194391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 198576827572553672537592521 148932620679415254403194391)
    ·
      refine ⟨223398931019122881604791587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148932620679415254403194391 223398931019122881604791587)
      ·
        refine ⟨335098396528684322407187381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 223398931019122881604791587 335098396528684322407187381)
        ·
          refine ⟨31415474674564155225673817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 335098396528684322407187381 31415474674564155225673817)
          ·
            refine ⟨23561606005923116419255363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31415474674564155225673817 23561606005923116419255363)
            ·
              refine ⟨35342409008884674628883045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23561606005923116419255363 35342409008884674628883045)
              ·
                refine ⟨6626701689165876492915571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35342409008884674628883045 6626701689165876492915571)
                ·
                  refine ⟨9940052533748814739373357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6626701689165876492915571 9940052533748814739373357)
                  ·
                    refine ⟨3727519700155805527265009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9940052533748814739373357 3727519700155805527265009)
                    ·
                      refine ⟨2795639775116854145448757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3727519700155805527265009 2795639775116854145448757)
                      ·
                        rfl

theorem cell23_5444489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 1, 4, 1, 3, 2].length) (baseStart_5444489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5444489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5444489 prefixEnd_5444489 := by exact prefixLift 5444489
  have htrace : WordTrace (prefixWord ++ tailWord_5444489) baseStart_5444489 baseEnd_5444489 := by
    simpa [prefixWord, tailWord_5444489, baseEnd_5444489] using wordTrace_append hprefix tailTrace_5444489
  have hstable : (prefixWord ++ tailWord_5444489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5444489).length < 2 ^ (prefixWord ++ tailWord_5444489).sum := by decide
  have hdescent : baseEnd_5444489 < baseStart_5444489 := by decide
  rcases family_descends (prefixWord ++ tailWord_5444489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5444505 : List Nat := [1, 2, 1, 2, 1, 3, 1, 2, 1, 6, 3]
def baseStart_5444505 : Nat := 118140960795 + 5444505 * 2 ^ 59
def prefixEnd_5444505 : Nat := 4983230072969 + 3 ^ 40 * 5444505 * 2
def baseEnd_5444505 : Nat := 2795647990807326082848683

theorem tailTrace_5444505 : CollatzResearch.WordTrace tailWord_5444505 prefixEnd_5444505 2795647990807326082848683 := by
  unfold tailWord_5444505
  simp only [CollatzResearch.WordTrace]
  refine ⟨198577411140495707270174969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132384940760330471513449979 198577411140495707270174969)
  ·
    refine ⟨148933058355371780452631227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 198577411140495707270174969 148933058355371780452631227)
    ·
      refine ⟨223399587533057670678946841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148933058355371780452631227 223399587533057670678946841)
      ·
        refine ⟨167549690649793253009210131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 223399587533057670678946841 167549690649793253009210131)
        ·
          refine ⟨251324535974689879513815197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 167549690649793253009210131 251324535974689879513815197)
          ·
            refine ⟨94246700990508704817680699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 251324535974689879513815197 94246700990508704817680699)
            ·
              refine ⟨141370051485763057226521049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 94246700990508704817680699 141370051485763057226521049)
              ·
                refine ⟨106027538614322292919890787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 141370051485763057226521049 106027538614322292919890787)
                ·
                  refine ⟨159041307921483439379836181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 106027538614322292919890787 159041307921483439379836181)
                  ·
                    refine ⟨7455061308819536220929821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 159041307921483439379836181 7455061308819536220929821)
                    ·
                      refine ⟨2795647990807326082848683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7455061308819536220929821 2795647990807326082848683)
                      ·
                        rfl

theorem cell23_5444505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 2, 1, 6, 3].length) (baseStart_5444505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5444505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5444505 prefixEnd_5444505 := by exact prefixLift 5444505
  have htrace : WordTrace (prefixWord ++ tailWord_5444505) baseStart_5444505 baseEnd_5444505 := by
    simpa [prefixWord, tailWord_5444505, baseEnd_5444505] using wordTrace_append hprefix tailTrace_5444505
  have hstable : (prefixWord ++ tailWord_5444505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5444505).length < 2 ^ (prefixWord ++ tailWord_5444505).sum := by decide
  have hdescent : baseEnd_5444505 < baseStart_5444505 := by decide
  rcases family_descends (prefixWord ++ tailWord_5444505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5444515 : List Nat := [1, 1, 1, 4, 1, 2, 2, 1, 4, 2, 4]
def baseStart_5444515 : Nat := 118140960795 + 5444515 * 2 ^ 59
def prefixEnd_5444515 : Nat := 4983230072969 + 3 ^ 40 * 5444515 * 2
def baseEnd_5444515 : Nat := 2795653125613871043723637

theorem tailTrace_5444515 : CollatzResearch.WordTrace tailWord_5444515 prefixEnd_5444515 2795653125613871043723637 := by
  unfold tailWord_5444515
  simp only [CollatzResearch.WordTrace]
  refine ⟨198577775870459478978038999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132385183913639652652025999 198577775870459478978038999)
  ·
    refine ⟨297866663805689218467058499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198577775870459478978038999 297866663805689218467058499)
    ·
      refine ⟨446799995708533827700587749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 297866663805689218467058499 446799995708533827700587749)
      ·
        refine ⟨83774999195350092693860203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 446799995708533827700587749 83774999195350092693860203)
        ·
          refine ⟨125662498793025139040790305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83774999195350092693860203 125662498793025139040790305)
          ·
            refine ⟨94246874094768854280592729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 125662498793025139040790305 94246874094768854280592729)
            ·
              refine ⟨70685155571076640710444547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 94246874094768854280592729 70685155571076640710444547)
              ·
                refine ⟨106027733356614961065666821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70685155571076640710444547 106027733356614961065666821)
                ·
                  refine ⟨19880200004365305199812529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 106027733356614961065666821 19880200004365305199812529)
                  ·
                    refine ⟨14910150003273978899859397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19880200004365305199812529 14910150003273978899859397)
                    ·
                      refine ⟨2795653125613871043723637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14910150003273978899859397 2795653125613871043723637)
                      ·
                        rfl

theorem cell23_5444515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 1, 4, 2, 4].length) (baseStart_5444515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5444515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5444515 prefixEnd_5444515 := by exact prefixLift 5444515
  have htrace : WordTrace (prefixWord ++ tailWord_5444515) baseStart_5444515 baseEnd_5444515 := by
    simpa [prefixWord, tailWord_5444515, baseEnd_5444515] using wordTrace_append hprefix tailTrace_5444515
  have hstable : (prefixWord ++ tailWord_5444515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5444515).length < 2 ^ (prefixWord ++ tailWord_5444515).sum := by decide
  have hdescent : baseEnd_5444515 < baseStart_5444515 := by decide
  rcases family_descends (prefixWord ++ tailWord_5444515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5444536 : List Nat := [2, 1, 2, 1, 2, 5, 1, 3, 2, 2, 2]
def baseStart_5444536 : Nat := 118140960795 + 5444536 * 2 ^ 59
def prefixEnd_5444536 : Nat := 4983230072969 + 3 ^ 40 * 5444536 * 2
def baseEnd_5444536 : Nat := 2795663908707615461561041

theorem tailTrace_5444536 : CollatzResearch.WordTrace tailWord_5444536 prefixEnd_5444536 2795663908707615461561041 := by
  unfold tailWord_5444536
  simp only [CollatzResearch.WordTrace]
  refine ⟨99289270901691699782276731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132385694535588933043035641 99289270901691699782276731)
  ·
    refine ⟨148933906352537549673415097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99289270901691699782276731 148933906352537549673415097)
    ·
      refine ⟨111700429764403162255061323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 148933906352537549673415097 111700429764403162255061323)
      ·
        refine ⟨167550644646604743382591985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111700429764403162255061323 167550644646604743382591985)
        ·
          refine ⟨125662983484953557536943989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 167550644646604743382591985 125662983484953557536943989)
          ·
            refine ⟨11780904701714396019088499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 125662983484953557536943989 11780904701714396019088499)
            ·
              refine ⟨17671357052571594028632749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11780904701714396019088499 17671357052571594028632749)
              ·
                refine ⟨6626758894714347760737281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17671357052571594028632749 6626758894714347760737281)
                ·
                  refine ⟨4970069171035760820552961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6626758894714347760737281 4970069171035760820552961)
                  ·
                    refine ⟨3727551878276820615414721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4970069171035760820552961 3727551878276820615414721)
                    ·
                      refine ⟨2795663908707615461561041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3727551878276820615414721 2795663908707615461561041)
                      ·
                        rfl

theorem cell23_5444536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 1, 3, 2, 2, 2].length) (baseStart_5444536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5444536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5444536 prefixEnd_5444536 := by exact prefixLift 5444536
  have htrace : WordTrace (prefixWord ++ tailWord_5444536) baseStart_5444536 baseEnd_5444536 := by
    simpa [prefixWord, tailWord_5444536, baseEnd_5444536] using wordTrace_append hprefix tailTrace_5444536
  have hstable : (prefixWord ++ tailWord_5444536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5444536).length < 2 ^ (prefixWord ++ tailWord_5444536).sum := by decide
  have hdescent : baseEnd_5444536 < baseStart_5444536 := by decide
  rcases family_descends (prefixWord ++ tailWord_5444536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5444609 : List Nat := [1, 2, 4, 1, 2, 2, 3, 1, 2, 1, 4]
def baseStart_5444609 : Nat := 118140960795 + 5444609 * 2 ^ 59
def prefixEnd_5444609 : Nat := 4983230072969 + 3 ^ 40 * 5444609 * 2
def baseEnd_5444609 : Nat := 2795701392795393675948205

theorem tailTrace_5444609 : CollatzResearch.WordTrace tailWord_5444609 prefixEnd_5444609 2795701392795393675948205 := by
  unfold tailWord_5444609
  simp only [CollatzResearch.WordTrace]
  refine ⟨198581204332118933031960881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132387469554745955354640587 198581204332118933031960881)
  ·
    refine ⟨148935903249089199773970661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 198581204332118933031960881 148935903249089199773970661)
    ·
      refine ⟨27925481859204224957619499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 148935903249089199773970661 27925481859204224957619499)
      ·
        refine ⟨41888222788806337436429249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27925481859204224957619499 41888222788806337436429249)
        ·
          refine ⟨31416167091604753077321937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41888222788806337436429249 31416167091604753077321937)
          ·
            refine ⟨23562125318703564807991453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31416167091604753077321937 23562125318703564807991453)
            ·
              refine ⟨8835796994513836802996795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23562125318703564807991453 8835796994513836802996795)
              ·
                refine ⟨13253695491770755204495193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8835796994513836802996795 13253695491770755204495193)
                ·
                  refine ⟨9940271618828066403371395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13253695491770755204495193 9940271618828066403371395)
                  ·
                    refine ⟨14910407428242099605057093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9940271618828066403371395 14910407428242099605057093)
                    ·
                      refine ⟨2795701392795393675948205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14910407428242099605057093 2795701392795393675948205)
                      ·
                        rfl

theorem cell23_5444609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 3, 1, 2, 1, 4].length) (baseStart_5444609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5444609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5444609 prefixEnd_5444609 := by exact prefixLift 5444609
  have htrace : WordTrace (prefixWord ++ tailWord_5444609) baseStart_5444609 baseEnd_5444609 := by
    simpa [prefixWord, tailWord_5444609, baseEnd_5444609] using wordTrace_append hprefix tailTrace_5444609
  have hstable : (prefixWord ++ tailWord_5444609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5444609).length < 2 ^ (prefixWord ++ tailWord_5444609).sum := by decide
  have hdescent : baseEnd_5444609 < baseStart_5444609 := by decide
  rcases family_descends (prefixWord ++ tailWord_5444609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5444622 : List Nat := [4, 1, 1, 2, 2, 2, 1, 1, 2, 1, 6]
def baseStart_5444622 : Nat := 118140960795 + 5444622 * 2 ^ 59
def prefixEnd_5444622 : Nat := 4983230072969 + 3 ^ 40 * 5444622 * 2
def baseEnd_5444622 : Nat := 2795708068043902125085645

theorem tailTrace_5444622 : CollatzResearch.WordTrace tailWord_5444622 prefixEnd_5444622 2795708068043902125085645 := by
  unfold tailWord_5444622
  simp only [CollatzResearch.WordTrace]
  refine ⟨24822709810133979531523015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 132387785654047890834789413 24822709810133979531523015)
  ·
    refine ⟨37234064715200969297284523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24822709810133979531523015 37234064715200969297284523)
    ·
      refine ⟨55851097072801453945926785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37234064715200969297284523 55851097072801453945926785)
      ·
        refine ⟨41888322804601090459445089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55851097072801453945926785 41888322804601090459445089)
        ·
          refine ⟨31416242103450817844583817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41888322804601090459445089 31416242103450817844583817)
          ·
            refine ⟨23562181577588113383437863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31416242103450817844583817 23562181577588113383437863)
            ·
              refine ⟨35343272366382170075156795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23562181577588113383437863 35343272366382170075156795)
              ·
                refine ⟨53014908549573255112735193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35343272366382170075156795 53014908549573255112735193)
                ·
                  refine ⟨39761181412179941334551395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 53014908549573255112735193 39761181412179941334551395)
                  ·
                    refine ⟨59641772118269912001827093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 39761181412179941334551395 59641772118269912001827093)
                    ·
                      refine ⟨2795708068043902125085645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 59641772118269912001827093 2795708068043902125085645)
                      ·
                        rfl

theorem cell23_5444622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 1, 1, 2, 1, 6].length) (baseStart_5444622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5444622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5444622 prefixEnd_5444622 := by exact prefixLift 5444622
  have htrace : WordTrace (prefixWord ++ tailWord_5444622) baseStart_5444622 baseEnd_5444622 := by
    simpa [prefixWord, tailWord_5444622, baseEnd_5444622] using wordTrace_append hprefix tailTrace_5444622
  have hstable : (prefixWord ++ tailWord_5444622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5444622).length < 2 ^ (prefixWord ++ tailWord_5444622).sum := by decide
  have hdescent : baseEnd_5444622 < baseStart_5444622 := by decide
  rcases family_descends (prefixWord ++ tailWord_5444622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5444632 : List Nat := [2, 1, 2, 3, 2, 3, 1, 1, 8]
def baseStart_5444632 : Nat := 118140960795 + 5444632 * 2 ^ 59
def prefixEnd_5444632 : Nat := 4983230072969 + 3 ^ 40 * 5444632 * 2
def baseEnd_5444632 : Nat := 310634800316716342884511

theorem tailTrace_5444632 : CollatzResearch.WordTrace tailWord_5444632 prefixEnd_5444632 310634800316716342884511 := by
  unfold tailWord_5444632
  simp only [CollatzResearch.WordTrace]
  refine ⟨99291021605517803980024075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132388028807357071973365433 99291021605517803980024075)
  ·
    refine ⟨148936532408276705970036113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99291021605517803980024075 148936532408276705970036113)
    ·
      refine ⟨111702399306207529477527085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 148936532408276705970036113 111702399306207529477527085)
      ·
        refine ⟨41888399739827823554072657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 111702399306207529477527085 41888399739827823554072657)
        ·
          refine ⟨31416299804870867665554493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41888399739827823554072657 31416299804870867665554493)
          ·
            refine ⟨11781112426826575374582935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31416299804870867665554493 11781112426826575374582935)
            ·
              refine ⟨17671668640239863061874403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11781112426826575374582935 17671668640239863061874403)
              ·
                refine ⟨26507502960359794592811605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17671668640239863061874403 26507502960359794592811605)
                ·
                  refine ⟨310634800316716342884511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 26507502960359794592811605 310634800316716342884511)
                  ·
                    rfl

theorem cell23_5444632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 1, 1, 8].length) (baseStart_5444632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5444632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5444632 prefixEnd_5444632 := by exact prefixLift 5444632
  have htrace : WordTrace (prefixWord ++ tailWord_5444632) baseStart_5444632 baseEnd_5444632 := by
    simpa [prefixWord, tailWord_5444632, baseEnd_5444632] using wordTrace_append hprefix tailTrace_5444632
  have hstable : (prefixWord ++ tailWord_5444632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5444632).length < 2 ^ (prefixWord ++ tailWord_5444632).sum := by decide
  have hdescent : baseEnd_5444632 < baseStart_5444632 := by decide
  rcases family_descends (prefixWord ++ tailWord_5444632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5444636 : List Nat := [2, 2, 3, 1, 4, 1, 2, 1, 3, 4]
def baseStart_5444636 : Nat := 118140960795 + 5444636 * 2 ^ 59
def prefixEnd_5444636 : Nat := 4983230072969 + 3 ^ 40 * 5444636 * 2
def baseEnd_5444636 : Nat := 931905085591021690103527

theorem tailTrace_5444636 : CollatzResearch.WordTrace tailWord_5444636 prefixEnd_5444636 931905085591021690103527 := by
  unfold tailWord_5444636
  simp only [CollatzResearch.WordTrace]
  refine ⟨99291094551510558321596881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132388126068680744428795841 99291094551510558321596881)
  ·
    refine ⟨74468320913632918741197661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99291094551510558321596881 74468320913632918741197661)
    ·
      refine ⟨27925620342612344527949123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74468320913632918741197661 27925620342612344527949123)
      ·
        refine ⟨41888430513918516791923685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27925620342612344527949123 41888430513918516791923685)
        ·
          refine ⟨7854080721359721898485691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 41888430513918516791923685 7854080721359721898485691)
          ·
            refine ⟨11781121082039582847728537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7854080721359721898485691 11781121082039582847728537)
            ·
              refine ⟨8835840811529687135796403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11781121082039582847728537 8835840811529687135796403)
              ·
                refine ⟨13253761217294530703694605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8835840811529687135796403 13253761217294530703694605)
                ·
                  refine ⟨4970160456485449013885477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13253761217294530703694605 4970160456485449013885477)
                  ·
                    refine ⟨931905085591021690103527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4970160456485449013885477 931905085591021690103527)
                    ·
                      rfl

theorem cell23_5444636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 2, 1, 3, 4].length) (baseStart_5444636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5444636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5444636 prefixEnd_5444636 := by exact prefixLift 5444636
  have htrace : WordTrace (prefixWord ++ tailWord_5444636) baseStart_5444636 baseEnd_5444636 := by
    simpa [prefixWord, tailWord_5444636, baseEnd_5444636] using wordTrace_append hprefix tailTrace_5444636
  have hstable : (prefixWord ++ tailWord_5444636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5444636).length < 2 ^ (prefixWord ++ tailWord_5444636).sum := by decide
  have hdescent : baseEnd_5444636 < baseStart_5444636 := by decide
  rcases family_descends (prefixWord ++ tailWord_5444636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5444670 : List Nat := [4, 2, 1, 3, 1, 3, 1, 3, 1, 4]
def baseStart_5444670 : Nat := 118140960795 + 5444670 * 2 ^ 59
def prefixEnd_5444670 : Nat := 4983230072969 + 3 ^ 40 * 5444670 * 2
def baseEnd_5444670 : Nat := 931910905038439312428475

theorem tailTrace_5444670 : CollatzResearch.WordTrace tailWord_5444670 prefixEnd_5444670 931910905038439312428475 := by
  unfold tailWord_5444670
  simp only [CollatzResearch.WordTrace]
  refine ⟨24822928648112242556241433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 132388952789931960299954309 24822928648112242556241433)
  ·
    refine ⟨18617196486084181917181075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24822928648112242556241433 18617196486084181917181075)
    ·
      refine ⟨27925794729126272875771613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18617196486084181917181075 27925794729126272875771613)
      ·
        refine ⟨10472173023422352328414355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27925794729126272875771613 10472173023422352328414355)
        ·
          refine ⟨15708259535133528492621533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10472173023422352328414355 15708259535133528492621533)
          ·
            refine ⟨5890597325675073184733075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15708259535133528492621533 5890597325675073184733075)
            ·
              refine ⟨8835895988512609777099613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5890597325675073184733075 8835895988512609777099613)
              ·
                refine ⟨3313460995692228666412355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8835895988512609777099613 3313460995692228666412355)
                ·
                  refine ⟨4970191493538342999618533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3313460995692228666412355 4970191493538342999618533)
                  ·
                    refine ⟨931910905038439312428475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4970191493538342999618533 931910905038439312428475)
                    ·
                      rfl

theorem cell23_5444670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 3, 1, 3, 1, 4].length) (baseStart_5444670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5444670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5444670 prefixEnd_5444670 := by exact prefixLift 5444670
  have htrace : WordTrace (prefixWord ++ tailWord_5444670) baseStart_5444670 baseEnd_5444670 := by
    simpa [prefixWord, tailWord_5444670, baseEnd_5444670] using wordTrace_append hprefix tailTrace_5444670
  have hstable : (prefixWord ++ tailWord_5444670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5444670).length < 2 ^ (prefixWord ++ tailWord_5444670).sum := by decide
  have hdescent : baseEnd_5444670 < baseStart_5444670 := by decide
  rcases family_descends (prefixWord ++ tailWord_5444670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5444679 : List Nat := [1, 1, 4, 1, 3, 2, 2, 3, 1, 5]
def baseStart_5444679 : Nat := 118140960795 + 5444679 * 2 ^ 59
def prefixEnd_5444679 : Nat := 4983230072969 + 3 ^ 40 * 5444679 * 2
def baseEnd_5444679 : Nat := 931912445480402800690961

theorem tailTrace_5444679 : CollatzResearch.WordTrace tailWord_5444679 prefixEnd_5444679 931912445480402800690961 := by
  unfold tailWord_5444679
  simp only [CollatzResearch.WordTrace]
  refine ⟨198583757441865334987009091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132389171627910223324672727 198583757441865334987009091)
  ·
    refine ⟨297875636162798002480513637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198583757441865334987009091 297875636162798002480513637)
    ·
      refine ⟨55851681780524625465096307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 297875636162798002480513637 55851681780524625465096307)
      ·
        refine ⟨83777522670786938197644461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55851681780524625465096307 83777522670786938197644461)
        ·
          refine ⟨31416571001545101824116673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 83777522670786938197644461 31416571001545101824116673)
          ·
            refine ⟨23562428251158826368087505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31416571001545101824116673 23562428251158826368087505)
            ·
              refine ⟨17671821188369119776065629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23562428251158826368087505 17671821188369119776065629)
              ·
                refine ⟨6626932945638419916024611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17671821188369119776065629 6626932945638419916024611)
                ·
                  refine ⟨9940399418457629874036917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6626932945638419916024611 9940399418457629874036917)
                  ·
                    refine ⟨931912445480402800690961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9940399418457629874036917 931912445480402800690961)
                    ·
                      rfl

theorem cell23_5444679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 2, 3, 1, 5].length) (baseStart_5444679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5444679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5444679 prefixEnd_5444679 := by exact prefixLift 5444679
  have htrace : WordTrace (prefixWord ++ tailWord_5444679) baseStart_5444679 baseEnd_5444679 := by
    simpa [prefixWord, tailWord_5444679, baseEnd_5444679] using wordTrace_append hprefix tailTrace_5444679
  have hstable : (prefixWord ++ tailWord_5444679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5444679).length < 2 ^ (prefixWord ++ tailWord_5444679).sum := by decide
  have hdescent : baseEnd_5444679 < baseStart_5444679 := by decide
  rcases family_descends (prefixWord ++ tailWord_5444679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5444686 : List Nat := [4, 1, 1, 1, 1, 3, 3, 2, 2, 3, 2]
def baseStart_5444686 : Nat := 118140960795 + 5444686 * 2 ^ 59
def prefixEnd_5444686 : Nat := 4983230072969 + 3 ^ 40 * 5444686 * 2
def baseEnd_5444686 : Nat := 2795740930805789874685351

theorem tailTrace_5444686 : CollatzResearch.WordTrace tailWord_5444686 prefixEnd_5444686 2795740930805789874685351 := by
  unfold tailWord_5444686
  simp only [CollatzResearch.WordTrace]
  refine ⟨24823001594104996897814239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 132389341835226650121675941 24823001594104996897814239)
  ·
    refine ⟨37234502391157495346721359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24823001594104996897814239 37234502391157495346721359)
    ·
      refine ⟨55851753586736243020082039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37234502391157495346721359 55851753586736243020082039)
      ·
        refine ⟨83777630380104364530123059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55851753586736243020082039 83777630380104364530123059)
        ·
          refine ⟨125666445570156546795184589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83777630380104364530123059 125666445570156546795184589)
          ·
            refine ⟨47124917088808705048194221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 125666445570156546795184589 47124917088808705048194221)
            ·
              refine ⟨17671843908303264393072833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47124917088808705048194221 17671843908303264393072833)
              ·
                refine ⟨13253882931227448294804625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17671843908303264393072833 13253882931227448294804625)
                ·
                  refine ⟨9940412198420586221103469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13253882931227448294804625 9940412198420586221103469)
                  ·
                    refine ⟨3727654574407719832913801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9940412198420586221103469 3727654574407719832913801)
                    ·
                      refine ⟨2795740930805789874685351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3727654574407719832913801 2795740930805789874685351)
                      ·
                        rfl

theorem cell23_5444686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 3, 2, 2, 3, 2].length) (baseStart_5444686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5444686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5444686 prefixEnd_5444686 := by exact prefixLift 5444686
  have htrace : WordTrace (prefixWord ++ tailWord_5444686) baseStart_5444686 baseEnd_5444686 := by
    simpa [prefixWord, tailWord_5444686, baseEnd_5444686] using wordTrace_append hprefix tailTrace_5444686
  have hstable : (prefixWord ++ tailWord_5444686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5444686).length < 2 ^ (prefixWord ++ tailWord_5444686).sum := by decide
  have hdescent : baseEnd_5444686 < baseStart_5444686 := by decide
  rcases family_descends (prefixWord ++ tailWord_5444686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5444716 : List Nat := [2, 2, 1, 1, 3, 2, 2, 1, 5, 2, 2]
def baseStart_5444716 : Nat := 118140960795 + 5444716 * 2 ^ 59
def prefixEnd_5444716 : Nat := 4983230072969 + 3 ^ 40 * 5444716 * 2
def baseEnd_5444716 : Nat := 2795756335225424757310213

theorem tailTrace_5444716 : CollatzResearch.WordTrace tailWord_5444716 prefixEnd_5444716 2795756335225424757310213 := by
  unfold tailWord_5444716
  simp only [CollatzResearch.WordTrace]
  refine ⟨99292553471365645153053001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132390071295154193537404001 99292553471365645153053001)
  ·
    refine ⟨74469415103524233864789751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99292553471365645153053001 74469415103524233864789751)
    ·
      refine ⟨111704122655286350797184627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74469415103524233864789751 111704122655286350797184627)
      ·
        refine ⟨167556183982929526195776941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111704122655286350797184627 167556183982929526195776941)
        ·
          refine ⟨62833568993598572323416353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 167556183982929526195776941 62833568993598572323416353)
          ·
            refine ⟨47125176745198929242562265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62833568993598572323416353 47125176745198929242562265)
            ·
              refine ⟨35343882558899196931921699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47125176745198929242562265 35343882558899196931921699)
              ·
                refine ⟨53015823838348795397882549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35343882558899196931921699 53015823838348795397882549)
                ·
                  refine ⟨4970233484845199568551489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 53015823838348795397882549 4970233484845199568551489)
                  ·
                    refine ⟨3727675113633899676413617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4970233484845199568551489 3727675113633899676413617)
                    ·
                      refine ⟨2795756335225424757310213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3727675113633899676413617 2795756335225424757310213)
                      ·
                        rfl

theorem cell23_5444716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 5, 2, 2].length) (baseStart_5444716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5444716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5444716 prefixEnd_5444716 := by exact prefixLift 5444716
  have htrace : WordTrace (prefixWord ++ tailWord_5444716) baseStart_5444716 baseEnd_5444716 := by
    simpa [prefixWord, tailWord_5444716, baseEnd_5444716] using wordTrace_append hprefix tailTrace_5444716
  have hstable : (prefixWord ++ tailWord_5444716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5444716).length < 2 ^ (prefixWord ++ tailWord_5444716).sum := by decide
  have hdescent : baseEnd_5444716 < baseStart_5444716 := by decide
  rcases family_descends (prefixWord ++ tailWord_5444716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5444719 : List Nat := [1, 1, 2, 1, 3, 3, 3, 1, 3, 2, 3]
def baseStart_5444719 : Nat := 118140960795 + 5444719 * 2 ^ 59
def prefixEnd_5444719 : Nat := 4983230072969 + 3 ^ 40 * 5444719 * 2
def baseEnd_5444719 : Nat := 2795757875667388245572699

theorem tailTrace_5444719 : CollatzResearch.WordTrace tailWord_5444719 prefixEnd_5444719 2795757875667388245572699 := by
  unfold tailWord_5444719
  simp only [CollatzResearch.WordTrace]
  refine ⟨198585216361720421818465211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132390144241146947878976807 198585216361720421818465211)
  ·
    refine ⟨297877824542580632727697817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198585216361720421818465211 297877824542580632727697817)
    ·
      refine ⟨223408368406935474545773363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 297877824542580632727697817 223408368406935474545773363)
      ·
        refine ⟨335112552610403211818660045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 223408368406935474545773363 335112552610403211818660045)
        ·
          refine ⟨125667207228901204431997517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 335112552610403211818660045 125667207228901204431997517)
          ·
            refine ⟨47125202710837951661999069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 125667207228901204431997517 47125202710837951661999069)
            ·
              refine ⟨17671951016564231873249651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47125202710837951661999069 17671951016564231873249651)
              ·
                refine ⟨26507926524846347809874477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17671951016564231873249651 26507926524846347809874477)
                ·
                  refine ⟨9940472446817380428702929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26507926524846347809874477 9940472446817380428702929)
                  ·
                    refine ⟨7455354335113035321527197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9940472446817380428702929 7455354335113035321527197)
                    ·
                      refine ⟨2795757875667388245572699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7455354335113035321527197 2795757875667388245572699)
                      ·
                        rfl

theorem cell23_5444719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 3, 1, 3, 2, 3].length) (baseStart_5444719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5444719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5444719 prefixEnd_5444719 := by exact prefixLift 5444719
  have htrace : WordTrace (prefixWord ++ tailWord_5444719) baseStart_5444719 baseEnd_5444719 := by
    simpa [prefixWord, tailWord_5444719, baseEnd_5444719] using wordTrace_append hprefix tailTrace_5444719
  have hstable : (prefixWord ++ tailWord_5444719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5444719).length < 2 ^ (prefixWord ++ tailWord_5444719).sum := by decide
  have hdescent : baseEnd_5444719 < baseStart_5444719 := by decide
  rcases family_descends (prefixWord ++ tailWord_5444719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5444722 : List Nat := [3, 2, 1, 2, 2, 1, 1, 11]
def baseStart_5444722 : Nat := 118140960795 + 5444722 * 2 ^ 59
def prefixEnd_5444722 : Nat := 4983230072969 + 3 ^ 40 * 5444722 * 2
def baseEnd_5444722 : Nat := 103546645041087101253155

theorem tailTrace_5444722 : CollatzResearch.WordTrace tailWord_5444722 prefixEnd_5444722 103546645041087101253155 := by
  unfold tailWord_5444722
  simp only [CollatzResearch.WordTrace]
  refine ⟨49646331445177388332706105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132390217187139702220549613 49646331445177388332706105)
  ·
    refine ⟨37234748583883041249529579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49646331445177388332706105 37234748583883041249529579)
    ·
      refine ⟨55852122875824561874294369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37234748583883041249529579 55852122875824561874294369)
      ·
        refine ⟨41889092156868421405720777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55852122875824561874294369 41889092156868421405720777)
        ·
          refine ⟨31416819117651316054290583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41889092156868421405720777 31416819117651316054290583)
          ·
            refine ⟨47125228676476974081435875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31416819117651316054290583 47125228676476974081435875)
            ·
              refine ⟨70687843014715461122153813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47125228676476974081435875 70687843014715461122153813)
              ·
                refine ⟨103546645041087101253155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 70687843014715461122153813 103546645041087101253155)
                ·
                  rfl

theorem cell23_5444722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 11].length) (baseStart_5444722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5444722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5444722 prefixEnd_5444722 := by exact prefixLift 5444722
  have htrace : WordTrace (prefixWord ++ tailWord_5444722) baseStart_5444722 baseEnd_5444722 := by
    simpa [prefixWord, tailWord_5444722, baseEnd_5444722] using wordTrace_append hprefix tailTrace_5444722
  have hstable : (prefixWord ++ tailWord_5444722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5444722).length < 2 ^ (prefixWord ++ tailWord_5444722).sum := by decide
  have hdescent : baseEnd_5444722 < baseStart_5444722 := by decide
  rcases family_descends (prefixWord ++ tailWord_5444722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5444744 : List Nat := [2, 1, 3, 4, 3, 1, 2, 2, 1, 1, 3]
def baseStart_5444744 : Nat := 118140960795 + 5444744 * 2 ^ 59
def prefixEnd_5444744 : Nat := 4983230072969 + 3 ^ 40 * 5444744 * 2
def baseEnd_5444744 : Nat := 2795770712683750647760085

theorem tailTrace_5444744 : CollatzResearch.WordTrace tailWord_5444744 prefixEnd_5444744 2795770712683750647760085 := by
  unfold tailWord_5444744
  simp only [CollatzResearch.WordTrace]
  refine ⟨99293064093314925544062643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132390752124419900725416857 99293064093314925544062643)
  ·
    refine ⟨148939596139972388316093965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99293064093314925544062643 148939596139972388316093965)
    ·
      refine ⟨55852348552489645618535237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 148939596139972388316093965 55852348552489645618535237)
      ·
        refine ⟨10472315353591808553475357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 55852348552489645618535237 10472315353591808553475357)
        ·
          refine ⟨3927118257596928207553259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10472315353591808553475357 3927118257596928207553259)
          ·
            refine ⟨5890677386395392311329889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3927118257596928207553259 5890677386395392311329889)
            ·
              refine ⟨4418008039796544233497417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5890677386395392311329889 4418008039796544233497417)
              ·
                refine ⟨3313506029847408175123063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4418008039796544233497417 3313506029847408175123063)
                ·
                  refine ⟨4970259044771112262684595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3313506029847408175123063 4970259044771112262684595)
                  ·
                    refine ⟨7455388567156668394026893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4970259044771112262684595 7455388567156668394026893)
                    ·
                      refine ⟨2795770712683750647760085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7455388567156668394026893 2795770712683750647760085)
                      ·
                        rfl

theorem cell23_5444744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 3, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 3, 1, 2, 2, 1, 1, 3].length) (baseStart_5444744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5444744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5444744 prefixEnd_5444744 := by exact prefixLift 5444744
  have htrace : WordTrace (prefixWord ++ tailWord_5444744) baseStart_5444744 baseEnd_5444744 := by
    simpa [prefixWord, tailWord_5444744, baseEnd_5444744] using wordTrace_append hprefix tailTrace_5444744
  have hstable : (prefixWord ++ tailWord_5444744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5444744).length < 2 ^ (prefixWord ++ tailWord_5444744).sum := by decide
  have hdescent : baseEnd_5444744 < baseStart_5444744 := by decide
  rcases family_descends (prefixWord ++ tailWord_5444744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5444793 : List Nat := [1, 2, 1, 4, 1, 4, 1, 3, 1, 3, 2]
def baseStart_5444793 : Nat := 118140960795 + 5444793 * 2 ^ 59
def prefixEnd_5444793 : Nat := 4983230072969 + 3 ^ 40 * 5444793 * 2
def baseEnd_5444793 : Nat := 2795795873235820956047359

theorem tailTrace_5444793 : CollatzResearch.WordTrace tailWord_5444793 prefixEnd_5444793 2795795873235820956047359 := by
  unfold tailWord_5444793
  simp only [CollatzResearch.WordTrace]
  refine ⟨198587915363452332456659033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132391943575634888304439355 198587915363452332456659033)
  ·
    refine ⟨148940936522589249342494275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 198587915363452332456659033 148940936522589249342494275)
    ·
      refine ⟨223411404783883874013741413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148940936522589249342494275 223411404783883874013741413)
      ·
        refine ⟨41889638396978226377576515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 223411404783883874013741413 41889638396978226377576515)
        ·
          refine ⟨62834457595467339566364773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41889638396978226377576515 62834457595467339566364773)
          ·
            refine ⟨11781460799150126168693395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 62834457595467339566364773 11781460799150126168693395)
            ·
              refine ⟨17672191198725189253040093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11781460799150126168693395 17672191198725189253040093)
              ·
                refine ⟨6627071699521945969890035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17672191198725189253040093 6627071699521945969890035)
                ·
                  refine ⟨9940607549282918954835053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6627071699521945969890035 9940607549282918954835053)
                  ·
                    refine ⟨3727727830981094608063145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9940607549282918954835053 3727727830981094608063145)
                    ·
                      refine ⟨2795795873235820956047359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3727727830981094608063145 2795795873235820956047359)
                      ·
                        rfl

theorem cell23_5444793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 1, 3, 1, 3, 2].length) (baseStart_5444793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5444793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5444793 prefixEnd_5444793 := by exact prefixLift 5444793
  have htrace : WordTrace (prefixWord ++ tailWord_5444793) baseStart_5444793 baseEnd_5444793 := by
    simpa [prefixWord, tailWord_5444793, baseEnd_5444793] using wordTrace_append hprefix tailTrace_5444793
  have hstable : (prefixWord ++ tailWord_5444793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5444793).length < 2 ^ (prefixWord ++ tailWord_5444793).sum := by decide
  have hdescent : baseEnd_5444793 < baseStart_5444793 := by decide
  rcases family_descends (prefixWord ++ tailWord_5444793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5444800 : List Nat := [2, 1, 1, 2, 6, 2, 1, 2, 2, 1, 3]
def baseStart_5444800 : Nat := 118140960795 + 5444800 * 2 ^ 59
def prefixEnd_5444800 : Nat := 4983230072969 + 3 ^ 40 * 5444800 * 2
def baseEnd_5444800 : Nat := 2795799467600402428659827

theorem tailTrace_5444800 : CollatzResearch.WordTrace tailWord_5444800 prefixEnd_5444800 2795799467600402428659827 := by
  unfold tailWord_5444800
  simp only [CollatzResearch.WordTrace]
  refine ⟨99294085337213486326081927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132392113782951315101442569 99294085337213486326081927)
  ·
    refine ⟨148941128005820229489122891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99294085337213486326081927 148941128005820229489122891)
    ·
      refine ⟨223411692008730344233684337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148941128005820229489122891 223411692008730344233684337)
      ·
        refine ⟨167558769006547758175263253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 223411692008730344233684337 167558769006547758175263253)
        ·
          refine ⟨7854317297181926164465465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 167558769006547758175263253 7854317297181926164465465)
          ·
            refine ⟨5890737972886444623349099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7854317297181926164465465 5890737972886444623349099)
            ·
              refine ⟨8836106959329666935023649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5890737972886444623349099 8836106959329666935023649)
              ·
                refine ⟨6627080219497250201267737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8836106959329666935023649 6627080219497250201267737)
                ·
                  refine ⟨4970310164622937650950803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6627080219497250201267737 4970310164622937650950803)
                  ·
                    refine ⟨7455465246934406476426205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4970310164622937650950803 7455465246934406476426205)
                    ·
                      refine ⟨2795799467600402428659827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7455465246934406476426205 2795799467600402428659827)
                      ·
                        rfl

theorem cell23_5444800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 2, 1, 2, 2, 1, 3].length) (baseStart_5444800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5444800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5444800 prefixEnd_5444800 := by exact prefixLift 5444800
  have htrace : WordTrace (prefixWord ++ tailWord_5444800) baseStart_5444800 baseEnd_5444800 := by
    simpa [prefixWord, tailWord_5444800, baseEnd_5444800] using wordTrace_append hprefix tailTrace_5444800
  have hstable : (prefixWord ++ tailWord_5444800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5444800).length < 2 ^ (prefixWord ++ tailWord_5444800).sum := by decide
  have hdescent : baseEnd_5444800 < baseStart_5444800 := by decide
  rcases family_descends (prefixWord ++ tailWord_5444800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5444823 : List Nat := [1, 1, 3, 2, 1, 2, 2, 5, 2, 2, 2]
def baseStart_5444823 : Nat := 118140960795 + 5444823 * 2 ^ 59
def prefixEnd_5444823 : Nat := 4983230072969 + 3 ^ 40 * 5444823 * 2
def baseEnd_5444823 : Nat := 2795811277655455838672221

theorem tailTrace_5444823 : CollatzResearch.WordTrace tailWord_5444823 prefixEnd_5444823 2795811277655455838672221 := by
  unfold tailWord_5444823
  simp only [CollatzResearch.WordTrace]
  refine ⟨198589009553343647580251123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132392673035562431720167415 198589009553343647580251123)
  ·
    refine ⟨297883514330015471370376685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198589009553343647580251123 297883514330015471370376685)
    ·
      refine ⟨111706317873755801763891257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 297883514330015471370376685 111706317873755801763891257)
      ·
        refine ⟨83779738405316851322918443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111706317873755801763891257 83779738405316851322918443)
        ·
          refine ⟨125669607607975276984377665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83779738405316851322918443 125669607607975276984377665)
          ·
            refine ⟨94252205705981457738283249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 125669607607975276984377665 94252205705981457738283249)
            ·
              refine ⟨70689154279486093303712437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 94252205705981457738283249 70689154279486093303712437)
              ·
                refine ⟨6627108213701821247223041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 70689154279486093303712437 6627108213701821247223041)
                ·
                  refine ⟨4970331160276365935417281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6627108213701821247223041 4970331160276365935417281)
                  ·
                    refine ⟨3727748370207274451562961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4970331160276365935417281 3727748370207274451562961)
                    ·
                      refine ⟨2795811277655455838672221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3727748370207274451562961 2795811277655455838672221)
                      ·
                        rfl

theorem cell23_5444823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 5, 2, 2, 2].length) (baseStart_5444823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5444823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5444823 prefixEnd_5444823 := by exact prefixLift 5444823
  have htrace : WordTrace (prefixWord ++ tailWord_5444823) baseStart_5444823 baseEnd_5444823 := by
    simpa [prefixWord, tailWord_5444823, baseEnd_5444823] using wordTrace_append hprefix tailTrace_5444823
  have hstable : (prefixWord ++ tailWord_5444823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5444823).length < 2 ^ (prefixWord ++ tailWord_5444823).sum := by decide
  have hdescent : baseEnd_5444823 < baseStart_5444823 := by decide
  rcases family_descends (prefixWord ++ tailWord_5444823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5444863 : List Nat := [1, 1, 2, 2, 1, 6, 3, 2, 5]
def baseStart_5444863 : Nat := 118140960795 + 5444863 * 2 ^ 59
def prefixEnd_5444863 : Nat := 4983230072969 + 3 ^ 40 * 5444863 * 2
def baseEnd_5444863 : Nat := 310647979653515075796893

theorem tailTrace_5444863 : CollatzResearch.WordTrace tailWord_5444863 prefixEnd_5444863 310647979653515075796893 := by
  unfold tailWord_5444863
  simp only [CollatzResearch.WordTrace]
  refine ⟨198590468473198734411707243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132393645648799156274471495 198590468473198734411707243)
  ·
    refine ⟨297885702709798101617560865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198590468473198734411707243 297885702709798101617560865)
    ·
      refine ⟨223414277032348576213170649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 297885702709798101617560865 223414277032348576213170649)
      ·
        refine ⟨167560707774261432159877987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 223414277032348576213170649 167560707774261432159877987)
        ·
          refine ⟨251341061661392148239816981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 167560707774261432159877987 251341061661392148239816981)
          ·
            refine ⟨11781612265377756948741421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 251341061661392148239816981 11781612265377756948741421)
            ·
              refine ⟨4418104599516658855778033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11781612265377756948741421 4418104599516658855778033)
              ·
                refine ⟨3313578449637494141833525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4418104599516658855778033 3313578449637494141833525)
                ·
                  refine ⟨310647979653515075796893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3313578449637494141833525 310647979653515075796893)
                  ·
                    rfl

theorem cell23_5444863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 3, 2, 5].length) (baseStart_5444863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5444863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5444863 prefixEnd_5444863 := by exact prefixLift 5444863
  have htrace : WordTrace (prefixWord ++ tailWord_5444863) baseStart_5444863 baseEnd_5444863 := by
    simpa [prefixWord, tailWord_5444863, baseEnd_5444863] using wordTrace_append hprefix tailTrace_5444863
  have hstable : (prefixWord ++ tailWord_5444863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5444863).length < 2 ^ (prefixWord ++ tailWord_5444863).sum := by decide
  have hdescent : baseEnd_5444863 < baseStart_5444863 := by decide
  rcases family_descends (prefixWord ++ tailWord_5444863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5444869 : List Nat := [1, 3, 1, 1, 2, 1, 5, 1, 1, 2, 5]
def baseStart_5444869 : Nat := 118140960795 + 5444869 * 2 ^ 59
def prefixEnd_5444869 : Nat := 4983230072969 + 3 ^ 40 * 5444869 * 2
def baseEnd_5444869 : Nat := 2795834897765562658697009

theorem tailTrace_5444869 : CollatzResearch.WordTrace tailWord_5444869 prefixEnd_5444869 2795834897765562658697009 := by
  unfold tailWord_5444869
  simp only [CollatzResearch.WordTrace]
  refine ⟨198590687311176997436425661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132393791540784664957617107 198590687311176997436425661)
  ·
    refine ⟨74471507741691374038659623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 198590687311176997436425661 74471507741691374038659623)
    ·
      refine ⟨111707261612537061057989435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74471507741691374038659623 111707261612537061057989435)
      ·
        refine ⟨167560892418805591586984153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111707261612537061057989435 167560892418805591586984153)
        ·
          refine ⟨125670669314104193690238115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 167560892418805591586984153 125670669314104193690238115)
          ·
            refine ⟨188506003971156290535357173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 125670669314104193690238115 188506003971156290535357173)
            ·
              refine ⟨17672437872295902237689735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 188506003971156290535357173 17672437872295902237689735)
              ·
                refine ⟨26508656808443853356534603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17672437872295902237689735 26508656808443853356534603)
                ·
                  refine ⟨39762985212665780034801905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26508656808443853356534603 39762985212665780034801905)
                  ·
                    refine ⟨29822238909499335026101429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 39762985212665780034801905 29822238909499335026101429)
                    ·
                      refine ⟨2795834897765562658697009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29822238909499335026101429 2795834897765562658697009)
                      ·
                        rfl

theorem cell23_5444869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 5, 1, 1, 2, 5].length) (baseStart_5444869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5444869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5444869 prefixEnd_5444869 := by exact prefixLift 5444869
  have htrace : WordTrace (prefixWord ++ tailWord_5444869) baseStart_5444869 baseEnd_5444869 := by
    simpa [prefixWord, tailWord_5444869, baseEnd_5444869] using wordTrace_append hprefix tailTrace_5444869
  have hstable : (prefixWord ++ tailWord_5444869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5444869).length < 2 ^ (prefixWord ++ tailWord_5444869).sum := by decide
  have hdescent : baseEnd_5444869 < baseStart_5444869 := by decide
  rcases family_descends (prefixWord ++ tailWord_5444869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5444893 : List Nat := [1, 4, 2, 3, 1, 2, 2, 1, 2, 5]
def baseStart_5444893 : Nat := 118140960795 + 5444893 * 2 ^ 59
def prefixEnd_5444893 : Nat := 4983230072969 + 3 ^ 40 * 5444893 * 2
def baseEnd_5444893 : Nat := 931949073767090188265633

theorem tailTrace_5444893 : CollatzResearch.WordTrace tailWord_5444893 prefixEnd_5444893 931949073767090188265633 := by
  unfold tailWord_5444893
  simp only [CollatzResearch.WordTrace]
  refine ⟨198591562663090049535299333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132394375108726699690199555 198591562663090049535299333)
  ·
    refine ⟨37235917999329384287868625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 198591562663090049535299333 37235917999329384287868625)
    ·
      refine ⟨27926938499497038215901469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37235917999329384287868625 27926938499497038215901469)
      ·
        refine ⟨10472601937311389330963051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27926938499497038215901469 10472601937311389330963051)
        ·
          refine ⟨15708902905967083996444577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10472601937311389330963051 15708902905967083996444577)
          ·
            refine ⟨11781677179475312997333433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15708902905967083996444577 11781677179475312997333433)
            ·
              refine ⟨8836257884606484748000075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11781677179475312997333433 8836257884606484748000075)
              ·
                refine ⟨13254386826909727122000113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8836257884606484748000075 13254386826909727122000113)
                ·
                  refine ⟨9940790120182295341500085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13254386826909727122000113 9940790120182295341500085)
                  ·
                    refine ⟨931949073767090188265633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9940790120182295341500085 931949073767090188265633)
                    ·
                      rfl

theorem cell23_5444893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 2, 1, 2, 5].length) (baseStart_5444893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5444893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5444893 prefixEnd_5444893 := by exact prefixLift 5444893
  have htrace : WordTrace (prefixWord ++ tailWord_5444893) baseStart_5444893 baseEnd_5444893 := by
    simpa [prefixWord, tailWord_5444893, baseEnd_5444893] using wordTrace_append hprefix tailTrace_5444893
  have hstable : (prefixWord ++ tailWord_5444893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5444893).length < 2 ^ (prefixWord ++ tailWord_5444893).sum := by decide
  have hdescent : baseEnd_5444893 < baseStart_5444893 := by decide
  rcases family_descends (prefixWord ++ tailWord_5444893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5444916 : List Nat := [2, 5, 1, 1, 1, 1, 1, 1, 2, 3, 5]
def baseStart_5444916 : Nat := 118140960795 + 5444916 * 2 ^ 59
def prefixEnd_5444916 : Nat := 4983230072969 + 3 ^ 40 * 5444916 * 2
def baseEnd_5444916 : Nat := 2795859031356323974809293

theorem tailTrace_5444916 : CollatzResearch.WordTrace tailWord_5444916 prefixEnd_5444916 2795859031356323974809293 := by
  unfold tailWord_5444916
  simp only [CollatzResearch.WordTrace]
  refine ⟨99296200771003362231693301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132394934361337816308924401 99296200771003362231693301)
  ·
    refine ⟨9309018822281565209221247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 99296200771003362231693301 9309018822281565209221247)
    ·
      refine ⟨13963528233422347813831871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9309018822281565209221247 13963528233422347813831871)
      ·
        refine ⟨20945292350133521720747807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13963528233422347813831871 20945292350133521720747807)
        ·
          refine ⟨31417938525200282581121711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20945292350133521720747807 31417938525200282581121711)
          ·
            refine ⟨47126907787800423871682567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31417938525200282581121711 47126907787800423871682567)
            ·
              refine ⟨70690361681700635807523851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47126907787800423871682567 70690361681700635807523851)
              ·
                refine ⟨106035542522550953711285777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70690361681700635807523851 106035542522550953711285777)
                ·
                  refine ⟨79526656891913215283464333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 106035542522550953711285777 79526656891913215283464333)
                  ·
                    refine ⟨29822496334467455731299125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 79526656891913215283464333 29822496334467455731299125)
                    ·
                      refine ⟨2795859031356323974809293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29822496334467455731299125 2795859031356323974809293)
                      ·
                        rfl

theorem cell23_5444916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 1, 2, 3, 5].length) (baseStart_5444916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5444916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5444916 prefixEnd_5444916 := by exact prefixLift 5444916
  have htrace : WordTrace (prefixWord ++ tailWord_5444916) baseStart_5444916 baseEnd_5444916 := by
    simpa [prefixWord, tailWord_5444916, baseEnd_5444916] using wordTrace_append hprefix tailTrace_5444916
  have hstable : (prefixWord ++ tailWord_5444916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5444916).length < 2 ^ (prefixWord ++ tailWord_5444916).sum := by decide
  have hdescent : baseEnd_5444916 < baseStart_5444916 := by decide
  rcases family_descends (prefixWord ++ tailWord_5444916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5444959 : List Nat := [1, 1, 2, 3, 1, 2, 1, 1, 2, 4, 5]
def baseStart_5444959 : Nat := 118140960795 + 5444959 * 2 ^ 59
def prefixEnd_5444959 : Nat := 4983230072969 + 3 ^ 40 * 5444959 * 2
def baseEnd_5444959 : Nat := 2795881111024467306571595

theorem tailTrace_5444959 : CollatzResearch.WordTrace tailWord_5444959 prefixEnd_5444959 2795881111024467306571595 := by
  unfold tailWord_5444959
  simp only [CollatzResearch.WordTrace]
  refine ⟨198593969880850942807201931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132395979920567295204801287 198593969880850942807201931)
  ·
    refine ⟨297890954821276414210802897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198593969880850942807201931 297890954821276414210802897)
    ·
      refine ⟨223418216115957310658102173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 297890954821276414210802897 223418216115957310658102173)
      ·
        refine ⟨83781831043483991496788315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 223418216115957310658102173 83781831043483991496788315)
        ·
          refine ⟨125672746565225987245182473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83781831043483991496788315 125672746565225987245182473)
          ·
            refine ⟨94254559923919490433886855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 125672746565225987245182473 94254559923919490433886855)
            ·
              refine ⟨141381839885879235650830283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 94254559923919490433886855 141381839885879235650830283)
              ·
                refine ⟨212072759828818853476245425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 141381839885879235650830283 212072759828818853476245425)
                ·
                  refine ⟨159054569871614140107184069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 212072759828818853476245425 159054569871614140107184069)
                  ·
                    refine ⟨29822731850927651270097013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 159054569871614140107184069 29822731850927651270097013)
                    ·
                      refine ⟨2795881111024467306571595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29822731850927651270097013 2795881111024467306571595)
                      ·
                        rfl

theorem cell23_5444959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 1, 2, 4, 5].length) (baseStart_5444959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5444959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5444959 prefixEnd_5444959 := by exact prefixLift 5444959
  have htrace : WordTrace (prefixWord ++ tailWord_5444959) baseStart_5444959 baseEnd_5444959 := by
    simpa [prefixWord, tailWord_5444959, baseEnd_5444959] using wordTrace_append hprefix tailTrace_5444959
  have hstable : (prefixWord ++ tailWord_5444959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5444959).length < 2 ^ (prefixWord ++ tailWord_5444959).sum := by decide
  have hdescent : baseEnd_5444959 < baseStart_5444959 := by decide
  rcases family_descends (prefixWord ++ tailWord_5444959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
