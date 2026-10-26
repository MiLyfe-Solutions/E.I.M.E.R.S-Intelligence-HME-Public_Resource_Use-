import V185TrunkScan23Chunk0656

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_3884311 : List Nat := [1, 1, 3, 4, 1, 1, 4, 2, 1, 2, 3]
def baseStart_3884311 : Nat := 118140960795 + 3884311 * 2 ^ 59
def prefixEnd_3884311 : Nat := 4983230072969 + 3 ^ 40 * 3884311 * 2
def baseEnd_3884311 : Nat := 1994518554546457349048885

theorem tailTrace_3884311 : CollatzResearch.WordTrace tailWord_3884311 prefixEnd_3884311 1994518554546457349048885 := by
  unfold tailWord_3884311
  simp only [CollatzResearch.WordTrace]
  refine ⟨141672461030812109348932787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94448307353874739565955191 141672461030812109348932787)
  ·
    refine ⟨212508691546218164023399181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141672461030812109348932787 212508691546218164023399181)
    ·
      refine ⟨79690759329831811508774693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 212508691546218164023399181 79690759329831811508774693)
      ·
        refine ⟨14942017374343464657895255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 79690759329831811508774693 14942017374343464657895255)
        ·
          refine ⟨22413026061515196986842883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14942017374343464657895255 22413026061515196986842883)
          ·
            refine ⟨33619539092272795480264325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22413026061515196986842883 33619539092272795480264325)
            ·
              refine ⟨6303663579801149152549561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33619539092272795480264325 6303663579801149152549561)
              ·
                refine ⟨4727747684850861864412171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6303663579801149152549561 4727747684850861864412171)
                ·
                  refine ⟨7091621527276292796618257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4727747684850861864412171 7091621527276292796618257)
                  ·
                    refine ⟨5318716145457219597463693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7091621527276292796618257 5318716145457219597463693)
                    ·
                      refine ⟨1994518554546457349048885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5318716145457219597463693 1994518554546457349048885)
                      ·
                        rfl

theorem cell23_3884311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 4, 2, 1, 2, 3].length) (baseStart_3884311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3884311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3884311 prefixEnd_3884311 := by exact prefixLift 3884311
  have htrace : WordTrace (prefixWord ++ tailWord_3884311) baseStart_3884311 baseEnd_3884311 := by
    simpa [prefixWord, tailWord_3884311, baseEnd_3884311] using wordTrace_append hprefix tailTrace_3884311
  have hstable : (prefixWord ++ tailWord_3884311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3884311).length < 2 ^ (prefixWord ++ tailWord_3884311).sum := by decide
  have hdescent : baseEnd_3884311 < baseStart_3884311 := by decide
  rcases family_descends (prefixWord ++ tailWord_3884311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3884314 : List Nat := [3, 1, 1, 3, 3, 1, 4, 7]
def baseStart_3884314 : Nat := 118140960795 + 3884314 * 2 ^ 59
def prefixEnd_3884314 : Nat := 4983230072969 + 3 ^ 40 * 3884314 * 2
def baseEnd_3884314 : Nat := 73871114629200771752273

theorem tailTrace_3884314 : CollatzResearch.WordTrace tailWord_3884314 prefixEnd_3884314 73871114629200771752273 := by
  unfold tailWord_3884314
  simp only [CollatzResearch.WordTrace]
  refine ⟨35418142612450310215322999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94448380299867493907527997 35418142612450310215322999)
  ·
    refine ⟨53127213918675465322984499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35418142612450310215322999 53127213918675465322984499)
    ·
      refine ⟨79690820878013197984476749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53127213918675465322984499 79690820878013197984476749)
      ·
        refine ⟨29884057829254949244178781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79690820878013197984476749 29884057829254949244178781)
        ·
          refine ⟨11206521685970605966567043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29884057829254949244178781 11206521685970605966567043)
          ·
            refine ⟨16809782528955908949850565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11206521685970605966567043 16809782528955908949850565)
            ·
              refine ⟨3151834224179232928096981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16809782528955908949850565 3151834224179232928096981)
              ·
                refine ⟨73871114629200771752273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3151834224179232928096981 73871114629200771752273)
                ·
                  rfl

theorem cell23_3884314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 4, 7].length) (baseStart_3884314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3884314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3884314 prefixEnd_3884314 := by exact prefixLift 3884314
  have htrace : WordTrace (prefixWord ++ tailWord_3884314) baseStart_3884314 baseEnd_3884314 := by
    simpa [prefixWord, tailWord_3884314, baseEnd_3884314] using wordTrace_append hprefix tailTrace_3884314
  have hstable : (prefixWord ++ tailWord_3884314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3884314).length < 2 ^ (prefixWord ++ tailWord_3884314).sum := by decide
  have hdescent : baseEnd_3884314 < baseStart_3884314 := by decide
  rcases family_descends (prefixWord ++ tailWord_3884314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3884324 : List Nat := [2, 3, 1, 3, 1, 1, 2, 1, 3, 3, 3]
def baseStart_3884324 : Nat := 118140960795 + 3884324 * 2 ^ 59
def prefixEnd_3884324 : Nat := 4983230072969 + 3 ^ 40 * 3884324 * 2
def baseEnd_3884324 : Nat := 1994525229794965798186325

theorem tailTrace_3884324 : CollatzResearch.WordTrace tailWord_3884324 prefixEnd_3884324 1994525229794965798186325 := by
  unfold tailWord_3884324
  simp only [CollatzResearch.WordTrace]
  refine ⟨70836467589882506284578013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94448623453176675046104017 70836467589882506284578013)
  ·
    refine ⟨26563675346205939856716755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70836467589882506284578013 26563675346205939856716755)
    ·
      refine ⟨39845513019308909785075133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26563675346205939856716755 39845513019308909785075133)
      ·
        refine ⟨14942067382240841169403175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39845513019308909785075133 14942067382240841169403175)
        ·
          refine ⟨22413101073361261754104763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14942067382240841169403175 22413101073361261754104763)
          ·
            refine ⟨33619651610041892631157145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22413101073361261754104763 33619651610041892631157145)
            ·
              refine ⟨25214738707531419473367859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33619651610041892631157145 25214738707531419473367859)
              ·
                refine ⟨37822108061297129210051789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25214738707531419473367859 37822108061297129210051789)
                ·
                  refine ⟨14183290522986423453769421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37822108061297129210051789 14183290522986423453769421)
                  ·
                    refine ⟨5318733946119908795163533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14183290522986423453769421 5318733946119908795163533)
                    ·
                      refine ⟨1994525229794965798186325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5318733946119908795163533 1994525229794965798186325)
                      ·
                        rfl

theorem cell23_3884324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 2, 1, 3, 3, 3].length) (baseStart_3884324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3884324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3884324 prefixEnd_3884324 := by exact prefixLift 3884324
  have htrace : WordTrace (prefixWord ++ tailWord_3884324) baseStart_3884324 baseEnd_3884324 := by
    simpa [prefixWord, tailWord_3884324, baseEnd_3884324] using wordTrace_append hprefix tailTrace_3884324
  have hstable : (prefixWord ++ tailWord_3884324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3884324).length < 2 ^ (prefixWord ++ tailWord_3884324).sum := by decide
  have hdescent : baseEnd_3884324 < baseStart_3884324 := by decide
  rcases family_descends (prefixWord ++ tailWord_3884324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3884325 : List Nat := [1, 3, 1, 2, 4, 1, 3, 3, 1, 2, 2]
def baseStart_3884325 : Nat := 118140960795 + 3884325 * 2 ^ 59
def prefixEnd_3884325 : Nat := 4983230072969 + 3 ^ 40 * 3884325 * 2
def baseEnd_3884325 : Nat := 1994525743275620294273821

theorem tailTrace_3884325 : CollatzResearch.WordTrace tailWord_3884325 prefixEnd_3884325 1994525743275620294273821 := by
  unfold tailWord_3884325
  simp only [CollatzResearch.WordTrace]
  refine ⟨141672971652761389739942429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94448647768507593159961619 141672971652761389739942429)
  ·
    refine ⟨53127364369785521152478411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 141672971652761389739942429 53127364369785521152478411)
    ·
      refine ⟨79691046554678281728717617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53127364369785521152478411 79691046554678281728717617)
      ·
        refine ⟨59768284916008711296538213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79691046554678281728717617 59768284916008711296538213)
        ·
          refine ⟨11206553421751633368100915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 59768284916008711296538213 11206553421751633368100915)
          ·
            refine ⟨16809830132627450052151373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11206553421751633368100915 16809830132627450052151373)
            ·
              refine ⟨6303686299735293769556765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16809830132627450052151373 6303686299735293769556765)
              ·
                refine ⟨2363882362400735163583787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6303686299735293769556765 2363882362400735163583787)
                ·
                  refine ⟨3545823543601102745375681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2363882362400735163583787 3545823543601102745375681)
                  ·
                    refine ⟨2659367657700827059031761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3545823543601102745375681 2659367657700827059031761)
                    ·
                      refine ⟨1994525743275620294273821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2659367657700827059031761 1994525743275620294273821)
                      ·
                        rfl

theorem cell23_3884325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 3, 3, 1, 2, 2].length) (baseStart_3884325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3884325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3884325 prefixEnd_3884325 := by exact prefixLift 3884325
  have htrace : WordTrace (prefixWord ++ tailWord_3884325) baseStart_3884325 baseEnd_3884325 := by
    simpa [prefixWord, tailWord_3884325, baseEnd_3884325] using wordTrace_append hprefix tailTrace_3884325
  have hstable : (prefixWord ++ tailWord_3884325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3884325).length < 2 ^ (prefixWord ++ tailWord_3884325).sum := by decide
  have hdescent : baseEnd_3884325 < baseStart_3884325 := by decide
  rcases family_descends (prefixWord ++ tailWord_3884325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3884341 : List Nat := [1, 3, 3, 1, 2, 2, 2, 1, 4, 1, 3]
def baseStart_3884341 : Nat := 118140960795 + 3884341 * 2 ^ 59
def prefixEnd_3884341 : Nat := 4983230072969 + 3 ^ 40 * 3884341 * 2
def baseEnd_3884341 : Nat := 1994533958966092231673747

theorem tailTrace_3884341 : CollatzResearch.WordTrace tailWord_3884341 prefixEnd_3884341 1994533958966092231673747 := by
  unfold tailWord_3884341
  simp only [CollatzResearch.WordTrace]
  refine ⟨141673555220703424472524877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94449036813802282981683251 141673555220703424472524877)
  ·
    refine ⟨53127583207763784177196829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 141673555220703424472524877 53127583207763784177196829)
    ·
      refine ⟨19922843702911419066448811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53127583207763784177196829 19922843702911419066448811)
      ·
        refine ⟨29884265554367128599673217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19922843702911419066448811 29884265554367128599673217)
        ·
          refine ⟨22413199165775346449754913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29884265554367128599673217 22413199165775346449754913)
          ·
            refine ⟨16809899374331509837316185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22413199165775346449754913 16809899374331509837316185)
            ·
              refine ⟨12607424530748632377987139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16809899374331509837316185 12607424530748632377987139)
              ·
                refine ⟨18911136796122948566980709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12607424530748632377987139 18911136796122948566980709)
                ·
                  refine ⟨3545838149273052856308883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18911136796122948566980709 3545838149273052856308883)
                  ·
                    refine ⟨5318757223909579284463325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3545838149273052856308883 5318757223909579284463325)
                    ·
                      refine ⟨1994533958966092231673747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5318757223909579284463325 1994533958966092231673747)
                      ·
                        rfl

theorem cell23_3884341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 2, 1, 4, 1, 3].length) (baseStart_3884341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3884341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3884341 prefixEnd_3884341 := by exact prefixLift 3884341
  have htrace : WordTrace (prefixWord ++ tailWord_3884341) baseStart_3884341 baseEnd_3884341 := by
    simpa [prefixWord, tailWord_3884341, baseEnd_3884341] using wordTrace_append hprefix tailTrace_3884341
  have hstable : (prefixWord ++ tailWord_3884341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3884341).length < 2 ^ (prefixWord ++ tailWord_3884341).sum := by decide
  have hdescent : baseEnd_3884341 < baseStart_3884341 := by decide
  rcases family_descends (prefixWord ++ tailWord_3884341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3884357 : List Nat := [1, 3, 1, 1, 1, 2, 1, 5, 2, 6]
def baseStart_3884357 : Nat := 118140960795 + 3884357 * 2 ^ 59
def prefixEnd_3884357 : Nat := 4983230072969 + 3 ^ 40 * 3884357 * 2
def baseEnd_3884357 : Nat := 664847391552188056357891

theorem tailTrace_3884357 : CollatzResearch.WordTrace tailWord_3884357 prefixEnd_3884357 664847391552188056357891 := by
  unfold tailWord_3884357
  simp only [CollatzResearch.WordTrace]
  refine ⟨141674138788645459205107325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94449425859096972803404883 141674138788645459205107325)
  ·
    refine ⟨53127802045742047201915247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 141674138788645459205107325 53127802045742047201915247)
    ·
      refine ⟨79691703068613070802872871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53127802045742047201915247 79691703068613070802872871)
      ·
        refine ⟨119537554602919606204309307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79691703068613070802872871 119537554602919606204309307)
        ·
          refine ⟨179306331904379409306463961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119537554602919606204309307 179306331904379409306463961)
          ·
            refine ⟨134479748928284556979847971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 179306331904379409306463961 134479748928284556979847971)
            ·
              refine ⟨201719623392426835469771957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 134479748928284556979847971 201719623392426835469771957)
              ·
                refine ⟨18911214693040015825291121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 201719623392426835469771957 18911214693040015825291121)
                ·
                  refine ⟨14183411019780011868968341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18911214693040015825291121 14183411019780011868968341)
                  ·
                    refine ⟨664847391552188056357891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14183411019780011868968341 664847391552188056357891)
                    ·
                      rfl

theorem cell23_3884357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 5, 2, 6].length) (baseStart_3884357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3884357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3884357 prefixEnd_3884357 := by exact prefixLift 3884357
  have htrace : WordTrace (prefixWord ++ tailWord_3884357) baseStart_3884357 baseEnd_3884357 := by
    simpa [prefixWord, tailWord_3884357, baseEnd_3884357] using wordTrace_append hprefix tailTrace_3884357
  have hstable : (prefixWord ++ tailWord_3884357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3884357).length < 2 ^ (prefixWord ++ tailWord_3884357).sum := by decide
  have hdescent : baseEnd_3884357 < baseStart_3884357 := by decide
  rcases family_descends (prefixWord ++ tailWord_3884357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3884384 : List Nat := [2, 1, 1, 3, 4, 1, 2, 1, 2, 1, 5]
def baseStart_3884384 : Nat := 118140960795 + 3884384 * 2 ^ 59
def prefixEnd_3884384 : Nat := 4983230072969 + 3 ^ 40 * 3884384 * 2
def baseEnd_3884384 : Nat := 1994556038634235563436049

theorem tailTrace_3884384 : CollatzResearch.WordTrace tailWord_3884384 prefixEnd_3884384 1994556038634235563436049 := by
  unfold tailWord_3884384
  simp only [CollatzResearch.WordTrace]
  refine ⟨70837561779773821408170103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94450082373031761877560137 70837561779773821408170103)
  ·
    refine ⟨106256342669660732112255155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70837561779773821408170103 106256342669660732112255155)
    ·
      refine ⟨159384514004491098168382733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106256342669660732112255155 159384514004491098168382733)
      ·
        refine ⟨59769192751684161813143525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 159384514004491098168382733 59769192751684161813143525)
        ·
          refine ⟨11206723640940780339964411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 59769192751684161813143525 11206723640940780339964411)
          ·
            refine ⟨16810085461411170509946617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11206723640940780339964411 16810085461411170509946617)
            ·
              refine ⟨12607564096058377882459963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16810085461411170509946617 12607564096058377882459963)
              ·
                refine ⟨18911346144087566823689945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12607564096058377882459963 18911346144087566823689945)
                ·
                  refine ⟨14183509608065675117767459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18911346144087566823689945 14183509608065675117767459)
                  ·
                    refine ⟨21275264412098512676651189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14183509608065675117767459 21275264412098512676651189)
                    ·
                      refine ⟨1994556038634235563436049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21275264412098512676651189 1994556038634235563436049)
                      ·
                        rfl

theorem cell23_3884384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 2, 1, 2, 1, 5].length) (baseStart_3884384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3884384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3884384 prefixEnd_3884384 := by exact prefixLift 3884384
  have htrace : WordTrace (prefixWord ++ tailWord_3884384) baseStart_3884384 baseEnd_3884384 := by
    simpa [prefixWord, tailWord_3884384, baseEnd_3884384] using wordTrace_append hprefix tailTrace_3884384
  have hstable : (prefixWord ++ tailWord_3884384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3884384).length < 2 ^ (prefixWord ++ tailWord_3884384).sum := by decide
  have hdescent : baseEnd_3884384 < baseStart_3884384 := by decide
  rcases family_descends (prefixWord ++ tailWord_3884384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3884471 : List Nat := [1, 1, 3, 1, 3, 2, 1, 3, 2, 4, 2]
def baseStart_3884471 : Nat := 118140960795 + 3884471 * 2 ^ 59
def prefixEnd_3884471 : Nat := 4983230072969 + 3 ^ 40 * 3884471 * 2
def baseEnd_3884471 : Nat := 1994600711451176723048149

theorem tailTrace_3884471 : CollatzResearch.WordTrace tailWord_3884471 prefixEnd_3884471 1994600711451176723048149 := by
  unfold tailWord_3884471
  simp only [CollatzResearch.WordTrace]
  refine ⟨141678296710232456674757267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94452197806821637783171511 141678296710232456674757267)
  ·
    refine ⟨212517445065348685012135901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141678296710232456674757267 212517445065348685012135901)
    ·
      refine ⟨79694041899505756879550963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 212517445065348685012135901 79694041899505756879550963)
      ·
        refine ⟨119541062849258635319326445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79694041899505756879550963 119541062849258635319326445)
        ·
          refine ⟨44827898568471988244747417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 119541062849258635319326445 44827898568471988244747417)
          ·
            refine ⟨33620923926353991183560563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44827898568471988244747417 33620923926353991183560563)
            ·
              refine ⟨50431385889530986775340845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33620923926353991183560563 50431385889530986775340845)
              ·
                refine ⟨18911769708574120040752817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50431385889530986775340845 18911769708574120040752817)
                ·
                  refine ⟨14183827281430590030564613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18911769708574120040752817 14183827281430590030564613)
                  ·
                    refine ⟨2659467615268235630730865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14183827281430590030564613 2659467615268235630730865)
                    ·
                      refine ⟨1994600711451176723048149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2659467615268235630730865 1994600711451176723048149)
                      ·
                        rfl

theorem cell23_3884471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 3, 2, 4, 2].length) (baseStart_3884471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3884471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3884471 prefixEnd_3884471 := by exact prefixLift 3884471
  have htrace : WordTrace (prefixWord ++ tailWord_3884471) baseStart_3884471 baseEnd_3884471 := by
    simpa [prefixWord, tailWord_3884471, baseEnd_3884471] using wordTrace_append hprefix tailTrace_3884471
  have hstable : (prefixWord ++ tailWord_3884471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3884471).length < 2 ^ (prefixWord ++ tailWord_3884471).sum := by decide
  have hdescent : baseEnd_3884471 < baseStart_3884471 := by decide
  rcases family_descends (prefixWord ++ tailWord_3884471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3884494 : List Nat := [4, 1, 1, 1, 2, 1, 3, 2, 8]
def baseStart_3884494 : Nat := 118140960795 + 3884494 * 2 ^ 59
def prefixEnd_3884494 : Nat := 4983230072969 + 3 ^ 40 * 3884494 * 2
def baseEnd_3884494 : Nat := 221623613500692237006727

theorem tailTrace_3884494 : CollatzResearch.WordTrace tailWord_3884494 prefixEnd_3884494 221623613500692237006727 := by
  unfold tailWord_3884494
  simp only [CollatzResearch.WordTrace]
  refine ⟨17709891948643641450355567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 94452757059432754401896357 17709891948643641450355567)
  ·
    refine ⟨26564837922965462175533351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17709891948643641450355567 26564837922965462175533351)
    ·
      refine ⟨39847256884448193263300027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26564837922965462175533351 39847256884448193263300027)
      ·
        refine ⟨59770885326672289894950041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39847256884448193263300027 59770885326672289894950041)
        ·
          refine ⟨44828163995004217421212531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59770885326672289894950041 44828163995004217421212531)
          ·
            refine ⟨67242245992506326131818797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44828163995004217421212531 67242245992506326131818797)
            ·
              refine ⟨25215842247189872299432049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67242245992506326131818797 25215842247189872299432049)
              ·
                refine ⟨18911881685392404224574037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25215842247189872299432049 18911881685392404224574037)
                ·
                  refine ⟨221623613500692237006727, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 18911881685392404224574037 221623613500692237006727)
                  ·
                    rfl

theorem cell23_3884494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 3, 2, 8].length) (baseStart_3884494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3884494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3884494 prefixEnd_3884494 := by exact prefixLift 3884494
  have htrace : WordTrace (prefixWord ++ tailWord_3884494) baseStart_3884494 baseEnd_3884494 := by
    simpa [prefixWord, tailWord_3884494, baseEnd_3884494] using wordTrace_append hprefix tailTrace_3884494
  have hstable : (prefixWord ++ tailWord_3884494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3884494).length < 2 ^ (prefixWord ++ tailWord_3884494).sum := by decide
  have hdescent : baseEnd_3884494 < baseStart_3884494 := by decide
  rcases family_descends (prefixWord ++ tailWord_3884494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3884528 : List Nat := [2, 1, 1, 1, 3, 6, 2, 1, 6]
def baseStart_3884528 : Nat := 118140960795 + 3884528 * 2 ^ 59
def prefixEnd_3884528 : Nat := 4983230072969 + 3 ^ 40 * 3884528 * 2
def baseEnd_3884528 : Nat := 221625553316498111115043

theorem tailTrace_3884528 : CollatzResearch.WordTrace tailWord_3884528 prefixEnd_3884528 221625553316498111115043 := by
  unfold tailWord_3884528
  simp only [CollatzResearch.WordTrace]
  refine ⟨70840187835512977704791119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94453583780683970273054825 70840187835512977704791119)
  ·
    refine ⟨106260281753269466557186679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70840187835512977704791119 106260281753269466557186679)
    ·
      refine ⟨159390422629904199835780019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106260281753269466557186679 159390422629904199835780019)
      ·
        refine ⟨239085633944856299753670029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159390422629904199835780019 239085633944856299753670029)
        ·
          refine ⟨89657112729321112407626261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 239085633944856299753670029 89657112729321112407626261)
          ·
            refine ⟨4202677159186927144107481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 89657112729321112407626261 4202677159186927144107481)
            ·
              refine ⟨3152007869390195358080611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4202677159186927144107481 3152007869390195358080611)
              ·
                refine ⟨4728011804085293037120917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3152007869390195358080611 4728011804085293037120917)
                ·
                  refine ⟨221625553316498111115043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4728011804085293037120917 221625553316498111115043)
                  ·
                    rfl

theorem cell23_3884528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 6, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 6, 2, 1, 6].length) (baseStart_3884528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3884528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3884528 prefixEnd_3884528 := by exact prefixLift 3884528
  have htrace : WordTrace (prefixWord ++ tailWord_3884528) baseStart_3884528 baseEnd_3884528 := by
    simpa [prefixWord, tailWord_3884528, baseEnd_3884528] using wordTrace_append hprefix tailTrace_3884528
  have hstable : (prefixWord ++ tailWord_3884528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3884528).length < 2 ^ (prefixWord ++ tailWord_3884528).sum := by decide
  have hdescent : baseEnd_3884528 < baseStart_3884528 := by decide
  rcases family_descends (prefixWord ++ tailWord_3884528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3884531 : List Nat := [1, 1, 1, 2, 2, 2, 2, 4, 1, 5, 2]
def baseStart_3884531 : Nat := 118140960795 + 3884531 * 2 ^ 59
def prefixEnd_3884531 : Nat := 4983230072969 + 3 ^ 40 * 3884531 * 2
def baseEnd_3884531 : Nat := 1994631520290446488297873

theorem tailTrace_3884531 : CollatzResearch.WordTrace tailWord_3884531 prefixEnd_3884531 1994631520290446488297873 := by
  unfold tailWord_3884531
  simp only [CollatzResearch.WordTrace]
  refine ⟨141680485090015086921941447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94453656726676724614627631 141680485090015086921941447)
  ·
    refine ⟨212520727635022630382912171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141680485090015086921941447 212520727635022630382912171)
    ·
      refine ⟨318781091452533945574368257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212520727635022630382912171 318781091452533945574368257)
      ·
        refine ⟨239085818589400459180776193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 318781091452533945574368257 239085818589400459180776193)
        ·
          refine ⟨179314363942050344385582145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 239085818589400459180776193 179314363942050344385582145)
          ·
            refine ⟨134485772956537758289186609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 179314363942050344385582145 134485772956537758289186609)
            ·
              refine ⟨100864329717403318716889957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 134485772956537758289186609 100864329717403318716889957)
              ·
                refine ⟨18912061822013122259416867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 100864329717403318716889957 18912061822013122259416867)
                ·
                  refine ⟨28368092733019683389125301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18912061822013122259416867 28368092733019683389125301)
                  ·
                    refine ⟨2659508693720595317730497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 28368092733019683389125301 2659508693720595317730497)
                    ·
                      refine ⟨1994631520290446488297873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2659508693720595317730497 1994631520290446488297873)
                      ·
                        rfl

theorem cell23_3884531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 4, 1, 5, 2].length) (baseStart_3884531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3884531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3884531 prefixEnd_3884531 := by exact prefixLift 3884531
  have htrace : WordTrace (prefixWord ++ tailWord_3884531) baseStart_3884531 baseEnd_3884531 := by
    simpa [prefixWord, tailWord_3884531, baseEnd_3884531] using wordTrace_append hprefix tailTrace_3884531
  have hstable : (prefixWord ++ tailWord_3884531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3884531).length < 2 ^ (prefixWord ++ tailWord_3884531).sum := by decide
  have hdescent : baseEnd_3884531 < baseStart_3884531 := by decide
  rcases family_descends (prefixWord ++ tailWord_3884531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3884541 : List Nat := [1, 4, 1, 1, 1, 5, 1, 1, 3, 5]
def baseStart_3884541 : Nat := 118140960795 + 3884541 * 2 ^ 59
def prefixEnd_3884541 : Nat := 4983230072969 + 3 ^ 40 * 3884541 * 2
def baseEnd_3884541 : Nat := 664878885032330483057609

theorem tailTrace_3884541 : CollatzResearch.WordTrace tailWord_3884541 prefixEnd_3884541 664878885032330483057609 := by
  unfold tailWord_3884541
  simp only [CollatzResearch.WordTrace]
  refine ⟨141680849819978858629805477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94453899879985905753203651 141680849819978858629805477)
  ·
    refine ⟨26565159341246035993088527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 141680849819978858629805477 26565159341246035993088527)
    ·
      refine ⟨39847739011869053989632791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26565159341246035993088527 39847739011869053989632791)
      ·
        refine ⟨59771608517803580984449187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39847739011869053989632791 59771608517803580984449187)
        ·
          refine ⟨89657412776705371476673781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59771608517803580984449187 89657412776705371476673781)
          ·
            refine ⟨8405382447816128575938167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 89657412776705371476673781 8405382447816128575938167)
            ·
              refine ⟨12608073671724192863907251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8405382447816128575938167 12608073671724192863907251)
              ·
                refine ⟨18912110507586289295860877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12608073671724192863907251 18912110507586289295860877)
                ·
                  refine ⟨7092041440344858485947829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18912110507586289295860877 7092041440344858485947829)
                  ·
                    refine ⟨664878885032330483057609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7092041440344858485947829 664878885032330483057609)
                    ·
                      rfl

theorem cell23_3884541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 1, 1, 3, 5].length) (baseStart_3884541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3884541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3884541 prefixEnd_3884541 := by exact prefixLift 3884541
  have htrace : WordTrace (prefixWord ++ tailWord_3884541) baseStart_3884541 baseEnd_3884541 := by
    simpa [prefixWord, tailWord_3884541, baseEnd_3884541] using wordTrace_append hprefix tailTrace_3884541
  have hstable : (prefixWord ++ tailWord_3884541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3884541).length < 2 ^ (prefixWord ++ tailWord_3884541).sum := by decide
  have hdescent : baseEnd_3884541 < baseStart_3884541 := by decide
  rcases family_descends (prefixWord ++ tailWord_3884541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3884542 : List Nat := [4, 2, 2, 3, 1, 1, 2, 1, 2, 2, 3]
def baseStart_3884542 : Nat := 118140960795 + 3884542 * 2 ^ 59
def prefixEnd_3884542 : Nat := 4983230072969 + 3 ^ 40 * 3884542 * 2
def baseEnd_3884542 : Nat := 1994637168577645945260323

theorem tailTrace_3884542 : CollatzResearch.WordTrace tailWord_3884542 prefixEnd_3884542 1994637168577645945260323 := by
  unfold tailWord_3884542
  simp only [CollatzResearch.WordTrace]
  refine ⟨17710110786621904475073985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 94453924195316823867061253 17710110786621904475073985)
  ·
    refine ⟨13282583089966428356305489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17710110786621904475073985 13282583089966428356305489)
    ·
      refine ⟨9961937317474821267229117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13282583089966428356305489 9961937317474821267229117)
      ·
        refine ⟨3735726494053057975210919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9961937317474821267229117 3735726494053057975210919)
        ·
          refine ⟨5603589741079586962816379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3735726494053057975210919 5603589741079586962816379)
          ·
            refine ⟨8405384611619380444224569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5603589741079586962816379 8405384611619380444224569)
            ·
              refine ⟨6304038458714535333168427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8405384611619380444224569 6304038458714535333168427)
              ·
                refine ⟨9456057688071802999752641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6304038458714535333168427 9456057688071802999752641)
                ·
                  refine ⟨7092043266053852249814481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9456057688071802999752641 7092043266053852249814481)
                  ·
                    refine ⟨5319032449540389187360861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7092043266053852249814481 5319032449540389187360861)
                    ·
                      refine ⟨1994637168577645945260323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5319032449540389187360861 1994637168577645945260323)
                      ·
                        rfl

theorem cell23_3884542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 2, 1, 2, 2, 3].length) (baseStart_3884542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3884542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3884542 prefixEnd_3884542 := by exact prefixLift 3884542
  have htrace : WordTrace (prefixWord ++ tailWord_3884542) baseStart_3884542 baseEnd_3884542 := by
    simpa [prefixWord, tailWord_3884542, baseEnd_3884542] using wordTrace_append hprefix tailTrace_3884542
  have hstable : (prefixWord ++ tailWord_3884542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3884542).length < 2 ^ (prefixWord ++ tailWord_3884542).sum := by decide
  have hdescent : baseEnd_3884542 < baseStart_3884542 := by decide
  rcases family_descends (prefixWord ++ tailWord_3884542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3884595 : List Nat := [1, 1, 1, 2, 4, 4, 1, 2, 3, 2, 2]
def baseStart_3884595 : Nat := 118140960795 + 3884595 * 2 ^ 59
def prefixEnd_3884595 : Nat := 4983230072969 + 3 ^ 40 * 3884595 * 2
def baseEnd_3884595 : Nat := 1994664383052334237897579

theorem tailTrace_3884595 : CollatzResearch.WordTrace tailWord_3884595 prefixEnd_3884595 1994664383052334237897579 := by
  unfold tailWord_3884595
  simp only [CollatzResearch.WordTrace]
  refine ⟨141682819361783225852271239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94455212907855483901514159 141682819361783225852271239)
  ·
    refine ⟨212524229042674838778406859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141682819361783225852271239 212524229042674838778406859)
    ·
      refine ⟨318786343564012258167610289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212524229042674838778406859 318786343564012258167610289)
      ·
        refine ⟨239089757673009193625707717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 318786343564012258167610289 239089757673009193625707717)
        ·
          refine ⟨44829329563689223804820197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 239089757673009193625707717 44829329563689223804820197)
          ·
            refine ⟨8405499293191729463403787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44829329563689223804820197 8405499293191729463403787)
            ·
              refine ⟨12608248939787594195105681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8405499293191729463403787 12608248939787594195105681)
              ·
                refine ⟨9456186704840695646329261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12608248939787594195105681 9456186704840695646329261)
                ·
                  refine ⟨3546070014315260867373473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9456186704840695646329261 3546070014315260867373473)
                  ·
                    refine ⟨2659552510736445650530105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3546070014315260867373473 2659552510736445650530105)
                    ·
                      refine ⟨1994664383052334237897579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2659552510736445650530105 1994664383052334237897579)
                      ·
                        rfl

theorem cell23_3884595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 1, 2, 3, 2, 2].length) (baseStart_3884595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3884595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3884595 prefixEnd_3884595 := by exact prefixLift 3884595
  have htrace : WordTrace (prefixWord ++ tailWord_3884595) baseStart_3884595 baseEnd_3884595 := by
    simpa [prefixWord, tailWord_3884595, baseEnd_3884595] using wordTrace_append hprefix tailTrace_3884595
  have hstable : (prefixWord ++ tailWord_3884595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3884595).length < 2 ^ (prefixWord ++ tailWord_3884595).sum := by decide
  have hdescent : baseEnd_3884595 < baseStart_3884595 := by decide
  rcases family_descends (prefixWord ++ tailWord_3884595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3884615 : List Nat := [1, 1, 4, 1, 5, 1, 1, 3, 1, 2, 3]
def baseStart_3884615 : Nat := 118140960795 + 3884615 * 2 ^ 59
def prefixEnd_3884615 : Nat := 4983230072969 + 3 ^ 40 * 3884615 * 2
def baseEnd_3884615 : Nat := 1994674652665424159647487

theorem tailTrace_3884615 : CollatzResearch.WordTrace tailWord_3884615 prefixEnd_3884615 1994674652665424159647487 := by
  unfold tailWord_3884615
  simp only [CollatzResearch.WordTrace]
  refine ⟨141683548821710769267999299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94455699214473846178666199 141683548821710769267999299)
  ·
    refine ⟨212525323232566153901998949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141683548821710769267999299 212525323232566153901998949)
    ·
      refine ⟨39848498106106153856624803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 212525323232566153901998949 39848498106106153856624803)
      ·
        refine ⟨59772747159159230784937205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39848498106106153856624803 59772747159159230784937205)
        ·
          refine ⟨5603695046171177886087863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 59772747159159230784937205 5603695046171177886087863)
          ·
            refine ⟨8405542569256766829131795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5603695046171177886087863 8405542569256766829131795)
            ·
              refine ⟨12608313853885150243697693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8405542569256766829131795 12608313853885150243697693)
              ·
                refine ⟨4728117695206931341386635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12608313853885150243697693 4728117695206931341386635)
                ·
                  refine ⟨7092176542810397012079953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4728117695206931341386635 7092176542810397012079953)
                  ·
                    refine ⟨5319132407107797759059965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7092176542810397012079953 5319132407107797759059965)
                    ·
                      refine ⟨1994674652665424159647487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5319132407107797759059965 1994674652665424159647487)
                      ·
                        rfl

theorem cell23_3884615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 1, 3, 1, 2, 3].length) (baseStart_3884615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3884615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3884615 prefixEnd_3884615 := by exact prefixLift 3884615
  have htrace : WordTrace (prefixWord ++ tailWord_3884615) baseStart_3884615 baseEnd_3884615 := by
    simpa [prefixWord, tailWord_3884615, baseEnd_3884615] using wordTrace_append hprefix tailTrace_3884615
  have hstable : (prefixWord ++ tailWord_3884615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3884615).length < 2 ^ (prefixWord ++ tailWord_3884615).sum := by decide
  have hdescent : baseEnd_3884615 < baseStart_3884615 := by decide
  rcases family_descends (prefixWord ++ tailWord_3884615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3884645 : List Nat := [1, 3, 1, 3, 3, 3, 1, 1, 1, 3, 3]
def baseStart_3884645 : Nat := 118140960795 + 3884645 * 2 ^ 59
def prefixEnd_3884645 : Nat := 4983230072969 + 3 ^ 40 * 3884645 * 2
def baseEnd_3884645 : Nat := 1994690057085059042272349

theorem tailTrace_3884645 : CollatzResearch.WordTrace tailWord_3884645 prefixEnd_3884645 1994690057085059042272349 := by
  unfold tailWord_3884645
  simp only [CollatzResearch.WordTrace]
  refine ⟨141684643011602084391591389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94456428674401389594394259 141684643011602084391591389)
  ·
    refine ⟨53131741129350781646846771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 141684643011602084391591389 53131741129350781646846771)
    ·
      refine ⟨79697611694026172470270157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53131741129350781646846771 79697611694026172470270157)
      ·
        refine ⟨29886604385259814676351309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79697611694026172470270157 29886604385259814676351309)
        ·
          refine ⟨11207476644472430503631741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29886604385259814676351309 11207476644472430503631741)
          ·
            refine ⟨4202803741677161438861903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11207476644472430503631741 4202803741677161438861903)
            ·
              refine ⟨6304205612515742158292855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4202803741677161438861903 6304205612515742158292855)
              ·
                refine ⟨9456308418773613237439283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6304205612515742158292855 9456308418773613237439283)
                ·
                  refine ⟨14184462628160419856158925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9456308418773613237439283 14184462628160419856158925)
                  ·
                    refine ⟨5319173485560157446059597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14184462628160419856158925 5319173485560157446059597)
                    ·
                      refine ⟨1994690057085059042272349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5319173485560157446059597 1994690057085059042272349)
                      ·
                        rfl

theorem cell23_3884645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 3, 1, 1, 1, 3, 3].length) (baseStart_3884645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3884645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3884645 prefixEnd_3884645 := by exact prefixLift 3884645
  have htrace : WordTrace (prefixWord ++ tailWord_3884645) baseStart_3884645 baseEnd_3884645 := by
    simpa [prefixWord, tailWord_3884645, baseEnd_3884645] using wordTrace_append hprefix tailTrace_3884645
  have hstable : (prefixWord ++ tailWord_3884645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3884645).length < 2 ^ (prefixWord ++ tailWord_3884645).sum := by decide
  have hdescent : baseEnd_3884645 < baseStart_3884645 := by decide
  rcases family_descends (prefixWord ++ tailWord_3884645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3884668 : List Nat := [2, 2, 2, 1, 1, 2, 1, 3, 3, 4, 2]
def baseStart_3884668 : Nat := 118140960795 + 3884668 * 2 ^ 59
def prefixEnd_3884668 : Nat := 4983230072969 + 3 ^ 40 * 3884668 * 2
def baseEnd_3884668 : Nat := 1994701867140112452284743

theorem tailTrace_3884668 : CollatzResearch.WordTrace tailWord_3884668 prefixEnd_3884668 1994701867140112452284743 := by
  unfold tailWord_3884668
  simp only [CollatzResearch.WordTrace]
  refine ⟨70842740945259379659839329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94456987927012506213119105 70842740945259379659839329)
  ·
    refine ⟨53132055708944534744879497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70842740945259379659839329 53132055708944534744879497)
    ·
      refine ⟨39849041781708401058659623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53132055708944534744879497 39849041781708401058659623)
      ·
        refine ⟨59773562672562601587989435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39849041781708401058659623 59773562672562601587989435)
        ·
          refine ⟨89660344008843902381984153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59773562672562601587989435 89660344008843902381984153)
          ·
            refine ⟨67245258006632926786488115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89660344008843902381984153 67245258006632926786488115)
            ·
              refine ⟨100867887009949390179732173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67245258006632926786488115 100867887009949390179732173)
              ·
                refine ⟨37825457628731021317399565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 100867887009949390179732173 37825457628731021317399565)
                ·
                  refine ⟨14184546610774132994024837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37825457628731021317399565 14184546610774132994024837)
                  ·
                    refine ⟨2659602489520149936379657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14184546610774132994024837 2659602489520149936379657)
                    ·
                      refine ⟨1994701867140112452284743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2659602489520149936379657 1994701867140112452284743)
                      ·
                        rfl

theorem cell23_3884668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 3, 3, 4, 2].length) (baseStart_3884668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3884668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3884668 prefixEnd_3884668 := by exact prefixLift 3884668
  have htrace : WordTrace (prefixWord ++ tailWord_3884668) baseStart_3884668 baseEnd_3884668 := by
    simpa [prefixWord, tailWord_3884668, baseEnd_3884668] using wordTrace_append hprefix tailTrace_3884668
  have hstable : (prefixWord ++ tailWord_3884668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3884668).length < 2 ^ (prefixWord ++ tailWord_3884668).sum := by decide
  have hdescent : baseEnd_3884668 < baseStart_3884668 := by decide
  rcases family_descends (prefixWord ++ tailWord_3884668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3884681 : List Nat := [1, 2, 1, 1, 4, 1, 2, 1, 4, 2, 4]
def baseStart_3884681 : Nat := 118140960795 + 3884681 * 2 ^ 59
def prefixEnd_3884681 : Nat := 4983230072969 + 3 ^ 40 * 3884681 * 2
def baseEnd_3884681 : Nat := 1994708542388620901422183

theorem tailTrace_3884681 : CollatzResearch.WordTrace tailWord_3884681 prefixEnd_3884681 1994708542388620901422183 := by
  unfold tailWord_3884681
  simp only [CollatzResearch.WordTrace]
  refine ⟨141685956039471662539901897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94457304026314441693267931 141685956039471662539901897)
  ·
    refine ⟨106264467029603746904926423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141685956039471662539901897 106264467029603746904926423)
    ·
      refine ⟨159396700544405620357389635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106264467029603746904926423 159396700544405620357389635)
      ·
        refine ⟨239095050816608430536084453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159396700544405620357389635 239095050816608430536084453)
        ·
          refine ⟨44830322028114080725515835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 239095050816608430536084453 44830322028114080725515835)
          ·
            refine ⟨67245483042171121088273753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44830322028114080725515835 67245483042171121088273753)
            ·
              refine ⟨50434112281628340816205315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67245483042171121088273753 50434112281628340816205315)
              ·
                refine ⟨75651168422442511224307973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50434112281628340816205315 75651168422442511224307973)
                ·
                  refine ⟨14184594079207970854557745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 75651168422442511224307973 14184594079207970854557745)
                  ·
                    refine ⟨10638445559405978140918309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14184594079207970854557745 10638445559405978140918309)
                    ·
                      refine ⟨1994708542388620901422183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10638445559405978140918309 1994708542388620901422183)
                      ·
                        rfl

theorem cell23_3884681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 1, 4, 2, 4].length) (baseStart_3884681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3884681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3884681 prefixEnd_3884681 := by exact prefixLift 3884681
  have htrace : WordTrace (prefixWord ++ tailWord_3884681) baseStart_3884681 baseEnd_3884681 := by
    simpa [prefixWord, tailWord_3884681, baseEnd_3884681] using wordTrace_append hprefix tailTrace_3884681
  have hstable : (prefixWord ++ tailWord_3884681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3884681).length < 2 ^ (prefixWord ++ tailWord_3884681).sum := by decide
  have hdescent : baseEnd_3884681 < baseStart_3884681 := by decide
  rcases family_descends (prefixWord ++ tailWord_3884681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3884706 : List Nat := [3, 3, 1, 4, 1, 2, 1, 2, 1, 3, 2]
def baseStart_3884706 : Nat := 118140960795 + 3884706 * 2 ^ 59
def prefixEnd_3884706 : Nat := 4983230072969 + 3 ^ 40 * 3884706 * 2
def baseEnd_3884706 : Nat := 1994721379404983303609569

theorem tailTrace_3884706 : CollatzResearch.WordTrace tailWord_3884706 prefixEnd_3884706 1994721379404983303609569 := by
  unfold tailWord_3884706
  simp only [CollatzResearch.WordTrace]
  refine ⟨35421716966095272952390493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94457911909587394539707981 35421716966095272952390493)
  ·
    refine ⟨13283143862285727357146435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35421716966095272952390493 13283143862285727357146435)
    ·
      refine ⟨19924715793428591035719653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13283143862285727357146435 19924715793428591035719653)
      ·
        refine ⟨3735884211267860819197435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19924715793428591035719653 3735884211267860819197435)
        ·
          refine ⟨5603826316901791228796153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3735884211267860819197435 5603826316901791228796153)
          ·
            refine ⟨4202869737676343421597115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5603826316901791228796153 4202869737676343421597115)
            ·
              refine ⟨6304304606514515132395673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4202869737676343421597115 6304304606514515132395673)
              ·
                refine ⟨4728228454885886349296755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6304304606514515132395673 4728228454885886349296755)
                ·
                  refine ⟨7092342682328829523945133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4728228454885886349296755 7092342682328829523945133)
                  ·
                    refine ⟨2659628505873311071479425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7092342682328829523945133 2659628505873311071479425)
                    ·
                      refine ⟨1994721379404983303609569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2659628505873311071479425 1994721379404983303609569)
                      ·
                        rfl

theorem cell23_3884706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 2, 1, 2, 1, 3, 2].length) (baseStart_3884706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3884706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3884706 prefixEnd_3884706 := by exact prefixLift 3884706
  have htrace : WordTrace (prefixWord ++ tailWord_3884706) baseStart_3884706 baseEnd_3884706 := by
    simpa [prefixWord, tailWord_3884706, baseEnd_3884706] using wordTrace_append hprefix tailTrace_3884706
  have hstable : (prefixWord ++ tailWord_3884706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3884706).length < 2 ^ (prefixWord ++ tailWord_3884706).sum := by decide
  have hdescent : baseEnd_3884706 < baseStart_3884706 := by decide
  rcases family_descends (prefixWord ++ tailWord_3884706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3884728 : List Nat := [2, 1, 2, 1, 2, 1, 1, 2, 4, 5, 2]
def baseStart_3884728 : Nat := 118140960795 + 3884728 * 2 ^ 59
def prefixEnd_3884728 : Nat := 4983230072969 + 3 ^ 40 * 3884728 * 2
def baseEnd_3884728 : Nat := 1994732675979382217534467

theorem tailTrace_3884728 : CollatzResearch.WordTrace tailWord_3884728 prefixEnd_3884728 1994732675979382217534467 := by
  unfold tailWord_3884728
  simp only [CollatzResearch.WordTrace]
  refine ⟨70843835135150694783431419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94458446846867593044575225 70843835135150694783431419)
  ·
    refine ⟨106265752702726042175147129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70843835135150694783431419 106265752702726042175147129)
    ·
      refine ⟨79699314527044531631360347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106265752702726042175147129 79699314527044531631360347)
      ·
        refine ⟨119548971790566797447040521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79699314527044531631360347 119548971790566797447040521)
        ·
          refine ⟨89661728842925098085280391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119548971790566797447040521 89661728842925098085280391)
          ·
            refine ⟨134492593264387647127920587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89661728842925098085280391 134492593264387647127920587)
            ·
              refine ⟨201738889896581470691880881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 134492593264387647127920587 201738889896581470691880881)
              ·
                refine ⟨151304167422436103018910661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 201738889896581470691880881 151304167422436103018910661)
                ·
                  refine ⟨28369531391706769316045749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 151304167422436103018910661 28369531391706769316045749)
                  ·
                    refine ⟨2659643567972509623379289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 28369531391706769316045749 2659643567972509623379289)
                    ·
                      refine ⟨1994732675979382217534467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2659643567972509623379289 1994732675979382217534467)
                      ·
                        rfl

theorem cell23_3884728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 2, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 2, 4, 5, 2].length) (baseStart_3884728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3884728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3884728 prefixEnd_3884728 := by exact prefixLift 3884728
  have htrace : WordTrace (prefixWord ++ tailWord_3884728) baseStart_3884728 baseEnd_3884728 := by
    simpa [prefixWord, tailWord_3884728, baseEnd_3884728] using wordTrace_append hprefix tailTrace_3884728
  have hstable : (prefixWord ++ tailWord_3884728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3884728).length < 2 ^ (prefixWord ++ tailWord_3884728).sum := by decide
  have hdescent : baseEnd_3884728 < baseStart_3884728 := by decide
  rcases family_descends (prefixWord ++ tailWord_3884728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3884768 : List Nat := [2, 1, 1, 3, 1, 2, 3, 1, 5, 4]
def baseStart_3884768 : Nat := 118140960795 + 3884768 * 2 ^ 59
def prefixEnd_3884768 : Nat := 4983230072969 + 3 ^ 40 * 3884768 * 2
def baseEnd_3884768 : Nat := 664917738401854020344761

theorem tailTrace_3884768 : CollatzResearch.WordTrace tailWord_3884768 prefixEnd_3884768 664917738401854020344761 := by
  unfold tailWord_3884768
  simp only [CollatzResearch.WordTrace]
  refine ⟨70844564595078238199159479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94459419460104317598879305 70844564595078238199159479)
  ·
    refine ⟨106266846892617357298739219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70844564595078238199159479 106266846892617357298739219)
    ·
      refine ⟨159400270338926035948108829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106266846892617357298739219 159400270338926035948108829)
      ·
        refine ⟨59775101377097263480540811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 159400270338926035948108829 59775101377097263480540811)
        ·
          refine ⟨89662652065645895220811217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59775101377097263480540811 89662652065645895220811217)
          ·
            refine ⟨67246989049234421415608413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89662652065645895220811217 67246989049234421415608413)
            ·
              refine ⟨25217620893462908030853155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67246989049234421415608413 25217620893462908030853155)
              ·
                refine ⟨37826431340194362046279733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25217620893462908030853155 37826431340194362046279733)
                ·
                  refine ⟨3546227938143221441838725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 37826431340194362046279733 3546227938143221441838725)
                  ·
                    refine ⟨664917738401854020344761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3546227938143221441838725 664917738401854020344761)
                    ·
                      rfl

theorem cell23_3884768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 3, 1, 5, 4].length) (baseStart_3884768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3884768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3884768 prefixEnd_3884768 := by exact prefixLift 3884768
  have htrace : WordTrace (prefixWord ++ tailWord_3884768) baseStart_3884768 baseEnd_3884768 := by
    simpa [prefixWord, tailWord_3884768, baseEnd_3884768] using wordTrace_append hprefix tailTrace_3884768
  have hstable : (prefixWord ++ tailWord_3884768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3884768).length < 2 ^ (prefixWord ++ tailWord_3884768).sum := by decide
  have hdescent : baseEnd_3884768 < baseStart_3884768 := by decide
  rcases family_descends (prefixWord ++ tailWord_3884768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3884802 : List Nat := [3, 4, 1, 1, 1, 1, 4, 1, 3, 4]
def baseStart_3884802 : Nat := 118140960795 + 3884802 * 2 ^ 59
def prefixEnd_3884802 : Nat := 4983230072969 + 3 ^ 40 * 3884802 * 2
def baseEnd_3884802 : Nat := 664923557849271642669709

theorem tailTrace_3884802 : CollatzResearch.WordTrace tailWord_3884802 prefixEnd_3884802 664923557849271642669709 := by
  unfold tailWord_3884802
  simp only [CollatzResearch.WordTrace]
  refine ⟨35422592318008325051264165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94460246181355533470037773 35422592318008325051264165)
  ·
    refine ⟨6641736059626560947112031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35422592318008325051264165 6641736059626560947112031)
    ·
      refine ⟨9962604089439841420668047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6641736059626560947112031 9962604089439841420668047)
      ·
        refine ⟨14943906134159762131002071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9962604089439841420668047 14943906134159762131002071)
        ·
          refine ⟨22415859201239643196503107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14943906134159762131002071 22415859201239643196503107)
          ·
            refine ⟨33623788801859464794754661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22415859201239643196503107 33623788801859464794754661)
            ·
              refine ⟨6304460400348649649016499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33623788801859464794754661 6304460400348649649016499)
              ·
                refine ⟨9456690600522974473524749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6304460400348649649016499 9456690600522974473524749)
                ·
                  refine ⟨3546258975196115427571781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9456690600522974473524749 3546258975196115427571781)
                  ·
                    refine ⟨664923557849271642669709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3546258975196115427571781 664923557849271642669709)
                    ·
                      rfl

theorem cell23_3884802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 4, 1, 3, 4].length) (baseStart_3884802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3884802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3884802 prefixEnd_3884802 := by exact prefixLift 3884802
  have htrace : WordTrace (prefixWord ++ tailWord_3884802) baseStart_3884802 baseEnd_3884802 := by
    simpa [prefixWord, tailWord_3884802, baseEnd_3884802] using wordTrace_append hprefix tailTrace_3884802
  have hstable : (prefixWord ++ tailWord_3884802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3884802).length < 2 ^ (prefixWord ++ tailWord_3884802).sum := by decide
  have hdescent : baseEnd_3884802 < baseStart_3884802 := by decide
  rcases family_descends (prefixWord ++ tailWord_3884802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3884835 : List Nat := [1, 1, 1, 4, 2, 1, 4, 1, 1, 5, 2]
def baseStart_3884835 : Nat := 118140960795 + 3884835 * 2 ^ 59
def prefixEnd_3884835 : Nat := 4983230072969 + 3 ^ 40 * 3884835 * 2
def baseEnd_3884835 : Nat := 1994787618409413298896475

theorem tailTrace_3884835 : CollatzResearch.WordTrace tailWord_3884835 prefixEnd_3884835 1994787618409413298896475 := by
  unfold tailWord_3884835
  simp only [CollatzResearch.WordTrace]
  refine ⟨141691572880913746841007959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94461048587275831227338639 141691572880913746841007959)
  ·
    refine ⟨212537359321370620261511939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141691572880913746841007959 212537359321370620261511939)
    ·
      refine ⟨318806038982055930392267909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212537359321370620261511939 318806038982055930392267909)
      ·
        refine ⟨59776132309135486948550233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 318806038982055930392267909 59776132309135486948550233)
        ·
          refine ⟨44832099231851615211412675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59776132309135486948550233 44832099231851615211412675)
          ·
            refine ⟨67248148847777422817119013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44832099231851615211412675 67248148847777422817119013)
            ·
              refine ⟨12609027908958266778209815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 67248148847777422817119013 12609027908958266778209815)
              ·
                refine ⟨18913541863437400167314723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12609027908958266778209815 18913541863437400167314723)
                ·
                  refine ⟨28370312795156100250972085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18913541863437400167314723 28370312795156100250972085)
                  ·
                    refine ⟨2659716824545884398528633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 28370312795156100250972085 2659716824545884398528633)
                    ·
                      refine ⟨1994787618409413298896475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2659716824545884398528633 1994787618409413298896475)
                      ·
                        rfl

theorem cell23_3884835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 4, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 4, 1, 1, 5, 2].length) (baseStart_3884835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3884835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3884835 prefixEnd_3884835 := by exact prefixLift 3884835
  have htrace : WordTrace (prefixWord ++ tailWord_3884835) baseStart_3884835 baseEnd_3884835 := by
    simpa [prefixWord, tailWord_3884835, baseEnd_3884835] using wordTrace_append hprefix tailTrace_3884835
  have hstable : (prefixWord ++ tailWord_3884835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3884835).length < 2 ^ (prefixWord ++ tailWord_3884835).sum := by decide
  have hdescent : baseEnd_3884835 < baseStart_3884835 := by decide
  rcases family_descends (prefixWord ++ tailWord_3884835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3884848 : List Nat := [2, 1, 1, 1, 2, 2, 1, 1, 7, 1, 4]
def baseStart_3884848 : Nat := 118140960795 + 3884848 * 2 ^ 59
def prefixEnd_3884848 : Nat := 4983230072969 + 3 ^ 40 * 3884848 * 2
def baseEnd_3884848 : Nat := 1994794293657921748033915

theorem tailTrace_3884848 : CollatzResearch.WordTrace tailWord_3884848 prefixEnd_3884848 1994794293657921748033915 := by
  unfold tailWord_3884848
  simp only [CollatzResearch.WordTrace]
  refine ⟨70846023514933325030615599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94461364686577766707487465 70846023514933325030615599)
  ·
    refine ⟨106269035272399987545923399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70846023514933325030615599 106269035272399987545923399)
    ·
      refine ⟨159403552908599981318885099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106269035272399987545923399 159403552908599981318885099)
      ·
        refine ⟨239105329362899971978327649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159403552908599981318885099 239105329362899971978327649)
        ·
          refine ⟨179328997022174978983745737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 239105329362899971978327649 179328997022174978983745737)
          ·
            refine ⟨134496747766631234237809303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 179328997022174978983745737 134496747766631234237809303)
            ·
              refine ⟨201745121649946851356713955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 134496747766631234237809303 201745121649946851356713955)
              ·
                refine ⟨302617682474920277035070933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 201745121649946851356713955 302617682474920277035070933)
                ·
                  refine ⟨7092601933005943993009475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 302617682474920277035070933 7092601933005943993009475)
                  ·
                    refine ⟨10638902899508915989514213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7092601933005943993009475 10638902899508915989514213)
                    ·
                      refine ⟨1994794293657921748033915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10638902899508915989514213 1994794293657921748033915)
                      ·
                        rfl

theorem cell23_3884848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 1, 7, 1, 4].length) (baseStart_3884848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3884848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3884848 prefixEnd_3884848 := by exact prefixLift 3884848
  have htrace : WordTrace (prefixWord ++ tailWord_3884848) baseStart_3884848 baseEnd_3884848 := by
    simpa [prefixWord, tailWord_3884848, baseEnd_3884848] using wordTrace_append hprefix tailTrace_3884848
  have hstable : (prefixWord ++ tailWord_3884848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3884848).length < 2 ^ (prefixWord ++ tailWord_3884848).sum := by decide
  have hdescent : baseEnd_3884848 < baseStart_3884848 := by decide
  rcases family_descends (prefixWord ++ tailWord_3884848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3884882 : List Nat := [3, 2, 2, 1, 1, 3, 3, 2, 1, 1, 4]
def baseStart_3884882 : Nat := 118140960795 + 3884882 * 2 ^ 59
def prefixEnd_3884882 : Nat := 4983230072969 + 3 ^ 40 * 3884882 * 2
def baseEnd_3884882 : Nat := 1994811752000174615008759

theorem tailTrace_3884882 : CollatzResearch.WordTrace tailWord_3884882 prefixEnd_3884882 1994811752000174615008759 := by
  unfold tailWord_3884882
  simp only [CollatzResearch.WordTrace]
  refine ⟨35423321777935868466992225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94462191407828982578645933 35423321777935868466992225)
  ·
    refine ⟨26567491333451901350244169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35423321777935868466992225 26567491333451901350244169)
    ·
      refine ⟨19925618500088926012683127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26567491333451901350244169 19925618500088926012683127)
      ·
        refine ⟨29888427750133389019024691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19925618500088926012683127 29888427750133389019024691)
        ·
          refine ⟨44832641625200083528537037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29888427750133389019024691 44832641625200083528537037)
          ·
            refine ⟨16812240609450031323201389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44832641625200083528537037 16812240609450031323201389)
            ·
              refine ⟨6304590228543761746200521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16812240609450031323201389 6304590228543761746200521)
              ·
                refine ⟨4728442671407821309650391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6304590228543761746200521 4728442671407821309650391)
                ·
                  refine ⟨7092664007111731964475587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4728442671407821309650391 7092664007111731964475587)
                  ·
                    refine ⟨10638996010667597946713381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7092664007111731964475587 10638996010667597946713381)
                    ·
                      refine ⟨1994811752000174615008759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10638996010667597946713381 1994811752000174615008759)
                      ·
                        rfl

theorem cell23_3884882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 3, 2, 1, 1, 4].length) (baseStart_3884882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3884882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3884882 prefixEnd_3884882 := by exact prefixLift 3884882
  have htrace : WordTrace (prefixWord ++ tailWord_3884882) baseStart_3884882 baseEnd_3884882 := by
    simpa [prefixWord, tailWord_3884882, baseEnd_3884882] using wordTrace_append hprefix tailTrace_3884882
  have hstable : (prefixWord ++ tailWord_3884882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3884882).length < 2 ^ (prefixWord ++ tailWord_3884882).sum := by decide
  have hdescent : baseEnd_3884882 < baseStart_3884882 := by decide
  rcases family_descends (prefixWord ++ tailWord_3884882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3884892 : List Nat := [2, 2, 4, 2, 2, 1, 1, 2, 1, 6]
def baseStart_3884892 : Nat := 118140960795 + 3884892 * 2 ^ 59
def prefixEnd_3884892 : Nat := 4983230072969 + 3 ^ 40 * 3884892 * 2
def baseEnd_3884892 : Nat := 664938962268906525294571

theorem tailTrace_3884892 : CollatzResearch.WordTrace tailWord_3884892 prefixEnd_3884892 664938962268906525294571 := by
  unfold tailWord_3884892
  simp only [CollatzResearch.WordTrace]
  refine ⟨70846825920853622787916465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94462434561138163717221953 70846825920853622787916465)
  ·
    refine ⟨53135119440640217090937349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70846825920853622787916465 53135119440640217090937349)
    ·
      refine ⟨9962834895120040704550753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 53135119440640217090937349 9962834895120040704550753)
      ·
        refine ⟨7472126171340030528413065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9962834895120040704550753 7472126171340030528413065)
        ·
          refine ⟨5604094628505022896309799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7472126171340030528413065 5604094628505022896309799)
          ·
            refine ⟨8406141942757534344464699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5604094628505022896309799 8406141942757534344464699)
            ·
              refine ⟨12609212914136301516697049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8406141942757534344464699 12609212914136301516697049)
              ·
                refine ⟨9456909685602226137522787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12609212914136301516697049 9456909685602226137522787)
                ·
                  refine ⟨14185364528403339206284181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9456909685602226137522787 14185364528403339206284181)
                  ·
                    refine ⟨664938962268906525294571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14185364528403339206284181 664938962268906525294571)
                    ·
                      rfl

theorem cell23_3884892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 1, 2, 1, 6].length) (baseStart_3884892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3884892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3884892 prefixEnd_3884892 := by exact prefixLift 3884892
  have htrace : WordTrace (prefixWord ++ tailWord_3884892) baseStart_3884892 baseEnd_3884892 := by
    simpa [prefixWord, tailWord_3884892, baseEnd_3884892] using wordTrace_append hprefix tailTrace_3884892
  have hstable : (prefixWord ++ tailWord_3884892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3884892).length < 2 ^ (prefixWord ++ tailWord_3884892).sum := by decide
  have hdescent : baseEnd_3884892 < baseStart_3884892 := by decide
  rcases family_descends (prefixWord ++ tailWord_3884892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3884895 : List Nat := [1, 1, 2, 3, 1, 5, 1, 2, 1, 2, 4]
def baseStart_3884895 : Nat := 118140960795 + 3884895 * 2 ^ 59
def prefixEnd_3884895 : Nat := 4983230072969 + 3 ^ 40 * 3884895 * 2
def baseEnd_3884895 : Nat := 1994818427248683064146199

theorem tailTrace_3884895 : CollatzResearch.WordTrace tailWord_3884895 prefixEnd_3884895 1994818427248683064146199 := by
  unfold tailWord_3884895
  simp only [CollatzResearch.WordTrace]
  refine ⟨141693761260696377088192139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94462507507130918058794759 141693761260696377088192139)
  ·
    refine ⟨212540641891044565632288209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141693761260696377088192139 212540641891044565632288209)
    ·
      refine ⟨159405481418283424224216157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 212540641891044565632288209 159405481418283424224216157)
      ·
        refine ⟨59777055531856284084081059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 159405481418283424224216157 59777055531856284084081059)
        ·
          refine ⟨89665583297784426126121589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59777055531856284084081059 89665583297784426126121589)
          ·
            refine ⟨8406148434167289949323899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 89665583297784426126121589 8406148434167289949323899)
            ·
              refine ⟨12609222651250934923985849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8406148434167289949323899 12609222651250934923985849)
              ·
                refine ⟨9456916988438201192989387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12609222651250934923985849 9456916988438201192989387)
                ·
                  refine ⟨14185375482657301789484081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9456916988438201192989387 14185375482657301789484081)
                  ·
                    refine ⟨10639031611992976342113061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14185375482657301789484081 10639031611992976342113061)
                    ·
                      refine ⟨1994818427248683064146199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10639031611992976342113061 1994818427248683064146199)
                      ·
                        rfl

theorem cell23_3884895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 1, 2, 1, 2, 4].length) (baseStart_3884895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3884895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3884895 prefixEnd_3884895 := by exact prefixLift 3884895
  have htrace : WordTrace (prefixWord ++ tailWord_3884895) baseStart_3884895 baseEnd_3884895 := by
    simpa [prefixWord, tailWord_3884895, baseEnd_3884895] using wordTrace_append hprefix tailTrace_3884895
  have hstable : (prefixWord ++ tailWord_3884895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3884895).length < 2 ^ (prefixWord ++ tailWord_3884895).sum := by decide
  have hdescent : baseEnd_3884895 < baseStart_3884895 := by decide
  rcases family_descends (prefixWord ++ tailWord_3884895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3884899 : List Nat := [1, 1, 1, 5, 4, 1, 3, 1, 1, 1, 4]
def baseStart_3884899 : Nat := 118140960795 + 3884899 * 2 ^ 59
def prefixEnd_3884899 : Nat := 4983230072969 + 3 ^ 40 * 3884899 * 2
def baseEnd_3884899 : Nat := 1994820481171301048496181

theorem tailTrace_3884899 : CollatzResearch.WordTrace tailWord_3884899 prefixEnd_3884899 1994820481171301048496181 := by
  unfold tailWord_3884899
  simp only [CollatzResearch.WordTrace]
  refine ⟨141693907152681885771337751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94462604768454590514225167 141693907152681885771337751)
  ·
    refine ⟨212540860729022828657006627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141693907152681885771337751 212540860729022828657006627)
    ·
      refine ⟨318811291093534242985509941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212540860729022828657006627 318811291093534242985509941)
      ·
        refine ⟨29888558540018835279891557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 318811291093534242985509941 29888558540018835279891557)
        ·
          refine ⟨5604104726253531614979667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29888558540018835279891557 5604104726253531614979667)
          ·
            refine ⟨8406157089380297422469501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5604104726253531614979667 8406157089380297422469501)
            ·
              refine ⟨3152308908517611533426063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8406157089380297422469501 3152308908517611533426063)
              ·
                refine ⟨4728463362776417300139095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3152308908517611533426063 4728463362776417300139095)
                ·
                  refine ⟨7092695044164625950208643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4728463362776417300139095 7092695044164625950208643)
                  ·
                    refine ⟨10639042566246938925312965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7092695044164625950208643 10639042566246938925312965)
                    ·
                      refine ⟨1994820481171301048496181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10639042566246938925312965 1994820481171301048496181)
                      ·
                        rfl

theorem cell23_3884899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 3, 1, 1, 1, 4].length) (baseStart_3884899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3884899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3884899 prefixEnd_3884899 := by exact prefixLift 3884899
  have htrace : WordTrace (prefixWord ++ tailWord_3884899) baseStart_3884899 baseEnd_3884899 := by
    simpa [prefixWord, tailWord_3884899, baseEnd_3884899] using wordTrace_append hprefix tailTrace_3884899
  have hstable : (prefixWord ++ tailWord_3884899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3884899).length < 2 ^ (prefixWord ++ tailWord_3884899).sum := by decide
  have hdescent : baseEnd_3884899 < baseStart_3884899 := by decide
  rcases family_descends (prefixWord ++ tailWord_3884899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3884929 : List Nat := [1, 2, 4, 4, 1, 1, 2, 1, 1, 2, 4]
def baseStart_3884929 : Nat := 118140960795 + 3884929 * 2 ^ 59
def prefixEnd_3884929 : Nat := 4983230072969 + 3 ^ 40 * 3884929 * 2
def baseEnd_3884929 : Nat := 1994835885590935931121043

theorem tailTrace_3884929 : CollatzResearch.WordTrace tailWord_3884929 prefixEnd_3884929 1994835885590935931121043 := by
  unfold tailWord_3884929
  simp only [CollatzResearch.WordTrace]
  refine ⟨141695001342573200894929841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94463334228382133929953227 141695001342573200894929841)
  ·
    refine ⟨106271251006929900671197381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141695001342573200894929841 106271251006929900671197381)
    ·
      refine ⟨19925859563799356375849509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 106271251006929900671197381 19925859563799356375849509)
      ·
        refine ⟨3736098668212379320471783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19925859563799356375849509 3736098668212379320471783)
        ·
          refine ⟨5604148002318568980707675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3736098668212379320471783 5604148002318568980707675)
          ·
            refine ⟨8406222003477853471061513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5604148002318568980707675 8406222003477853471061513)
            ·
              refine ⟨6304666502608390103296135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8406222003477853471061513 6304666502608390103296135)
              ·
                refine ⟨9456999753912585154944203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6304666502608390103296135 9456999753912585154944203)
                ·
                  refine ⟨14185499630868877732416305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9456999753912585154944203 14185499630868877732416305)
                  ·
                    refine ⟨10639124723151658299312229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14185499630868877732416305 10639124723151658299312229)
                    ·
                      refine ⟨1994835885590935931121043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10639124723151658299312229 1994835885590935931121043)
                      ·
                        rfl

theorem cell23_3884929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 2, 1, 1, 2, 4].length) (baseStart_3884929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3884929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3884929 prefixEnd_3884929 := by exact prefixLift 3884929
  have htrace : WordTrace (prefixWord ++ tailWord_3884929) baseStart_3884929 baseEnd_3884929 := by
    simpa [prefixWord, tailWord_3884929, baseEnd_3884929] using wordTrace_append hprefix tailTrace_3884929
  have hstable : (prefixWord ++ tailWord_3884929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3884929).length < 2 ^ (prefixWord ++ tailWord_3884929).sum := by decide
  have hdescent : baseEnd_3884929 < baseStart_3884929 := by decide
  rcases family_descends (prefixWord ++ tailWord_3884929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3884950 : List Nat := [5, 3, 1, 1, 2, 2, 2, 1, 1, 1, 4]
def baseStart_3884950 : Nat := 118140960795 + 3884950 * 2 ^ 59
def prefixEnd_3884950 : Nat := 4983230072969 + 3 ^ 40 * 3884950 * 2
def baseEnd_3884950 : Nat := 1994846668684680348958447

theorem tailTrace_3884950 : CollatzResearch.WordTrace tailWord_3884950 prefixEnd_3884950 1994846668684680348958447 := by
  unfold tailWord_3884950
  simp only [CollatzResearch.WordTrace]
  refine ⟨8855985454718570092590269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 94463844850331414320962869 8855985454718570092590269)
  ·
    refine ⟨3320994545519463784721351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8855985454718570092590269 3320994545519463784721351)
    ·
      refine ⟨4981491818279195677082027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3320994545519463784721351 4981491818279195677082027)
      ·
        refine ⟨7472237727418793515623041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4981491818279195677082027 7472237727418793515623041)
        ·
          refine ⟨5604178295564095136717281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7472237727418793515623041 5604178295564095136717281)
          ·
            refine ⟨4203133721673071352537961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5604178295564095136717281 4203133721673071352537961)
            ·
              refine ⟨3152350291254803514403471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4203133721673071352537961 3152350291254803514403471)
              ·
                refine ⟨4728525436882205271605207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3152350291254803514403471 4728525436882205271605207)
                ·
                  refine ⟨7092788155323307907407811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4728525436882205271605207 7092788155323307907407811)
                  ·
                    refine ⟨10639182232984961861111717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7092788155323307907407811 10639182232984961861111717)
                    ·
                      refine ⟨1994846668684680348958447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10639182232984961861111717 1994846668684680348958447)
                      ·
                        rfl

theorem cell23_3884950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 2, 2, 1, 1, 1, 4].length) (baseStart_3884950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3884950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3884950 prefixEnd_3884950 := by exact prefixLift 3884950
  have htrace : WordTrace (prefixWord ++ tailWord_3884950) baseStart_3884950 baseEnd_3884950 := by
    simpa [prefixWord, tailWord_3884950, baseEnd_3884950] using wordTrace_append hprefix tailTrace_3884950
  have hstable : (prefixWord ++ tailWord_3884950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3884950).length < 2 ^ (prefixWord ++ tailWord_3884950).sum := by decide
  have hdescent : baseEnd_3884950 < baseStart_3884950 := by decide
  rcases family_descends (prefixWord ++ tailWord_3884950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3884985 : List Nat := [1, 2, 1, 4, 2, 1, 1, 3, 2, 2, 4]
def baseStart_3884985 : Nat := 118140960795 + 3884985 * 2 ^ 59
def prefixEnd_3884985 : Nat := 4983230072969 + 3 ^ 40 * 3884985 * 2
def baseEnd_3884985 : Nat := 1994864640507587712020785

theorem tailTrace_3884985 : CollatzResearch.WordTrace tailWord_3884985 prefixEnd_3884985 1994864640507587712020785 := by
  unfold tailWord_3884985
  simp only [CollatzResearch.WordTrace]
  refine ⟨141697043830370322458968409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94464695886913548305978939 141697043830370322458968409)
  ·
    refine ⟨106272782872777741844226307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141697043830370322458968409 106272782872777741844226307)
    ·
      refine ⟨159409174309166612766339461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106272782872777741844226307 159409174309166612766339461)
      ·
        refine ⟨29889220182968739893688649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 159409174309166612766339461 29889220182968739893688649)
        ·
          refine ⟨22416915137226554920266487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29889220182968739893688649 22416915137226554920266487)
          ·
            refine ⟨33625372705839832380399731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22416915137226554920266487 33625372705839832380399731)
            ·
              refine ⟨50438059058759748570599597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33625372705839832380399731 50438059058759748570599597)
              ·
                refine ⟨18914272147034905713974849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50438059058759748570599597 18914272147034905713974849)
                ·
                  refine ⟨14185704110276179285481137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18914272147034905713974849 14185704110276179285481137)
                  ·
                    refine ⟨10639278082707134464110853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14185704110276179285481137 10639278082707134464110853)
                    ·
                      refine ⟨1994864640507587712020785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10639278082707134464110853 1994864640507587712020785)
                      ·
                        rfl

theorem cell23_3884985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 3, 2, 2, 4].length) (baseStart_3884985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3884985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3884985 prefixEnd_3884985 := by exact prefixLift 3884985
  have htrace : WordTrace (prefixWord ++ tailWord_3884985) baseStart_3884985 baseEnd_3884985 := by
    simpa [prefixWord, tailWord_3884985, baseEnd_3884985] using wordTrace_append hprefix tailTrace_3884985
  have hstable : (prefixWord ++ tailWord_3884985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3884985).length < 2 ^ (prefixWord ++ tailWord_3884985).sum := by decide
  have hdescent : baseEnd_3884985 < baseStart_3884985 := by decide
  rcases family_descends (prefixWord ++ tailWord_3884985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3884989 : List Nat := [1, 4, 1, 2, 3, 1, 3, 1, 1, 4, 2]
def baseStart_3884989 : Nat := 118140960795 + 3884989 * 2 ^ 59
def prefixEnd_3884989 : Nat := 4983230072969 + 3 ^ 40 * 3884989 * 2
def baseEnd_3884989 : Nat := 1994866694430205696370767

theorem tailTrace_3884989 : CollatzResearch.WordTrace tailWord_3884989 prefixEnd_3884989 1994866694430205696370767 := by
  unfold tailWord_3884989
  simp only [CollatzResearch.WordTrace]
  refine ⟨141697189722355831142114021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94464793148237220761409347 141697189722355831142114021)
  ·
    refine ⟨26568223072941718339146379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 141697189722355831142114021 26568223072941718339146379)
    ·
      refine ⟨39852334609412577508719569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26568223072941718339146379 39852334609412577508719569)
      ·
        refine ⟨29889250957059433131539677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39852334609412577508719569 29889250957059433131539677)
        ·
          refine ⟨11208469108897287424327379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29889250957059433131539677 11208469108897287424327379)
          ·
            refine ⟨16812703663345931136491069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11208469108897287424327379 16812703663345931136491069)
            ·
              refine ⟨6304763873754724176184151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16812703663345931136491069 6304763873754724176184151)
              ·
                refine ⟨9457145810632086264276227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6304763873754724176184151 9457145810632086264276227)
                ·
                  refine ⟨14185718715948129396414341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9457145810632086264276227 14185718715948129396414341)
                  ·
                    refine ⟨2659822259240274261827689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14185718715948129396414341 2659822259240274261827689)
                    ·
                      refine ⟨1994866694430205696370767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2659822259240274261827689 1994866694430205696370767)
                      ·
                        rfl

theorem cell23_3884989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 3, 1, 1, 4, 2].length) (baseStart_3884989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3884989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3884989 prefixEnd_3884989 := by exact prefixLift 3884989
  have htrace : WordTrace (prefixWord ++ tailWord_3884989) baseStart_3884989 baseEnd_3884989 := by
    simpa [prefixWord, tailWord_3884989, baseEnd_3884989] using wordTrace_append hprefix tailTrace_3884989
  have hstable : (prefixWord ++ tailWord_3884989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3884989).length < 2 ^ (prefixWord ++ tailWord_3884989).sum := by decide
  have hdescent : baseEnd_3884989 < baseStart_3884989 := by decide
  rcases family_descends (prefixWord ++ tailWord_3884989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3885025 : List Nat := [1, 2, 3, 1, 2, 1, 3, 1, 4, 5]
def baseStart_3885025 : Nat := 118140960795 + 3885025 * 2 ^ 59
def prefixEnd_3885025 : Nat := 4983230072969 + 3 ^ 40 * 3885025 * 2
def baseEnd_3885025 : Nat := 664961726577922518506867

theorem tailTrace_3885025 : CollatzResearch.WordTrace tailWord_3885025 prefixEnd_3885025 664961726577922518506867 := by
  unfold tailWord_3885025
  simp only [CollatzResearch.WordTrace]
  refine ⟨141698502750225409290424529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94465668500150272860283019 141698502750225409290424529)
  ·
    refine ⟨106273877062669056967818397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141698502750225409290424529 106273877062669056967818397)
    ·
      refine ⟨39852703898500896362931899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106273877062669056967818397 39852703898500896362931899)
      ·
        refine ⟨59779055847751344544397849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39852703898500896362931899 59779055847751344544397849)
        ·
          refine ⟨44834291885813508408298387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59779055847751344544397849 44834291885813508408298387)
          ·
            refine ⟨67251437828720262612447581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44834291885813508408298387 67251437828720262612447581)
            ·
              refine ⟨25219289185770098479667843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67251437828720262612447581 25219289185770098479667843)
              ·
                refine ⟨37828933778655147719501765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25219289185770098479667843 37828933778655147719501765)
                ·
                  refine ⟨7092925083497840197406581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37828933778655147719501765 7092925083497840197406581)
                  ·
                    refine ⟨664961726577922518506867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7092925083497840197406581 664961726577922518506867)
                    ·
                      rfl

theorem cell23_3885025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 3, 1, 4, 5].length) (baseStart_3885025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3885025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3885025 prefixEnd_3885025 := by exact prefixLift 3885025
  have htrace : WordTrace (prefixWord ++ tailWord_3885025) baseStart_3885025 baseEnd_3885025 := by
    simpa [prefixWord, tailWord_3885025, baseEnd_3885025] using wordTrace_append hprefix tailTrace_3885025
  have hstable : (prefixWord ++ tailWord_3885025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3885025).length < 2 ^ (prefixWord ++ tailWord_3885025).sum := by decide
  have hdescent : baseEnd_3885025 < baseStart_3885025 := by decide
  rcases family_descends (prefixWord ++ tailWord_3885025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3885032 : List Nat := [2, 1, 4, 1, 1, 1, 1, 3, 2, 5, 2]
def baseStart_3885032 : Nat := 118140960795 + 3885032 * 2 ^ 59
def prefixEnd_3885032 : Nat := 4983230072969 + 3 ^ 40 * 3885032 * 2
def baseEnd_3885032 : Nat := 1994888774098349028133069

theorem tailTrace_3885032 : CollatzResearch.WordTrace tailWord_3885032 prefixEnd_3885032 1994888774098349028133069 := by
  unfold tailWord_3885032
  simp only [CollatzResearch.WordTrace]
  refine ⟨70849379030600024742964675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94465838707466699657286233 70849379030600024742964675)
  ·
    refine ⟨106274068545900037114447013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70849379030600024742964675 106274068545900037114447013)
    ·
      refine ⟨19926387852356256958958815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 106274068545900037114447013 19926387852356256958958815)
      ·
        refine ⟨29889581778534385438438223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19926387852356256958958815 29889581778534385438438223)
        ·
          refine ⟨44834372667801578157657335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29889581778534385438438223 44834372667801578157657335)
          ·
            refine ⟨67251559001702367236486003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44834372667801578157657335 67251559001702367236486003)
            ·
              refine ⟨100877338502553550854729005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67251559001702367236486003 100877338502553550854729005)
              ·
                refine ⟨37829001938457581570523377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 100877338502553550854729005 37829001938457581570523377)
                ·
                  refine ⟨28371751453843186177892533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37829001938457581570523377 28371751453843186177892533)
                  ·
                    refine ⟨2659851698797798704177425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 28371751453843186177892533 2659851698797798704177425)
                    ·
                      refine ⟨1994888774098349028133069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2659851698797798704177425 1994888774098349028133069)
                      ·
                        rfl

theorem cell23_3885032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 3, 2, 5, 2].length) (baseStart_3885032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3885032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3885032 prefixEnd_3885032 := by exact prefixLift 3885032
  have htrace : WordTrace (prefixWord ++ tailWord_3885032) baseStart_3885032 baseEnd_3885032 := by
    simpa [prefixWord, tailWord_3885032, baseEnd_3885032] using wordTrace_append hprefix tailTrace_3885032
  have hstable : (prefixWord ++ tailWord_3885032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3885032).length < 2 ^ (prefixWord ++ tailWord_3885032).sum := by decide
  have hdescent : baseEnd_3885032 < baseStart_3885032 := by decide
  rcases family_descends (prefixWord ++ tailWord_3885032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3885125 : List Nat := [1, 3, 1, 1, 1, 3, 1, 1, 2, 4, 5]
def baseStart_3885125 : Nat := 118140960795 + 3885125 * 2 ^ 59
def prefixEnd_3885125 : Nat := 4983230072969 + 3 ^ 40 * 3885125 * 2
def baseEnd_3885125 : Nat := 1994936527799217164270141

theorem tailTrace_3885125 : CollatzResearch.WordTrace tailWord_3885125 prefixEnd_3885125 1994936527799217164270141 := by
  unfold tailWord_3885125
  simp only [CollatzResearch.WordTrace]
  refine ⟨141702150049863126369064829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94468100033242084246043219 141702150049863126369064829)
  ·
    refine ⟨53138306268698672388399311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 141702150049863126369064829 53138306268698672388399311)
    ·
      refine ⟨79707459403048008582598967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53138306268698672388399311 79707459403048008582598967)
      ·
        refine ⟨119561189104572012873898451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79707459403048008582598967 119561189104572012873898451)
        ·
          refine ⟨179341783656858019310847677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119561189104572012873898451 179341783656858019310847677)
          ·
            refine ⟨67253168871321757241567879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 179341783656858019310847677 67253168871321757241567879)
            ·
              refine ⟨100879753306982635862351819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67253168871321757241567879 100879753306982635862351819)
              ·
                refine ⟨151319629960473953793527729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100879753306982635862351819 151319629960473953793527729)
                ·
                  refine ⟨113489722470355465345145797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 151319629960473953793527729 113489722470355465345145797)
                  ·
                    refine ⟨21279322963191649752214837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 113489722470355465345145797 21279322963191649752214837)
                    ·
                      refine ⟨1994936527799217164270141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21279322963191649752214837 1994936527799217164270141)
                      ·
                        rfl

theorem cell23_3885125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 1, 2, 4, 5].length) (baseStart_3885125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3885125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3885125 prefixEnd_3885125 := by exact prefixLift 3885125
  have htrace : WordTrace (prefixWord ++ tailWord_3885125) baseStart_3885125 baseEnd_3885125 := by
    simpa [prefixWord, tailWord_3885125, baseEnd_3885125] using wordTrace_append hprefix tailTrace_3885125
  have hstable : (prefixWord ++ tailWord_3885125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3885125).length < 2 ^ (prefixWord ++ tailWord_3885125).sum := by decide
  have hdescent : baseEnd_3885125 < baseStart_3885125 := by decide
  rcases family_descends (prefixWord ++ tailWord_3885125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3885146 : List Nat := [3, 1, 1, 2, 1, 1, 3, 6, 1, 1, 3]
def baseStart_3885146 : Nat := 118140960795 + 3885146 * 2 ^ 59
def prefixEnd_3885146 : Nat := 4983230072969 + 3 ^ 40 * 3885146 * 2
def baseEnd_3885146 : Nat := 1994947310892961582107545

theorem tailTrace_3885146 : CollatzResearch.WordTrace tailWord_3885146 prefixEnd_3885146 1994947310892961582107545 := by
  unfold tailWord_3885146
  simp only [CollatzResearch.WordTrace]
  refine ⟨35425728995696761738894823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94468610655191364637052861 35425728995696761738894823)
  ·
    refine ⟨53138593493545142608342235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35425728995696761738894823 53138593493545142608342235)
    ·
      refine ⟨79707890240317713912513353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53138593493545142608342235 79707890240317713912513353)
      ·
        refine ⟨59780917680238285434385015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79707890240317713912513353 59780917680238285434385015)
        ·
          refine ⟨89671376520357428151577523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59780917680238285434385015 89671376520357428151577523)
          ·
            refine ⟨134507064780536142227366285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89671376520357428151577523 134507064780536142227366285)
            ·
              refine ⟨50440149292701053335262357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 134507064780536142227366285 50440149292701053335262357)
              ·
                refine ⟨2364381998095361875090423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 50440149292701053335262357 2364381998095361875090423)
                ·
                  refine ⟨3546572997143042812635635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2364381998095361875090423 3546572997143042812635635)
                  ·
                    refine ⟨5319859495714564218953453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3546572997143042812635635 5319859495714564218953453)
                    ·
                      refine ⟨1994947310892961582107545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5319859495714564218953453 1994947310892961582107545)
                      ·
                        rfl

theorem cell23_3885146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 6, 1, 1, 3].length) (baseStart_3885146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3885146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3885146 prefixEnd_3885146 := by exact prefixLift 3885146
  have htrace : WordTrace (prefixWord ++ tailWord_3885146) baseStart_3885146 baseEnd_3885146 := by
    simpa [prefixWord, tailWord_3885146, baseEnd_3885146] using wordTrace_append hprefix tailTrace_3885146
  have hstable : (prefixWord ++ tailWord_3885146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3885146).length < 2 ^ (prefixWord ++ tailWord_3885146).sum := by decide
  have hdescent : baseEnd_3885146 < baseStart_3885146 := by decide
  rcases family_descends (prefixWord ++ tailWord_3885146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3885169 : List Nat := [1, 2, 2, 2, 1, 1, 6, 2, 1, 1, 4]
def baseStart_3885169 : Nat := 118140960795 + 3885169 * 2 ^ 59
def prefixEnd_3885169 : Nat := 4983230072969 + 3 ^ 40 * 3885169 * 2
def baseEnd_3885169 : Nat := 1994959120948014992119939

theorem tailTrace_3885169 : CollatzResearch.WordTrace tailWord_3885169 prefixEnd_3885169 1994959120948014992119939 := by
  unfold tailWord_3885169
  simp only [CollatzResearch.WordTrace]
  refine ⟨141703754861703721883666561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94469169907802481255777707 141703754861703721883666561)
  ·
    refine ⟨106277816146277791412749921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141703754861703721883666561 106277816146277791412749921)
    ·
      refine ⟨79708362109708343559562441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106277816146277791412749921 79708362109708343559562441)
      ·
        refine ⟨59781271582281257669671831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79708362109708343559562441 59781271582281257669671831)
        ·
          refine ⟨89671907373421886504507747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59781271582281257669671831 89671907373421886504507747)
          ·
            refine ⟨134507861060132829756761621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89671907373421886504507747 134507861060132829756761621)
            ·
              refine ⟨6305055987193726394848201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 134507861060132829756761621 6305055987193726394848201)
              ·
                refine ⟨4728791990395294796136151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6305055987193726394848201 4728791990395294796136151)
                ·
                  refine ⟨7093187985592942194204227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4728791990395294796136151 7093187985592942194204227)
                  ·
                    refine ⟨10639781978389413291306341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7093187985592942194204227 10639781978389413291306341)
                    ·
                      refine ⟨1994959120948014992119939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10639781978389413291306341 1994959120948014992119939)
                      ·
                        rfl

theorem cell23_3885169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 6, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 6, 2, 1, 1, 4].length) (baseStart_3885169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3885169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3885169 prefixEnd_3885169 := by exact prefixLift 3885169
  have htrace : WordTrace (prefixWord ++ tailWord_3885169) baseStart_3885169 baseEnd_3885169 := by
    simpa [prefixWord, tailWord_3885169, baseEnd_3885169] using wordTrace_append hprefix tailTrace_3885169
  have hstable : (prefixWord ++ tailWord_3885169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3885169).length < 2 ^ (prefixWord ++ tailWord_3885169).sum := by decide
  have hdescent : baseEnd_3885169 < baseStart_3885169 := by decide
  rcases family_descends (prefixWord ++ tailWord_3885169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3885189 : List Nat := [1, 3, 1, 1, 5, 2, 2, 1, 1, 1, 5]
def baseStart_3885189 : Nat := 118140960795 + 3885189 * 2 ^ 59
def prefixEnd_3885189 : Nat := 4983230072969 + 3 ^ 40 * 3885189 * 2
def baseEnd_3885189 : Nat := 1994969390561104913869847

theorem tailTrace_3885189 : CollatzResearch.WordTrace tailWord_3885189 prefixEnd_3885189 1994969390561104913869847 := by
  unfold tailWord_3885189
  simp only [CollatzResearch.WordTrace]
  refine ⟨141704484321631265299394621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94469656214420843532929747 141704484321631265299394621)
  ·
    refine ⟨53139181620611724487272983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 141704484321631265299394621 53139181620611724487272983)
    ·
      refine ⟨79708772430917586730909475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53139181620611724487272983 79708772430917586730909475)
      ·
        refine ⟨119563158646376380096364213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79708772430917586730909475 119563158646376380096364213)
        ·
          refine ⟨11209046123097785634034145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 119563158646376380096364213 11209046123097785634034145)
          ·
            refine ⟨8406784592323339225525609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11209046123097785634034145 8406784592323339225525609)
            ·
              refine ⟨6305088444242504419144207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8406784592323339225525609 6305088444242504419144207)
              ·
                refine ⟨9457632666363756628716311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6305088444242504419144207 9457632666363756628716311)
                ·
                  refine ⟨14186448999545634943074467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9457632666363756628716311 14186448999545634943074467)
                  ·
                    refine ⟨21279673499318452414611701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14186448999545634943074467 21279673499318452414611701)
                    ·
                      refine ⟨1994969390561104913869847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21279673499318452414611701 1994969390561104913869847)
                      ·
                        rfl

theorem cell23_3885189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 2, 1, 1, 1, 5].length) (baseStart_3885189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3885189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3885189 prefixEnd_3885189 := by exact prefixLift 3885189
  have htrace : WordTrace (prefixWord ++ tailWord_3885189) baseStart_3885189 baseEnd_3885189 := by
    simpa [prefixWord, tailWord_3885189, baseEnd_3885189] using wordTrace_append hprefix tailTrace_3885189
  have hstable : (prefixWord ++ tailWord_3885189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3885189).length < 2 ^ (prefixWord ++ tailWord_3885189).sum := by decide
  have hdescent : baseEnd_3885189 < baseStart_3885189 := by decide
  rcases family_descends (prefixWord ++ tailWord_3885189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3885192 : List Nat := [2, 1, 3, 4, 1, 1, 11]
def baseStart_3885192 : Nat := 118140960795 + 3885192 * 2 ^ 59
def prefixEnd_3885192 : Nat := 4983230072969 + 3 ^ 40 * 3885192 * 2
def baseEnd_3885192 : Nat := 24629270753124301260893

theorem tailTrace_3885192 : CollatzResearch.WordTrace tailWord_3885192 prefixEnd_3885192 24629270753124301260893 := by
  unfold tailWord_3885192
  simp only [CollatzResearch.WordTrace]
  refine ⟨70852296870310198405876915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94469729160413597874502553 70852296870310198405876915)
  ·
    refine ⟨106278445305465297608815373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70852296870310198405876915 106278445305465297608815373)
    ·
      refine ⟨39854416989549486603305765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106278445305465297608815373 39854416989549486603305765)
      ·
        refine ⟨7472703185540528738119831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39854416989549486603305765 7472703185540528738119831)
        ·
          refine ⟨11209054778310793107179747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7472703185540528738119831 11209054778310793107179747)
          ·
            refine ⟨16813582167466189660769621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11209054778310793107179747 16813582167466189660769621)
            ·
              refine ⟨24629270753124301260893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 16813582167466189660769621 24629270753124301260893)
              ·
                rfl

theorem cell23_3885192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 11].length) (baseStart_3885192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3885192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3885192 prefixEnd_3885192 := by exact prefixLift 3885192
  have htrace : WordTrace (prefixWord ++ tailWord_3885192) baseStart_3885192 baseEnd_3885192 := by
    simpa [prefixWord, tailWord_3885192, baseEnd_3885192] using wordTrace_append hprefix tailTrace_3885192
  have hstable : (prefixWord ++ tailWord_3885192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3885192).length < 2 ^ (prefixWord ++ tailWord_3885192).sum := by decide
  have hdescent : baseEnd_3885192 < baseStart_3885192 := by decide
  rcases family_descends (prefixWord ++ tailWord_3885192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3885212 : List Nat := [2, 2, 3, 2, 1, 1, 1, 1, 2, 2, 6]
def baseStart_3885212 : Nat := 118140960795 + 3885212 * 2 ^ 59
def prefixEnd_3885212 : Nat := 4983230072969 + 3 ^ 40 * 3885212 * 2
def baseEnd_3885212 : Nat := 1994981200616158323882241

theorem tailTrace_3885212 : CollatzResearch.WordTrace tailWord_3885212 prefixEnd_3885212 1994981200616158323882241 := by
  unfold tailWord_3885212
  simp only [CollatzResearch.WordTrace]
  refine ⟨70852661600273970113740945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94470215467031960151654593 70852661600273970113740945)
  ·
    refine ⟨53139496200205477585305709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70852661600273970113740945 53139496200205477585305709)
    ·
      refine ⟨19927311075077054094489641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53139496200205477585305709 19927311075077054094489641)
      ·
        refine ⟨14945483306307790570867231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19927311075077054094489641 14945483306307790570867231)
        ·
          refine ⟨22418224959461685856300847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14945483306307790570867231 22418224959461685856300847)
          ·
            refine ⟨33627337439192528784451271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22418224959461685856300847 33627337439192528784451271)
            ·
              refine ⟨50441006158788793176676907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33627337439192528784451271 50441006158788793176676907)
              ·
                refine ⟨75661509238183189765015361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50441006158788793176676907 75661509238183189765015361)
                ·
                  refine ⟨56746131928637392323761521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 75661509238183189765015361 56746131928637392323761521)
                  ·
                    refine ⟨42559598946478044242821141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 56746131928637392323761521 42559598946478044242821141)
                    ·
                      refine ⟨1994981200616158323882241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 42559598946478044242821141 1994981200616158323882241)
                      ·
                        rfl

theorem cell23_3885212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 1, 2, 2, 6].length) (baseStart_3885212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3885212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3885212 prefixEnd_3885212 := by exact prefixLift 3885212
  have htrace : WordTrace (prefixWord ++ tailWord_3885212) baseStart_3885212 baseEnd_3885212 := by
    simpa [prefixWord, tailWord_3885212, baseEnd_3885212] using wordTrace_append hprefix tailTrace_3885212
  have hstable : (prefixWord ++ tailWord_3885212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3885212).length < 2 ^ (prefixWord ++ tailWord_3885212).sum := by decide
  have hdescent : baseEnd_3885212 < baseStart_3885212 := by decide
  rcases family_descends (prefixWord ++ tailWord_3885212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3885213 : List Nat := [1, 4, 2, 1, 1, 5, 2, 1, 2, 4]
def baseStart_3885213 : Nat := 118140960795 + 3885213 * 2 ^ 59
def prefixEnd_3885213 : Nat := 4983230072969 + 3 ^ 40 * 3885213 * 2
def baseEnd_3885213 : Nat := 664993904698937606656579

theorem tailTrace_3885213 : CollatzResearch.WordTrace tailWord_3885213 prefixEnd_3885213 664993904698937606656579 := by
  unfold tailWord_3885213
  simp only [CollatzResearch.WordTrace]
  refine ⟨141705359673544317398268293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94470239782362878265512195 141705359673544317398268293)
  ·
    refine ⟨26569754938789559512175305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 141705359673544317398268293 26569754938789559512175305)
    ·
      refine ⟨19927316204092169634131479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26569754938789559512175305 19927316204092169634131479)
      ·
        refine ⟨29890974306138254451197219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19927316204092169634131479 29890974306138254451197219)
        ·
          refine ⟨44836461459207381676795829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29890974306138254451197219 44836461459207381676795829)
          ·
            refine ⟨4203418261800692032199609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 44836461459207381676795829 4203418261800692032199609)
            ·
              refine ⟨3152563696350519024149707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4203418261800692032199609 3152563696350519024149707)
              ·
                refine ⟨4728845544525778536224561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3152563696350519024149707 4728845544525778536224561)
                ·
                  refine ⟨3546634158394333902168421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4728845544525778536224561 3546634158394333902168421)
                  ·
                    refine ⟨664993904698937606656579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3546634158394333902168421 664993904698937606656579)
                    ·
                      rfl

theorem cell23_3885213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 5, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 5, 2, 1, 2, 4].length) (baseStart_3885213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3885213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3885213 prefixEnd_3885213 := by exact prefixLift 3885213
  have htrace : WordTrace (prefixWord ++ tailWord_3885213) baseStart_3885213 baseEnd_3885213 := by
    simpa [prefixWord, tailWord_3885213, baseEnd_3885213] using wordTrace_append hprefix tailTrace_3885213
  have hstable : (prefixWord ++ tailWord_3885213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3885213).length < 2 ^ (prefixWord ++ tailWord_3885213).sum := by decide
  have hdescent : baseEnd_3885213 < baseStart_3885213 := by decide
  rcases family_descends (prefixWord ++ tailWord_3885213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3885259 : List Nat := [1, 1, 1, 1, 3, 2, 3, 2, 3, 4, 2]
def baseStart_3885259 : Nat := 118140960795 + 3885259 * 2 ^ 59
def prefixEnd_3885259 : Nat := 4983230072969 + 3 ^ 40 * 3885259 * 2
def baseEnd_3885259 : Nat := 1995005334206919639994525

theorem tailTrace_3885259 : CollatzResearch.WordTrace tailWord_3885259 prefixEnd_3885259 1995005334206919639994525 := by
  unfold tailWord_3885259
  simp only [CollatzResearch.WordTrace]
  refine ⟨141707037431377667254442831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94471358287585111502961887 141707037431377667254442831)
  ·
    refine ⟨212560556147066500881664247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141707037431377667254442831 212560556147066500881664247)
    ·
      refine ⟨318840834220599751322496371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212560556147066500881664247 318840834220599751322496371)
      ·
        refine ⟨478261251330899626983744557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 318840834220599751322496371 478261251330899626983744557)
        ·
          refine ⟨179347969249087360118904209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 478261251330899626983744557 179347969249087360118904209)
          ·
            refine ⟨134510976936815520089178157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 179347969249087360118904209 134510976936815520089178157)
            ·
              refine ⟨50441616351305820033441809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 134510976936815520089178157 50441616351305820033441809)
              ·
                refine ⟨37831212263479365025081357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50441616351305820033441809 37831212263479365025081357)
                ·
                  refine ⟨14186704598804761884405509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37831212263479365025081357 14186704598804761884405509)
                  ·
                    refine ⟨2660007112275892853326033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14186704598804761884405509 2660007112275892853326033)
                    ·
                      refine ⟨1995005334206919639994525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2660007112275892853326033 1995005334206919639994525)
                      ·
                        rfl

theorem cell23_3885259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 2, 3, 4, 2].length) (baseStart_3885259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3885259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3885259 prefixEnd_3885259 := by exact prefixLift 3885259
  have htrace : WordTrace (prefixWord ++ tailWord_3885259) baseStart_3885259 baseEnd_3885259 := by
    simpa [prefixWord, tailWord_3885259, baseEnd_3885259] using wordTrace_append hprefix tailTrace_3885259
  have hstable : (prefixWord ++ tailWord_3885259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3885259).length < 2 ^ (prefixWord ++ tailWord_3885259).sum := by decide
  have hdescent : baseEnd_3885259 < baseStart_3885259 := by decide
  rcases family_descends (prefixWord ++ tailWord_3885259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3885270 : List Nat := [5, 2, 1, 2, 1, 1, 2, 3, 2, 1, 3]
def baseStart_3885270 : Nat := 118140960795 + 3885270 * 2 ^ 59
def prefixEnd_3885270 : Nat := 4983230072969 + 3 ^ 40 * 3885270 * 2
def baseEnd_3885270 : Nat := 1995010982494119096956975

theorem tailTrace_3885270 : CollatzResearch.WordTrace tailWord_3885270 prefixEnd_3885270 1995010982494119096956975 := by
  unfold tailWord_3885270
  simp only [CollatzResearch.WordTrace]
  refine ⟨8856714914646113508318329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 94471625756225210755395509 8856714914646113508318329)
  ·
    refine ⟨6642536185984585131238747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8856714914646113508318329 6642536185984585131238747)
    ·
      refine ⟨9963804278976877696858121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6642536185984585131238747 9963804278976877696858121)
      ·
        refine ⟨7472853209232658272643591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9963804278976877696858121 7472853209232658272643591)
        ·
          refine ⟨11209279813848987408965387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7472853209232658272643591 11209279813848987408965387)
          ·
            refine ⟨16813919720773481113448081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11209279813848987408965387 16813919720773481113448081)
            ·
              refine ⟨12610439790580110835086061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16813919720773481113448081 12610439790580110835086061)
              ·
                refine ⟨4728914921467541563157273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12610439790580110835086061 4728914921467541563157273)
                ·
                  refine ⟨3546686191100656172367955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4728914921467541563157273 3546686191100656172367955)
                  ·
                    refine ⟨5320029286650984258551933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3546686191100656172367955 5320029286650984258551933)
                    ·
                      refine ⟨1995010982494119096956975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5320029286650984258551933 1995010982494119096956975)
                      ·
                        rfl

theorem cell23_3885270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 2, 3, 2, 1, 3].length) (baseStart_3885270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3885270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3885270 prefixEnd_3885270 := by exact prefixLift 3885270
  have htrace : WordTrace (prefixWord ++ tailWord_3885270) baseStart_3885270 baseEnd_3885270 := by
    simpa [prefixWord, tailWord_3885270, baseEnd_3885270] using wordTrace_append hprefix tailTrace_3885270
  have hstable : (prefixWord ++ tailWord_3885270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3885270).length < 2 ^ (prefixWord ++ tailWord_3885270).sum := by decide
  have hdescent : baseEnd_3885270 < baseStart_3885270 := by decide
  rcases family_descends (prefixWord ++ tailWord_3885270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3885316 : List Nat := [2, 3, 2, 2, 3, 1, 2, 1, 7]
def baseStart_3885316 : Nat := 118140960795 + 3885316 * 2 ^ 59
def prefixEnd_3885316 : Nat := 4983230072969 + 3 ^ 40 * 3885316 * 2
def baseEnd_3885316 : Nat := 221670511400469546331307

theorem tailTrace_3885316 : CollatzResearch.WordTrace tailWord_3885316 prefixEnd_3885316 221670511400469546331307 := by
  unfold tailWord_3885316
  simp only [CollatzResearch.WordTrace]
  refine ⟨70854558196085582994633901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94472744261447443992845201 70854558196085582994633901)
  ·
    refine ⟨26570459323532093622987713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70854558196085582994633901 26570459323532093622987713)
    ·
      refine ⟨19927844492649070217240785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26570459323532093622987713 19927844492649070217240785)
      ·
        refine ⟨14945883369486802662930589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19927844492649070217240785 14945883369486802662930589)
        ·
          refine ⟨5604706263557550998598971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14945883369486802662930589 5604706263557550998598971)
          ·
            refine ⟨8407059395336326497898457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5604706263557550998598971 8407059395336326497898457)
            ·
              refine ⟨6305294546502244873423843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8407059395336326497898457 6305294546502244873423843)
              ·
                refine ⟨9457941819753367310135765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6305294546502244873423843 9457941819753367310135765)
                ·
                  refine ⟨221670511400469546331307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9457941819753367310135765 221670511400469546331307)
                  ·
                    rfl

theorem cell23_3885316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 2, 1, 7].length) (baseStart_3885316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3885316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3885316 prefixEnd_3885316 := by exact prefixLift 3885316
  have htrace : WordTrace (prefixWord ++ tailWord_3885316) baseStart_3885316 baseEnd_3885316 := by
    simpa [prefixWord, tailWord_3885316, baseEnd_3885316] using wordTrace_append hprefix tailTrace_3885316
  have hstable : (prefixWord ++ tailWord_3885316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3885316).length < 2 ^ (prefixWord ++ tailWord_3885316).sum := by decide
  have hdescent : baseEnd_3885316 < baseStart_3885316 := by decide
  rcases family_descends (prefixWord ++ tailWord_3885316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3885359 : List Nat := [1, 1, 2, 1, 2, 1, 4, 2, 5, 4]
def baseStart_3885359 : Nat := 118140960795 + 3885359 * 2 ^ 59
def prefixEnd_3885359 : Nat := 4983230072969 + 3 ^ 40 * 3885359 * 2
def baseEnd_3885359 : Nat := 665018894090789749581355

theorem tailTrace_3885359 : CollatzResearch.WordTrace tailWord_3885359 prefixEnd_3885359 665018894090789749581355 := by
  unfold tailWord_3885359
  simp only [CollatzResearch.WordTrace]
  refine ⟨141710684731015384333083131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94473789820676922888722087 141710684731015384333083131)
  ·
    refine ⟨212566027096523076499624697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141710684731015384333083131 212566027096523076499624697)
    ·
      refine ⟨159424520322392307374718523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 212566027096523076499624697 159424520322392307374718523)
      ·
        refine ⟨239136780483588461062077785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159424520322392307374718523 239136780483588461062077785)
        ·
          refine ⟨179352585362691345796558339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 239136780483588461062077785 179352585362691345796558339)
          ·
            refine ⟨269028878044037018694837509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 179352585362691345796558339 269028878044037018694837509)
            ·
              refine ⟨50442914633256941005282033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 269028878044037018694837509 50442914633256941005282033)
              ·
                refine ⟨37832185974942705753961525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50442914633256941005282033 37832185974942705753961525)
                ·
                  refine ⟨3546767435150878664433893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 37832185974942705753961525 3546767435150878664433893)
                  ·
                    refine ⟨665018894090789749581355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3546767435150878664433893 665018894090789749581355)
                    ·
                      rfl

theorem cell23_3885359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 2, 5, 4].length) (baseStart_3885359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3885359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3885359 prefixEnd_3885359 := by exact prefixLift 3885359
  have htrace : WordTrace (prefixWord ++ tailWord_3885359) baseStart_3885359 baseEnd_3885359 := by
    simpa [prefixWord, tailWord_3885359, baseEnd_3885359] using wordTrace_append hprefix tailTrace_3885359
  have hstable : (prefixWord ++ tailWord_3885359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3885359).length < 2 ^ (prefixWord ++ tailWord_3885359).sum := by decide
  have hdescent : baseEnd_3885359 < baseStart_3885359 := by decide
  rcases family_descends (prefixWord ++ tailWord_3885359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3885460 : List Nat := [2, 4, 2, 1, 3, 1, 1, 1, 1, 5, 2]
def baseStart_3885460 : Nat := 118140960795 + 3885460 * 2 ^ 59
def prefixEnd_3885460 : Nat := 4983230072969 + 3 ^ 40 * 3885460 * 2
def baseEnd_3885460 : Nat := 1995108543818473353581101

theorem tailTrace_3885460 : CollatzResearch.WordTrace tailWord_3885460 prefixEnd_3885460 1995108543818473353581101 := by
  unfold tailWord_3885460
  simp only [CollatzResearch.WordTrace]
  refine ⟨70857184251824739291254917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94476245669099652388339889 70857184251824739291254917)
  ·
    refine ⟨13285722047217138617110297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 70857184251824739291254917 13285722047217138617110297)
    ·
      refine ⟨9964291535412853962832723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13285722047217138617110297 9964291535412853962832723)
      ·
        refine ⟨14946437303119280944249085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9964291535412853962832723 14946437303119280944249085)
        ·
          refine ⟨5604913988669730354093407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14946437303119280944249085 5604913988669730354093407)
          ·
            refine ⟨8407370983004595531140111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5604913988669730354093407 8407370983004595531140111)
            ·
              refine ⟨12611056474506893296710167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8407370983004595531140111 12611056474506893296710167)
              ·
                refine ⟨18916584711760339945065251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12611056474506893296710167 18916584711760339945065251)
                ·
                  refine ⟨28374877067640509917597877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18916584711760339945065251 28374877067640509917597877)
                  ·
                    refine ⟨2660144725091297804774801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 28374877067640509917597877 2660144725091297804774801)
                    ·
                      refine ⟨1995108543818473353581101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2660144725091297804774801 1995108543818473353581101)
                      ·
                        rfl

theorem cell23_3885460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 1, 1, 1, 5, 2].length) (baseStart_3885460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3885460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3885460 prefixEnd_3885460 := by exact prefixLift 3885460
  have htrace : WordTrace (prefixWord ++ tailWord_3885460) baseStart_3885460 baseEnd_3885460 := by
    simpa [prefixWord, tailWord_3885460, baseEnd_3885460] using wordTrace_append hprefix tailTrace_3885460
  have hstable : (prefixWord ++ tailWord_3885460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3885460).length < 2 ^ (prefixWord ++ tailWord_3885460).sum := by decide
  have hdescent : baseEnd_3885460 < baseStart_3885460 := by decide
  rcases family_descends (prefixWord ++ tailWord_3885460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3885466 : List Nat := [3, 1, 1, 4, 1, 2, 2, 2, 1, 6]
def baseStart_3885466 : Nat := 118140960795 + 3885466 * 2 ^ 59
def prefixEnd_3885466 : Nat := 4983230072969 + 3 ^ 40 * 3885466 * 2
def baseEnd_3885466 : Nat := 665037208234133443368691

theorem tailTrace_3885466 : CollatzResearch.WordTrace tailWord_3885466 prefixEnd_3885466 665037208234133443368691 := by
  unfold tailWord_3885466
  simp only [CollatzResearch.WordTrace]
  refine ⟨35428646835406935401807063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94476391561085161071485501 35428646835406935401807063)
  ·
    refine ⟨53142970253110403102710595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35428646835406935401807063 53142970253110403102710595)
    ·
      refine ⟨79714455379665604654065893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53142970253110403102710595 79714455379665604654065893)
      ·
        refine ⟨14946460383687300872637355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 79714455379665604654065893 14946460383687300872637355)
        ·
          refine ⟨22419690575530951308956033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14946460383687300872637355 22419690575530951308956033)
          ·
            refine ⟨16814767931648213481717025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22419690575530951308956033 16814767931648213481717025)
            ·
              refine ⟨12611075948736160111287769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16814767931648213481717025 12611075948736160111287769)
              ·
                refine ⟨9458306961552120083465827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12611075948736160111287769 9458306961552120083465827)
                ·
                  refine ⟨14187460442328180125198741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9458306961552120083465827 14187460442328180125198741)
                  ·
                    refine ⟨665037208234133443368691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14187460442328180125198741 665037208234133443368691)
                    ·
                      rfl

theorem cell23_3885466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 2, 2, 1, 6].length) (baseStart_3885466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3885466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3885466 prefixEnd_3885466 := by exact prefixLift 3885466
  have htrace : WordTrace (prefixWord ++ tailWord_3885466) baseStart_3885466 baseEnd_3885466 := by
    simpa [prefixWord, tailWord_3885466, baseEnd_3885466] using wordTrace_append hprefix tailTrace_3885466
  have hstable : (prefixWord ++ tailWord_3885466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3885466).length < 2 ^ (prefixWord ++ tailWord_3885466).sum := by decide
  have hdescent : baseEnd_3885466 < baseStart_3885466 := by decide
  rcases family_descends (prefixWord ++ tailWord_3885466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3885470 : List Nat := [4, 3, 1, 2, 1, 2, 1, 3, 1, 5]
def baseStart_3885470 : Nat := 118140960795 + 3885470 * 2 ^ 59
def prefixEnd_3885470 : Nat := 4983230072969 + 3 ^ 40 * 3885470 * 2
def baseEnd_3885470 : Nat := 665037892875006104818685

theorem tailTrace_3885470 : CollatzResearch.WordTrace tailWord_3885470 prefixEnd_3885470 665037892875006104818685 := by
  unfold tailWord_3885470
  simp only [CollatzResearch.WordTrace]
  refine ⟨17714341654201656286296733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 94476488822408833526915909 17714341654201656286296733)
  ·
    refine ⟨6642878120325621107361275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17714341654201656286296733 6642878120325621107361275)
    ·
      refine ⟨9964317180488431661041913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6642878120325621107361275 9964317180488431661041913)
      ·
        refine ⟨7473237885366323745781435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9964317180488431661041913 7473237885366323745781435)
        ·
          refine ⟨11209856828049485618672153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7473237885366323745781435 11209856828049485618672153)
          ·
            refine ⟨8407392621037114214004115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11209856828049485618672153 8407392621037114214004115)
            ·
              refine ⟨12611088931555671321006173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8407392621037114214004115 12611088931555671321006173)
              ·
                refine ⟨4729158349333376745377315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12611088931555671321006173 4729158349333376745377315)
                ·
                  refine ⟨7093737524000065118065973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4729158349333376745377315 7093737524000065118065973)
                  ·
                    refine ⟨665037892875006104818685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7093737524000065118065973 665037892875006104818685)
                    ·
                      rfl

theorem cell23_3885470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 1, 3, 1, 5].length) (baseStart_3885470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3885470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3885470 prefixEnd_3885470 := by exact prefixLift 3885470
  have htrace : WordTrace (prefixWord ++ tailWord_3885470) baseStart_3885470 baseEnd_3885470 := by
    simpa [prefixWord, tailWord_3885470, baseEnd_3885470] using wordTrace_append hprefix tailTrace_3885470
  have hstable : (prefixWord ++ tailWord_3885470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3885470).length < 2 ^ (prefixWord ++ tailWord_3885470).sum := by decide
  have hdescent : baseEnd_3885470 < baseStart_3885470 := by decide
  rcases family_descends (prefixWord ++ tailWord_3885470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3885490 : List Nat := [3, 2, 1, 1, 1, 1, 6, 1, 3, 2, 2]
def baseStart_3885490 : Nat := 118140960795 + 3885490 * 2 ^ 59
def prefixEnd_3885490 : Nat := 4983230072969 + 3 ^ 40 * 3885490 * 2
def baseEnd_3885490 : Nat := 1995123948238108236205963

theorem tailTrace_3885490 : CollatzResearch.WordTrace tailWord_3885490 prefixEnd_3885490 1995123948238108236205963 := by
  unfold tailWord_3885490
  simp only [CollatzResearch.WordTrace]
  refine ⟨35428865673385198426525481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94476975129027195804067949 35428865673385198426525481)
  ·
    refine ⟨26571649255038898819894111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35428865673385198426525481 26571649255038898819894111)
    ·
      refine ⟨39857473882558348229841167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26571649255038898819894111 39857473882558348229841167)
      ·
        refine ⟨59786210823837522344761751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39857473882558348229841167 59786210823837522344761751)
        ·
          refine ⟨89679316235756283517142627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59786210823837522344761751 89679316235756283517142627)
          ·
            refine ⟨134518974353634425275713941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89679316235756283517142627 134518974353634425275713941)
            ·
              refine ⟨6305576922826613684799091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 134518974353634425275713941 6305576922826613684799091)
              ·
                refine ⟨9458365384239920527198637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6305576922826613684799091 9458365384239920527198637)
                ·
                  refine ⟨3546887019089970197699489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9458365384239920527198637 3546887019089970197699489)
                  ·
                    refine ⟨2660165264317477648274617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3546887019089970197699489 2660165264317477648274617)
                    ·
                      refine ⟨1995123948238108236205963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2660165264317477648274617 1995123948238108236205963)
                      ·
                        rfl

theorem cell23_3885490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 6, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 6, 1, 3, 2, 2].length) (baseStart_3885490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3885490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3885490 prefixEnd_3885490 := by exact prefixLift 3885490
  have htrace : WordTrace (prefixWord ++ tailWord_3885490) baseStart_3885490 baseEnd_3885490 := by
    simpa [prefixWord, tailWord_3885490, baseEnd_3885490] using wordTrace_append hprefix tailTrace_3885490
  have hstable : (prefixWord ++ tailWord_3885490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3885490).length < 2 ^ (prefixWord ++ tailWord_3885490).sum := by decide
  have hdescent : baseEnd_3885490 < baseStart_3885490 := by decide
  rcases family_descends (prefixWord ++ tailWord_3885490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3885493 : List Nat := [1, 3, 3, 2, 3, 1, 1, 2, 1, 1, 5]
def baseStart_3885493 : Nat := 118140960795 + 3885493 * 2 ^ 59
def prefixEnd_3885493 : Nat := 4983230072969 + 3 ^ 40 * 3885493 * 2
def baseEnd_3885493 : Nat := 1995125488680071724468449

theorem tailTrace_3885493 : CollatzResearch.WordTrace tailWord_3885493 prefixEnd_3885493 1995125488680071724468449 := by
  unfold tailWord_3885493
  simp only [CollatzResearch.WordTrace]
  refine ⟨141715572112529925218461133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94477048075019950145640755 141715572112529925218461133)
  ·
    refine ⟨53143339542198721956922925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 141715572112529925218461133 53143339542198721956922925)
    ·
      refine ⟨19928752328324520733846097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53143339542198721956922925 19928752328324520733846097)
      ·
        refine ⟨14946564246243390550384573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19928752328324520733846097 14946564246243390550384573)
        ·
          refine ⟨5604961592341271456394215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14946564246243390550384573 5604961592341271456394215)
          ·
            refine ⟨8407442388511907184591323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5604961592341271456394215 8407442388511907184591323)
            ·
              refine ⟨12611163582767860776886985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8407442388511907184591323 12611163582767860776886985)
              ·
                refine ⟨9458372687075895582665239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12611163582767860776886985 9458372687075895582665239)
                ·
                  refine ⟨14187559030613843373997859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9458372687075895582665239 14187559030613843373997859)
                  ·
                    refine ⟨21281338545920765060996789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14187559030613843373997859 21281338545920765060996789)
                    ·
                      refine ⟨1995125488680071724468449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21281338545920765060996789 1995125488680071724468449)
                      ·
                        rfl

theorem cell23_3885493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 1, 2, 1, 1, 5].length) (baseStart_3885493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3885493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3885493 prefixEnd_3885493 := by exact prefixLift 3885493
  have htrace : WordTrace (prefixWord ++ tailWord_3885493) baseStart_3885493 baseEnd_3885493 := by
    simpa [prefixWord, tailWord_3885493, baseEnd_3885493] using wordTrace_append hprefix tailTrace_3885493
  have hstable : (prefixWord ++ tailWord_3885493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3885493).length < 2 ^ (prefixWord ++ tailWord_3885493).sum := by decide
  have hdescent : baseEnd_3885493 < baseStart_3885493 := by decide
  rcases family_descends (prefixWord ++ tailWord_3885493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3885524 : List Nat := [2, 4, 1, 2, 2, 1, 3, 3, 1, 2, 2]
def baseStart_3885524 : Nat := 118140960795 + 3885524 * 2 ^ 59
def prefixEnd_3885524 : Nat := 4983230072969 + 3 ^ 40 * 3885524 * 2
def baseEnd_3885524 : Nat := 1995141406580361103180807

theorem tailTrace_3885524 : CollatzResearch.WordTrace tailWord_3885524 prefixEnd_3885524 1995141406580361103180807 := by
  unfold tailWord_3885524
  simp only [CollatzResearch.WordTrace]
  refine ⟨70858351387708808756419813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94477801850278411675226417 70858351387708808756419813)
  ·
    refine ⟨13285940885195401641828715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 70858351387708808756419813 13285940885195401641828715)
    ·
      refine ⟨19928911327793102462743073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13285940885195401641828715 19928911327793102462743073)
      ·
        refine ⟨14946683495844826847057305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19928911327793102462743073 14946683495844826847057305)
        ·
          refine ⟨11210012621883620135292979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14946683495844826847057305 11210012621883620135292979)
          ·
            refine ⟨16815018932825430202939469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11210012621883620135292979 16815018932825430202939469)
            ·
              refine ⟨6305632099809536326102301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16815018932825430202939469 6305632099809536326102301)
              ·
                refine ⟨2364612037428576122288363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6305632099809536326102301 2364612037428576122288363)
                ·
                  refine ⟨3546918056142864183432545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2364612037428576122288363 3546918056142864183432545)
                  ·
                    refine ⟨2660188542107148137574409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3546918056142864183432545 2660188542107148137574409)
                    ·
                      refine ⟨1995141406580361103180807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2660188542107148137574409 1995141406580361103180807)
                      ·
                        rfl

theorem cell23_3885524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 3, 3, 1, 2, 2].length) (baseStart_3885524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3885524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3885524 prefixEnd_3885524 := by exact prefixLift 3885524
  have htrace : WordTrace (prefixWord ++ tailWord_3885524) baseStart_3885524 baseEnd_3885524 := by
    simpa [prefixWord, tailWord_3885524, baseEnd_3885524] using wordTrace_append hprefix tailTrace_3885524
  have hstable : (prefixWord ++ tailWord_3885524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3885524).length < 2 ^ (prefixWord ++ tailWord_3885524).sum := by decide
  have hdescent : baseEnd_3885524 < baseStart_3885524 := by decide
  rcases family_descends (prefixWord ++ tailWord_3885524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3885541 : List Nat := [1, 3, 1, 5, 2, 1, 3, 2, 1, 2, 2]
def baseStart_3885541 : Nat := 118140960795 + 3885541 * 2 ^ 59
def prefixEnd_3885541 : Nat := 4983230072969 + 3 ^ 40 * 3885541 * 2
def baseEnd_3885541 : Nat := 1995150135751487536668229

theorem tailTrace_3885541 : CollatzResearch.WordTrace tailWord_3885541 prefixEnd_3885541 1995150135751487536668229 := by
  unfold tailWord_3885541
  simp only [CollatzResearch.WordTrace]
  refine ⟨141717322816356029416208477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94478215210904019610805651 141717322816356029416208477)
  ·
    refine ⟨53143996056133511031078179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 141717322816356029416208477 53143996056133511031078179)
    ·
      refine ⟨79715994084200266546617269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53143996056133511031078179 79715994084200266546617269)
      ·
        refine ⟨7473374445393774988745369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 79715994084200266546617269 7473374445393774988745369)
        ·
          refine ⟨5605030834045331241559027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7473374445393774988745369 5605030834045331241559027)
          ·
            refine ⟨8407546251067996862338541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5605030834045331241559027 8407546251067996862338541)
            ·
              refine ⟨3152829844150498823376953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8407546251067996862338541 3152829844150498823376953)
              ·
                refine ⟨2364622383112874117532715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3152829844150498823376953 2364622383112874117532715)
                ·
                  refine ⟨3546933574669311176299073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2364622383112874117532715 3546933574669311176299073)
                  ·
                    refine ⟨2660200181001983382224305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3546933574669311176299073 2660200181001983382224305)
                    ·
                      refine ⟨1995150135751487536668229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2660200181001983382224305 1995150135751487536668229)
                      ·
                        rfl

theorem cell23_3885541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 3, 2, 1, 2, 2].length) (baseStart_3885541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3885541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3885541 prefixEnd_3885541 := by exact prefixLift 3885541
  have htrace : WordTrace (prefixWord ++ tailWord_3885541) baseStart_3885541 baseEnd_3885541 := by
    simpa [prefixWord, tailWord_3885541, baseEnd_3885541] using wordTrace_append hprefix tailTrace_3885541
  have hstable : (prefixWord ++ tailWord_3885541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3885541).length < 2 ^ (prefixWord ++ tailWord_3885541).sum := by decide
  have hdescent : baseEnd_3885541 < baseStart_3885541 := by decide
  rcases family_descends (prefixWord ++ tailWord_3885541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3885574 : List Nat := [6, 2, 1, 1, 1, 2, 1, 2, 1, 3, 3]
def baseStart_3885574 : Nat := 118140960795 + 3885574 * 2 ^ 59
def prefixEnd_3885574 : Nat := 4983230072969 + 3 ^ 40 * 3885574 * 2
def baseEnd_3885574 : Nat := 1995167080613085907555577

theorem tailTrace_3885574 : CollatzResearch.WordTrace tailWord_3885574 prefixEnd_3885574 1995167080613085907555577 := by
  unfold tailWord_3885574
  simp only [CollatzResearch.WordTrace]
  refine ⟨4428703950788639876629993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 94479017616824317368106517 4428703950788639876629993)
  ·
    refine ⟨3321527963091479907472495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4428703950788639876629993 3321527963091479907472495)
    ·
      refine ⟨4982291944637219861208743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3321527963091479907472495 4982291944637219861208743)
      ·
        refine ⟨7473437916955829791813115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4982291944637219861208743 7473437916955829791813115)
        ·
          refine ⟨11210156875433744687719673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7473437916955829791813115 11210156875433744687719673)
          ·
            refine ⟨8407617656575308515789755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11210156875433744687719673 8407617656575308515789755)
            ·
              refine ⟨12611426484862962773684633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8407617656575308515789755 12611426484862962773684633)
              ·
                refine ⟨9458569863647222080263475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12611426484862962773684633 9458569863647222080263475)
                ·
                  refine ⟨14187854795470833120395213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9458569863647222080263475 14187854795470833120395213)
                  ·
                    refine ⟨5320445548301562420148205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14187854795470833120395213 5320445548301562420148205)
                    ·
                      refine ⟨1995167080613085907555577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5320445548301562420148205 1995167080613085907555577)
                      ·
                        rfl

theorem cell23_3885574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 1, 2, 1, 3, 3].length) (baseStart_3885574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3885574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3885574 prefixEnd_3885574 := by exact prefixLift 3885574
  have htrace : WordTrace (prefixWord ++ tailWord_3885574) baseStart_3885574 baseEnd_3885574 := by
    simpa [prefixWord, tailWord_3885574, baseEnd_3885574] using wordTrace_append hprefix tailTrace_3885574
  have hstable : (prefixWord ++ tailWord_3885574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3885574).length < 2 ^ (prefixWord ++ tailWord_3885574).sum := by decide
  have hdescent : baseEnd_3885574 < baseStart_3885574 := by decide
  rcases family_descends (prefixWord ++ tailWord_3885574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3885576 : List Nat := [2, 1, 3, 2, 1, 1, 1, 2, 4, 2, 4]
def baseStart_3885576 : Nat := 118140960795 + 3885576 * 2 ^ 59
def prefixEnd_3885576 : Nat := 4983230072969 + 3 ^ 40 * 3885576 * 2
def baseEnd_3885576 : Nat := 1995168107574394899730567

theorem tailTrace_3885576 : CollatzResearch.WordTrace tailWord_3885576 prefixEnd_3885576 1995168107574394899730567 := by
  unfold tailWord_3885576
  simp only [CollatzResearch.WordTrace]
  refine ⟨70859299685614615196866291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94479066247486153595821721 70859299685614615196866291)
  ·
    refine ⟨106288949528421922795299437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70859299685614615196866291 106288949528421922795299437)
    ·
      refine ⟨39858356073158221048237289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106288949528421922795299437 39858356073158221048237289)
      ·
        refine ⟨29893767054868665786177967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39858356073158221048237289 29893767054868665786177967)
        ·
          refine ⟨44840650582302998679266951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29893767054868665786177967 44840650582302998679266951)
          ·
            refine ⟨67260975873454498018900427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44840650582302998679266951 67260975873454498018900427)
            ·
              refine ⟨100891463810181747028350641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67260975873454498018900427 100891463810181747028350641)
              ·
                refine ⟨75668597857636310271262981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 100891463810181747028350641 75668597857636310271262981)
                ·
                  refine ⟨14187862098306808175861809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 75668597857636310271262981 14187862098306808175861809)
                  ·
                    refine ⟨10640896573730106131896357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14187862098306808175861809 10640896573730106131896357)
                    ·
                      refine ⟨1995168107574394899730567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10640896573730106131896357 1995168107574394899730567)
                      ·
                        rfl

theorem cell23_3885576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 2, 4, 2, 4].length) (baseStart_3885576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3885576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3885576 prefixEnd_3885576 := by exact prefixLift 3885576
  have htrace : WordTrace (prefixWord ++ tailWord_3885576) baseStart_3885576 baseEnd_3885576 := by
    simpa [prefixWord, tailWord_3885576, baseEnd_3885576] using wordTrace_append hprefix tailTrace_3885576
  have hstable : (prefixWord ++ tailWord_3885576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3885576).length < 2 ^ (prefixWord ++ tailWord_3885576).sum := by decide
  have hdescent : baseEnd_3885576 < baseStart_3885576 := by decide
  rcases family_descends (prefixWord ++ tailWord_3885576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3885580 : List Nat := [2, 2, 1, 2, 4, 2, 1, 2, 1, 4, 2]
def baseStart_3885580 : Nat := 118140960795 + 3885580 * 2 ^ 59
def prefixEnd_3885580 : Nat := 4983230072969 + 3 ^ 40 * 3885580 * 2
def baseEnd_3885580 : Nat := 1995170161497012884080549

theorem tailTrace_3885580 : CollatzResearch.WordTrace tailWord_3885580 prefixEnd_3885580 1995170161497012884080549 := by
  unfold tailWord_3885580
  simp only [CollatzResearch.WordTrace]
  refine ⟨70859372631607369538439097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94479163508809826051252129 70859372631607369538439097)
  ·
    refine ⟨53144529473705527153829323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70859372631607369538439097 53144529473705527153829323)
    ·
      refine ⟨79716794210558290730743985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53144529473705527153829323 79716794210558290730743985)
      ·
        refine ⟨59787595657918718048057989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79716794210558290730743985 59787595657918718048057989)
        ·
          refine ⟨11210174185859759634010873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 59787595657918718048057989 11210174185859759634010873)
          ·
            refine ⟨8407630639394819725508155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11210174185859759634010873 8407630639394819725508155)
            ·
              refine ⟨12611445959092229588262233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8407630639394819725508155 12611445959092229588262233)
              ·
                refine ⟨9458584469319172191196675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12611445959092229588262233 9458584469319172191196675)
                ·
                  refine ⟨14187876703978758286795013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9458584469319172191196675 14187876703978758286795013)
                  ·
                    refine ⟨2660226881996017178774065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14187876703978758286795013 2660226881996017178774065)
                    ·
                      refine ⟨1995170161497012884080549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2660226881996017178774065 1995170161497012884080549)
                      ·
                        rfl

theorem cell23_3885580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 1, 2, 1, 4, 2].length) (baseStart_3885580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3885580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3885580 prefixEnd_3885580 := by exact prefixLift 3885580
  have htrace : WordTrace (prefixWord ++ tailWord_3885580) baseStart_3885580 baseEnd_3885580 := by
    simpa [prefixWord, tailWord_3885580, baseEnd_3885580] using wordTrace_append hprefix tailTrace_3885580
  have hstable : (prefixWord ++ tailWord_3885580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3885580).length < 2 ^ (prefixWord ++ tailWord_3885580).sum := by decide
  have hdescent : baseEnd_3885580 < baseStart_3885580 := by decide
  rcases family_descends (prefixWord ++ tailWord_3885580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3885597 : List Nat := [1, 4, 2, 2, 1, 2, 1, 4, 2, 2, 2]
def baseStart_3885597 : Nat := 118140960795 + 3885597 * 2 ^ 59
def prefixEnd_3885597 : Nat := 4983230072969 + 3 ^ 40 * 3885597 * 2
def baseEnd_3885597 : Nat := 1995178890668139317567971

theorem tailTrace_3885597 : CollatzResearch.WordTrace tailWord_3885597 prefixEnd_3885597 1995178890668139317567971 := by
  unfold tailWord_3885597
  simp only [CollatzResearch.WordTrace]
  refine ⟨141719365304153150980247045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94479576869435433986831363 141719365304153150980247045)
  ·
    refine ⟨26572380994528715808796321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 141719365304153150980247045 26572380994528715808796321)
    ·
      refine ⟨19929285745896536856597241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26572380994528715808796321 19929285745896536856597241)
      ·
        refine ⟨14946964309422402642447931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19929285745896536856597241 14946964309422402642447931)
        ·
          refine ⟨22420446464133603963671897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14946964309422402642447931 22420446464133603963671897)
          ·
            refine ⟨16815334848100202972753923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22420446464133603963671897 16815334848100202972753923)
            ·
              refine ⟨25223002272150304459130885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16815334848100202972753923 25223002272150304459130885)
              ·
                refine ⟨4729312926028182086087041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25223002272150304459130885 4729312926028182086087041)
                ·
                  refine ⟨3546984694521136564565281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4729312926028182086087041 3546984694521136564565281)
                  ·
                    refine ⟨2660238520890852423423961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3546984694521136564565281 2660238520890852423423961)
                    ·
                      refine ⟨1995178890668139317567971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2660238520890852423423961 1995178890668139317567971)
                      ·
                        rfl

theorem cell23_3885597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 1, 4, 2, 2, 2].length) (baseStart_3885597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3885597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3885597 prefixEnd_3885597 := by exact prefixLift 3885597
  have htrace : WordTrace (prefixWord ++ tailWord_3885597) baseStart_3885597 baseEnd_3885597 := by
    simpa [prefixWord, tailWord_3885597, baseEnd_3885597] using wordTrace_append hprefix tailTrace_3885597
  have hstable : (prefixWord ++ tailWord_3885597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3885597).length < 2 ^ (prefixWord ++ tailWord_3885597).sum := by decide
  have hdescent : baseEnd_3885597 < baseStart_3885597 := by decide
  rcases family_descends (prefixWord ++ tailWord_3885597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3885616 : List Nat := [2, 1, 1, 1, 2, 3, 2, 2, 4, 5]
def baseStart_3885616 : Nat := 118140960795 + 3885616 * 2 ^ 59
def prefixEnd_3885616 : Nat := 4983230072969 + 3 ^ 40 * 3885616 * 2
def baseEnd_3885616 : Nat := 665062882266858247743461

theorem tailTrace_3885616 : CollatzResearch.WordTrace tailWord_3885616 prefixEnd_3885616 665062882266858247743461 := by
  unfold tailWord_3885616
  simp only [CollatzResearch.WordTrace]
  refine ⟨70860029145542158612594351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94480038860722878150125801 70860029145542158612594351)
  ·
    refine ⟨106290043718313237918891527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70860029145542158612594351 106290043718313237918891527)
    ·
      refine ⟨159435065577469856878337291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106290043718313237918891527 159435065577469856878337291)
      ·
        refine ⟨239152598366204785317505937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159435065577469856878337291 239152598366204785317505937)
        ·
          refine ⟨179364448774653588988129453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 239152598366204785317505937 179364448774653588988129453)
          ·
            refine ⟨67261668290495095870548545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 179364448774653588988129453 67261668290495095870548545)
            ·
              refine ⟨50446251217871321902911409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67261668290495095870548545 50446251217871321902911409)
              ·
                refine ⟨37834688413403491427183557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50446251217871321902911409 37834688413403491427183557)
                ·
                  refine ⟨7094004077513154642596917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37834688413403491427183557 7094004077513154642596917)
                  ·
                    refine ⟨665062882266858247743461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7094004077513154642596917 665062882266858247743461)
                    ·
                      rfl

theorem cell23_3885616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 2, 4, 5].length) (baseStart_3885616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3885616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3885616 prefixEnd_3885616 := by exact prefixLift 3885616
  have htrace : WordTrace (prefixWord ++ tailWord_3885616) baseStart_3885616 baseEnd_3885616 := by
    simpa [prefixWord, tailWord_3885616, baseEnd_3885616] using wordTrace_append hprefix tailTrace_3885616
  have hstable : (prefixWord ++ tailWord_3885616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3885616).length < 2 ^ (prefixWord ++ tailWord_3885616).sum := by decide
  have hdescent : baseEnd_3885616 < baseStart_3885616 := by decide
  rcases family_descends (prefixWord ++ tailWord_3885616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3885623 : List Nat := [1, 1, 3, 1, 2, 3, 1, 2, 2, 5, 2]
def baseStart_3885623 : Nat := 118140960795 + 3885623 * 2 ^ 59
def prefixEnd_3885623 : Nat := 4983230072969 + 3 ^ 40 * 3885623 * 2
def baseEnd_3885623 : Nat := 1995192241165156215842851

theorem tailTrace_3885623 : CollatzResearch.WordTrace tailWord_3885623 prefixEnd_3885623 1995192241165156215842851 := by
  unfold tailWord_3885623
  simp only [CollatzResearch.WordTrace]
  refine ⟨141720313602058957420693523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94480209068039304947129015 141720313602058957420693523)
  ·
    refine ⟨212580470403088436131040285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141720313602058957420693523 212580470403088436131040285)
    ·
      refine ⟨79717676401158163549140107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 212580470403088436131040285 79717676401158163549140107)
      ·
        refine ⟨119576514601737245323710161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79717676401158163549140107 119576514601737245323710161)
        ·
          refine ⟨89682385951302933992782621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119576514601737245323710161 89682385951302933992782621)
          ·
            refine ⟨33630894731738600247293483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 89682385951302933992782621 33630894731738600247293483)
            ·
              refine ⟨50446342097607900370940225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33630894731738600247293483 50446342097607900370940225)
              ·
                refine ⟨37834756573205925278205169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50446342097607900370940225 37834756573205925278205169)
                ·
                  refine ⟨28376067429904443958653877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37834756573205925278205169 28376067429904443958653877)
                  ·
                    refine ⟨2660256321553541621123801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 28376067429904443958653877 2660256321553541621123801)
                    ·
                      refine ⟨1995192241165156215842851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2660256321553541621123801 1995192241165156215842851)
                      ·
                        rfl

theorem cell23_3885623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 2, 2, 5, 2].length) (baseStart_3885623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3885623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3885623 prefixEnd_3885623 := by exact prefixLift 3885623
  have htrace : WordTrace (prefixWord ++ tailWord_3885623) baseStart_3885623 baseEnd_3885623 := by
    simpa [prefixWord, tailWord_3885623, baseEnd_3885623] using wordTrace_append hprefix tailTrace_3885623
  have hstable : (prefixWord ++ tailWord_3885623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3885623).length < 2 ^ (prefixWord ++ tailWord_3885623).sum := by decide
  have hdescent : baseEnd_3885623 < baseStart_3885623 := by decide
  rcases family_descends (prefixWord ++ tailWord_3885623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3885633 : List Nat := [1, 2, 5, 1, 1, 3, 1, 1, 1, 7]
def baseStart_3885633 : Nat := 118140960795 + 3885633 * 2 ^ 59
def prefixEnd_3885633 : Nat := 4983230072969 + 3 ^ 40 * 3885633 * 2
def baseEnd_3885633 : Nat := 665065791990567058905935

theorem tailTrace_3885633 : CollatzResearch.WordTrace tailWord_3885633 prefixEnd_3885633 665065791990567058905935 := by
  unfold tailWord_3885633
  simp only [CollatzResearch.WordTrace]
  refine ⟨141720678332022729128557553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94480452221348486085705035 141720678332022729128557553)
  ·
    refine ⟨106290508749017046846418165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141720678332022729128557553 106290508749017046846418165)
    ·
      refine ⟨9964735195220348141851703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 106290508749017046846418165 9964735195220348141851703)
      ·
        refine ⟨14947102792830522212777555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9964735195220348141851703 14947102792830522212777555)
        ·
          refine ⟨22420654189245783319166333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14947102792830522212777555 22420654189245783319166333)
          ·
            refine ⟨8407745320967168744687375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22420654189245783319166333 8407745320967168744687375)
            ·
              refine ⟨12611617981450753117031063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8407745320967168744687375 12611617981450753117031063)
              ·
                refine ⟨18917426972176129675546595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12611617981450753117031063 18917426972176129675546595)
                ·
                  refine ⟨28376140458264194513319893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18917426972176129675546595 28376140458264194513319893)
                  ·
                    refine ⟨665065791990567058905935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 28376140458264194513319893 665065791990567058905935)
                    ·
                      rfl

theorem cell23_3885633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 1, 1, 1, 7].length) (baseStart_3885633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3885633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3885633 prefixEnd_3885633 := by exact prefixLift 3885633
  have htrace : WordTrace (prefixWord ++ tailWord_3885633) baseStart_3885633 baseEnd_3885633 := by
    simpa [prefixWord, tailWord_3885633, baseEnd_3885633] using wordTrace_append hprefix tailTrace_3885633
  have hstable : (prefixWord ++ tailWord_3885633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3885633).length < 2 ^ (prefixWord ++ tailWord_3885633).sum := by decide
  have hdescent : baseEnd_3885633 < baseStart_3885633 := by decide
  rcases family_descends (prefixWord ++ tailWord_3885633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3885653 : List Nat := [1, 3, 2, 2, 1, 1, 2, 4, 2, 1, 4]
def baseStart_3885653 : Nat := 118140960795 + 3885653 * 2 ^ 59
def prefixEnd_3885653 : Nat := 4983230072969 + 3 ^ 40 * 3885653 * 2
def baseEnd_3885653 : Nat := 1995207645584791098467713

theorem tailTrace_3885653 : CollatzResearch.WordTrace tailWord_3885653 prefixEnd_3885653 1995207645584791098467713 := by
  unfold tailWord_3885653
  simp only [CollatzResearch.WordTrace]
  refine ⟨141721407791950272544285613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94480938527966848362857075 141721407791950272544285613)
  ·
    refine ⟨53145527921981352204107105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 141721407791950272544285613 53145527921981352204107105)
    ·
      refine ⟨39859145941486014153080329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53145527921981352204107105 39859145941486014153080329)
      ·
        refine ⟨29894359456114510614810247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39859145941486014153080329 29894359456114510614810247)
        ·
          refine ⟨44841539184171765922215371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29894359456114510614810247 44841539184171765922215371)
          ·
            refine ⟨67262308776257648883323057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44841539184171765922215371 67262308776257648883323057)
            ·
              refine ⟨50446731582193236662492293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67262308776257648883323057 50446731582193236662492293)
              ·
                refine ⟨9458762171661231874217305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50446731582193236662492293 9458762171661231874217305)
                ·
                  refine ⟨7094071628745923905662979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9458762171661231874217305 7094071628745923905662979)
                  ·
                    refine ⟨10641107443118885858494469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7094071628745923905662979 10641107443118885858494469)
                    ·
                      refine ⟨1995207645584791098467713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10641107443118885858494469 1995207645584791098467713)
                      ·
                        rfl

theorem cell23_3885653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 4, 2, 1, 4].length) (baseStart_3885653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3885653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3885653 prefixEnd_3885653 := by exact prefixLift 3885653
  have htrace : WordTrace (prefixWord ++ tailWord_3885653) baseStart_3885653 baseEnd_3885653 := by
    simpa [prefixWord, tailWord_3885653, baseEnd_3885653] using wordTrace_append hprefix tailTrace_3885653
  have hstable : (prefixWord ++ tailWord_3885653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3885653).length < 2 ^ (prefixWord ++ tailWord_3885653).sum := by decide
  have hdescent : baseEnd_3885653 < baseStart_3885653 := by decide
  rcases family_descends (prefixWord ++ tailWord_3885653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3885656 : List Nat := [2, 1, 2, 2, 1, 2, 2, 1, 2, 3, 5]
def baseStart_3885656 : Nat := 118140960795 + 3885656 * 2 ^ 59
def prefixEnd_3885656 : Nat := 4983230072969 + 3 ^ 40 * 3885656 * 2
def baseEnd_3885656 : Nat := 1995209186026754586730199

theorem tailTrace_3885656 : CollatzResearch.WordTrace tailWord_3885656 prefixEnd_3885656 1995209186026754586730199 := by
  unfold tailWord_3885656
  simp only [CollatzResearch.WordTrace]
  refine ⟨70860758605469702028322411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94481011473959602704429881 70860758605469702028322411)
  ·
    refine ⟨106291137908204553042483617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70860758605469702028322411 106291137908204553042483617)
    ·
      refine ⟨79718353431153414781862713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106291137908204553042483617 79718353431153414781862713)
      ·
        refine ⟨59788765073365061086397035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79718353431153414781862713 59788765073365061086397035)
        ·
          refine ⟨89683147610047591629595553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59788765073365061086397035 89683147610047591629595553)
          ·
            refine ⟨67262360707535693722196665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89683147610047591629595553 67262360707535693722196665)
            ·
              refine ⟨50446770530651770291647499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67262360707535693722196665 50446770530651770291647499)
              ·
                refine ⟨75670155795977655437471249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50446770530651770291647499 75670155795977655437471249)
                ·
                  refine ⟨56752616846983241578103437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 75670155795977655437471249 56752616846983241578103437)
                  ·
                    refine ⟨21282231317618715591788789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 56752616846983241578103437 21282231317618715591788789)
                    ·
                      refine ⟨1995209186026754586730199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21282231317618715591788789 1995209186026754586730199)
                      ·
                        rfl

theorem cell23_3885656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 1, 2, 3, 5].length) (baseStart_3885656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3885656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3885656 prefixEnd_3885656 := by exact prefixLift 3885656
  have htrace : WordTrace (prefixWord ++ tailWord_3885656) baseStart_3885656 baseEnd_3885656 := by
    simpa [prefixWord, tailWord_3885656, baseEnd_3885656] using wordTrace_append hprefix tailTrace_3885656
  have hstable : (prefixWord ++ tailWord_3885656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3885656).length < 2 ^ (prefixWord ++ tailWord_3885656).sum := by decide
  have hdescent : baseEnd_3885656 < baseStart_3885656 := by decide
  rcases family_descends (prefixWord ++ tailWord_3885656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3885747 : List Nat := [1, 1, 1, 2, 3, 5, 2, 1, 2, 3, 2]
def baseStart_3885747 : Nat := 118140960795 + 3885747 * 2 ^ 59
def prefixEnd_3885747 : Nat := 4983230072969 + 3 ^ 40 * 3885747 * 2
def baseEnd_3885747 : Nat := 1995255912766313730692281

theorem tailTrace_3885747 : CollatzResearch.WordTrace tailWord_3885747 prefixEnd_3885747 1995255912766313730692281 := by
  unfold tailWord_3885747
  simp only [CollatzResearch.WordTrace]
  refine ⟨141724836253609726598207495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94483224169073151065471663 141724836253609726598207495)
  ·
    refine ⟨212587254380414589897311243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141724836253609726598207495 212587254380414589897311243)
    ·
      refine ⟨318880881570621884845966865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212587254380414589897311243 318880881570621884845966865)
      ·
        refine ⟨239160661177966413634475149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 318880881570621884845966865 239160661177966413634475149)
        ·
          refine ⟨89685247941737405112928181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 239160661177966413634475149 89685247941737405112928181)
          ·
            refine ⟨8407991994537881729337017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 89685247941737405112928181 8407991994537881729337017)
            ·
              refine ⟨6305993995903411297002763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8407991994537881729337017 6305993995903411297002763)
              ·
                refine ⟨9458990993855116945504145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6305993995903411297002763 9458990993855116945504145)
                ·
                  refine ⟨7094243245391337709128109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9458990993855116945504145 7094243245391337709128109)
                  ·
                    refine ⟨2660341217021751640923041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7094243245391337709128109 2660341217021751640923041)
                    ·
                      refine ⟨1995255912766313730692281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2660341217021751640923041 1995255912766313730692281)
                      ·
                        rfl

theorem cell23_3885747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 2, 1, 2, 3, 2].length) (baseStart_3885747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3885747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3885747 prefixEnd_3885747 := by exact prefixLift 3885747
  have htrace : WordTrace (prefixWord ++ tailWord_3885747) baseStart_3885747 baseEnd_3885747 := by
    simpa [prefixWord, tailWord_3885747, baseEnd_3885747] using wordTrace_append hprefix tailTrace_3885747
  have hstable : (prefixWord ++ tailWord_3885747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3885747).length < 2 ^ (prefixWord ++ tailWord_3885747).sum := by decide
  have hdescent : baseEnd_3885747 < baseStart_3885747 := by decide
  rcases family_descends (prefixWord ++ tailWord_3885747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3885757 : List Nat := [1, 4, 1, 2, 1, 4, 3, 1, 1, 5]
def baseStart_3885757 : Nat := 118140960795 + 3885757 * 2 ^ 59
def prefixEnd_3885757 : Nat := 4983230072969 + 3 ^ 40 * 3885757 * 2
def baseEnd_3885757 : Nat := 665087015857619563855745

theorem tailTrace_3885757 : CollatzResearch.WordTrace tailWord_3885757 prefixEnd_3885757 665087015857619563855745 := by
  unfold tailWord_3885757
  simp only [CollatzResearch.WordTrace]
  refine ⟨141725200983573498306071525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94483467322382332204047683 141725200983573498306071525)
  ·
    refine ⟨26573475184420030932388411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 141725200983573498306071525 26573475184420030932388411)
    ·
      refine ⟨39860212776630046398582617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26573475184420030932388411 39860212776630046398582617)
      ·
        refine ⟨29895159582472534798936963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39860212776630046398582617 29895159582472534798936963)
        ·
          refine ⟨44842739373708802198405445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29895159582472534798936963 44842739373708802198405445)
          ·
            refine ⟨8408013632570400412201021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44842739373708802198405445 8408013632570400412201021)
            ·
              refine ⟨3153005112213900154575383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8408013632570400412201021 3153005112213900154575383)
              ·
                refine ⟨4729507668320850231863075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3153005112213900154575383 4729507668320850231863075)
                ·
                  refine ⟨7094261502481275347794613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4729507668320850231863075 7094261502481275347794613)
                  ·
                    refine ⟨665087015857619563855745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7094261502481275347794613 665087015857619563855745)
                    ·
                      rfl

theorem cell23_3885757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 3, 1, 1, 5].length) (baseStart_3885757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3885757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3885757 prefixEnd_3885757 := by exact prefixLift 3885757
  have htrace : WordTrace (prefixWord ++ tailWord_3885757) baseStart_3885757 baseEnd_3885757 := by
    simpa [prefixWord, tailWord_3885757, baseEnd_3885757] using wordTrace_append hprefix tailTrace_3885757
  have hstable : (prefixWord ++ tailWord_3885757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3885757).length < 2 ^ (prefixWord ++ tailWord_3885757).sum := by decide
  have hdescent : baseEnd_3885757 < baseStart_3885757 := by decide
  rcases family_descends (prefixWord ++ tailWord_3885757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3885777 : List Nat := [1, 2, 2, 1, 2, 3, 2, 3, 3, 2, 2]
def baseStart_3885777 : Nat := 118140960795 + 3885777 * 2 ^ 59
def prefixEnd_3885777 : Nat := 4983230072969 + 3 ^ 40 * 3885777 * 2
def baseEnd_3885777 : Nat := 1995271317185948613317143

theorem tailTrace_3885777 : CollatzResearch.WordTrace tailWord_3885777 prefixEnd_3885777 1995271317185948613317143 := by
  unfold tailWord_3885777
  simp only [CollatzResearch.WordTrace]
  refine ⟨141725930443501041721799585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94483953629000694481199723 141725930443501041721799585)
  ·
    refine ⟨106294447832625781291349689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141725930443501041721799585 106294447832625781291349689)
    ·
      refine ⟨79720835874469335968512267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106294447832625781291349689 79720835874469335968512267)
      ·
        refine ⟨119581253811704003952768401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79720835874469335968512267 119581253811704003952768401)
        ·
          refine ⟨89685940358778002964576301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119581253811704003952768401 89685940358778002964576301)
          ·
            refine ⟨33632227634541751111716113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 89685940358778002964576301 33632227634541751111716113)
            ·
              refine ⟨25224170725906313333787085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33632227634541751111716113 25224170725906313333787085)
              ·
                refine ⟨9459064022214867500170157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25224170725906313333787085 9459064022214867500170157)
                ·
                  refine ⟨3547149008330575312563809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9459064022214867500170157 3547149008330575312563809)
                  ·
                    refine ⟨2660361756247931484422857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3547149008330575312563809 2660361756247931484422857)
                    ·
                      refine ⟨1995271317185948613317143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2660361756247931484422857 1995271317185948613317143)
                      ·
                        rfl

theorem cell23_3885777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 2, 3, 3, 2, 2].length) (baseStart_3885777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3885777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3885777 prefixEnd_3885777 := by exact prefixLift 3885777
  have htrace : WordTrace (prefixWord ++ tailWord_3885777) baseStart_3885777 baseEnd_3885777 := by
    simpa [prefixWord, tailWord_3885777, baseEnd_3885777] using wordTrace_append hprefix tailTrace_3885777
  have hstable : (prefixWord ++ tailWord_3885777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3885777).length < 2 ^ (prefixWord ++ tailWord_3885777).sum := by decide
  have hdescent : baseEnd_3885777 < baseStart_3885777 := by decide
  rcases family_descends (prefixWord ++ tailWord_3885777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3885783 : List Nat := [1, 1, 3, 2, 1, 4, 3, 8]
def baseStart_3885783 : Nat := 118140960795 + 3885783 * 2 ^ 59
def prefixEnd_3885783 : Nat := 4983230072969 + 3 ^ 40 * 3885783 * 2
def baseEnd_3885783 : Nat := 73899051780365762586745

theorem tailTrace_3885783 : CollatzResearch.WordTrace tailWord_3885783 prefixEnd_3885783 73899051780365762586745 := by
  unfold tailWord_3885783
  simp only [CollatzResearch.WordTrace]
  refine ⟨141726149281479304746518003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94484099520986203164345335 141726149281479304746518003)
  ·
    refine ⟨212589223922218957119777005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141726149281479304746518003 212589223922218957119777005)
    ·
      refine ⟨79720958970832108919916377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 212589223922218957119777005 79720958970832108919916377)
      ·
        refine ⟨59790719228124081689937283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79720958970832108919916377 59790719228124081689937283)
        ·
          refine ⟨89686078842186122534905925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59790719228124081689937283 89686078842186122534905925)
          ·
            refine ⟨16816139782909897975294861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 89686078842186122534905925 16816139782909897975294861)
            ·
              refine ⟨6306052418591211740735573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16816139782909897975294861 6306052418591211740735573)
              ·
                refine ⟨73899051780365762586745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6306052418591211740735573 73899051780365762586745)
                ·
                  rfl

theorem cell23_3885783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 3, 8].length) (baseStart_3885783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3885783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3885783 prefixEnd_3885783 := by exact prefixLift 3885783
  have htrace : WordTrace (prefixWord ++ tailWord_3885783) baseStart_3885783 baseEnd_3885783 := by
    simpa [prefixWord, tailWord_3885783, baseEnd_3885783] using wordTrace_append hprefix tailTrace_3885783
  have hstable : (prefixWord ++ tailWord_3885783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3885783).length < 2 ^ (prefixWord ++ tailWord_3885783).sum := by decide
  have hdescent : baseEnd_3885783 < baseStart_3885783 := by decide
  rcases family_descends (prefixWord ++ tailWord_3885783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3885833 : List Nat := [1, 2, 1, 1, 3, 2, 2, 1, 1, 5, 4]
def baseStart_3885833 : Nat := 118140960795 + 3885833 * 2 ^ 59
def prefixEnd_3885833 : Nat := 4983230072969 + 3 ^ 40 * 3885833 * 2
def baseEnd_3885833 : Nat := 1995300072102600394216885

theorem tailTrace_3885833 : CollatzResearch.WordTrace tailWord_3885833 prefixEnd_3885833 1995300072102600394216885 := by
  unfold tailWord_3885833
  simp only [CollatzResearch.WordTrace]
  refine ⟨141727972931298163285838153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94485315287532108857225435 141727972931298163285838153)
  ·
    refine ⟨106295979698473622464378615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141727972931298163285838153 106295979698473622464378615)
    ·
      refine ⟨159443969547710433696567923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106295979698473622464378615 159443969547710433696567923)
      ·
        refine ⟨239165954321565650544851885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159443969547710433696567923 239165954321565650544851885)
        ·
          refine ⟨89687232870587118954319457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 239165954321565650544851885 89687232870587118954319457)
          ·
            refine ⟨67265424652940339215739593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89687232870587118954319457 67265424652940339215739593)
            ·
              refine ⟨50449068489705254411804695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67265424652940339215739593 50449068489705254411804695)
              ·
                refine ⟨75673602734557881617707043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50449068489705254411804695 75673602734557881617707043)
                ·
                  refine ⟨113510404101836822426560565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 75673602734557881617707043 113510404101836822426560565)
                  ·
                    refine ⟨10641600384547202102490053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 113510404101836822426560565 10641600384547202102490053)
                    ·
                      refine ⟨1995300072102600394216885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10641600384547202102490053 1995300072102600394216885)
                      ·
                        rfl

theorem cell23_3885833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 1, 1, 5, 4].length) (baseStart_3885833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3885833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3885833 prefixEnd_3885833 := by exact prefixLift 3885833
  have htrace : WordTrace (prefixWord ++ tailWord_3885833) baseStart_3885833 baseEnd_3885833 := by
    simpa [prefixWord, tailWord_3885833, baseEnd_3885833] using wordTrace_append hprefix tailTrace_3885833
  have hstable : (prefixWord ++ tailWord_3885833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3885833).length < 2 ^ (prefixWord ++ tailWord_3885833).sum := by decide
  have hdescent : baseEnd_3885833 < baseStart_3885833 := by decide
  rcases family_descends (prefixWord ++ tailWord_3885833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3885843 : List Nat := [1, 1, 1, 2, 1, 3, 3, 3, 2, 6]
def baseStart_3885843 : Nat := 118140960795 + 3885843 * 2 ^ 59
def prefixEnd_3885843 : Nat := 4983230072969 + 3 ^ 40 * 3885843 * 2
def baseEnd_3885843 : Nat := 665101735636381785030613

theorem tailTrace_3885843 : CollatzResearch.WordTrace tailWord_3885843 prefixEnd_3885843 665101735636381785030613 := by
  unfold tailWord_3885843
  simp only [CollatzResearch.WordTrace]
  refine ⟨141728337661261934993702183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94485558440841289995801455 141728337661261934993702183)
  ·
    refine ⟨212592506491892902490553275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141728337661261934993702183 212592506491892902490553275)
    ·
      refine ⟨318888759737839353735829913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212592506491892902490553275 318888759737839353735829913)
      ·
        refine ⟨239166569803379515301872435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 318888759737839353735829913 239166569803379515301872435)
        ·
          refine ⟨358749854705069272952808653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 239166569803379515301872435 358749854705069272952808653)
          ·
            refine ⟨134531195514400977357303245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 358749854705069272952808653 134531195514400977357303245)
            ·
              refine ⟨50449198317900366508988717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 134531195514400977357303245 50449198317900366508988717)
              ·
                refine ⟨18918449369212637440870769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50449198317900366508988717 18918449369212637440870769)
                ·
                  refine ⟨14188837026909478080653077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18918449369212637440870769 14188837026909478080653077)
                  ·
                    refine ⟨665101735636381785030613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14188837026909478080653077 665101735636381785030613)
                    ·
                      rfl

theorem cell23_3885843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 3, 2, 6].length) (baseStart_3885843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3885843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3885843 prefixEnd_3885843 := by exact prefixLift 3885843
  have htrace : WordTrace (prefixWord ++ tailWord_3885843) baseStart_3885843 baseEnd_3885843 := by
    simpa [prefixWord, tailWord_3885843, baseEnd_3885843] using wordTrace_append hprefix tailTrace_3885843
  have hstable : (prefixWord ++ tailWord_3885843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3885843).length < 2 ^ (prefixWord ++ tailWord_3885843).sum := by decide
  have hdescent : baseEnd_3885843 < baseStart_3885843 := by decide
  rcases family_descends (prefixWord ++ tailWord_3885843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3885867 : List Nat := [1, 1, 1, 1, 2, 1, 2, 6, 4, 2, 2]
def baseStart_3885867 : Nat := 118140960795 + 3885867 * 2 ^ 59
def prefixEnd_3885867 : Nat := 4983230072969 + 3 ^ 40 * 3885867 * 2
def baseEnd_3885867 : Nat := 1995317530444853261191729

theorem tailTrace_3885867 : CollatzResearch.WordTrace tailWord_3885867 prefixEnd_3885867 1995317530444853261191729 := by
  unfold tailWord_3885867
  simp only [CollatzResearch.WordTrace]
  refine ⟨141729213013174987092575855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94486142008783324728383903 141729213013174987092575855)
  ·
    refine ⟨212593819519762480638863783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141729213013174987092575855 212593819519762480638863783)
    ·
      refine ⟨318890729279643720958295675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212593819519762480638863783 318890729279643720958295675)
      ·
        refine ⟨478336093919465581437443513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 318890729279643720958295675 478336093919465581437443513)
        ·
          refine ⟨358752070439599186078082635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 478336093919465581437443513 358752070439599186078082635)
          ·
            refine ⟨538128105659398779117123953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 358752070439599186078082635 538128105659398779117123953)
            ·
              refine ⟨403596079244549084337842965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 538128105659398779117123953 403596079244549084337842965)
              ·
                refine ⟨18918566214588238328336389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 403596079244549084337842965 18918566214588238328336389)
                ·
                  refine ⟨3547231165235294686563073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18918566214588238328336389 3547231165235294686563073)
                  ·
                    refine ⟨2660423373926471014922305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3547231165235294686563073 2660423373926471014922305)
                    ·
                      refine ⟨1995317530444853261191729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2660423373926471014922305 1995317530444853261191729)
                      ·
                        rfl

theorem cell23_3885867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 6, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 6, 4, 2, 2].length) (baseStart_3885867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3885867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3885867 prefixEnd_3885867 := by exact prefixLift 3885867
  have htrace : WordTrace (prefixWord ++ tailWord_3885867) baseStart_3885867 baseEnd_3885867 := by
    simpa [prefixWord, tailWord_3885867, baseEnd_3885867] using wordTrace_append hprefix tailTrace_3885867
  have hstable : (prefixWord ++ tailWord_3885867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3885867).length < 2 ^ (prefixWord ++ tailWord_3885867).sum := by decide
  have hdescent : baseEnd_3885867 < baseStart_3885867 := by decide
  rcases family_descends (prefixWord ++ tailWord_3885867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3885884 : List Nat := [2, 2, 2, 2, 1, 1, 1, 6, 2, 2, 2]
def baseStart_3885884 : Nat := 118140960795 + 3885884 * 2 ^ 59
def prefixEnd_3885884 : Nat := 4983230072969 + 3 ^ 40 * 3885884 * 2
def baseEnd_3885884 : Nat := 1995326259615979694679151

theorem tailTrace_3885884 : CollatzResearch.WordTrace tailWord_3885884 prefixEnd_3885884 1995326259615979694679151 := by
  unfold tailWord_3885884
  simp only [CollatzResearch.WordTrace]
  refine ⟨70864916527056699497972353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94486555369408932663963137 70864916527056699497972353)
  ·
    refine ⟨53148687395292524623479265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70864916527056699497972353 53148687395292524623479265)
    ·
      refine ⟨39861515546469393467609449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53148687395292524623479265 39861515546469393467609449)
      ·
        refine ⟨29896136659852045100707087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39861515546469393467609449 29896136659852045100707087)
        ·
          refine ⟨44844204989778067651060631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29896136659852045100707087 44844204989778067651060631)
          ·
            refine ⟨67266307484667101476590947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44844204989778067651060631 67266307484667101476590947)
            ·
              refine ⟨100899461227000652214886421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67266307484667101476590947 100899461227000652214886421)
              ·
                refine ⟨4729662245015655572572801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 100899461227000652214886421 4729662245015655572572801)
                ·
                  refine ⟨3547246683761741679429601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4729662245015655572572801 3547246683761741679429601)
                  ·
                    refine ⟨2660435012821306259572201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3547246683761741679429601 2660435012821306259572201)
                    ·
                      refine ⟨1995326259615979694679151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2660435012821306259572201 1995326259615979694679151)
                      ·
                        rfl

theorem cell23_3885884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 6, 2, 2, 2].length) (baseStart_3885884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3885884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3885884 prefixEnd_3885884 := by exact prefixLift 3885884
  have htrace : WordTrace (prefixWord ++ tailWord_3885884) baseStart_3885884 baseEnd_3885884 := by
    simpa [prefixWord, tailWord_3885884, baseEnd_3885884] using wordTrace_append hprefix tailTrace_3885884
  have hstable : (prefixWord ++ tailWord_3885884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3885884).length < 2 ^ (prefixWord ++ tailWord_3885884).sum := by decide
  have hdescent : baseEnd_3885884 < baseStart_3885884 := by decide
  rcases family_descends (prefixWord ++ tailWord_3885884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3885893 : List Nat := [1, 3, 1, 1, 1, 2, 2, 1, 2, 1, 8]
def baseStart_3885893 : Nat := 118140960795 + 3885893 * 2 ^ 59
def prefixEnd_3885893 : Nat := 4983230072969 + 3 ^ 40 * 3885893 * 2
def baseEnd_3885893 : Nat := 1995330880941870159466609

theorem tailTrace_3885893 : CollatzResearch.WordTrace tailWord_3885893 prefixEnd_3885893 1995330880941870159466609 := by
  unfold tailWord_3885893
  simp only [CollatzResearch.WordTrace]
  refine ⟨141730161311080793533022333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94486774207387195688681555 141730161311080793533022333)
  ·
    refine ⟨53148810491655297574883375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 141730161311080793533022333 53148810491655297574883375)
    ·
      refine ⟨79723215737482946362325063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53148810491655297574883375 79723215737482946362325063)
      ·
        refine ⟨119584823606224419543487595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79723215737482946362325063 119584823606224419543487595)
        ·
          refine ⟨179377235409336629315231393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119584823606224419543487595 179377235409336629315231393)
          ·
            refine ⟨134532926557002471986423545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 179377235409336629315231393 134532926557002471986423545)
            ·
              refine ⟨100899694917751853989817659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 134532926557002471986423545 100899694917751853989817659)
              ·
                refine ⟨151349542376627780984726489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100899694917751853989817659 151349542376627780984726489)
                ·
                  refine ⟨113512156782470835738544867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 151349542376627780984726489 113512156782470835738544867)
                  ·
                    refine ⟨170268235173706253607817301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 113512156782470835738544867 170268235173706253607817301)
                    ·
                      refine ⟨1995330880941870159466609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 170268235173706253607817301 1995330880941870159466609)
                      ·
                        rfl

theorem cell23_3885893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 1, 2, 1, 8].length) (baseStart_3885893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3885893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3885893 prefixEnd_3885893 := by exact prefixLift 3885893
  have htrace : WordTrace (prefixWord ++ tailWord_3885893) baseStart_3885893 baseEnd_3885893 := by
    simpa [prefixWord, tailWord_3885893, baseEnd_3885893] using wordTrace_append hprefix tailTrace_3885893
  have hstable : (prefixWord ++ tailWord_3885893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3885893).length < 2 ^ (prefixWord ++ tailWord_3885893).sum := by decide
  have hdescent : baseEnd_3885893 < baseStart_3885893 := by decide
  rcases family_descends (prefixWord ++ tailWord_3885893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3885941 : List Nat := [1, 3, 4, 1, 1, 4, 2, 2, 5]
def baseStart_3885941 : Nat := 118140960795 + 3885941 * 2 ^ 59
def prefixEnd_3885941 : Nat := 4983230072969 + 3 ^ 40 * 3885941 * 2
def baseEnd_3885941 : Nat := 221706169779253996851821

theorem tailTrace_3885941 : CollatzResearch.WordTrace tailWord_3885941 prefixEnd_3885941 221706169779253996851821 := by
  unfold tailWord_3885941
  simp only [CollatzResearch.WordTrace]
  refine ⟨141731912014906897730769677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94487941343271265153846451 141731912014906897730769677)
  ·
    refine ⟨53149467005590086649038629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 141731912014906897730769677 53149467005590086649038629)
    ·
      refine ⟨9965525063548141246694743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 53149467005590086649038629 9965525063548141246694743)
      ·
        refine ⟨14948287595322211870042115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9965525063548141246694743 14948287595322211870042115)
        ·
          refine ⟨22422431392983317805063173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14948287595322211870042115 22422431392983317805063173)
          ·
            refine ⟨4204205886184372088449345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22422431392983317805063173 4204205886184372088449345)
            ·
              refine ⟨3153154414638279066337009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4204205886184372088449345 3153154414638279066337009)
              ·
                refine ⟨2364865810978709299752757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3153154414638279066337009 2364865810978709299752757)
                ·
                  refine ⟨221706169779253996851821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2364865810978709299752757 221706169779253996851821)
                  ·
                    rfl

theorem cell23_3885941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 4, 2, 2, 5].length) (baseStart_3885941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3885941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3885941 prefixEnd_3885941 := by exact prefixLift 3885941
  have htrace : WordTrace (prefixWord ++ tailWord_3885941) baseStart_3885941 baseEnd_3885941 := by
    simpa [prefixWord, tailWord_3885941, baseEnd_3885941] using wordTrace_append hprefix tailTrace_3885941
  have hstable : (prefixWord ++ tailWord_3885941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3885941).length < 2 ^ (prefixWord ++ tailWord_3885941).sum := by decide
  have hdescent : baseEnd_3885941 < baseStart_3885941 := by decide
  rcases family_descends (prefixWord ++ tailWord_3885941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3885957 : List Nat := [1, 3, 1, 1, 3, 3, 1, 1, 1, 6, 2]
def baseStart_3885957 : Nat := 118140960795 + 3885957 * 2 ^ 59
def prefixEnd_3885957 : Nat := 4983230072969 + 3 ^ 40 * 3885957 * 2
def baseEnd_3885957 : Nat := 1995363743703757909066315

theorem tailTrace_3885957 : CollatzResearch.WordTrace tailWord_3885957 prefixEnd_3885957 1995363743703757909066315 := by
  unfold tailWord_3885957
  simp only [CollatzResearch.WordTrace]
  refine ⟨141732495582848932463352125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94488330388565954975568083 141732495582848932463352125)
  ·
    refine ⟨53149685843568349673757047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 141732495582848932463352125 53149685843568349673757047)
    ·
      refine ⟨79724528765352524510635571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53149685843568349673757047 79724528765352524510635571)
      ·
        refine ⟨119586793148028786765953357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79724528765352524510635571 119586793148028786765953357)
        ·
          refine ⟨44845047430510795037232509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 119586793148028786765953357 44845047430510795037232509)
          ·
            refine ⟨16816892786441548138962191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44845047430510795037232509 16816892786441548138962191)
            ·
              refine ⟨25225339179662322208443287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16816892786441548138962191 25225339179662322208443287)
              ·
                refine ⟨37838008769493483312664931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25225339179662322208443287 37838008769493483312664931)
                ·
                  refine ⟨56757013154240224968997397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37838008769493483312664931 56757013154240224968997397)
                  ·
                    refine ⟨2660484991605010545421753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 56757013154240224968997397 2660484991605010545421753)
                    ·
                      refine ⟨1995363743703757909066315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2660484991605010545421753 1995363743703757909066315)
                      ·
                        rfl

theorem cell23_3885957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 1, 1, 1, 6, 2].length) (baseStart_3885957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3885957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3885957 prefixEnd_3885957 := by exact prefixLift 3885957
  have htrace : WordTrace (prefixWord ++ tailWord_3885957) baseStart_3885957 baseEnd_3885957 := by
    simpa [prefixWord, tailWord_3885957, baseEnd_3885957] using wordTrace_append hprefix tailTrace_3885957
  have hstable : (prefixWord ++ tailWord_3885957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3885957).length < 2 ^ (prefixWord ++ tailWord_3885957).sum := by decide
  have hdescent : baseEnd_3885957 < baseStart_3885957 := by decide
  rcases family_descends (prefixWord ++ tailWord_3885957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3885984 : List Nat := [2, 1, 1, 4, 1, 1, 3, 5, 1, 4]
def baseStart_3885984 : Nat := 118140960795 + 3885984 * 2 ^ 59
def prefixEnd_3885984 : Nat := 4983230072969 + 3 ^ 40 * 3885984 * 2
def baseEnd_3885984 : Nat := 665125869227143101142897

theorem tailTrace_3885984 : CollatzResearch.WordTrace tailWord_3885984 prefixEnd_3885984 665125869227143101142897 := by
  unfold tailWord_3885984
  simp only [CollatzResearch.WordTrace]
  refine ⟨70866740176875558037292503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94488986902500744049723337 70866740176875558037292503)
  ·
    refine ⟨106300110265313337055938755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70866740176875558037292503 106300110265313337055938755)
    ·
      refine ⟨159450165397970005583908133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106300110265313337055938755 159450165397970005583908133)
      ·
        refine ⟨29896906012119376046982775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 159450165397970005583908133 29896906012119376046982775)
        ·
          refine ⟨44845359018179064070474163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29896906012119376046982775 44845359018179064070474163)
          ·
            refine ⟨67268038527268596105711245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44845359018179064070474163 67268038527268596105711245)
            ·
              refine ⟨25225514447725723539641717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67268038527268596105711245 25225514447725723539641717)
              ·
                refine ⟨2364891979474286581841411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25225514447725723539641717 2364891979474286581841411)
                ·
                  refine ⟨3547337969211429872762117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2364891979474286581841411 3547337969211429872762117)
                  ·
                    refine ⟨665125869227143101142897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3547337969211429872762117 665125869227143101142897)
                    ·
                      rfl

theorem cell23_3885984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 3, 5, 1, 4].length) (baseStart_3885984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3885984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3885984 prefixEnd_3885984 := by exact prefixLift 3885984
  have htrace : WordTrace (prefixWord ++ tailWord_3885984) baseStart_3885984 baseEnd_3885984 := by
    simpa [prefixWord, tailWord_3885984, baseEnd_3885984] using wordTrace_append hprefix tailTrace_3885984
  have hstable : (prefixWord ++ tailWord_3885984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3885984).length < 2 ^ (prefixWord ++ tailWord_3885984).sum := by decide
  have hdescent : baseEnd_3885984 < baseStart_3885984 := by decide
  rcases family_descends (prefixWord ++ tailWord_3885984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3886014 : List Nat := [4, 2, 1, 1, 1, 2, 5, 1, 6]
def baseStart_3886014 : Nat := 118140960795 + 3886014 * 2 ^ 59
def prefixEnd_3886014 : Nat := 4983230072969 + 3 ^ 40 * 3886014 * 2
def baseEnd_3886014 : Nat := 221710334677896020672617

theorem tailTrace_3886014 : CollatzResearch.WordTrace tailWord_3886014 prefixEnd_3886014 221710334677896020672617 := by
  unfold tailWord_3886014
  simp only [CollatzResearch.WordTrace]
  refine ⟨17716821817955303899772137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 94489716362428287465451397 17716821817955303899772137)
  ·
    refine ⟨13287616363466477924829103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17716821817955303899772137 13287616363466477924829103)
    ·
      refine ⟨19931424545199716887243655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13287616363466477924829103 19931424545199716887243655)
      ·
        refine ⟨29897136817799575330865483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19931424545199716887243655 29897136817799575330865483)
        ·
          refine ⟨44845705226699362996298225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29897136817799575330865483 44845705226699362996298225)
          ·
            refine ⟨33634278920024522247223669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44845705226699362996298225 33634278920024522247223669)
            ·
              refine ⟨3153213648752298960677219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 33634278920024522247223669 3153213648752298960677219)
              ·
                refine ⟨4729820473128448441015829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3153213648752298960677219 4729820473128448441015829)
                ·
                  refine ⟨221710334677896020672617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4729820473128448441015829 221710334677896020672617)
                  ·
                    rfl

theorem cell23_3886014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 5, 1, 6].length) (baseStart_3886014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3886014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3886014 prefixEnd_3886014 := by exact prefixLift 3886014
  have htrace : WordTrace (prefixWord ++ tailWord_3886014) baseStart_3886014 baseEnd_3886014 := by
    simpa [prefixWord, tailWord_3886014, baseEnd_3886014] using wordTrace_append hprefix tailTrace_3886014
  have hstable : (prefixWord ++ tailWord_3886014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3886014).length < 2 ^ (prefixWord ++ tailWord_3886014).sum := by decide
  have hdescent : baseEnd_3886014 < baseStart_3886014 := by decide
  rcases family_descends (prefixWord ++ tailWord_3886014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3886027 : List Nat := [1, 1, 1, 1, 3, 5, 1, 4, 1, 5]
def baseStart_3886027 : Nat := 118140960795 + 3886027 * 2 ^ 59
def prefixEnd_3886027 : Nat := 4983230072969 + 3 ^ 40 * 3886027 * 2
def baseEnd_3886027 : Nat := 665133229116524211730331

theorem tailTrace_3886027 : CollatzResearch.WordTrace tailWord_3886027 prefixEnd_3886027 665133229116524211730331 := by
  unfold tailWord_3886027
  simp only [CollatzResearch.WordTrace]
  refine ⟨141735048692595334418400335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94490032461730222945600223 141735048692595334418400335)
  ·
    refine ⟨212602573038893001627600503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141735048692595334418400335 212602573038893001627600503)
    ·
      refine ⟨318903859558339502441400755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212602573038893001627600503 318903859558339502441400755)
      ·
        refine ⟨478355789337509253662101133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 318903859558339502441400755 478355789337509253662101133)
        ·
          refine ⟨179383421001565970123287925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 478355789337509253662101133 179383421001565970123287925)
          ·
            refine ⟨16817195718896809699058243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 179383421001565970123287925 16817195718896809699058243)
            ·
              refine ⟨25225793578345214548587365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16817195718896809699058243 25225793578345214548587365)
              ·
                refine ⟨4729836295939727727860131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25225793578345214548587365 4729836295939727727860131)
                ·
                  refine ⟨7094754443909591591790197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4729836295939727727860131 7094754443909591591790197)
                  ·
                    refine ⟨665133229116524211730331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7094754443909591591790197 665133229116524211730331)
                    ·
                      rfl

theorem cell23_3886027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 1, 4, 1, 5].length) (baseStart_3886027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3886027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3886027 prefixEnd_3886027 := by exact prefixLift 3886027
  have htrace : WordTrace (prefixWord ++ tailWord_3886027) baseStart_3886027 baseEnd_3886027 := by
    simpa [prefixWord, tailWord_3886027, baseEnd_3886027] using wordTrace_append hprefix tailTrace_3886027
  have hstable : (prefixWord ++ tailWord_3886027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3886027).length < 2 ^ (prefixWord ++ tailWord_3886027).sum := by decide
  have hdescent : baseEnd_3886027 < baseStart_3886027 := by decide
  rcases family_descends (prefixWord ++ tailWord_3886027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3886077 : List Nat := [1, 4, 1, 1, 1, 2, 1, 5, 1, 2, 4]
def baseStart_3886077 : Nat := 118140960795 + 3886077 * 2 ^ 59
def prefixEnd_3886077 : Nat := 4983230072969 + 3 ^ 40 * 3886077 * 2
def baseEnd_3886077 : Nat := 1995425361382297439565763

theorem tailTrace_3886077 : CollatzResearch.WordTrace tailWord_3886077 prefixEnd_3886077 1995425361382297439565763 := by
  unfold tailWord_3886077
  simp only [CollatzResearch.WordTrace]
  refine ⟨141736872342414192957720485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94491248228276128638480323 141736872342414192957720485)
  ·
    refine ⟨26575663564202661179572591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 141736872342414192957720485 26575663564202661179572591)
    ·
      refine ⟨39863495346303991769358887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26575663564202661179572591 39863495346303991769358887)
      ·
        refine ⟨59795243019455987654038331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39863495346303991769358887 59795243019455987654038331)
        ·
          refine ⟨89692864529183981481057497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59795243019455987654038331 89692864529183981481057497)
          ·
            refine ⟨67269648396887986110793123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89692864529183981481057497 67269648396887986110793123)
            ·
              refine ⟨100904472595331979166189685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67269648396887986110793123 100904472595331979166189685)
              ·
                refine ⟨9459794305812373046830283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 100904472595331979166189685 9459794305812373046830283)
                ·
                  refine ⟨14189691458718559570245425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9459794305812373046830283 14189691458718559570245425)
                  ·
                    refine ⟨10642268594038919677684069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14189691458718559570245425 10642268594038919677684069)
                    ·
                      refine ⟨1995425361382297439565763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10642268594038919677684069 1995425361382297439565763)
                      ·
                        rfl

theorem cell23_3886077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 5, 1, 2, 4].length) (baseStart_3886077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3886077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3886077 prefixEnd_3886077 := by exact prefixLift 3886077
  have htrace : WordTrace (prefixWord ++ tailWord_3886077) baseStart_3886077 baseEnd_3886077 := by
    simpa [prefixWord, tailWord_3886077, baseEnd_3886077] using wordTrace_append hprefix tailTrace_3886077
  have hstable : (prefixWord ++ tailWord_3886077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3886077).length < 2 ^ (prefixWord ++ tailWord_3886077).sum := by decide
  have hdescent : baseEnd_3886077 < baseStart_3886077 := by decide
  rcases family_descends (prefixWord ++ tailWord_3886077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3886078 : List Nat := [4, 2, 2, 2, 2, 2, 1, 2, 1, 5]
def baseStart_3886078 : Nat := 118140960795 + 3886078 * 2 ^ 59
def prefixEnd_3886078 : Nat := 4983230072969 + 3 ^ 40 * 3886078 * 2
def baseEnd_3886078 : Nat := 665141958287650645217753

theorem tailTrace_3886078 : CollatzResearch.WordTrace tailWord_3886078 prefixEnd_3886078 665141958287650645217753 := by
  unfold tailWord_3886078
  simp only [CollatzResearch.WordTrace]
  refine ⟨17717113601926321266063361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 94491272543607046752337925 17717113601926321266063361)
  ·
    refine ⟨13287835201444740949547521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17717113601926321266063361 13287835201444740949547521)
    ·
      refine ⟨9965876401083555712160641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13287835201444740949547521 9965876401083555712160641)
      ·
        refine ⟨7474407300812666784120481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9965876401083555712160641 7474407300812666784120481)
        ·
          refine ⟨5605805475609500088090361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7474407300812666784120481 5605805475609500088090361)
          ·
            refine ⟨4204354106707125066067771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5605805475609500088090361 4204354106707125066067771)
            ·
              refine ⟨6306531160060687599101657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4204354106707125066067771 6306531160060687599101657)
              ·
                refine ⟨4729898370045515699326243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6306531160060687599101657 4729898370045515699326243)
                ·
                  refine ⟨7094847555068273548989365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4729898370045515699326243 7094847555068273548989365)
                  ·
                    refine ⟨665141958287650645217753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7094847555068273548989365 665141958287650645217753)
                    ·
                      rfl

theorem cell23_3886078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 2, 1, 2, 1, 5].length) (baseStart_3886078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3886078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3886078 prefixEnd_3886078 := by exact prefixLift 3886078
  have htrace : WordTrace (prefixWord ++ tailWord_3886078) baseStart_3886078 baseEnd_3886078 := by
    simpa [prefixWord, tailWord_3886078, baseEnd_3886078] using wordTrace_append hprefix tailTrace_3886078
  have hstable : (prefixWord ++ tailWord_3886078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3886078).length < 2 ^ (prefixWord ++ tailWord_3886078).sum := by decide
  have hdescent : baseEnd_3886078 < baseStart_3886078 := by decide
  rcases family_descends (prefixWord ++ tailWord_3886078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3886081 : List Nat := [1, 2, 4, 1, 2, 4, 1, 2, 1, 1, 4]
def baseStart_3886081 : Nat := 118140960795 + 3886081 * 2 ^ 59
def prefixEnd_3886081 : Nat := 4983230072969 + 3 ^ 40 * 3886081 * 2
def baseEnd_3886081 : Nat := 1995427415304915423915745

theorem tailTrace_3886081 : CollatzResearch.WordTrace tailWord_3886081 prefixEnd_3886081 1995427415304915423915745 := by
  unfold tailWord_3886081
  simp only [CollatzResearch.WordTrace]
  refine ⟨141737018234399701640866097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94491345489599801093910731 141737018234399701640866097)
  ·
    refine ⟨106302763675799776230649573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141737018234399701640866097 106302763675799776230649573)
    ·
      refine ⟨19931768189212458043246795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 106302763675799776230649573 19931768189212458043246795)
      ·
        refine ⟨29897652283818687064870193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19931768189212458043246795 29897652283818687064870193)
        ·
          refine ⟨22423239212864015298652645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29897652283818687064870193 22423239212864015298652645)
          ·
            refine ⟨4204357352412002868497371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22423239212864015298652645 4204357352412002868497371)
            ·
              refine ⟨6306536028618004302746057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4204357352412002868497371 6306536028618004302746057)
              ·
                refine ⟨4729902021463503227059543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6306536028618004302746057 4729902021463503227059543)
                ·
                  refine ⟨7094853032195254840589315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4729902021463503227059543 7094853032195254840589315)
                  ·
                    refine ⟨10642279548292882260883973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7094853032195254840589315 10642279548292882260883973)
                    ·
                      refine ⟨1995427415304915423915745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10642279548292882260883973 1995427415304915423915745)
                      ·
                        rfl

theorem cell23_3886081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 4, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 4, 1, 2, 1, 1, 4].length) (baseStart_3886081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3886081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3886081 prefixEnd_3886081 := by exact prefixLift 3886081
  have htrace : WordTrace (prefixWord ++ tailWord_3886081) baseStart_3886081 baseEnd_3886081 := by
    simpa [prefixWord, tailWord_3886081, baseEnd_3886081] using wordTrace_append hprefix tailTrace_3886081
  have hstable : (prefixWord ++ tailWord_3886081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3886081).length < 2 ^ (prefixWord ++ tailWord_3886081).sum := by decide
  have hdescent : baseEnd_3886081 < baseStart_3886081 := by decide
  rcases family_descends (prefixWord ++ tailWord_3886081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3886094 : List Nat := [4, 1, 1, 2, 2, 3, 1, 2, 1, 2, 4]
def baseStart_3886094 : Nat := 118140960795 + 3886094 * 2 ^ 59
def prefixEnd_3886094 : Nat := 4983230072969 + 3 ^ 40 * 3886094 * 2
def baseEnd_3886094 : Nat := 1995434090553423873053185

theorem tailTrace_3886094 : CollatzResearch.WordTrace tailWord_3886094 prefixEnd_3886094 1995434090553423873053185 := by
  unfold tailWord_3886094
  simp only [CollatzResearch.WordTrace]
  refine ⟨17717186547919075607636167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 94491661588901736574059557 17717186547919075607636167)
  ·
    refine ⟨26575779821878613411454251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17717186547919075607636167 26575779821878613411454251)
    ·
      refine ⟨39863669732817920117181377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26575779821878613411454251 39863669732817920117181377)
      ·
        refine ⟨29897752299613440087886033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39863669732817920117181377 29897752299613440087886033)
        ·
          refine ⟨22423314224710080065914525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29897752299613440087886033 22423314224710080065914525)
          ·
            refine ⟨8408742834266280024717947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22423314224710080065914525 8408742834266280024717947)
            ·
              refine ⟨12613114251399420037076921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8408742834266280024717947 12613114251399420037076921)
              ·
                refine ⟨9459835688549565027807691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12613114251399420037076921 9459835688549565027807691)
                ·
                  refine ⟨14189753532824347541711537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9459835688549565027807691 14189753532824347541711537)
                  ·
                    refine ⟨10642315149618260656283653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14189753532824347541711537 10642315149618260656283653)
                    ·
                      refine ⟨1995434090553423873053185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10642315149618260656283653 1995434090553423873053185)
                      ·
                        rfl

theorem cell23_3886094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 1, 2, 1, 2, 4].length) (baseStart_3886094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3886094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3886094 prefixEnd_3886094 := by exact prefixLift 3886094
  have htrace : WordTrace (prefixWord ++ tailWord_3886094) baseStart_3886094 baseEnd_3886094 := by
    simpa [prefixWord, tailWord_3886094, baseEnd_3886094] using wordTrace_append hprefix tailTrace_3886094
  have hstable : (prefixWord ++ tailWord_3886094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3886094).length < 2 ^ (prefixWord ++ tailWord_3886094).sum := by decide
  have hdescent : baseEnd_3886094 < baseStart_3886094 := by decide
  rcases family_descends (prefixWord ++ tailWord_3886094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3886115 : List Nat := [1, 1, 1, 4, 3, 2, 4, 2, 1, 2, 2]
def baseStart_3886115 : Nat := 118140960795 + 3886115 * 2 ^ 59
def prefixEnd_3886115 : Nat := 4983230072969 + 3 ^ 40 * 3886115 * 2
def baseEnd_3886115 : Nat := 1995444873647168290890589

theorem tailTrace_3886115 : CollatzResearch.WordTrace tailWord_3886115 prefixEnd_3886115 1995444873647168290890589 := by
  unfold tailWord_3886115
  simp only [CollatzResearch.WordTrace]
  refine ⟨141738258316276525447603799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94492172210851016965069199 141738258316276525447603799)
  ·
    refine ⟨212607387474414788171405699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141738258316276525447603799 212607387474414788171405699)
    ·
      refine ⟨318911081211622182257108549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212607387474414788171405699 318911081211622182257108549)
      ·
        refine ⟨59795827727179159173207853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 318911081211622182257108549 59795827727179159173207853)
        ·
          refine ⟨22423435397692184689952945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59795827727179159173207853 22423435397692184689952945)
          ·
            refine ⟨16817576548269138517464709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22423435397692184689952945 16817576548269138517464709)
            ·
              refine ⟨3153295602800463472024633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16817576548269138517464709 3153295602800463472024633)
              ·
                refine ⟨2364971702100347604018475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3153295602800463472024633 2364971702100347604018475)
                ·
                  refine ⟨3547457553150521406027713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2364971702100347604018475 3547457553150521406027713)
                  ·
                    refine ⟨2660593164862891054520785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3547457553150521406027713 2660593164862891054520785)
                    ·
                      refine ⟨1995444873647168290890589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2660593164862891054520785 1995444873647168290890589)
                      ·
                        rfl

theorem cell23_3886115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 4, 2, 1, 2, 2].length) (baseStart_3886115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3886115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3886115 prefixEnd_3886115 := by exact prefixLift 3886115
  have htrace : WordTrace (prefixWord ++ tailWord_3886115) baseStart_3886115 baseEnd_3886115 := by
    simpa [prefixWord, tailWord_3886115, baseEnd_3886115] using wordTrace_append hprefix tailTrace_3886115
  have hstable : (prefixWord ++ tailWord_3886115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3886115).length < 2 ^ (prefixWord ++ tailWord_3886115).sum := by decide
  have hdescent : baseEnd_3886115 < baseStart_3886115 := by decide
  rcases family_descends (prefixWord ++ tailWord_3886115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3886124 : List Nat := [2, 2, 1, 1, 1, 2, 3, 1, 5, 3, 2]
def baseStart_3886124 : Nat := 118140960795 + 3886124 * 2 ^ 59
def prefixEnd_3886124 : Nat := 4983230072969 + 3 ^ 40 * 3886124 * 2
def baseEnd_3886124 : Nat := 1995449494973058755678047

theorem tailTrace_3886124 : CollatzResearch.WordTrace tailWord_3886124 prefixEnd_3886124 1995449494973058755678047 := by
  unfold tailWord_3886124
  simp only [CollatzResearch.WordTrace]
  refine ⟨70869293286621959992340713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94492391048829279989787617 70869293286621959992340713)
  ·
    refine ⟨53151969964966469994255535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70869293286621959992340713 53151969964966469994255535)
    ·
      refine ⟨79727954947449704991383303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53151969964966469994255535 79727954947449704991383303)
      ·
        refine ⟨119591932421174557487074955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79727954947449704991383303 119591932421174557487074955)
        ·
          refine ⟨179387898631761836230612433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119591932421174557487074955 179387898631761836230612433)
          ·
            refine ⟨134540923973821377172959325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 179387898631761836230612433 134540923973821377172959325)
            ·
              refine ⟨50452846490183016439859747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 134540923973821377172959325 50452846490183016439859747)
              ·
                refine ⟨75679269735274524659789621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50452846490183016439859747 75679269735274524659789621)
                ·
                  refine ⟨7094931537681986686855277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 75679269735274524659789621 7094931537681986686855277)
                  ·
                    refine ⟨2660599326630745007570729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7094931537681986686855277 2660599326630745007570729)
                    ·
                      refine ⟨1995449494973058755678047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2660599326630745007570729 1995449494973058755678047)
                      ·
                        rfl

theorem cell23_3886124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 3, 2].length) (baseStart_3886124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3886124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3886124 prefixEnd_3886124 := by exact prefixLift 3886124
  have htrace : WordTrace (prefixWord ++ tailWord_3886124) baseStart_3886124 baseEnd_3886124 := by
    simpa [prefixWord, tailWord_3886124, baseEnd_3886124] using wordTrace_append hprefix tailTrace_3886124
  have hstable : (prefixWord ++ tailWord_3886124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3886124).length < 2 ^ (prefixWord ++ tailWord_3886124).sum := by decide
  have hdescent : baseEnd_3886124 < baseStart_3886124 := by decide
  rcases family_descends (prefixWord ++ tailWord_3886124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3886141 : List Nat := [1, 4, 1, 3, 1, 2, 2, 1, 3, 3, 2]
def baseStart_3886141 : Nat := 118140960795 + 3886141 * 2 ^ 59
def prefixEnd_3886141 : Nat := 4983230072969 + 3 ^ 40 * 3886141 * 2
def baseEnd_3886141 : Nat := 1995458224144185189165469

theorem tailTrace_3886141 : CollatzResearch.WordTrace tailWord_3886141 prefixEnd_3886141 1995458224144185189165469 := by
  unfold tailWord_3886141
  simp only [CollatzResearch.WordTrace]
  refine ⟨141739206614182331888050277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94492804409454887925366851 141739206614182331888050277)
  ·
    refine ⟨26576101240159187229009427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 141739206614182331888050277 26576101240159187229009427)
    ·
      refine ⟨39864151860238780843514141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26576101240159187229009427 39864151860238780843514141)
      ·
        refine ⟨14949056947589542816317803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39864151860238780843514141 14949056947589542816317803)
        ·
          refine ⟨22423585421384314224476705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14949056947589542816317803 22423585421384314224476705)
          ·
            refine ⟨16817689066038235668357529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22423585421384314224476705 16817689066038235668357529)
            ·
              refine ⟨12613266799528676751268147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16817689066038235668357529 12613266799528676751268147)
              ·
                refine ⟨18919900199293015126902221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12613266799528676751268147 18919900199293015126902221)
                ·
                  refine ⟨7094962574734880672588333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18919900199293015126902221 7094962574734880672588333)
                  ·
                    refine ⟨2660610965525580252220625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7094962574734880672588333 2660610965525580252220625)
                    ·
                      refine ⟨1995458224144185189165469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2660610965525580252220625 1995458224144185189165469)
                      ·
                        rfl

theorem cell23_3886141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 2, 1, 3, 3, 2].length) (baseStart_3886141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3886141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3886141 prefixEnd_3886141 := by exact prefixLift 3886141
  have htrace : WordTrace (prefixWord ++ tailWord_3886141) baseStart_3886141 baseEnd_3886141 := by
    simpa [prefixWord, tailWord_3886141, baseEnd_3886141] using wordTrace_append hprefix tailTrace_3886141
  have hstable : (prefixWord ++ tailWord_3886141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3886141).length < 2 ^ (prefixWord ++ tailWord_3886141).sum := by decide
  have hdescent : baseEnd_3886141 < baseStart_3886141 := by decide
  rcases family_descends (prefixWord ++ tailWord_3886141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3886177 : List Nat := [1, 2, 3, 1, 1, 2, 3, 3, 7]
def baseStart_3886177 : Nat := 118140960795 + 3886177 * 2 ^ 59
def prefixEnd_3886177 : Nat := 4983230072969 + 3 ^ 40 * 3886177 * 2
def baseEnd_3886177 : Nat := 221719634383083005368367

theorem tailTrace_3886177 : CollatzResearch.WordTrace tailWord_3886177 prefixEnd_3886177 221719634383083005368367 := by
  unfold tailWord_3886177
  simp only [CollatzResearch.WordTrace]
  refine ⟨141740519642051910036360785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94493679761367940024240523 141740519642051910036360785)
  ·
    refine ⟨106305389731538932527270589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141740519642051910036360785 106305389731538932527270589)
    ·
      refine ⟨39864521149327099697726471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106305389731538932527270589 39864521149327099697726471)
      ·
        refine ⟨59796781723990649546589707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39864521149327099697726471 59796781723990649546589707)
        ·
          refine ⟨89695172585985974319884561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59796781723990649546589707 89695172585985974319884561)
          ·
            refine ⟨67271379439489480739913421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89695172585985974319884561 67271379439489480739913421)
            ·
              refine ⟨25226767289808555277467533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67271379439489480739913421 25226767289808555277467533)
              ·
                refine ⟨9460037733678208229050325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25226767289808555277467533 9460037733678208229050325)
                ·
                  refine ⟨221719634383083005368367, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9460037733678208229050325 221719634383083005368367)
                  ·
                    rfl

theorem cell23_3886177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 3, 3, 7].length) (baseStart_3886177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3886177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3886177 prefixEnd_3886177 := by exact prefixLift 3886177
  have htrace : WordTrace (prefixWord ++ tailWord_3886177) baseStart_3886177 baseEnd_3886177 := by
    simpa [prefixWord, tailWord_3886177, baseEnd_3886177] using wordTrace_append hprefix tailTrace_3886177
  have hstable : (prefixWord ++ tailWord_3886177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3886177).length < 2 ^ (prefixWord ++ tailWord_3886177).sum := by decide
  have hdescent : baseEnd_3886177 < baseStart_3886177 := by decide
  rcases family_descends (prefixWord ++ tailWord_3886177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3886207 : List Nat := [1, 1, 2, 2, 1, 1, 1, 1, 8, 5]
def baseStart_3886207 : Nat := 118140960795 + 3886207 * 2 ^ 59
def prefixEnd_3886207 : Nat := 4983230072969 + 3 ^ 40 * 3886207 * 2
def baseEnd_3886207 : Nat := 665164037955793976980055

theorem tailTrace_3886207 : CollatzResearch.WordTrace tailWord_3886207 prefixEnd_3886207 665164037955793976980055 := by
  unfold tailWord_3886207
  simp only [CollatzResearch.WordTrace]
  refine ⟨141741613831943225159952875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94494409221295483439968583 141741613831943225159952875)
  ·
    refine ⟨212612420747914837739929313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141741613831943225159952875 212612420747914837739929313)
    ·
      refine ⟨159459315560936128304946985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 212612420747914837739929313 159459315560936128304946985)
      ·
        refine ⟨119594486670702096228710239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159459315560936128304946985 119594486670702096228710239)
        ·
          refine ⟨179391730006053144343065359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119594486670702096228710239 179391730006053144343065359)
          ·
            refine ⟨269087595009079716514598039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 179391730006053144343065359 269087595009079716514598039)
            ·
              refine ⟨403631392513619574771897059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 269087595009079716514598039 403631392513619574771897059)
              ·
                refine ⟨605447088770429362157845589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 403631392513619574771897059 605447088770429362157845589)
                ·
                  refine ⟨7095083071528469087787253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 605447088770429362157845589 7095083071528469087787253)
                  ·
                    refine ⟨665164037955793976980055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7095083071528469087787253 665164037955793976980055)
                    ·
                      rfl

theorem cell23_3886207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 1, 8, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 1, 8, 5].length) (baseStart_3886207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3886207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3886207 prefixEnd_3886207 := by exact prefixLift 3886207
  have htrace : WordTrace (prefixWord ++ tailWord_3886207) baseStart_3886207 baseEnd_3886207 := by
    simpa [prefixWord, tailWord_3886207, baseEnd_3886207] using wordTrace_append hprefix tailTrace_3886207
  have hstable : (prefixWord ++ tailWord_3886207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3886207).length < 2 ^ (prefixWord ++ tailWord_3886207).sum := by decide
  have hdescent : baseEnd_3886207 < baseStart_3886207 := by decide
  rcases family_descends (prefixWord ++ tailWord_3886207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3886234 : List Nat := [3, 1, 1, 5, 1, 1, 1, 1, 1, 1, 7]
def baseStart_3886234 : Nat := 118140960795 + 3886234 * 2 ^ 59
def prefixEnd_3886234 : Nat := 4983230072969 + 3 ^ 40 * 3886234 * 2
def baseEnd_3886234 : Nat := 1995505977845053325302541

theorem tailTrace_3886234 : CollatzResearch.WordTrace tailWord_3886234 prefixEnd_3886234 1995505977845053325302541 := by
  unfold tailWord_3886234
  simp only [CollatzResearch.WordTrace]
  refine ⟨35435649650711352192796439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94495065735230272514123837 35435649650711352192796439)
  ·
    refine ⟨53153474476067028289194659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35435649650711352192796439 53153474476067028289194659)
    ·
      refine ⟨79730211714100542433791989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53153474476067028289194659 79730211714100542433791989)
      ·
        refine ⟨7474707348196925853167999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 79730211714100542433791989 7474707348196925853167999)
        ·
          refine ⟨11212061022295388779751999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7474707348196925853167999 11212061022295388779751999)
          ·
            refine ⟨16818091533443083169627999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11212061022295388779751999 16818091533443083169627999)
            ·
              refine ⟨25227137300164624754441999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16818091533443083169627999 25227137300164624754441999)
              ·
                refine ⟨37840705950246937131662999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25227137300164624754441999 37840705950246937131662999)
                ·
                  refine ⟨56761058925370405697494499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37840705950246937131662999 56761058925370405697494499)
                  ·
                    refine ⟨85141588388055608546241749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 56761058925370405697494499 85141588388055608546241749)
                    ·
                      refine ⟨1995505977845053325302541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 85141588388055608546241749 1995505977845053325302541)
                      ·
                        rfl

theorem cell23_3886234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 1, 1, 1, 1, 7].length) (baseStart_3886234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3886234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3886234 prefixEnd_3886234 := by exact prefixLift 3886234
  have htrace : WordTrace (prefixWord ++ tailWord_3886234) baseStart_3886234 baseEnd_3886234 := by
    simpa [prefixWord, tailWord_3886234, baseEnd_3886234] using wordTrace_append hprefix tailTrace_3886234
  have hstable : (prefixWord ++ tailWord_3886234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3886234).length < 2 ^ (prefixWord ++ tailWord_3886234).sum := by decide
  have hdescent : baseEnd_3886234 < baseStart_3886234 := by decide
  rcases family_descends (prefixWord ++ tailWord_3886234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3886239 : List Nat := [1, 1, 2, 6, 3, 1, 2, 1, 2, 2, 2]
def baseStart_3886239 : Nat := 118140960795 + 3886239 * 2 ^ 59
def prefixEnd_3886239 : Nat := 4983230072969 + 3 ^ 40 * 3886239 * 2
def baseEnd_3886239 : Nat := 1995508545248325805740019

theorem tailTrace_3886239 : CollatzResearch.WordTrace tailWord_3886239 prefixEnd_3886239 1995508545248325805740019 := by
  unfold tailWord_3886239
  simp only [CollatzResearch.WordTrace]
  refine ⟨141742780967827294625117771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94495187311884863083411847 141742780967827294625117771)
  ·
    refine ⟨212614171451740941937676657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141742780967827294625117771 212614171451740941937676657)
    ·
      refine ⟨159460628588805706453257493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 212614171451740941937676657 159460628588805706453257493)
      ·
        refine ⟨7474716965100267489996445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 159460628588805706453257493 7474716965100267489996445)
        ·
          refine ⟨2803018861912600308748667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7474716965100267489996445 2803018861912600308748667)
          ·
            refine ⟨4204528292868900463123001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2803018861912600308748667 4204528292868900463123001)
            ·
              refine ⟨3153396219651675347342251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4204528292868900463123001 3153396219651675347342251)
              ·
                refine ⟨4730094329477513021013377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3153396219651675347342251 4730094329477513021013377)
                ·
                  refine ⟨3547570747108134765760033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4730094329477513021013377 3547570747108134765760033)
                  ·
                    refine ⟨2660678060331101074320025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3547570747108134765760033 2660678060331101074320025)
                    ·
                      refine ⟨1995508545248325805740019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2660678060331101074320025 1995508545248325805740019)
                      ·
                        rfl

theorem cell23_3886239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 3, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 3, 1, 2, 1, 2, 2, 2].length) (baseStart_3886239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3886239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3886239 prefixEnd_3886239 := by exact prefixLift 3886239
  have htrace : WordTrace (prefixWord ++ tailWord_3886239) baseStart_3886239 baseEnd_3886239 := by
    simpa [prefixWord, tailWord_3886239, baseEnd_3886239] using wordTrace_append hprefix tailTrace_3886239
  have hstable : (prefixWord ++ tailWord_3886239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3886239).length < 2 ^ (prefixWord ++ tailWord_3886239).sum := by decide
  have hdescent : baseEnd_3886239 < baseStart_3886239 := by decide
  rcases family_descends (prefixWord ++ tailWord_3886239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3886267 : List Nat := [1, 1, 1, 1, 1, 2, 4, 4, 8]
def baseStart_3886267 : Nat := 118140960795 + 3886267 * 2 ^ 59
def prefixEnd_3886267 : Nat := 4983230072969 + 3 ^ 40 * 3886267 * 2
def baseEnd_3886267 : Nat := 221724769189627966243321

theorem tailTrace_3886267 : CollatzResearch.WordTrace tailWord_3886267 prefixEnd_3886267 221724769189627966243321 := by
  unfold tailWord_3886267
  simp only [CollatzResearch.WordTrace]
  refine ⟨141743802211725855407137055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94495868141150570271424703 141743802211725855407137055)
  ·
    refine ⟨212615703317588783110705583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141743802211725855407137055 212615703317588783110705583)
    ·
      refine ⟨318923554976383174666058375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212615703317588783110705583 318923554976383174666058375)
      ·
        refine ⟨478385332464574761999087563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 318923554976383174666058375 478385332464574761999087563)
        ·
          refine ⟨717577998696862142998631345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 478385332464574761999087563 717577998696862142998631345)
          ·
            refine ⟨538183499022646607248973509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 717577998696862142998631345 538183499022646607248973509)
            ·
              refine ⟨100909406066746238859182533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 538183499022646607248973509 100909406066746238859182533)
              ·
                refine ⟨18920513637514919786096725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 100909406066746238859182533 18920513637514919786096725)
                ·
                  refine ⟨221724769189627966243321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 18920513637514919786096725 221724769189627966243321)
                  ·
                    rfl

theorem cell23_3886267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 4, 8].length) (baseStart_3886267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3886267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3886267 prefixEnd_3886267 := by exact prefixLift 3886267
  have htrace : WordTrace (prefixWord ++ tailWord_3886267) baseStart_3886267 baseEnd_3886267 := by
    simpa [prefixWord, tailWord_3886267, baseEnd_3886267] using wordTrace_append hprefix tailTrace_3886267
  have hstable : (prefixWord ++ tailWord_3886267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3886267).length < 2 ^ (prefixWord ++ tailWord_3886267).sum := by decide
  have hdescent : baseEnd_3886267 < baseStart_3886267 := by decide
  rcases family_descends (prefixWord ++ tailWord_3886267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3886378 : List Nat := [3, 1, 4, 2, 1, 1, 1, 2, 4, 4]
def baseStart_3886378 : Nat := 118140960795 + 3886378 * 2 ^ 59
def prefixEnd_3886378 : Nat := 4983230072969 + 3 ^ 40 * 3886378 * 2
def baseEnd_3886378 : Nat := 665193306353100253967293

theorem tailTrace_3886378 : CollatzResearch.WordTrace tailWord_3886378 prefixEnd_3886378 665193306353100253967293 := by
  unfold tailWord_3886378
  simp only [CollatzResearch.WordTrace]
  refine ⟨35436962678580930341106947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94498567142882480909618525 35436962678580930341106947)
  ·
    refine ⟨53155444017871395511660421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35436962678580930341106947 53155444017871395511660421)
    ·
      refine ⟨9966645753350886658436329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 53155444017871395511660421 9966645753350886658436329)
      ·
        refine ⟨7474984315013164993827247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9966645753350886658436329 7474984315013164993827247)
        ·
          refine ⟨11212476472519747490740871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7474984315013164993827247 11212476472519747490740871)
          ·
            refine ⟨16818714708779621236111307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11212476472519747490740871 16818714708779621236111307)
            ·
              refine ⟨25228072063169431854166961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16818714708779621236111307 25228072063169431854166961)
              ·
                refine ⟨18921054047377073890625221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25228072063169431854166961 18921054047377073890625221)
                ·
                  refine ⟨3547697633883201354492229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18921054047377073890625221 3547697633883201354492229)
                  ·
                    refine ⟨665193306353100253967293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3547697633883201354492229 665193306353100253967293)
                    ·
                      rfl

theorem cell23_3886378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 1, 2, 4, 4].length) (baseStart_3886378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3886378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3886378 prefixEnd_3886378 := by exact prefixLift 3886378
  have htrace : WordTrace (prefixWord ++ tailWord_3886378) baseStart_3886378 baseEnd_3886378 := by
    simpa [prefixWord, tailWord_3886378, baseEnd_3886378] using wordTrace_append hprefix tailTrace_3886378
  have hstable : (prefixWord ++ tailWord_3886378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3886378).length < 2 ^ (prefixWord ++ tailWord_3886378).sum := by decide
  have hdescent : baseEnd_3886378 < baseStart_3886378 := by decide
  rcases family_descends (prefixWord ++ tailWord_3886378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3886388 : List Nat := [2, 5, 1, 1, 1, 1, 4, 1, 1, 1, 5]
def baseStart_3886388 : Nat := 118140960795 + 3886388 * 2 ^ 59
def prefixEnd_3886388 : Nat := 4983230072969 + 3 ^ 40 * 3886388 * 2
def baseEnd_3886388 : Nat := 1995585053865845722776833

theorem tailTrace_3886388 : CollatzResearch.WordTrace tailWord_3886388 prefixEnd_3886388 1995585053865845722776833 := by
  unfold tailWord_3886388
  simp only [CollatzResearch.WordTrace]
  refine ⟨70874107722143746536145909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94498810296191662048194545 70874107722143746536145909)
  ·
    refine ⟨6644447598950976237763679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 70874107722143746536145909 6644447598950976237763679)
    ·
      refine ⟨9966671398426464356645519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6644447598950976237763679 9966671398426464356645519)
      ·
        refine ⟨14950007097639696534968279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9966671398426464356645519 14950007097639696534968279)
        ·
          refine ⟨22425010646459544802452419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14950007097639696534968279 22425010646459544802452419)
          ·
            refine ⟨33637515969689317203678629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22425010646459544802452419 33637515969689317203678629)
            ·
              refine ⟨6307034244316746975689743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33637515969689317203678629 6307034244316746975689743)
              ·
                refine ⟨9460551366475120463534615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6307034244316746975689743 9460551366475120463534615)
                ·
                  refine ⟨14190827049712680695301923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9460551366475120463534615 14190827049712680695301923)
                  ·
                    refine ⟨21286240574569021042952885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14190827049712680695301923 21286240574569021042952885)
                    ·
                      refine ⟨1995585053865845722776833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21286240574569021042952885 1995585053865845722776833)
                      ·
                        rfl

theorem cell23_3886388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 4, 1, 1, 1, 5].length) (baseStart_3886388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3886388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3886388 prefixEnd_3886388 := by exact prefixLift 3886388
  have htrace : WordTrace (prefixWord ++ tailWord_3886388) baseStart_3886388 baseEnd_3886388 := by
    simpa [prefixWord, tailWord_3886388, baseEnd_3886388] using wordTrace_append hprefix tailTrace_3886388
  have hstable : (prefixWord ++ tailWord_3886388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3886388).length < 2 ^ (prefixWord ++ tailWord_3886388).sum := by decide
  have hdescent : baseEnd_3886388 < baseStart_3886388 := by decide
  rcases family_descends (prefixWord ++ tailWord_3886388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3886453 : List Nat := [1, 3, 4, 1, 4, 1, 2, 2, 1, 2, 2]
def baseStart_3886453 : Nat := 118140960795 + 3886453 * 2 ^ 59
def prefixEnd_3886453 : Nat := 4983230072969 + 3 ^ 40 * 3886453 * 2
def baseEnd_3886453 : Nat := 1995618430108387968464035

theorem tailTrace_3886453 : CollatzResearch.WordTrace tailWord_3886453 prefixEnd_3886453 1995618430108387968464035 := by
  unfold tailWord_3886453
  simp only [CollatzResearch.WordTrace]
  refine ⟨141750586189052009173408013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94500390792701339448938675 141750586189052009173408013)
  ·
    refine ⟨53156469820894503440028005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 141750586189052009173408013 53156469820894503440028005)
    ·
      refine ⟨9966838091417719395005251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 53156469820894503440028005 9966838091417719395005251)
      ·
        refine ⟨14950257137126579092507877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9966838091417719395005251 14950257137126579092507877)
        ·
          refine ⟨2803173213211233579845227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14950257137126579092507877 2803173213211233579845227)
          ·
            refine ⟨4204759819816850369767841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2803173213211233579845227 4204759819816850369767841)
            ·
              refine ⟨3153569864862637777325881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4204759819816850369767841 3153569864862637777325881)
              ·
                refine ⟨2365177398646978332994411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3153569864862637777325881 2365177398646978332994411)
                ·
                  refine ⟨3547766097970467499491617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2365177398646978332994411 3547766097970467499491617)
                  ·
                    refine ⟨2660824573477850624618713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3547766097970467499491617 2660824573477850624618713)
                    ·
                      refine ⟨1995618430108387968464035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2660824573477850624618713 1995618430108387968464035)
                      ·
                        rfl

theorem cell23_3886453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 4, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 4, 1, 2, 2, 1, 2, 2].length) (baseStart_3886453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3886453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3886453 prefixEnd_3886453 := by exact prefixLift 3886453
  have htrace : WordTrace (prefixWord ++ tailWord_3886453) baseStart_3886453 baseEnd_3886453 := by
    simpa [prefixWord, tailWord_3886453, baseEnd_3886453] using wordTrace_append hprefix tailTrace_3886453
  have hstable : (prefixWord ++ tailWord_3886453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3886453).length < 2 ^ (prefixWord ++ tailWord_3886453).sum := by decide
  have hdescent : baseEnd_3886453 < baseStart_3886453 := by decide
  rcases family_descends (prefixWord ++ tailWord_3886453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3886461 : List Nat := [1, 4, 1, 1, 2, 2, 1, 1, 1, 6, 3]
def baseStart_3886461 : Nat := 118140960795 + 3886461 * 2 ^ 59
def prefixEnd_3886461 : Nat := 4983230072969 + 3 ^ 40 * 3886461 * 2
def baseEnd_3886461 : Nat := 1995622537953623937163997

theorem tailTrace_3886461 : CollatzResearch.WordTrace tailWord_3886461 prefixEnd_3886461 1995622537953623937163997 := by
  unfold tailWord_3886461
  simp only [CollatzResearch.WordTrace]
  refine ⟨141750877973023026539699237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94500585315348684359799491 141750877973023026539699237)
  ·
    refine ⟨26578289619941817476193607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 141750877973023026539699237 26578289619941817476193607)
    ·
      refine ⟨39867434429912726214290411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26578289619941817476193607 39867434429912726214290411)
      ·
        refine ⟨59801151644869089321435617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39867434429912726214290411 59801151644869089321435617)
        ·
          refine ⟨44850863733651816991076713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59801151644869089321435617 44850863733651816991076713)
          ·
            refine ⟨33638147800238862743307535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44850863733651816991076713 33638147800238862743307535)
            ·
              refine ⟨50457221700358294114961303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33638147800238862743307535 50457221700358294114961303)
              ·
                refine ⟨75685832550537441172441955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50457221700358294114961303 75685832550537441172441955)
                ·
                  refine ⟨113528748825806161758662933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 75685832550537441172441955 113528748825806161758662933)
                  ·
                    refine ⟨5321660101209663832437325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 113528748825806161758662933 5321660101209663832437325)
                    ·
                      refine ⟨1995622537953623937163997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5321660101209663832437325 1995622537953623937163997)
                      ·
                        rfl

theorem cell23_3886461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 1, 1, 6, 3].length) (baseStart_3886461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3886461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3886461 prefixEnd_3886461 := by exact prefixLift 3886461
  have htrace : WordTrace (prefixWord ++ tailWord_3886461) baseStart_3886461 baseEnd_3886461 := by
    simpa [prefixWord, tailWord_3886461, baseEnd_3886461] using wordTrace_append hprefix tailTrace_3886461
  have hstable : (prefixWord ++ tailWord_3886461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3886461).length < 2 ^ (prefixWord ++ tailWord_3886461).sum := by decide
  have hdescent : baseEnd_3886461 < baseStart_3886461 := by decide
  rcases family_descends (prefixWord ++ tailWord_3886461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3886464 : List Nat := [2, 1, 1, 2, 1, 2, 1, 2, 11]
def baseStart_3886464 : Nat := 118140960795 + 3886464 * 2 ^ 59
def prefixEnd_3886464 : Nat := 4983230072969 + 3 ^ 40 * 3886464 * 2
def baseEnd_3886464 : Nat := 221736008710620825047387

theorem tailTrace_3886464 : CollatzResearch.WordTrace tailWord_3886464 prefixEnd_3886464 221736008710620825047387 := by
  unfold tailWord_3886464
  simp only [CollatzResearch.WordTrace]
  refine ⟨70875493696006079026029223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94500658261341438701372297 70875493696006079026029223)
  ·
    refine ⟨106313240544009118539043835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70875493696006079026029223 106313240544009118539043835)
    ·
      refine ⟨159469860816013677808565753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106313240544009118539043835 159469860816013677808565753)
      ·
        refine ⟨119602395612010258356424315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159469860816013677808565753 119602395612010258356424315)
        ·
          refine ⟨179403593418015387534636473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119602395612010258356424315 179403593418015387534636473)
          ·
            refine ⟨134552695063511540650977355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 179403593418015387534636473 134552695063511540650977355)
            ·
              refine ⟨201829042595267310976466033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 134552695063511540650977355 201829042595267310976466033)
              ·
                refine ⟨151371781946450483232349525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 201829042595267310976466033 151371781946450483232349525)
                ·
                  refine ⟨221736008710620825047387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 151371781946450483232349525 221736008710620825047387)
                  ·
                    rfl

theorem cell23_3886464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 2, 11].length) (baseStart_3886464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3886464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3886464 prefixEnd_3886464 := by exact prefixLift 3886464
  have htrace : WordTrace (prefixWord ++ tailWord_3886464) baseStart_3886464 baseEnd_3886464 := by
    simpa [prefixWord, tailWord_3886464, baseEnd_3886464] using wordTrace_append hprefix tailTrace_3886464
  have hstable : (prefixWord ++ tailWord_3886464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3886464).length < 2 ^ (prefixWord ++ tailWord_3886464).sum := by decide
  have hdescent : baseEnd_3886464 < baseStart_3886464 := by decide
  rcases family_descends (prefixWord ++ tailWord_3886464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3886471 : List Nat := [1, 1, 4, 2, 2, 2, 1, 1, 1, 4, 4]
def baseStart_3886471 : Nat := 118140960795 + 3886471 * 2 ^ 59
def prefixEnd_3886471 : Nat := 4983230072969 + 3 ^ 40 * 3886471 * 2
def baseEnd_3886471 : Nat := 1995627672760168898038951

theorem tailTrace_3886471 : CollatzResearch.WordTrace tailWord_3886471 prefixEnd_3886471 1995627672760168898038951 := by
  unfold tailWord_3886471
  simp only [CollatzResearch.WordTrace]
  refine ⟨141751242702986798247563267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94500828468657865498375511 141751242702986798247563267)
  ·
    refine ⟨212626864054480197371344901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141751242702986798247563267 212626864054480197371344901)
    ·
      refine ⟨39867537010215037007127169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 212626864054480197371344901 39867537010215037007127169)
      ·
        refine ⟨29900652757661277755345377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39867537010215037007127169 29900652757661277755345377)
        ·
          refine ⟨22425489568245958316509033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29900652757661277755345377 22425489568245958316509033)
          ·
            refine ⟨16819117176184468737381775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22425489568245958316509033 16819117176184468737381775)
            ·
              refine ⟨25228675764276703106072663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16819117176184468737381775 25228675764276703106072663)
              ·
                refine ⟨37843013646415054659108995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25228675764276703106072663 37843013646415054659108995)
                ·
                  refine ⟨56764520469622581988663493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37843013646415054659108995 56764520469622581988663493)
                  ·
                    refine ⟨10643347588054234122874405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 56764520469622581988663493 10643347588054234122874405)
                    ·
                      refine ⟨1995627672760168898038951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10643347588054234122874405 1995627672760168898038951)
                      ·
                        rfl

theorem cell23_3886471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 1, 1, 1, 4, 4].length) (baseStart_3886471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3886471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3886471 prefixEnd_3886471 := by exact prefixLift 3886471
  have htrace : WordTrace (prefixWord ++ tailWord_3886471) baseStart_3886471 baseEnd_3886471 := by
    simpa [prefixWord, tailWord_3886471, baseEnd_3886471] using wordTrace_append hprefix tailTrace_3886471
  have hstable : (prefixWord ++ tailWord_3886471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3886471).length < 2 ^ (prefixWord ++ tailWord_3886471).sum := by decide
  have hdescent : baseEnd_3886471 < baseStart_3886471 := by decide
  rcases family_descends (prefixWord ++ tailWord_3886471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3886475 : List Nat := [1, 1, 1, 1, 4, 3, 1, 5, 2, 2, 2]
def baseStart_3886475 : Nat := 118140960795 + 3886475 * 2 ^ 59
def prefixEnd_3886475 : Nat := 4983230072969 + 3 ^ 40 * 3886475 * 2
def baseEnd_3886475 : Nat := 1995629726682786882388933

theorem tailTrace_3886475 : CollatzResearch.WordTrace tailWord_3886475 prefixEnd_3886475 1995629726682786882388933 := by
  unfold tailWord_3886475
  simp only [CollatzResearch.WordTrace]
  refine ⟨141751388594972306930708879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94500925729981537953805919 141751388594972306930708879)
  ·
    refine ⟨212627082892458460396063319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141751388594972306930708879 212627082892458460396063319)
    ·
      refine ⟨318940624338687690594094979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212627082892458460396063319 318940624338687690594094979)
      ·
        refine ⟨478410936508031535891142469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 318940624338687690594094979 478410936508031535891142469)
        ·
          refine ⟨89702050595255912979589213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 478410936508031535891142469 89702050595255912979589213)
          ·
            refine ⟨33638268973220967367345955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 89702050595255912979589213 33638268973220967367345955)
            ·
              refine ⟨50457403459831451051018933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33638268973220967367345955 50457403459831451051018933)
              ·
                refine ⟨4730381574359198536033025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 50457403459831451051018933 4730381574359198536033025)
                ·
                  refine ⟨3547786180769398902024769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4730381574359198536033025 3547786180769398902024769)
                  ·
                    refine ⟨2660839635577049176518577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3547786180769398902024769 2660839635577049176518577)
                    ·
                      refine ⟨1995629726682786882388933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2660839635577049176518577 1995629726682786882388933)
                      ·
                        rfl

theorem cell23_3886475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 5, 2, 2, 2].length) (baseStart_3886475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3886475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3886475 prefixEnd_3886475 := by exact prefixLift 3886475
  have htrace : WordTrace (prefixWord ++ tailWord_3886475) baseStart_3886475 baseEnd_3886475 := by
    simpa [prefixWord, tailWord_3886475, baseEnd_3886475] using wordTrace_append hprefix tailTrace_3886475
  have hstable : (prefixWord ++ tailWord_3886475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3886475).length < 2 ^ (prefixWord ++ tailWord_3886475).sum := by decide
  have hdescent : baseEnd_3886475 < baseStart_3886475 := by decide
  rcases family_descends (prefixWord ++ tailWord_3886475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3886509 : List Nat := [1, 5, 2, 2, 1, 1, 3, 2, 2, 2, 2]
def baseStart_3886509 : Nat := 118140960795 + 3886509 * 2 ^ 59
def prefixEnd_3886509 : Nat := 4983230072969 + 3 ^ 40 * 3886509 * 2
def baseEnd_3886509 : Nat := 1995647185025039749363777

theorem tailTrace_3886509 : CollatzResearch.WordTrace tailWord_3886509 prefixEnd_3886509 1995647185025039749363777 := by
  unfold tailWord_3886509
  simp only [CollatzResearch.WordTrace]
  refine ⟨141752628676849130737446581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94501752451232753824964387 141752628676849130737446581)
  ·
    refine ⟨13289308938454606006635617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 141752628676849130737446581 13289308938454606006635617)
    ·
      refine ⟨9966981703840954504976713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13289308938454606006635617 9966981703840954504976713)
      ·
        refine ⟨7475236277880715878732535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9966981703840954504976713 7475236277880715878732535)
        ·
          refine ⟨11212854416821073818098803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7475236277880715878732535 11212854416821073818098803)
          ·
            refine ⟨16819281625231610727148205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11212854416821073818098803 16819281625231610727148205)
            ·
              refine ⟨6307230609461854022680577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16819281625231610727148205 6307230609461854022680577)
              ·
                refine ⟨4730422957096390517010433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6307230609461854022680577 4730422957096390517010433)
                ·
                  refine ⟨3547817217822292887757825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4730422957096390517010433 3547817217822292887757825)
                  ·
                    refine ⟨2660862913366719665818369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3547817217822292887757825 2660862913366719665818369)
                    ·
                      refine ⟨1995647185025039749363777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2660862913366719665818369 1995647185025039749363777)
                      ·
                        rfl

theorem cell23_3886509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 3, 2, 2, 2, 2].length) (baseStart_3886509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3886509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3886509 prefixEnd_3886509 := by exact prefixLift 3886509
  have htrace : WordTrace (prefixWord ++ tailWord_3886509) baseStart_3886509 baseEnd_3886509 := by
    simpa [prefixWord, tailWord_3886509, baseEnd_3886509] using wordTrace_append hprefix tailTrace_3886509
  have hstable : (prefixWord ++ tailWord_3886509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3886509).length < 2 ^ (prefixWord ++ tailWord_3886509).sum := by decide
  have hdescent : baseEnd_3886509 < baseStart_3886509 := by decide
  rcases family_descends (prefixWord ++ tailWord_3886509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3886511 : List Nat := [1, 1, 2, 1, 2, 2, 1, 6, 2, 5]
def baseStart_3886511 : Nat := 118140960795 + 3886511 * 2 ^ 59
def prefixEnd_3886511 : Nat := 4983230072969 + 3 ^ 40 * 3886511 * 2
def baseEnd_3886511 : Nat := 665216070662116247179589

theorem tailTrace_3886511 : CollatzResearch.WordTrace tailWord_3886511 prefixEnd_3886511 665216070662116247179589 := by
  unfold tailWord_3886511
  simp only [CollatzResearch.WordTrace]
  refine ⟨141752701622841885079019387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94501801081894590052679591 141752701622841885079019387)
  ·
    refine ⟨212629052434262827618529081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141752701622841885079019387 212629052434262827618529081)
    ·
      refine ⟨159471789325697120713896811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 212629052434262827618529081 159471789325697120713896811)
      ·
        refine ⟨239207683988545681070845217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159471789325697120713896811 239207683988545681070845217)
        ·
          refine ⟨179405762991409260803133913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 239207683988545681070845217 179405762991409260803133913)
          ·
            refine ⟨134554322243556945602350435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 179405762991409260803133913 134554322243556945602350435)
            ·
              refine ⟨201831483365335418403525653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 134554322243556945602350435 201831483365335418403525653)
              ·
                refine ⟨9460850782750097737665265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 201831483365335418403525653 9460850782750097737665265)
                ·
                  refine ⟨7095638087062573303248949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9460850782750097737665265 7095638087062573303248949)
                  ·
                    refine ⟨665216070662116247179589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7095638087062573303248949 665216070662116247179589)
                    ·
                      rfl

theorem cell23_3886511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 6, 2, 5].length) (baseStart_3886511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3886511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3886511 prefixEnd_3886511 := by exact prefixLift 3886511
  have htrace : WordTrace (prefixWord ++ tailWord_3886511) baseStart_3886511 baseEnd_3886511 := by
    simpa [prefixWord, tailWord_3886511, baseEnd_3886511] using wordTrace_append hprefix tailTrace_3886511
  have hstable : (prefixWord ++ tailWord_3886511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3886511).length < 2 ^ (prefixWord ++ tailWord_3886511).sum := by decide
  have hdescent : baseEnd_3886511 < baseStart_3886511 := by decide
  rcases family_descends (prefixWord ++ tailWord_3886511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3886531 : List Nat := [1, 1, 1, 3, 1, 1, 5, 2, 1, 3, 4]
def baseStart_3886531 : Nat := 118140960795 + 3886531 * 2 ^ 59
def prefixEnd_3886531 : Nat := 4983230072969 + 3 ^ 40 * 3886531 * 2
def baseEnd_3886531 : Nat := 1995658481599438663288675

theorem tailTrace_3886531 : CollatzResearch.WordTrace tailWord_3886531 prefixEnd_3886531 1995658481599438663288675 := by
  unfold tailWord_3886531
  simp only [CollatzResearch.WordTrace]
  refine ⟨141753431082769428494747447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94502287388512952329831631 141753431082769428494747447)
  ·
    refine ⟨212630146624154142742121171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141753431082769428494747447 212630146624154142742121171)
    ·
      refine ⟨318945219936231214113181757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212630146624154142742121171 318945219936231214113181757)
      ·
        refine ⟨119604457476086705292443159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 318945219936231214113181757 119604457476086705292443159)
        ·
          refine ⟨179406686214130057938664739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119604457476086705292443159 179406686214130057938664739)
          ·
            refine ⟨269110029321195086907997109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 179406686214130057938664739 269110029321195086907997109)
            ·
              refine ⟨25229065248862039397624729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 269110029321195086907997109 25229065248862039397624729)
              ·
                refine ⟨18921798936646529548218547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25229065248862039397624729 18921798936646529548218547)
                ·
                  refine ⟨28382698404969794322327821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18921798936646529548218547 28382698404969794322327821)
                  ·
                    refine ⟨10643511901863672870872933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28382698404969794322327821 10643511901863672870872933)
                    ·
                      refine ⟨1995658481599438663288675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10643511901863672870872933 1995658481599438663288675)
                      ·
                        rfl

theorem cell23_3886531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 5, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 5, 2, 1, 3, 4].length) (baseStart_3886531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3886531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3886531 prefixEnd_3886531 := by exact prefixLift 3886531
  have htrace : WordTrace (prefixWord ++ tailWord_3886531) baseStart_3886531 baseEnd_3886531 := by
    simpa [prefixWord, tailWord_3886531, baseEnd_3886531] using wordTrace_append hprefix tailTrace_3886531
  have hstable : (prefixWord ++ tailWord_3886531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3886531).length < 2 ^ (prefixWord ++ tailWord_3886531).sum := by decide
  have hdescent : baseEnd_3886531 < baseStart_3886531 := by decide
  rcases family_descends (prefixWord ++ tailWord_3886531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3886565 : List Nat := [1, 3, 1, 5, 1, 2, 1, 2, 2, 1, 4]
def baseStart_3886565 : Nat := 118140960795 + 3886565 * 2 ^ 59
def prefixEnd_3886565 : Nat := 4983230072969 + 3 ^ 40 * 3886565 * 2
def baseEnd_3886565 : Nat := 1995675939941691530263519

theorem tailTrace_3886565 : CollatzResearch.WordTrace tailWord_3886565 prefixEnd_3886565 1995675939941691530263519 := by
  unfold tailWord_3886565
  simp only [CollatzResearch.WordTrace]
  refine ⟨141754671164646252301485149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94503114109764168200990099 141754671164646252301485149)
  ·
    refine ⟨53158001686742344613056931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 141754671164646252301485149 53158001686742344613056931)
    ·
      refine ⟨79737002530113516919585397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53158001686742344613056931 79737002530113516919585397)
      ·
        refine ⟨7475343987198142211211131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 79737002530113516919585397 7475343987198142211211131)
        ·
          refine ⟨11213015980797213316816697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7475343987198142211211131 11213015980797213316816697)
          ·
            refine ⟨8409761985597909987612523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11213015980797213316816697 8409761985597909987612523)
            ·
              refine ⟨12614642978396864981418785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8409761985597909987612523 12614642978396864981418785)
              ·
                refine ⟨9460982233797648736064089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12614642978396864981418785 9460982233797648736064089)
                ·
                  refine ⟨7095736675348236552048067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9460982233797648736064089 7095736675348236552048067)
                  ·
                    refine ⟨10643605013022354828072101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7095736675348236552048067 10643605013022354828072101)
                    ·
                      refine ⟨1995675939941691530263519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10643605013022354828072101 1995675939941691530263519)
                      ·
                        rfl

theorem cell23_3886565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 1, 2, 2, 1, 4].length) (baseStart_3886565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3886565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3886565 prefixEnd_3886565 := by exact prefixLift 3886565
  have htrace : WordTrace (prefixWord ++ tailWord_3886565) baseStart_3886565 baseEnd_3886565 := by
    simpa [prefixWord, tailWord_3886565, baseEnd_3886565] using wordTrace_append hprefix tailTrace_3886565
  have hstable : (prefixWord ++ tailWord_3886565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3886565).length < 2 ^ (prefixWord ++ tailWord_3886565).sum := by decide
  have hdescent : baseEnd_3886565 < baseStart_3886565 := by decide
  rcases family_descends (prefixWord ++ tailWord_3886565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3886575 : List Nat := [1, 1, 2, 1, 4, 1, 2, 6, 1, 4]
def baseStart_3886575 : Nat := 118140960795 + 3886575 * 2 ^ 59
def prefixEnd_3886575 : Nat := 4983230072969 + 3 ^ 40 * 3886575 * 2
def baseEnd_3886575 : Nat := 665227024916078830379491

theorem tailTrace_3886575 : CollatzResearch.WordTrace tailWord_3886575 prefixEnd_3886575 665227024916078830379491 := by
  unfold tailWord_3886575
  simp only [CollatzResearch.WordTrace]
  refine ⟨141755035894610024009349179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94503357263073349339566119 141755035894610024009349179)
  ·
    refine ⟨212632553841915036014023769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141755035894610024009349179 212632553841915036014023769)
    ·
      refine ⟨159474415381436277010517827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 212632553841915036014023769 159474415381436277010517827)
      ·
        refine ⟨239211623072154415515776741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159474415381436277010517827 239211623072154415515776741)
        ·
          refine ⟨44852179326028952909208139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 239211623072154415515776741 44852179326028952909208139)
          ·
            refine ⟨67278268989043429363812209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44852179326028952909208139 67278268989043429363812209)
            ·
              refine ⟨50458701741782572022859157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67278268989043429363812209 50458701741782572022859157)
              ·
                refine ⟨2365251644146058063571523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 50458701741782572022859157 2365251644146058063571523)
                ·
                  refine ⟨3547877466219087095357285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2365251644146058063571523 3547877466219087095357285)
                  ·
                    refine ⟨665227024916078830379491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3547877466219087095357285 665227024916078830379491)
                    ·
                      rfl

theorem cell23_3886575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 6, 1, 4].length) (baseStart_3886575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3886575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3886575 prefixEnd_3886575 := by exact prefixLift 3886575
  have htrace : WordTrace (prefixWord ++ tailWord_3886575) baseStart_3886575 baseEnd_3886575 := by
    simpa [prefixWord, tailWord_3886575, baseEnd_3886575] using wordTrace_append hprefix tailTrace_3886575
  have hstable : (prefixWord ++ tailWord_3886575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3886575).length < 2 ^ (prefixWord ++ tailWord_3886575).sum := by decide
  have hdescent : baseEnd_3886575 < baseStart_3886575 := by decide
  rcases family_descends (prefixWord ++ tailWord_3886575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3886648 : List Nat := [2, 1, 2, 1, 4, 2, 1, 3, 1, 6]
def baseStart_3886648 : Nat := 118140960795 + 3886648 * 2 ^ 59
def prefixEnd_3886648 : Nat := 4983230072969 + 3 ^ 40 * 3886648 * 2
def baseEnd_3886648 : Nat := 665239519612004901841879

theorem tailTrace_3886648 : CollatzResearch.WordTrace tailWord_3886648 prefixEnd_3886648 665239519612004901841879 := by
  unfold tailWord_3886648
  simp only [CollatzResearch.WordTrace]
  refine ⟨70878849211672778738378299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94505132282230371651171065 70878849211672778738378299)
  ·
    refine ⟨106318273817509168107567449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70878849211672778738378299 106318273817509168107567449)
    ·
      refine ⟨79738705363131876080675587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106318273817509168107567449 79738705363131876080675587)
      ·
        refine ⟨119608058044697814121013381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79738705363131876080675587 119608058044697814121013381)
        ·
          refine ⟨22426510883380840147690009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 119608058044697814121013381 22426510883380840147690009)
          ·
            refine ⟨16819883162535630110767507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22426510883380840147690009 16819883162535630110767507)
            ·
              refine ⟨25229824743803445166151261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16819883162535630110767507 25229824743803445166151261)
              ·
                refine ⟨9461184278926291937306723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25229824743803445166151261 9461184278926291937306723)
                ·
                  refine ⟨14191776418389437905960085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9461184278926291937306723 14191776418389437905960085)
                  ·
                    refine ⟨665239519612004901841879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14191776418389437905960085 665239519612004901841879)
                    ·
                      rfl

theorem cell23_3886648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 1, 3, 1, 6].length) (baseStart_3886648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3886648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3886648 prefixEnd_3886648 := by exact prefixLift 3886648
  have htrace : WordTrace (prefixWord ++ tailWord_3886648) baseStart_3886648 baseEnd_3886648 := by
    simpa [prefixWord, tailWord_3886648, baseEnd_3886648] using wordTrace_append hprefix tailTrace_3886648
  have hstable : (prefixWord ++ tailWord_3886648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3886648).length < 2 ^ (prefixWord ++ tailWord_3886648).sum := by decide
  have hdescent : baseEnd_3886648 < baseStart_3886648 := by decide
  rcases family_descends (prefixWord ++ tailWord_3886648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3886689 : List Nat := [1, 2, 3, 1, 1, 3, 1, 6, 1, 2, 2]
def baseStart_3886689 : Nat := 118140960795 + 3886689 * 2 ^ 59
def prefixEnd_3886689 : Nat := 4983230072969 + 3 ^ 40 * 3886689 * 2
def baseEnd_3886689 : Nat := 1995739611542849045112949

theorem tailTrace_3886689 : CollatzResearch.WordTrace tailWord_3886689 prefixEnd_3886689 1995739611542849045112949 := by
  unfold tailWord_3886689
  simp only [CollatzResearch.WordTrace]
  refine ⟨141759193816197021478999121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94506129210798014319332747 141759193816197021478999121)
  ·
    refine ⟨106319395362147766109249341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141759193816197021478999121 106319395362147766109249341)
    ·
      refine ⟨39869773260805412290968503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106319395362147766109249341 39869773260805412290968503)
      ·
        refine ⟨59804659891208118436452755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39869773260805412290968503 59804659891208118436452755)
        ·
          refine ⟨89706989836812177654679133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59804659891208118436452755 89706989836812177654679133)
          ·
            refine ⟨33640121188804566620504675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 89706989836812177654679133 33640121188804566620504675)
            ·
              refine ⟨50460181783206849930757013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33640121188804566620504675 50460181783206849930757013)
              ·
                refine ⟨2365321021087821090504235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 50460181783206849930757013 2365321021087821090504235)
                ·
                  refine ⟨3547981531631731635756353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2365321021087821090504235 3547981531631731635756353)
                  ·
                    refine ⟨2660986148723798726817265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3547981531631731635756353 2660986148723798726817265)
                    ·
                      refine ⟨1995739611542849045112949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2660986148723798726817265 1995739611542849045112949)
                      ·
                        rfl

theorem cell23_3886689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 6, 1, 2, 2].length) (baseStart_3886689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3886689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3886689 prefixEnd_3886689 := by exact prefixLift 3886689
  have htrace : WordTrace (prefixWord ++ tailWord_3886689) baseStart_3886689 baseEnd_3886689 := by
    simpa [prefixWord, tailWord_3886689, baseEnd_3886689] using wordTrace_append hprefix tailTrace_3886689
  have hstable : (prefixWord ++ tailWord_3886689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3886689).length < 2 ^ (prefixWord ++ tailWord_3886689).sum := by decide
  have hdescent : baseEnd_3886689 < baseStart_3886689 := by decide
  rcases family_descends (prefixWord ++ tailWord_3886689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3886709 : List Nat := [1, 3, 4, 2, 1, 2, 2, 2, 1, 2, 3]
def baseStart_3886709 : Nat := 118140960795 + 3886709 * 2 ^ 59
def prefixEnd_3886709 : Nat := 4983230072969 + 3 ^ 40 * 3886709 * 2
def baseEnd_3886709 : Nat := 1995749881155938966862857

theorem tailTrace_3886709 : CollatzResearch.WordTrace tailWord_3886709 prefixEnd_3886709 1995749881155938966862857 := by
  unfold tailWord_3886709
  simp only [CollatzResearch.WordTrace]
  refine ⟨141759923276124564894727181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94506615517416376596484787 141759923276124564894727181)
  ·
    refine ⟨53159971228546711835522693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 141759923276124564894727181 53159971228546711835522693)
    ·
      refine ⟨9967494605352508469160505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 53159971228546711835522693 9967494605352508469160505)
      ·
        refine ⟨7475620954014381351870379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9967494605352508469160505 7475620954014381351870379)
        ·
          refine ⟨11213431431021572027805569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7475620954014381351870379 11213431431021572027805569)
          ·
            refine ⟨8410073573266179020854177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11213431431021572027805569 8410073573266179020854177)
            ·
              refine ⟨6307555179949634265640633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8410073573266179020854177 6307555179949634265640633)
              ·
                refine ⟨4730666384962225699230475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6307555179949634265640633 4730666384962225699230475)
                ·
                  refine ⟨7095999577443338548845713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4730666384962225699230475 7095999577443338548845713)
                  ·
                    refine ⟨5321999683082503911634285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7095999577443338548845713 5321999683082503911634285)
                    ·
                      refine ⟨1995749881155938966862857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5321999683082503911634285 1995749881155938966862857)
                      ·
                        rfl

theorem cell23_3886709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 2, 2, 1, 2, 3].length) (baseStart_3886709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3886709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3886709 prefixEnd_3886709 := by exact prefixLift 3886709
  have htrace : WordTrace (prefixWord ++ tailWord_3886709) baseStart_3886709 baseEnd_3886709 := by
    simpa [prefixWord, tailWord_3886709, baseEnd_3886709] using wordTrace_append hprefix tailTrace_3886709
  have hstable : (prefixWord ++ tailWord_3886709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3886709).length < 2 ^ (prefixWord ++ tailWord_3886709).sum := by decide
  have hdescent : baseEnd_3886709 < baseStart_3886709 := by decide
  rcases family_descends (prefixWord ++ tailWord_3886709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3886732 : List Nat := [2, 2, 1, 2, 1, 1, 3, 5, 1, 3, 2]
def baseStart_3886732 : Nat := 118140960795 + 3886732 * 2 ^ 59
def prefixEnd_3886732 : Nat := 4983230072969 + 3 ^ 40 * 3886732 * 2
def baseEnd_3886732 : Nat := 1995761691210992376875251

theorem tailTrace_3886732 : CollatzResearch.WordTrace tailWord_3886732 prefixEnd_3886732 1995761691210992376875251 := by
  unfold tailWord_3886732
  simp only [CollatzResearch.WordTrace]
  refine ⟨70880381077520619911407225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94507174770027493215209633 70880381077520619911407225)
  ·
    refine ⟨53160285808140464933555419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70880381077520619911407225 53160285808140464933555419)
    ·
      refine ⟨79740428712210697400333129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53160285808140464933555419 79740428712210697400333129)
      ·
        refine ⟨59805321534158023050249847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79740428712210697400333129 59805321534158023050249847)
        ·
          refine ⟨89707982301237034575374771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59805321534158023050249847 89707982301237034575374771)
          ·
            refine ⟨134561973451855551863062157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89707982301237034575374771 134561973451855551863062157)
            ·
              refine ⟨50460740044445831948648309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 134561973451855551863062157 50460740044445831948648309)
              ·
                refine ⟨4730694379166796745185779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 50460740044445831948648309 4730694379166796745185779)
                ·
                  refine ⟨7096041568750195117778669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4730694379166796745185779 7096041568750195117778669)
                  ·
                    refine ⟨2661015588281323169167001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7096041568750195117778669 2661015588281323169167001)
                    ·
                      refine ⟨1995761691210992376875251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2661015588281323169167001 1995761691210992376875251)
                      ·
                        rfl

theorem cell23_3886732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 5, 1, 3, 2].length) (baseStart_3886732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3886732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3886732 prefixEnd_3886732 := by exact prefixLift 3886732
  have htrace : WordTrace (prefixWord ++ tailWord_3886732) baseStart_3886732 baseEnd_3886732 := by
    simpa [prefixWord, tailWord_3886732, baseEnd_3886732] using wordTrace_append hprefix tailTrace_3886732
  have hstable : (prefixWord ++ tailWord_3886732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3886732).length < 2 ^ (prefixWord ++ tailWord_3886732).sum := by decide
  have hdescent : baseEnd_3886732 < baseStart_3886732 := by decide
  rcases family_descends (prefixWord ++ tailWord_3886732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3886740 : List Nat := [2, 4, 2, 2, 2, 1, 3, 2, 1, 2, 2]
def baseStart_3886740 : Nat := 118140960795 + 3886740 * 2 ^ 59
def prefixEnd_3886740 : Nat := 4983230072969 + 3 ^ 40 * 3886740 * 2
def baseEnd_3886740 : Nat := 1995765799056228345575215

theorem tailTrace_3886740 : CollatzResearch.WordTrace tailWord_3886740 prefixEnd_3886740 1995765799056228345575215 := by
  unfold tailWord_3886740
  simp only [CollatzResearch.WordTrace]
  refine ⟨70880526969506128594552837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94507369292674838126070449 70880526969506128594552837)
  ·
    refine ⟨13290098806782399111478657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 70880526969506128594552837 13290098806782399111478657)
    ·
      refine ⟨9967574105086799333608993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13290098806782399111478657 9967574105086799333608993)
      ·
        refine ⟨7475680578815099500206745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9967574105086799333608993 7475680578815099500206745)
        ·
          refine ⟨5606760434111324625155059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7475680578815099500206745 5606760434111324625155059)
          ·
            refine ⟨8410140651166986937732589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5606760434111324625155059 8410140651166986937732589)
            ·
              refine ⟨3153802744187620101649721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8410140651166986937732589 3153802744187620101649721)
              ·
                refine ⟨2365352058140715076237291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3153802744187620101649721 2365352058140715076237291)
                ·
                  refine ⟨3548028087211072614355937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2365352058140715076237291 3548028087211072614355937)
                  ·
                    refine ⟨2661021065408304460766953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3548028087211072614355937 2661021065408304460766953)
                    ·
                      refine ⟨1995765799056228345575215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2661021065408304460766953 1995765799056228345575215)
                      ·
                        rfl

theorem cell23_3886740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 3, 2, 1, 2, 2].length) (baseStart_3886740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3886740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3886740 prefixEnd_3886740 := by exact prefixLift 3886740
  have htrace : WordTrace (prefixWord ++ tailWord_3886740) baseStart_3886740 baseEnd_3886740 := by
    simpa [prefixWord, tailWord_3886740, baseEnd_3886740] using wordTrace_append hprefix tailTrace_3886740
  have hstable : (prefixWord ++ tailWord_3886740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3886740).length < 2 ^ (prefixWord ++ tailWord_3886740).sum := by decide
  have hdescent : baseEnd_3886740 < baseStart_3886740 := by decide
  rcases family_descends (prefixWord ++ tailWord_3886740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3886745 : List Nat := [1, 2, 1, 2, 1, 2, 2, 1, 5, 4, 2]
def baseStart_3886745 : Nat := 118140960795 + 3886745 * 2 ^ 59
def prefixEnd_3886745 : Nat := 4983230072969 + 3 ^ 40 * 3886745 * 2
def baseEnd_3886745 : Nat := 1995768366459500826012691

theorem tailTrace_3886745 : CollatzResearch.WordTrace tailWord_3886745 prefixEnd_3886745 1995768366459500826012691 := by
  unfold tailWord_3886745
  simp only [CollatzResearch.WordTrace]
  refine ⟨141761236303994143043037689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94507490869329428695358459 141761236303994143043037689)
  ·
    refine ⟨106320927227995607282278267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141761236303994143043037689 106320927227995607282278267)
    ·
      refine ⟨159481390841993410923417401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106320927227995607282278267 159481390841993410923417401)
      ·
        refine ⟨119611043131495058192563051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159481390841993410923417401 119611043131495058192563051)
        ·
          refine ⟨179416564697242587288844577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119611043131495058192563051 179416564697242587288844577)
          ·
            refine ⟨134562423522931940466633433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 179416564697242587288844577 134562423522931940466633433)
            ·
              refine ⟨100921817642198955349975075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 134562423522931940466633433 100921817642198955349975075)
              ·
                refine ⟨151382726463298433024962613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100921817642198955349975075 151382726463298433024962613)
                ·
                  refine ⟨14192130605934228096090245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 151382726463298433024962613 14192130605934228096090245)
                  ·
                    refine ⟨2661024488612667768016921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14192130605934228096090245 2661024488612667768016921)
                    ·
                      refine ⟨1995768366459500826012691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2661024488612667768016921 1995768366459500826012691)
                      ·
                        rfl

theorem cell23_3886745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 1, 5, 4, 2].length) (baseStart_3886745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3886745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3886745 prefixEnd_3886745 := by exact prefixLift 3886745
  have htrace : WordTrace (prefixWord ++ tailWord_3886745) baseStart_3886745 baseEnd_3886745 := by
    simpa [prefixWord, tailWord_3886745, baseEnd_3886745] using wordTrace_append hprefix tailTrace_3886745
  have hstable : (prefixWord ++ tailWord_3886745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3886745).length < 2 ^ (prefixWord ++ tailWord_3886745).sum := by decide
  have hdescent : baseEnd_3886745 < baseStart_3886745 := by decide
  rcases family_descends (prefixWord ++ tailWord_3886745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3886756 : List Nat := [2, 3, 1, 2, 2, 4, 2, 1, 2, 1, 3]
def baseStart_3886756 : Nat := 118140960795 + 3886756 * 2 ^ 59
def prefixEnd_3886756 : Nat := 4983230072969 + 3 ^ 40 * 3886756 * 2
def baseEnd_3886756 : Nat := 1995774014746700282975141

theorem tailTrace_3886756 : CollatzResearch.WordTrace tailWord_3886756 prefixEnd_3886756 1995774014746700282975141 := by
  unfold tailWord_3886756
  simp only [CollatzResearch.WordTrace]
  refine ⟨70880818753477145960844061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94507758337969527947792081 70880818753477145960844061)
  ·
    refine ⟨26580307032553929735316523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70880818753477145960844061 26580307032553929735316523)
    ·
      refine ⟨39870460548830894602974785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26580307032553929735316523 39870460548830894602974785)
      ·
        refine ⟨29902845411623170952231089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39870460548830894602974785 29902845411623170952231089)
        ·
          refine ⟨22427134058717378214173317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29902845411623170952231089 22427134058717378214173317)
          ·
            refine ⟨4205087636009508415157497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22427134058717378214173317 4205087636009508415157497)
            ·
              refine ⟨3153815727007131311368123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4205087636009508415157497 3153815727007131311368123)
              ·
                refine ⟨4730723590510696967052185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3153815727007131311368123 4730723590510696967052185)
                ·
                  refine ⟨3548042692883022725289139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4730723590510696967052185 3548042692883022725289139)
                  ·
                    refine ⟨5322064039324534087933709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3548042692883022725289139 5322064039324534087933709)
                    ·
                      refine ⟨1995774014746700282975141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5322064039324534087933709 1995774014746700282975141)
                      ·
                        rfl

theorem cell23_3886756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 4, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 4, 2, 1, 2, 1, 3].length) (baseStart_3886756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3886756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3886756 prefixEnd_3886756 := by exact prefixLift 3886756
  have htrace : WordTrace (prefixWord ++ tailWord_3886756) baseStart_3886756 baseEnd_3886756 := by
    simpa [prefixWord, tailWord_3886756, baseEnd_3886756] using wordTrace_append hprefix tailTrace_3886756
  have hstable : (prefixWord ++ tailWord_3886756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3886756).length < 2 ^ (prefixWord ++ tailWord_3886756).sum := by decide
  have hdescent : baseEnd_3886756 < baseStart_3886756 := by decide
  rcases family_descends (prefixWord ++ tailWord_3886756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3886760 : List Nat := [2, 1, 7, 1, 2, 1, 1, 2, 1, 2, 3]
def baseStart_3886760 : Nat := 118140960795 + 3886760 * 2 ^ 59
def prefixEnd_3886760 : Nat := 4983230072969 + 3 ^ 40 * 3886760 * 2
def baseEnd_3886760 : Nat := 1995776068669318267325123

theorem tailTrace_3886760 : CollatzResearch.WordTrace tailWord_3886760 prefixEnd_3886760 1995776068669318267325123 := by
  unfold tailWord_3886760
  simp only [CollatzResearch.WordTrace]
  refine ⟨70880891699469900302416867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94507855599293200403222489 70880891699469900302416867)
  ·
    refine ⟨106321337549204850453625301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70880891699469900302416867 106321337549204850453625301)
    ·
      refine ⟨2491906348809488682506843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 106321337549204850453625301 2491906348809488682506843)
      ·
        refine ⟨3737859523214233023760265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2491906348809488682506843 3737859523214233023760265)
        ·
          refine ⟨2803394642410674767820199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3737859523214233023760265 2803394642410674767820199)
          ·
            refine ⟨4205091963616012151730299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2803394642410674767820199 4205091963616012151730299)
            ·
              refine ⟨6307637945424018227595449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4205091963616012151730299 6307637945424018227595449)
              ·
                refine ⟨4730728459068013670696587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6307637945424018227595449 4730728459068013670696587)
                ·
                  refine ⟨7096092688602020506044881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4730728459068013670696587 7096092688602020506044881)
                  ·
                    refine ⟨5322069516451515379533661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7096092688602020506044881 5322069516451515379533661)
                    ·
                      refine ⟨1995776068669318267325123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5322069516451515379533661 1995776068669318267325123)
                      ·
                        rfl

theorem cell23_3886760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 2, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 2, 1, 1, 2, 1, 2, 3].length) (baseStart_3886760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3886760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3886760 prefixEnd_3886760 := by exact prefixLift 3886760
  have htrace : WordTrace (prefixWord ++ tailWord_3886760) baseStart_3886760 baseEnd_3886760 := by
    simpa [prefixWord, tailWord_3886760, baseEnd_3886760] using wordTrace_append hprefix tailTrace_3886760
  have hstable : (prefixWord ++ tailWord_3886760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3886760).length < 2 ^ (prefixWord ++ tailWord_3886760).sum := by decide
  have hdescent : baseEnd_3886760 < baseStart_3886760 := by decide
  rcases family_descends (prefixWord ++ tailWord_3886760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3886765 : List Nat := [1, 5, 2, 1, 1, 1, 1, 1, 4, 1, 5]
def baseStart_3886765 : Nat := 118140960795 + 3886765 * 2 ^ 59
def prefixEnd_3886765 : Nat := 4983230072969 + 3 ^ 40 * 3886765 * 2
def baseEnd_3886765 : Nat := 1995778636072590747762599

theorem tailTrace_3886765 : CollatzResearch.WordTrace tailWord_3886765 prefixEnd_3886765 1995778636072590747762599 := by
  unfold tailWord_3886765
  simp only [CollatzResearch.WordTrace]
  refine ⟨141761965763921686458765749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94507977175947790972510499 141761965763921686458765749)
  ·
    refine ⟨13290184290367658105509289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 141761965763921686458765749 13290184290367658105509289)
    ·
      refine ⟨9967638217775743579131967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13290184290367658105509289 9967638217775743579131967)
      ·
        refine ⟨14951457326663615368697951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9967638217775743579131967 14951457326663615368697951)
        ·
          refine ⟨22427185989995423053046927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14951457326663615368697951 22427185989995423053046927)
          ·
            refine ⟨33640778984993134579570391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22427185989995423053046927 33640778984993134579570391)
            ·
              refine ⟨50461168477489701869355587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33640778984993134579570391 50461168477489701869355587)
              ·
                refine ⟨75691752716234552804033381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50461168477489701869355587 75691752716234552804033381)
                ·
                  refine ⟨14192203634293978650756259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 75691752716234552804033381 14192203634293978650756259)
                  ·
                    refine ⟨21288305451440967976134389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14192203634293978650756259 21288305451440967976134389)
                    ·
                      refine ⟨1995778636072590747762599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21288305451440967976134389 1995778636072590747762599)
                      ·
                        rfl

theorem cell23_3886765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 1, 4, 1, 5].length) (baseStart_3886765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3886765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3886765 prefixEnd_3886765 := by exact prefixLift 3886765
  have htrace : WordTrace (prefixWord ++ tailWord_3886765) baseStart_3886765 baseEnd_3886765 := by
    simpa [prefixWord, tailWord_3886765, baseEnd_3886765] using wordTrace_append hprefix tailTrace_3886765
  have hstable : (prefixWord ++ tailWord_3886765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3886765).length < 2 ^ (prefixWord ++ tailWord_3886765).sum := by decide
  have hdescent : baseEnd_3886765 < baseStart_3886765 := by decide
  rcases family_descends (prefixWord ++ tailWord_3886765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3886766 : List Nat := [4, 1, 4, 1, 2, 1, 1, 1, 3, 3, 2]
def baseStart_3886766 : Nat := 118140960795 + 3886766 * 2 ^ 59
def prefixEnd_3886766 : Nat := 4983230072969 + 3 ^ 40 * 3886766 * 2
def baseEnd_3886766 : Nat := 1995779149553245243850095

theorem tailTrace_3886766 : CollatzResearch.WordTrace tailWord_3886766 prefixEnd_3886766 1995779149553245243850095 := by
  unfold tailWord_3886766
  simp only [CollatzResearch.WordTrace]
  refine ⟨17720250279614757953694019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 94508001491278709086368101 17720250279614757953694019)
  ·
    refine ⟨26580375419422136930541029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17720250279614757953694019 26580375419422136930541029)
    ·
      refine ⟨4983820391141650674476443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26580375419422136930541029 4983820391141650674476443)
      ·
        refine ⟨7475730586712476011714665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4983820391141650674476443 7475730586712476011714665)
        ·
          refine ⟨5606797940034357008785999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7475730586712476011714665 5606797940034357008785999)
          ·
            refine ⟨8410196910051535513178999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5606797940034357008785999 8410196910051535513178999)
            ·
              refine ⟨12615295365077303269768499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8410196910051535513178999 12615295365077303269768499)
              ·
                refine ⟨18922943047615954904652749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12615295365077303269768499 18922943047615954904652749)
                ·
                  refine ⟨7096103642855983089244781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18922943047615954904652749 7096103642855983089244781)
                  ·
                    refine ⟨2661038866070993658466793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7096103642855983089244781 2661038866070993658466793)
                    ·
                      refine ⟨1995779149553245243850095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2661038866070993658466793 1995779149553245243850095)
                      ·
                        rfl

theorem cell23_3886766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 1, 1, 3, 3, 2].length) (baseStart_3886766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3886766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3886766 prefixEnd_3886766 := by exact prefixLift 3886766
  have htrace : WordTrace (prefixWord ++ tailWord_3886766) baseStart_3886766 baseEnd_3886766 := by
    simpa [prefixWord, tailWord_3886766, baseEnd_3886766] using wordTrace_append hprefix tailTrace_3886766
  have hstable : (prefixWord ++ tailWord_3886766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3886766).length < 2 ^ (prefixWord ++ tailWord_3886766).sum := by decide
  have hdescent : baseEnd_3886766 < baseStart_3886766 := by decide
  rcases family_descends (prefixWord ++ tailWord_3886766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3886768 : List Nat := [2, 1, 1, 1, 2, 1, 4, 4, 7]
def baseStart_3886768 : Nat := 118140960795 + 3886768 * 2 ^ 59
def prefixEnd_3886768 : Nat := 4983230072969 + 3 ^ 40 * 3886768 * 2
def baseEnd_3886768 : Nat := 221753352946061581780565

theorem tailTrace_3886768 : CollatzResearch.WordTrace tailWord_3886768 prefixEnd_3886768 221753352946061581780565 := by
  unfold tailWord_3886768
  simp only [CollatzResearch.WordTrace]
  refine ⟨70881037591455408985562479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94508050121940545314083305 70881037591455408985562479)
  ·
    refine ⟨106321556387183113478343719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70881037591455408985562479 106321556387183113478343719)
    ·
      refine ⟨159482334580774670217515579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106321556387183113478343719 159482334580774670217515579)
      ·
        refine ⟨239223501871162005326273369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159482334580774670217515579 239223501871162005326273369)
        ·
          refine ⟨179417626403371503994705027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 239223501871162005326273369 179417626403371503994705027)
          ·
            refine ⟨269126439605057255992057541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 179417626403371503994705027 269126439605057255992057541)
            ·
              refine ⟨50461207425948235498510789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 269126439605057255992057541 50461207425948235498510789)
              ·
                refine ⟨9461476392365294155970773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50461207425948235498510789 9461476392365294155970773)
                ·
                  refine ⟨221753352946061581780565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9461476392365294155970773 221753352946061581780565)
                  ·
                    rfl

theorem cell23_3886768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 4, 7].length) (baseStart_3886768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3886768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3886768 prefixEnd_3886768 := by exact prefixLift 3886768
  have htrace : WordTrace (prefixWord ++ tailWord_3886768) baseStart_3886768 baseEnd_3886768 := by
    simpa [prefixWord, tailWord_3886768, baseEnd_3886768] using wordTrace_append hprefix tailTrace_3886768
  have hstable : (prefixWord ++ tailWord_3886768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3886768).length < 2 ^ (prefixWord ++ tailWord_3886768).sum := by decide
  have hdescent : baseEnd_3886768 < baseStart_3886768 := by decide
  rcases family_descends (prefixWord ++ tailWord_3886768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3886836 : List Nat := [2, 6, 1, 1, 1, 1, 1, 5, 5]
def baseStart_3886836 : Nat := 118140960795 + 3886836 * 2 ^ 59
def prefixEnd_3886836 : Nat := 4983230072969 + 3 ^ 40 * 3886836 * 2
def baseEnd_3886836 : Nat := 221757232577673329997197

theorem tailTrace_3886836 : CollatzResearch.WordTrace tailWord_3886836 prefixEnd_3886836 221757232577673329997197 := by
  unfold tailWord_3886836
  simp only [CollatzResearch.WordTrace]
  refine ⟨70882277673332232792300181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94509703564442977056400241 70882277673332232792300181)
  ·
    refine ⟨3322606765937448412139071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 70882277673332232792300181 3322606765937448412139071)
    ·
      refine ⟨4983910148906172618208607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3322606765937448412139071 4983910148906172618208607)
      ·
        refine ⟨7475865223359258927312911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4983910148906172618208607 7475865223359258927312911)
        ·
          refine ⟨11213797835038888390969367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7475865223359258927312911 11213797835038888390969367)
          ·
            refine ⟨16820696752558332586454051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11213797835038888390969367 16820696752558332586454051)
            ·
              refine ⟨25231045128837498879681077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16820696752558332586454051 25231045128837498879681077)
              ·
                refine ⟨2365410480828515519970101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25231045128837498879681077 2365410480828515519970101)
                ·
                  refine ⟨221757232577673329997197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2365410480828515519970101 221757232577673329997197)
                  ·
                    rfl

theorem cell23_3886836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 1, 5, 5].length) (baseStart_3886836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3886836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3886836 prefixEnd_3886836 := by exact prefixLift 3886836
  have htrace : WordTrace (prefixWord ++ tailWord_3886836) baseStart_3886836 baseEnd_3886836 := by
    simpa [prefixWord, tailWord_3886836, baseEnd_3886836] using wordTrace_append hprefix tailTrace_3886836
  have hstable : (prefixWord ++ tailWord_3886836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3886836).length < 2 ^ (prefixWord ++ tailWord_3886836).sum := by decide
  have hdescent : baseEnd_3886836 < baseStart_3886836 := by decide
  rcases family_descends (prefixWord ++ tailWord_3886836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3886862 : List Nat := [4, 1, 1, 2, 1, 1, 3, 3, 3, 4]
def baseStart_3886862 : Nat := 118140960795 + 3886862 * 2 ^ 59
def prefixEnd_3886862 : Nat := 4983230072969 + 3 ^ 40 * 3886862 * 2
def baseEnd_3886862 : Nat := 665276147898692289416551

theorem tailTrace_3886862 : CollatzResearch.WordTrace tailWord_3886862 prefixEnd_3886862 665276147898692289416551 := by
  unfold tailWord_3886862
  simp only [CollatzResearch.WordTrace]
  refine ⟨17720687955571284003130855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 94510335763046848016697893 17720687955571284003130855)
  ·
    refine ⟨26581031933356926004696283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17720687955571284003130855 26581031933356926004696283)
    ·
      refine ⟨39871547900035389007044425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26581031933356926004696283 39871547900035389007044425)
      ·
        refine ⟨29903660925026541755283319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39871547900035389007044425 29903660925026541755283319)
        ·
          refine ⟨44855491387539812632924979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29903660925026541755283319 44855491387539812632924979)
          ·
            refine ⟨67283237081309718949387469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44855491387539812632924979 67283237081309718949387469)
            ·
              refine ⟨25231213905491144606020301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67283237081309718949387469 25231213905491144606020301)
              ·
                refine ⟨9461705214559179227257613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25231213905491144606020301 9461705214559179227257613)
                ·
                  refine ⟨3548139455459692210221605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9461705214559179227257613 3548139455459692210221605)
                  ·
                    refine ⟨665276147898692289416551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3548139455459692210221605 665276147898692289416551)
                    ·
                      rfl

theorem cell23_3886862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 3, 3, 3, 4].length) (baseStart_3886862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3886862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3886862 prefixEnd_3886862 := by exact prefixLift 3886862
  have htrace : WordTrace (prefixWord ++ tailWord_3886862) baseStart_3886862 baseEnd_3886862 := by
    simpa [prefixWord, tailWord_3886862, baseEnd_3886862] using wordTrace_append hprefix tailTrace_3886862
  have hstable : (prefixWord ++ tailWord_3886862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3886862).length < 2 ^ (prefixWord ++ tailWord_3886862).sum := by decide
  have hdescent : baseEnd_3886862 < baseStart_3886862 := by decide
  rcases family_descends (prefixWord ++ tailWord_3886862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3886919 : List Nat := [1, 1, 4, 1, 2, 1, 5, 1, 3, 1, 3]
def baseStart_3886919 : Nat := 118140960795 + 3886919 * 2 ^ 59
def prefixEnd_3886919 : Nat := 4983230072969 + 3 ^ 40 * 3886919 * 2
def baseEnd_3886919 : Nat := 1995857712093383145236891

theorem tailTrace_3886919 : CollatzResearch.WordTrace tailWord_3886919 prefixEnd_3886919 1995857712093383145236891 := by
  unfold tailWord_3886919
  simp only [CollatzResearch.WordTrace]
  refine ⟨141767582605363770759871811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94511721736909180506581207 141767582605363770759871811)
  ·
    refine ⟨212651373908045656139807717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141767582605363770759871811 212651373908045656139807717)
    ·
      refine ⟨39872132607758560526213947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 212651373908045656139807717 39872132607758560526213947)
      ·
        refine ⟨59808198911637840789320921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39872132607758560526213947 59808198911637840789320921)
        ·
          refine ⟨44856149183728380591990691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59808198911637840789320921 44856149183728380591990691)
          ·
            refine ⟨67284223775592570887986037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44856149183728380591990691 67284223775592570887986037)
            ·
              refine ⟨6307895978961803520748691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 67284223775592570887986037 6307895978961803520748691)
              ·
                refine ⟨9461843968442705281123037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6307895978961803520748691 9461843968442705281123037)
                ·
                  refine ⟨3548191488166014480421139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9461843968442705281123037 3548191488166014480421139)
                  ·
                    refine ⟨5322287232249021720631709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3548191488166014480421139 5322287232249021720631709)
                    ·
                      refine ⟨1995857712093383145236891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5322287232249021720631709 1995857712093383145236891)
                      ·
                        rfl

theorem cell23_3886919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 5, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 5, 1, 3, 1, 3].length) (baseStart_3886919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3886919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3886919 prefixEnd_3886919 := by exact prefixLift 3886919
  have htrace : WordTrace (prefixWord ++ tailWord_3886919) baseStart_3886919 baseEnd_3886919 := by
    simpa [prefixWord, tailWord_3886919, baseEnd_3886919] using wordTrace_append hprefix tailTrace_3886919
  have hstable : (prefixWord ++ tailWord_3886919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3886919).length < 2 ^ (prefixWord ++ tailWord_3886919).sum := by decide
  have hdescent : baseEnd_3886919 < baseStart_3886919 := by decide
  rcases family_descends (prefixWord ++ tailWord_3886919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3886946 : List Nat := [3, 3, 2, 1, 2, 1, 1, 3, 2, 3, 2]
def baseStart_3886946 : Nat := 118140960795 + 3886946 * 2 ^ 59
def prefixEnd_3886946 : Nat := 4983230072969 + 3 ^ 40 * 3886946 * 2
def baseEnd_3886946 : Nat := 1995871576071054539599267

theorem tailTrace_3886946 : CollatzResearch.WordTrace tailWord_3886946 prefixEnd_3886946 1995871576071054539599267 := by
  unfold tailWord_3886946
  simp only [CollatzResearch.WordTrace]
  refine ⟨35442141844066488592776173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94512378250843969580736461 35442141844066488592776173)
  ·
    refine ⟨13290803191524933222291065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35442141844066488592776173 13290803191524933222291065)
    ·
      refine ⟨9968102393643699916718299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13290803191524933222291065 9968102393643699916718299)
      ·
        refine ⟨14952153590465549875077449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9968102393643699916718299 14952153590465549875077449)
        ·
          refine ⟨11214115192849162406308087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14952153590465549875077449 11214115192849162406308087)
          ·
            refine ⟨16821172789273743609462131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11214115192849162406308087 16821172789273743609462131)
            ·
              refine ⟨25231759183910615414193197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16821172789273743609462131 25231759183910615414193197)
              ·
                refine ⟨9461909693966480780322449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25231759183910615414193197 9461909693966480780322449)
                ·
                  refine ⟨7096432270474860585241837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9461909693966480780322449 7096432270474860585241837)
                  ·
                    refine ⟨2661162101428072719465689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7096432270474860585241837 2661162101428072719465689)
                    ·
                      refine ⟨1995871576071054539599267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2661162101428072719465689 1995871576071054539599267)
                      ·
                        rfl

theorem cell23_3886946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 1, 3, 2, 3, 2].length) (baseStart_3886946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3886946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3886946 prefixEnd_3886946 := by exact prefixLift 3886946
  have htrace : WordTrace (prefixWord ++ tailWord_3886946) baseStart_3886946 baseEnd_3886946 := by
    simpa [prefixWord, tailWord_3886946, baseEnd_3886946] using wordTrace_append hprefix tailTrace_3886946
  have hstable : (prefixWord ++ tailWord_3886946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3886946).length < 2 ^ (prefixWord ++ tailWord_3886946).sum := by decide
  have hdescent : baseEnd_3886946 < baseStart_3886946 := by decide
  rcases family_descends (prefixWord ++ tailWord_3886946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3886952 : List Nat := [2, 1, 4, 2, 1, 1, 3, 2, 1, 6]
def baseStart_3886952 : Nat := 118140960795 + 3886952 * 2 ^ 59
def prefixEnd_3886952 : Nat := 4983230072969 + 3 ^ 40 * 3886952 * 2
def baseEnd_3886952 : Nat := 665291552318327172041413

theorem tailTrace_3886952 : CollatzResearch.WordTrace tailWord_3886952 prefixEnd_3886952 665291552318327172041413 := by
  unfold tailWord_3886952
  simp only [CollatzResearch.WordTrace]
  refine ⟨70884393107122108697911555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94512524142829478263882073 70884393107122108697911555)
  ·
    refine ⟨106326589660683163046867333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70884393107122108697911555 106326589660683163046867333)
    ·
      refine ⟨19936235561378093071287625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 106326589660683163046867333 19936235561378093071287625)
      ·
        refine ⟨14952176671033569803465719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19936235561378093071287625 14952176671033569803465719)
        ·
          refine ⟨22428265006550354705198579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14952176671033569803465719 22428265006550354705198579)
          ·
            refine ⟨33642397509825532057797869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22428265006550354705198579 33642397509825532057797869)
            ·
              refine ⟨12615899066184574521674201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33642397509825532057797869 12615899066184574521674201)
              ·
                refine ⟨9461924299638430891255651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12615899066184574521674201 9461924299638430891255651)
                ·
                  refine ⟨14192886449457646336883477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9461924299638430891255651 14192886449457646336883477)
                  ·
                    refine ⟨665291552318327172041413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14192886449457646336883477 665291552318327172041413)
                    ·
                      rfl

theorem cell23_3886952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 3, 2, 1, 6].length) (baseStart_3886952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3886952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3886952 prefixEnd_3886952 := by exact prefixLift 3886952
  have htrace : WordTrace (prefixWord ++ tailWord_3886952) baseStart_3886952 baseEnd_3886952 := by
    simpa [prefixWord, tailWord_3886952, baseEnd_3886952] using wordTrace_append hprefix tailTrace_3886952
  have hstable : (prefixWord ++ tailWord_3886952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3886952).length < 2 ^ (prefixWord ++ tailWord_3886952).sum := by decide
  have hdescent : baseEnd_3886952 < baseStart_3886952 := by decide
  rcases family_descends (prefixWord ++ tailWord_3886952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3886969 : List Nat := [1, 2, 1, 3, 2, 2, 4, 2, 2, 4]
def baseStart_3886969 : Nat := 118140960795 + 3886969 * 2 ^ 59
def prefixEnd_3886969 : Nat := 4983230072969 + 3 ^ 40 * 3886969 * 2
def baseEnd_3886969 : Nat := 665294462042035983203887

theorem tailTrace_3886969 : CollatzResearch.WordTrace tailWord_3886969 prefixEnd_3886969 665294462042035983203887 := by
  unfold tailWord_3886969
  simp only [CollatzResearch.WordTrace]
  refine ⟨141769406255182629299191961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94512937503455086199461307 141769406255182629299191961)
  ·
    refine ⟨106327054691386971974393971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141769406255182629299191961 106327054691386971974393971)
    ·
      refine ⟨159490582037080457961590957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106327054691386971974393971 159490582037080457961590957)
      ·
        refine ⟨59808968263905171735596609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 159490582037080457961590957 59808968263905171735596609)
        ·
          refine ⟨44856726197928878801697457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59808968263905171735596609 44856726197928878801697457)
          ·
            refine ⟨33642544648446659101273093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44856726197928878801697457 33642544648446659101273093)
            ·
              refine ⟨6307977121583748581488705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33642544648446659101273093 6307977121583748581488705)
              ·
                refine ⟨4730982841187811436116529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6307977121583748581488705 4730982841187811436116529)
                ·
                  refine ⟨3548237130890858577087397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4730982841187811436116529 3548237130890858577087397)
                  ·
                    refine ⟨665294462042035983203887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3548237130890858577087397 665294462042035983203887)
                    ·
                      rfl

theorem cell23_3886969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 4, 2, 2, 4].length) (baseStart_3886969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3886969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3886969 prefixEnd_3886969 := by exact prefixLift 3886969
  have htrace : WordTrace (prefixWord ++ tailWord_3886969) baseStart_3886969 baseEnd_3886969 := by
    simpa [prefixWord, tailWord_3886969, baseEnd_3886969] using wordTrace_append hprefix tailTrace_3886969
  have hstable : (prefixWord ++ tailWord_3886969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3886969).length < 2 ^ (prefixWord ++ tailWord_3886969).sum := by decide
  have hdescent : baseEnd_3886969 < baseStart_3886969 := by decide
  rcases family_descends (prefixWord ++ tailWord_3886969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3886992 : List Nat := [2, 1, 1, 1, 1, 1, 2, 7, 1, 3, 3]
def baseStart_3886992 : Nat := 118140960795 + 3886992 * 2 ^ 59
def prefixEnd_3886992 : Nat := 4983230072969 + 3 ^ 40 * 3886992 * 2
def baseEnd_3886992 : Nat := 1995895196181161359624055

theorem tailTrace_3886992 : CollatzResearch.WordTrace tailWord_3886992 prefixEnd_3886992 1995895196181161359624055 := by
  unfold tailWord_3886992
  simp only [CollatzResearch.WordTrace]
  refine ⟨70885122567049652113639615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94513496756066202818186153 70885122567049652113639615)
  ·
    refine ⟨106327683850574478170459423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70885122567049652113639615 106327683850574478170459423)
    ·
      refine ⟨159491525775861717255689135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106327683850574478170459423 159491525775861717255689135)
      ·
        refine ⟨239237288663792575883533703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159491525775861717255689135 239237288663792575883533703)
        ·
          refine ⟨358855932995688863825300555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 239237288663792575883533703 358855932995688863825300555)
          ·
            refine ⟨538283899493533295737950833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 358855932995688863825300555 538283899493533295737950833)
            ·
              refine ⟨403712924620149971803463125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 538283899493533295737950833 403712924620149971803463125)
              ·
                refine ⟨9462021670784764964143667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 403712924620149971803463125 9462021670784764964143667)
                ·
                  refine ⟨14193032506177147446215501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9462021670784764964143667 14193032506177147446215501)
                  ·
                    refine ⟨5322387189816430292330813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14193032506177147446215501 5322387189816430292330813)
                    ·
                      refine ⟨1995895196181161359624055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5322387189816430292330813 1995895196181161359624055)
                      ·
                        rfl

theorem cell23_3886992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 7, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 7, 1, 3, 3].length) (baseStart_3886992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3886992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3886992 prefixEnd_3886992 := by exact prefixLift 3886992
  have htrace : WordTrace (prefixWord ++ tailWord_3886992) baseStart_3886992 baseEnd_3886992 := by
    simpa [prefixWord, tailWord_3886992, baseEnd_3886992] using wordTrace_append hprefix tailTrace_3886992
  have hstable : (prefixWord ++ tailWord_3886992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3886992).length < 2 ^ (prefixWord ++ tailWord_3886992).sum := by decide
  have hdescent : baseEnd_3886992 < baseStart_3886992 := by decide
  rcases family_descends (prefixWord ++ tailWord_3886992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3887010 : List Nat := [3, 3, 1, 2, 4, 1, 2, 1, 1, 1, 4]
def baseStart_3887010 : Nat := 118140960795 + 3887010 * 2 ^ 59
def prefixEnd_3887010 : Nat := 4983230072969 + 3 ^ 40 * 3887010 * 2
def baseEnd_3887010 : Nat := 1995904438832942289198973

theorem tailTrace_3887010 : CollatzResearch.WordTrace tailWord_3887010 prefixEnd_3887010 1995904438832942289198973 := by
  unfold tailWord_3887010
  simp only [CollatzResearch.WordTrace]
  refine ⟨35442725412008523325358621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94513934432022728867622989 35442725412008523325358621)
  ·
    refine ⟨13291022029503196247009483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35442725412008523325358621 13291022029503196247009483)
    ·
      refine ⟨19936533044254794370514225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13291022029503196247009483 19936533044254794370514225)
      ·
        refine ⟨14952399783191095777885669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19936533044254794370514225 14952399783191095777885669)
        ·
          refine ⟨2803574959348330458353563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14952399783191095777885669 2803574959348330458353563)
          ·
            refine ⟨4205362439022495687530345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2803574959348330458353563 4205362439022495687530345)
            ·
              refine ⟨3154021829266871765647759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4205362439022495687530345 3154021829266871765647759)
              ·
                refine ⟨4731032743900307648471639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3154021829266871765647759 4731032743900307648471639)
                ·
                  refine ⟨7096549115850461472707459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4731032743900307648471639 7096549115850461472707459)
                  ·
                    refine ⟨10644823673775692209061189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7096549115850461472707459 10644823673775692209061189)
                    ·
                      refine ⟨1995904438832942289198973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10644823673775692209061189 1995904438832942289198973)
                      ·
                        rfl

theorem cell23_3887010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 4, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 4, 1, 2, 1, 1, 1, 4].length) (baseStart_3887010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3887010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3887010 prefixEnd_3887010 := by exact prefixLift 3887010
  have htrace : WordTrace (prefixWord ++ tailWord_3887010) baseStart_3887010 baseEnd_3887010 := by
    simpa [prefixWord, tailWord_3887010, baseEnd_3887010] using wordTrace_append hprefix tailTrace_3887010
  have hstable : (prefixWord ++ tailWord_3887010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3887010).length < 2 ^ (prefixWord ++ tailWord_3887010).sum := by decide
  have hdescent : baseEnd_3887010 < baseStart_3887010 := by decide
  rcases family_descends (prefixWord ++ tailWord_3887010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3887082 : List Nat := [3, 1, 3, 1, 2, 1, 1, 1, 1, 2, 7]
def baseStart_3887082 : Nat := 118140960795 + 3887082 * 2 ^ 59
def prefixEnd_3887082 : Nat := 4983230072969 + 3 ^ 40 * 3887082 * 2
def baseEnd_3887082 : Nat := 1995941409440066007498641

theorem tailTrace_3887082 : CollatzResearch.WordTrace tailWord_3887082 prefixEnd_3887082 1995941409440066007498641 := by
  unfold tailWord_3887082
  simp only [CollatzResearch.WordTrace]
  refine ⟨35443381925943312399513875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94515685135848833065370333 35443381925943312399513875)
  ·
    refine ⟨53165072888914968599270813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35443381925943312399513875 53165072888914968599270813)
    ·
      refine ⟨19936902333343113224726555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53165072888914968599270813 19936902333343113224726555)
      ·
        refine ⟨29905353500014669837089833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19936902333343113224726555 29905353500014669837089833)
        ·
          refine ⟨22429015125011002377817375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29905353500014669837089833 22429015125011002377817375)
          ·
            refine ⟨33643522687516503566726063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22429015125011002377817375 33643522687516503566726063)
            ·
              refine ⟨50465284031274755350089095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33643522687516503566726063 50465284031274755350089095)
              ·
                refine ⟨75697926046912133025133643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50465284031274755350089095 75697926046912133025133643)
                ·
                  refine ⟨113546889070368199537700465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 75697926046912133025133643 113546889070368199537700465)
                  ·
                    refine ⟨85160166802776149653275349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 113546889070368199537700465 85160166802776149653275349)
                    ·
                      refine ⟨1995941409440066007498641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 85160166802776149653275349 1995941409440066007498641)
                      ·
                        rfl

theorem cell23_3887082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 1, 1, 2, 7].length) (baseStart_3887082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3887082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3887082 prefixEnd_3887082 := by exact prefixLift 3887082
  have htrace : WordTrace (prefixWord ++ tailWord_3887082) baseStart_3887082 baseEnd_3887082 := by
    simpa [prefixWord, tailWord_3887082, baseEnd_3887082] using wordTrace_append hprefix tailTrace_3887082
  have hstable : (prefixWord ++ tailWord_3887082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3887082).length < 2 ^ (prefixWord ++ tailWord_3887082).sum := by decide
  have hdescent : baseEnd_3887082 < baseStart_3887082 := by decide
  rcases family_descends (prefixWord ++ tailWord_3887082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3887112 : List Nat := [2, 1, 3, 2, 1, 2, 1, 2, 1, 1, 7]
def baseStart_3887112 : Nat := 118140960795 + 3887112 * 2 ^ 59
def prefixEnd_3887112 : Nat := 4983230072969 + 3 ^ 40 * 3887112 * 2
def baseEnd_3887112 : Nat := 1995956813859700890123503

theorem tailTrace_3887112 : CollatzResearch.WordTrace tailWord_3887112 prefixEnd_3887112 1995956813859700890123503 := by
  unfold tailWord_3887112
  simp only [CollatzResearch.WordTrace]
  refine ⟨70887310946832282360823795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94516414595776376481098393 70887310946832282360823795)
  ·
    refine ⟨106330966420248423541235693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70887310946832282360823795 106330966420248423541235693)
    ·
      refine ⟨39874112407593158827963385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106330966420248423541235693 39874112407593158827963385)
      ·
        refine ⟨29905584305694869120972539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39874112407593158827963385 29905584305694869120972539)
        ·
          refine ⟨44858376458542303681458809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29905584305694869120972539 44858376458542303681458809)
          ·
            refine ⟨33643782343906727761094107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44858376458542303681458809 33643782343906727761094107)
            ·
              refine ⟨50465673515860091641641161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33643782343906727761094107 50465673515860091641641161)
              ·
                refine ⟨37849255136895068731230871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50465673515860091641641161 37849255136895068731230871)
                ·
                  refine ⟨56773882705342603096846307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37849255136895068731230871 56773882705342603096846307)
                  ·
                    refine ⟨85160824058013904645269461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 56773882705342603096846307 85160824058013904645269461)
                    ·
                      refine ⟨1995956813859700890123503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 85160824058013904645269461 1995956813859700890123503)
                      ·
                        rfl

theorem cell23_3887112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 2, 1, 1, 7].length) (baseStart_3887112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3887112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3887112 prefixEnd_3887112 := by exact prefixLift 3887112
  have htrace : WordTrace (prefixWord ++ tailWord_3887112) baseStart_3887112 baseEnd_3887112 := by
    simpa [prefixWord, tailWord_3887112, baseEnd_3887112] using wordTrace_append hprefix tailTrace_3887112
  have hstable : (prefixWord ++ tailWord_3887112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3887112).length < 2 ^ (prefixWord ++ tailWord_3887112).sum := by decide
  have hdescent : baseEnd_3887112 < baseStart_3887112 := by decide
  rcases family_descends (prefixWord ++ tailWord_3887112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3887117 : List Nat := [1, 7, 1, 2, 1, 1, 1, 2, 1, 4, 2]
def baseStart_3887117 : Nat := 118140960795 + 3887117 * 2 ^ 59
def prefixEnd_3887117 : Nat := 4983230072969 + 3 ^ 40 * 3887117 * 2
def baseEnd_3887117 : Nat := 1995959381262973370560981

theorem tailTrace_3887117 : CollatzResearch.WordTrace tailWord_3887117 prefixEnd_3887117 1995959381262973370560981 := by
  unfold tailWord_3887117
  simp only [CollatzResearch.WordTrace]
  refine ⟨141774804258646450575579605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94516536172430967050386403 141774804258646450575579605)
  ·
    refine ⟨3322846974812026185365147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 141774804258646450575579605 3322846974812026185365147)
    ·
      refine ⟨4984270462218039278047721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3322846974812026185365147 4984270462218039278047721)
      ·
        refine ⟨3738202846663529458535791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4984270462218039278047721 3738202846663529458535791)
        ·
          refine ⟨5607304269995294187803687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3738202846663529458535791 5607304269995294187803687)
          ·
            refine ⟨8410956404992941281705531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5607304269995294187803687 8410956404992941281705531)
            ·
              refine ⟨12616434607489411922558297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8410956404992941281705531 12616434607489411922558297)
              ·
                refine ⟨9462325955617058941918723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12616434607489411922558297 9462325955617058941918723)
                ·
                  refine ⟨14193488933425588412878085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9462325955617058941918723 14193488933425588412878085)
                  ·
                    refine ⟨2661279175017297827414641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14193488933425588412878085 2661279175017297827414641)
                    ·
                      refine ⟨1995959381262973370560981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2661279175017297827414641 1995959381262973370560981)
                      ·
                        rfl

theorem cell23_3887117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 1, 2, 1, 4, 2].length) (baseStart_3887117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3887117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3887117 prefixEnd_3887117 := by exact prefixLift 3887117
  have htrace : WordTrace (prefixWord ++ tailWord_3887117) baseStart_3887117 baseEnd_3887117 := by
    simpa [prefixWord, tailWord_3887117, baseEnd_3887117] using wordTrace_append hprefix tailTrace_3887117
  have hstable : (prefixWord ++ tailWord_3887117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3887117).length < 2 ^ (prefixWord ++ tailWord_3887117).sum := by decide
  have hdescent : baseEnd_3887117 < baseStart_3887117 := by decide
  rcases family_descends (prefixWord ++ tailWord_3887117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3887139 : List Nat := [1, 1, 1, 4, 3, 1, 1, 4, 2, 1, 4]
def baseStart_3887139 : Nat := 118140960795 + 3887139 * 2 ^ 59
def prefixEnd_3887139 : Nat := 4983230072969 + 3 ^ 40 * 3887139 * 2
def baseEnd_3887139 : Nat := 1995970677837372284485879

theorem tailTrace_3887139 : CollatzResearch.WordTrace tailWord_3887139 prefixEnd_3887139 1995970677837372284485879 := by
  unfold tailWord_3887139
  simp only [CollatzResearch.WordTrace]
  refine ⟨141775606664566748332880471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94517071109711165555253647 141775606664566748332880471)
  ·
    refine ⟨212663409996850122499320707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141775606664566748332880471 212663409996850122499320707)
    ·
      refine ⟨318995114995275183748981061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212663409996850122499320707 318995114995275183748981061)
      ·
        refine ⟨59811584061614096952933949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 318995114995275183748981061 59811584061614096952933949)
        ·
          refine ⟨22429344023105286357350231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59811584061614096952933949 22429344023105286357350231)
          ·
            refine ⟨33644016034657929536025347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22429344023105286357350231 33644016034657929536025347)
            ·
              refine ⟨50466024051986894304038021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33644016034657929536025347 50466024051986894304038021)
              ·
                refine ⟨9462379509747542682007129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50466024051986894304038021 9462379509747542682007129)
                ·
                  refine ⟨7096784632310657011505347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9462379509747542682007129 7096784632310657011505347)
                  ·
                    refine ⟨10645176948465985517258021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7096784632310657011505347 10645176948465985517258021)
                    ·
                      refine ⟨1995970677837372284485879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10645176948465985517258021 1995970677837372284485879)
                      ·
                        rfl

theorem cell23_3887139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 4, 2, 1, 4].length) (baseStart_3887139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3887139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3887139 prefixEnd_3887139 := by exact prefixLift 3887139
  have htrace : WordTrace (prefixWord ++ tailWord_3887139) baseStart_3887139 baseEnd_3887139 := by
    simpa [prefixWord, tailWord_3887139, baseEnd_3887139] using wordTrace_append hprefix tailTrace_3887139
  have hstable : (prefixWord ++ tailWord_3887139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3887139).length < 2 ^ (prefixWord ++ tailWord_3887139).sum := by decide
  have hdescent : baseEnd_3887139 < baseStart_3887139 := by decide
  rcases family_descends (prefixWord ++ tailWord_3887139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3887140 : List Nat := [2, 3, 1, 4, 2, 2, 2, 2, 5]
def baseStart_3887140 : Nat := 118140960795 + 3887140 * 2 ^ 59
def prefixEnd_3887140 : Nat := 4983230072969 + 3 ^ 40 * 3887140 * 2
def baseEnd_3887140 : Nat := 221774576813114086730375

theorem tailTrace_3887140 : CollatzResearch.WordTrace tailWord_3887140 prefixEnd_3887140 221774576813114086730375 := by
  unfold tailWord_3887140
  simp only [CollatzResearch.WordTrace]
  refine ⟨70887821568781562751833437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94517095425042083669111249 70887821568781562751833437)
  ·
    refine ⟨26582933088293086031937539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70887821568781562751833437 26582933088293086031937539)
    ·
      refine ⟨39874399632439629047906309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26582933088293086031937539 39874399632439629047906309)
      ·
        refine ⟨7476449931082430446482433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39874399632439629047906309 7476449931082430446482433)
        ·
          refine ⟨5607337448311822834861825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7476449931082430446482433 5607337448311822834861825)
          ·
            refine ⟨4205503086233867126146369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5607337448311822834861825 4205503086233867126146369)
            ·
              refine ⟨3154127314675400344609777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4205503086233867126146369 3154127314675400344609777)
              ·
                refine ⟨2365595486006550258457333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3154127314675400344609777 2365595486006550258457333)
                ·
                  refine ⟨221774576813114086730375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2365595486006550258457333 221774576813114086730375)
                  ·
                    rfl

theorem cell23_3887140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 2, 2, 2, 5].length) (baseStart_3887140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3887140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3887140 prefixEnd_3887140 := by exact prefixLift 3887140
  have htrace : WordTrace (prefixWord ++ tailWord_3887140) baseStart_3887140 baseEnd_3887140 := by
    simpa [prefixWord, tailWord_3887140, baseEnd_3887140] using wordTrace_append hprefix tailTrace_3887140
  have hstable : (prefixWord ++ tailWord_3887140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3887140).length < 2 ^ (prefixWord ++ tailWord_3887140).sum := by decide
  have hdescent : baseEnd_3887140 < baseStart_3887140 := by decide
  rcases family_descends (prefixWord ++ tailWord_3887140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3887159 : List Nat := [1, 1, 3, 1, 2, 2, 2, 2, 4, 2, 3]
def baseStart_3887159 : Nat := 118140960795 + 3887159 * 2 ^ 59
def prefixEnd_3887159 : Nat := 4983230072969 + 3 ^ 40 * 3887159 * 2
def baseEnd_3887159 : Nat := 1995980947450462206235787

theorem tailTrace_3887159 : CollatzResearch.WordTrace tailWord_3887159 prefixEnd_3887159 1995980947450462206235787 := by
  unfold tailWord_3887159
  simp only [CollatzResearch.WordTrace]
  refine ⟨141776336124494291748608531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94517557416329527832405687 141776336124494291748608531)
  ·
    refine ⟨212664504186741437622912797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141776336124494291748608531 212664504186741437622912797)
    ·
      refine ⟨79749189070028039108592299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 212664504186741437622912797 79749189070028039108592299)
      ·
        refine ⟨119623783605042058662888449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79749189070028039108592299 119623783605042058662888449)
        ·
          refine ⟨89717837703781543997166337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119623783605042058662888449 89717837703781543997166337)
          ·
            refine ⟨67288378277836157997874753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89717837703781543997166337 67288378277836157997874753)
            ·
              refine ⟨50466283708377118498406065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67288378277836157997874753 50466283708377118498406065)
              ·
                refine ⟨37849712781282838873804549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50466283708377118498406065 37849712781282838873804549)
                ·
                  refine ⟨7096821146490532288838353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37849712781282838873804549 7096821146490532288838353)
                  ·
                    refine ⟨5322615859867899216628765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7096821146490532288838353 5322615859867899216628765)
                    ·
                      refine ⟨1995980947450462206235787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5322615859867899216628765 1995980947450462206235787)
                      ·
                        rfl

theorem cell23_3887159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 2, 4, 2, 3].length) (baseStart_3887159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3887159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3887159 prefixEnd_3887159 := by exact prefixLift 3887159
  have htrace : WordTrace (prefixWord ++ tailWord_3887159) baseStart_3887159 baseEnd_3887159 := by
    simpa [prefixWord, tailWord_3887159, baseEnd_3887159] using wordTrace_append hprefix tailTrace_3887159
  have hstable : (prefixWord ++ tailWord_3887159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3887159).length < 2 ^ (prefixWord ++ tailWord_3887159).sum := by decide
  have hdescent : baseEnd_3887159 < baseStart_3887159 := by decide
  rcases family_descends (prefixWord ++ tailWord_3887159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3887162 : List Nat := [3, 1, 1, 1, 3, 1, 1, 2, 10]
def baseStart_3887162 : Nat := 118140960795 + 3887162 * 2 ^ 59
def prefixEnd_3887162 : Nat := 4983230072969 + 3 ^ 40 * 3887162 * 2
def baseEnd_3887162 : Nat := 221775831988047299388697

theorem tailTrace_3887162 : CollatzResearch.WordTrace tailWord_3887162 prefixEnd_3887162 221775831988047299388697 := by
  unfold tailWord_3887162
  simp only [CollatzResearch.WordTrace]
  refine ⟨35444111385870855815241935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94517630362322282173978493 35444111385870855815241935)
  ·
    refine ⟨53166167078806283722862903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35444111385870855815241935 53166167078806283722862903)
    ·
      refine ⟨79749250618209425584294355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53166167078806283722862903 79749250618209425584294355)
      ·
        refine ⟨119623875927314138376441533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79749250618209425584294355 119623875927314138376441533)
        ·
          refine ⟨44858953472742801891165575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 119623875927314138376441533 44858953472742801891165575)
          ·
            refine ⟨67288430209114202836748363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44858953472742801891165575 67288430209114202836748363)
            ·
              refine ⟨100932645313671304255122545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67288430209114202836748363 100932645313671304255122545)
              ·
                refine ⟨75699483985253478191341909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 100932645313671304255122545 75699483985253478191341909)
                ·
                  refine ⟨221775831988047299388697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 75699483985253478191341909 221775831988047299388697)
                  ·
                    rfl

theorem cell23_3887162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 2, 10].length) (baseStart_3887162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3887162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3887162 prefixEnd_3887162 := by exact prefixLift 3887162
  have htrace : WordTrace (prefixWord ++ tailWord_3887162) baseStart_3887162 baseEnd_3887162 := by
    simpa [prefixWord, tailWord_3887162, baseEnd_3887162] using wordTrace_append hprefix tailTrace_3887162
  have hstable : (prefixWord ++ tailWord_3887162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3887162).length < 2 ^ (prefixWord ++ tailWord_3887162).sum := by decide
  have hdescent : baseEnd_3887162 < baseStart_3887162 := by decide
  rcases family_descends (prefixWord ++ tailWord_3887162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3887190 : List Nat := [5, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2]
def baseStart_3887190 : Nat := 118140960795 + 3887190 * 2 ^ 59
def prefixEnd_3887190 : Nat := 4983230072969 + 3 ^ 40 * 3887190 * 2
def baseEnd_3887190 : Nat := 1995996865350751584948145

theorem tailTrace_3887190 : CollatzResearch.WordTrace tailWord_3887190 prefixEnd_3887190 1995996865350751584948145 := by
  unfold tailWord_3887190
  simp only [CollatzResearch.WordTrace]
  refine ⟨8861091674211374002686689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 94518311191587989361991349 8861091674211374002686689)
  ·
    refine ⟨6645818755658530502015017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8861091674211374002686689 6645818755658530502015017)
    ·
      refine ⟨4984364066743897876511263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6645818755658530502015017 4984364066743897876511263)
      ·
        refine ⟨7476546100115846814766895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4984364066743897876511263 7476546100115846814766895)
        ·
          refine ⟨11214819150173770222150343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7476546100115846814766895 11214819150173770222150343)
          ·
            refine ⟨16822228725260655333225515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11214819150173770222150343 16822228725260655333225515)
            ·
              refine ⟨25233343087890982999838273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16822228725260655333225515 25233343087890982999838273)
              ·
                refine ⟨18925007315918237249878705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25233343087890982999838273 18925007315918237249878705)
                ·
                  refine ⟨14193755486938677937409029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18925007315918237249878705 14193755486938677937409029)
                  ·
                    refine ⟨2661329153801002113264193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14193755486938677937409029 2661329153801002113264193)
                    ·
                      refine ⟨1995996865350751584948145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2661329153801002113264193 1995996865350751584948145)
                      ·
                        rfl

theorem cell23_3887190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2].length) (baseStart_3887190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3887190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3887190 prefixEnd_3887190 := by exact prefixLift 3887190
  have htrace : WordTrace (prefixWord ++ tailWord_3887190) baseStart_3887190 baseEnd_3887190 := by
    simpa [prefixWord, tailWord_3887190, baseEnd_3887190] using wordTrace_append hprefix tailTrace_3887190
  have hstable : (prefixWord ++ tailWord_3887190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3887190).length < 2 ^ (prefixWord ++ tailWord_3887190).sum := by decide
  have hdescent : baseEnd_3887190 < baseStart_3887190 := by decide
  rcases family_descends (prefixWord ++ tailWord_3887190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3887196 : List Nat := [2, 2, 4, 1, 1, 2, 3, 2, 6]
def baseStart_3887196 : Nat := 118140960795 + 3887196 * 2 ^ 59
def prefixEnd_3887196 : Nat := 4983230072969 + 3 ^ 40 * 3887196 * 2
def baseEnd_3887196 : Nat := 221777771803853173497013

theorem tailTrace_3887196 : CollatzResearch.WordTrace tailWord_3887196 prefixEnd_3887196 221777771803853173497013 := by
  unfold tailWord_3887196
  simp only [CollatzResearch.WordTrace]
  refine ⟨70888842812680123533852721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94518457083573498045136961 70888842812680123533852721)
  ·
    refine ⟨53166632109510092650389541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70888842812680123533852721 53166632109510092650389541)
    ·
      refine ⟨9968743520533142371948039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 53166632109510092650389541 9968743520533142371948039)
      ·
        refine ⟨14953115280799713557922059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9968743520533142371948039 14953115280799713557922059)
        ·
          refine ⟨22429672921199570336883089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14953115280799713557922059 22429672921199570336883089)
          ·
            refine ⟨16822254690899677752662317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22429672921199570336883089 16822254690899677752662317)
            ·
              refine ⟨6308345509087379157248369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16822254690899677752662317 6308345509087379157248369)
              ·
                refine ⟨4731259131815534367936277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6308345509087379157248369 4731259131815534367936277)
                ·
                  refine ⟨221777771803853173497013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4731259131815534367936277 221777771803853173497013)
                  ·
                    rfl

theorem cell23_3887196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 3, 2, 6].length) (baseStart_3887196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3887196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3887196 prefixEnd_3887196 := by exact prefixLift 3887196
  have htrace : WordTrace (prefixWord ++ tailWord_3887196) baseStart_3887196 baseEnd_3887196 := by
    simpa [prefixWord, tailWord_3887196, baseEnd_3887196] using wordTrace_append hprefix tailTrace_3887196
  have hstable : (prefixWord ++ tailWord_3887196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3887196).length < 2 ^ (prefixWord ++ tailWord_3887196).sum := by decide
  have hdescent : baseEnd_3887196 < baseStart_3887196 := by decide
  rcases family_descends (prefixWord ++ tailWord_3887196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3887216 : List Nat := [2, 1, 1, 1, 5, 2, 1, 2, 1, 5, 2]
def baseStart_3887216 : Nat := 118140960795 + 3887216 * 2 ^ 59
def prefixEnd_3887216 : Nat := 4983230072969 + 3 ^ 40 * 3887216 * 2
def baseEnd_3887216 : Nat := 1996010215847768483223025

theorem tailTrace_3887216 : CollatzResearch.WordTrace tailWord_3887216 prefixEnd_3887216 1996010215847768483223025 := by
  unfold tailWord_3887216
  simp only [CollatzResearch.WordTrace]
  refine ⟨70889207542643895241716751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94518943390191860322289001 70889207542643895241716751)
  ·
    refine ⟨106333811313965842862575127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70889207542643895241716751 106333811313965842862575127)
    ·
      refine ⟨159500716970948764293862691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106333811313965842862575127 159500716970948764293862691)
      ·
        refine ⟨239251075456423146440794037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159500716970948764293862691 239251075456423146440794037)
        ·
          refine ⟨22429788324039669978824441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 239251075456423146440794037 22429788324039669978824441)
          ·
            refine ⟨16822341243029752484118331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22429788324039669978824441 16822341243029752484118331)
            ·
              refine ⟨25233511864544628726177497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16822341243029752484118331 25233511864544628726177497)
              ·
                refine ⟨18925133898408471544633123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25233511864544628726177497 18925133898408471544633123)
                ·
                  refine ⟨28387700847612707316949685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18925133898408471544633123 28387700847612707316949685)
                  ·
                    refine ⟨2661346954463691310964033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 28387700847612707316949685 2661346954463691310964033)
                    ·
                      refine ⟨1996010215847768483223025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2661346954463691310964033 1996010215847768483223025)
                      ·
                        rfl

theorem cell23_3887216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 1, 2, 1, 5, 2].length) (baseStart_3887216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3887216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3887216 prefixEnd_3887216 := by exact prefixLift 3887216
  have htrace : WordTrace (prefixWord ++ tailWord_3887216) baseStart_3887216 baseEnd_3887216 := by
    simpa [prefixWord, tailWord_3887216, baseEnd_3887216] using wordTrace_append hprefix tailTrace_3887216
  have hstable : (prefixWord ++ tailWord_3887216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3887216).length < 2 ^ (prefixWord ++ tailWord_3887216).sum := by decide
  have hdescent : baseEnd_3887216 < baseStart_3887216 := by decide
  rcases family_descends (prefixWord ++ tailWord_3887216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3887239 : List Nat := [1, 1, 4, 2, 1, 1, 2, 4, 1, 6]
def baseStart_3887239 : Nat := 118140960795 + 3887239 * 2 ^ 59
def prefixEnd_3887239 : Nat := 4983230072969 + 3 ^ 40 * 3887239 * 2
def baseEnd_3887239 : Nat := 665340675300940631078473

theorem tailTrace_3887239 : CollatzResearch.WordTrace tailWord_3887239 prefixEnd_3887239 665340675300940631078473 := by
  unfold tailWord_3887239
  simp only [CollatzResearch.WordTrace]
  refine ⟨141779253964204465411520771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94519502642802976941013847 141779253964204465411520771)
  ·
    refine ⟨212668880946306698117281157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141779253964204465411520771 212668880946306698117281157)
    ·
      refine ⟨39875415177432505896990217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 212668880946306698117281157 39875415177432505896990217)
      ·
        refine ⟨29906561383074379422742663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39875415177432505896990217 29906561383074379422742663)
        ·
          refine ⟨44859842074611569134113995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29906561383074379422742663 44859842074611569134113995)
          ·
            refine ⟨67289763111917353701170993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44859842074611569134113995 67289763111917353701170993)
            ·
              refine ⟨50467322333938015275878245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67289763111917353701170993 50467322333938015275878245)
              ·
                refine ⟨9462622937613377864227171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50467322333938015275878245 9462622937613377864227171)
                ·
                  refine ⟨14193934406420066796340757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9462622937613377864227171 14193934406420066796340757)
                  ·
                    refine ⟨665340675300940631078473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14193934406420066796340757 665340675300940631078473)
                    ·
                      rfl

theorem cell23_3887239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 4, 1, 6].length) (baseStart_3887239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3887239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3887239 prefixEnd_3887239 := by exact prefixLift 3887239
  have htrace : WordTrace (prefixWord ++ tailWord_3887239) baseStart_3887239 baseEnd_3887239 := by
    simpa [prefixWord, tailWord_3887239, baseEnd_3887239] using wordTrace_append hprefix tailTrace_3887239
  have hstable : (prefixWord ++ tailWord_3887239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3887239).length < 2 ^ (prefixWord ++ tailWord_3887239).sum := by decide
  have hdescent : baseEnd_3887239 < baseStart_3887239 := by decide
  rcases family_descends (prefixWord ++ tailWord_3887239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3887269 : List Nat := [1, 3, 1, 2, 1, 3, 4, 8]
def baseStart_3887269 : Nat := 118140960795 + 3887269 * 2 ^ 59
def prefixEnd_3887269 : Nat := 4983230072969 + 3 ^ 40 * 3887269 * 2
def baseEnd_3887269 : Nat := 73927312234165065772603

theorem tailTrace_3887269 : CollatzResearch.WordTrace tailWord_3887269 prefixEnd_3887269 73927312234165065772603 := by
  unfold tailWord_3887269
  simp only [CollatzResearch.WordTrace]
  refine ⟨141780348154095780535112861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94520232102730520356741907 141780348154095780535112861)
  ·
    refine ⟨53167630557785917700667323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 141780348154095780535112861 53167630557785917700667323)
    ·
      refine ⟨79751445836678876551000985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53167630557785917700667323 79751445836678876551000985)
      ·
        refine ⟨59813584377509157413250739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79751445836678876551000985 59813584377509157413250739)
        ·
          refine ⟨89720376566263736119876109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59813584377509157413250739 89720376566263736119876109)
          ·
            refine ⟨33645141212348901044953541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 89720376566263736119876109 33645141212348901044953541)
            ·
              refine ⟨6308463977315418945928789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33645141212348901044953541 6308463977315418945928789)
              ·
                refine ⟨73927312234165065772603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6308463977315418945928789 73927312234165065772603)
                ·
                  rfl

theorem cell23_3887269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 4, 8].length) (baseStart_3887269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3887269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3887269 prefixEnd_3887269 := by exact prefixLift 3887269
  have htrace : WordTrace (prefixWord ++ tailWord_3887269) baseStart_3887269 baseEnd_3887269 := by
    simpa [prefixWord, tailWord_3887269, baseEnd_3887269] using wordTrace_append hprefix tailTrace_3887269
  have hstable : (prefixWord ++ tailWord_3887269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3887269).length < 2 ^ (prefixWord ++ tailWord_3887269).sum := by decide
  have hdescent : baseEnd_3887269 < baseStart_3887269 := by decide
  rcases family_descends (prefixWord ++ tailWord_3887269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3887296 : List Nat := [2, 1, 1, 2, 5, 1, 1, 1, 3, 3, 3]
def baseStart_3887296 : Nat := 118140960795 + 3887296 * 2 ^ 59
def prefixEnd_3887296 : Nat := 4983230072969 + 3 ^ 40 * 3887296 * 2
def baseEnd_3887296 : Nat := 1996051294300128170222657

theorem tailTrace_3887296 : CollatzResearch.WordTrace tailWord_3887296 prefixEnd_3887296 1996051294300128170222657 := by
  unfold tailWord_3887296
  simp only [CollatzResearch.WordTrace]
  refine ⟨70890666462498982073172871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94520888616665309430897161 70890666462498982073172871)
  ·
    refine ⟨106335999693748473109759307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70890666462498982073172871 106335999693748473109759307)
    ·
      refine ⟨159503999540622709664638961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106335999693748473109759307 159503999540622709664638961)
      ·
        refine ⟨119627999655467032248479221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159503999540622709664638961 119627999655467032248479221)
        ·
          refine ⟨11215124967700034273294927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 119627999655467032248479221 11215124967700034273294927)
          ·
            refine ⟨16822687451550051409942391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11215124967700034273294927 16822687451550051409942391)
            ·
              refine ⟨25234031177325077114913587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16822687451550051409942391 25234031177325077114913587)
              ·
                refine ⟨37851046765987615672370381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25234031177325077114913587 37851046765987615672370381)
                ·
                  refine ⟨14194142537245355877138893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37851046765987615672370381 14194142537245355877138893)
                  ·
                    refine ⟨5322803451467008453927085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14194142537245355877138893 5322803451467008453927085)
                    ·
                      refine ⟨1996051294300128170222657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5322803451467008453927085 1996051294300128170222657)
                      ·
                        rfl

theorem cell23_3887296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 1, 1, 3, 3, 3].length) (baseStart_3887296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3887296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3887296 prefixEnd_3887296 := by exact prefixLift 3887296
  have htrace : WordTrace (prefixWord ++ tailWord_3887296) baseStart_3887296 baseEnd_3887296 := by
    simpa [prefixWord, tailWord_3887296, baseEnd_3887296] using wordTrace_append hprefix tailTrace_3887296
  have hstable : (prefixWord ++ tailWord_3887296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3887296).length < 2 ^ (prefixWord ++ tailWord_3887296).sum := by decide
  have hdescent : baseEnd_3887296 < baseStart_3887296 := by decide
  rcases family_descends (prefixWord ++ tailWord_3887296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3887297 : List Nat := [1, 2, 6, 1, 2, 1, 3, 1, 1, 1, 4]
def baseStart_3887297 : Nat := 118140960795 + 3887297 * 2 ^ 59
def prefixEnd_3887297 : Nat := 4983230072969 + 3 ^ 40 * 3887297 * 2
def baseEnd_3887297 : Nat := 1996051807780782666310153

theorem tailTrace_3887297 : CollatzResearch.WordTrace tailWord_3887297 prefixEnd_3887297 1996051807780782666310153 := by
  unfold tailWord_3887297
  simp only [CollatzResearch.WordTrace]
  refine ⟨141781369397994341317132145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94520912931996227544754763 141781369397994341317132145)
  ·
    refine ⟨106336027048495755987849109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141781369397994341317132145 106336027048495755987849109)
    ·
      refine ⟨4984501267898238561930427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 106336027048495755987849109 4984501267898238561930427)
      ·
        refine ⟨7476751901847357842895641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4984501267898238561930427 7476751901847357842895641)
        ·
          refine ⟨5607563926385518382171731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7476751901847357842895641 5607563926385518382171731)
          ·
            refine ⟨8411345889578277573257597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5607563926385518382171731 8411345889578277573257597)
            ·
              refine ⟨3154254708591854089971599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8411345889578277573257597 3154254708591854089971599)
              ·
                refine ⟨4731382062887781134957399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3154254708591854089971599 4731382062887781134957399)
                ·
                  refine ⟨7097073094331671702436099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4731382062887781134957399 7097073094331671702436099)
                  ·
                    refine ⟨10645609641497507553654149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7097073094331671702436099 10645609641497507553654149)
                    ·
                      refine ⟨1996051807780782666310153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10645609641497507553654149 1996051807780782666310153)
                      ·
                        rfl

theorem cell23_3887297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 3, 1, 1, 1, 4].length) (baseStart_3887297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3887297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3887297 prefixEnd_3887297 := by exact prefixLift 3887297
  have htrace : WordTrace (prefixWord ++ tailWord_3887297) baseStart_3887297 baseEnd_3887297 := by
    simpa [prefixWord, tailWord_3887297, baseEnd_3887297] using wordTrace_append hprefix tailTrace_3887297
  have hstable : (prefixWord ++ tailWord_3887297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3887297).length < 2 ^ (prefixWord ++ tailWord_3887297).sum := by decide
  have hdescent : baseEnd_3887297 < baseStart_3887297 := by decide
  rcases family_descends (prefixWord ++ tailWord_3887297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3887313 : List Nat := [1, 2, 2, 1, 2, 2, 3, 4, 2, 1, 3]
def baseStart_3887313 : Nat := 118140960795 + 3887313 * 2 ^ 59
def prefixEnd_3887313 : Nat := 4983230072969 + 3 ^ 40 * 3887313 * 2
def baseEnd_3887313 : Nat := 1996060023471254603710079

theorem tailTrace_3887313 : CollatzResearch.WordTrace tailWord_3887313 prefixEnd_3887313 1996060023471254603710079 := by
  unfold tailWord_3887313
  simp only [CollatzResearch.WordTrace]
  refine ⟨141781952965936376049714593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94521301977290917366476395 141781952965936376049714593)
  ·
    refine ⟨106336464724452282037285945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141781952965936376049714593 106336464724452282037285945)
    ·
      refine ⟨79752348543339211527964459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106336464724452282037285945 79752348543339211527964459)
      ·
        refine ⟨119628522815008817291946689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79752348543339211527964459 119628522815008817291946689)
        ·
          refine ⟨89721392111256612968960017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119628522815008817291946689 89721392111256612968960017)
          ·
            refine ⟨67291044083442459726720013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89721392111256612968960017 67291044083442459726720013)
            ·
              refine ⟨25234141531290922397520005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67291044083442459726720013 25234141531290922397520005)
              ·
                refine ⟨4731401537117047949535001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25234141531290922397520005 4731401537117047949535001)
                ·
                  refine ⟨3548551152837785962151251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4731401537117047949535001 3548551152837785962151251)
                  ·
                    refine ⟨5322826729256678943226877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3548551152837785962151251 5322826729256678943226877)
                    ·
                      refine ⟨1996060023471254603710079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5322826729256678943226877 1996060023471254603710079)
                      ·
                        rfl

theorem cell23_3887313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 3, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 3, 4, 2, 1, 3].length) (baseStart_3887313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3887313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3887313 prefixEnd_3887313 := by exact prefixLift 3887313
  have htrace : WordTrace (prefixWord ++ tailWord_3887313) baseStart_3887313 baseEnd_3887313 := by
    simpa [prefixWord, tailWord_3887313, baseEnd_3887313] using wordTrace_append hprefix tailTrace_3887313
  have hstable : (prefixWord ++ tailWord_3887313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3887313).length < 2 ^ (prefixWord ++ tailWord_3887313).sum := by decide
  have hdescent : baseEnd_3887313 < baseStart_3887313 := by decide
  rcases family_descends (prefixWord ++ tailWord_3887313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3887314 : List Nat := [3, 2, 2, 2, 1, 2, 4, 2, 1, 2, 2]
def baseStart_3887314 : Nat := 118140960795 + 3887314 * 2 ^ 59
def prefixEnd_3887314 : Nat := 4983230072969 + 3 ^ 40 * 3887314 * 2
def baseEnd_3887314 : Nat := 1996060536951909099797575

theorem tailTrace_3887314 : CollatzResearch.WordTrace tailWord_3887314 prefixEnd_3887314 1996060536951909099797575 := by
  unfold tailWord_3887314
  simp only [CollatzResearch.WordTrace]
  refine ⟨35445497359733188305125249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94521326292621835480333997 35445497359733188305125249)
  ·
    refine ⟨26584123019799891228843937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35445497359733188305125249 26584123019799891228843937)
    ·
      refine ⟨19938092264849918421632953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26584123019799891228843937 19938092264849918421632953)
      ·
        refine ⟨14953569198637438816224715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19938092264849918421632953 14953569198637438816224715)
        ·
          refine ⟨22430353797956158224337073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14953569198637438816224715 22430353797956158224337073)
          ·
            refine ⟨16822765348467118668252805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22430353797956158224337073 16822765348467118668252805)
            ·
              refine ⟨3154268502837584750297401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16822765348467118668252805 3154268502837584750297401)
              ·
                refine ⟨2365701377128188562723051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3154268502837584750297401 2365701377128188562723051)
                ·
                  refine ⟨3548552065692282844084577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2365701377128188562723051 3548552065692282844084577)
                  ·
                    refine ⟨2661414049269212133063433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3548552065692282844084577 2661414049269212133063433)
                    ·
                      refine ⟨1996060536951909099797575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2661414049269212133063433 1996060536951909099797575)
                      ·
                        rfl

theorem cell23_3887314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 4, 2, 1, 2, 2].length) (baseStart_3887314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3887314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3887314 prefixEnd_3887314 := by exact prefixLift 3887314
  have htrace : WordTrace (prefixWord ++ tailWord_3887314) baseStart_3887314 baseEnd_3887314 := by
    simpa [prefixWord, tailWord_3887314, baseEnd_3887314] using wordTrace_append hprefix tailTrace_3887314
  have hstable : (prefixWord ++ tailWord_3887314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3887314).length < 2 ^ (prefixWord ++ tailWord_3887314).sum := by decide
  have hdescent : baseEnd_3887314 < baseStart_3887314 := by decide
  rcases family_descends (prefixWord ++ tailWord_3887314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3887359 : List Nat := [1, 1, 2, 2, 1, 4, 1, 2, 9]
def baseStart_3887359 : Nat := 118140960795 + 3887359 * 2 ^ 59
def prefixEnd_3887359 : Nat := 4983230072969 + 3 ^ 40 * 3887359 * 2
def baseEnd_3887359 : Nat := 221787071509040158192763

theorem tailTrace_3887359 : CollatzResearch.WordTrace tailWord_3887359 prefixEnd_3887359 221787071509040158192763 := by
  unfold tailWord_3887359
  simp only [CollatzResearch.WordTrace]
  refine ⟨141783630723769725905889131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94522420482513150603926087 141783630723769725905889131)
  ·
    refine ⟨212675446085654588858833697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141783630723769725905889131 212675446085654588858833697)
    ·
      refine ⟨159506584564240941644125273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 212675446085654588858833697 159506584564240941644125273)
      ·
        refine ⟨119629938423180706233093955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159506584564240941644125273 119629938423180706233093955)
        ·
          refine ⟨179444907634771059349640933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119629938423180706233093955 179444907634771059349640933)
          ·
            refine ⟨33645920181519573628057675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 179444907634771059349640933 33645920181519573628057675)
            ·
              refine ⟨50468880272279360442086513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33645920181519573628057675 50468880272279360442086513)
              ·
                refine ⟨37851660204209520331564885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50468880272279360442086513 37851660204209520331564885)
                ·
                  refine ⟨221787071509040158192763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 37851660204209520331564885 221787071509040158192763)
                  ·
                    rfl

theorem cell23_3887359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 2, 9].length) (baseStart_3887359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3887359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3887359 prefixEnd_3887359 := by exact prefixLift 3887359
  have htrace : WordTrace (prefixWord ++ tailWord_3887359) baseStart_3887359 baseEnd_3887359 := by
    simpa [prefixWord, tailWord_3887359, baseEnd_3887359] using wordTrace_append hprefix tailTrace_3887359
  have hstable : (prefixWord ++ tailWord_3887359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3887359).length < 2 ^ (prefixWord ++ tailWord_3887359).sum := by decide
  have hdescent : baseEnd_3887359 < baseStart_3887359 := by decide
  rcases family_descends (prefixWord ++ tailWord_3887359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3887364 : List Nat := [2, 3, 2, 2, 4, 1, 1, 2, 2, 1, 3]
def baseStart_3887364 : Nat := 118140960795 + 3887364 * 2 ^ 59
def prefixEnd_3887364 : Nat := 4983230072969 + 3 ^ 40 * 3887364 * 2
def baseEnd_3887364 : Nat := 1996086210984633904172345

theorem tailTrace_3887364 : CollatzResearch.WordTrace tailWord_3887364 prefixEnd_3887364 1996086210984633904172345 := by
  unfold tailWord_3887364
  simp only [CollatzResearch.WordTrace]
  refine ⟨70891906544375805879910573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94522542059167741173214097 70891906544375805879910573)
  ·
    refine ⟨26584464954140927204966465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70891906544375805879910573 26584464954140927204966465)
    ·
      refine ⟨19938348715605695403724849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26584464954140927204966465 19938348715605695403724849)
      ·
        refine ⟨14953761536704271552793637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19938348715605695403724849 14953761536704271552793637)
        ·
          refine ⟨2803830288132050916148807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14953761536704271552793637 2803830288132050916148807)
          ·
            refine ⟨4205745432198076374223211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2803830288132050916148807 4205745432198076374223211)
            ·
              refine ⟨6308618148297114561334817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4205745432198076374223211 6308618148297114561334817)
              ·
                refine ⟨4731463611222835921001113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6308618148297114561334817 4731463611222835921001113)
                ·
                  refine ⟨3548597708417126940750835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4731463611222835921001113 3548597708417126940750835)
                  ·
                    refine ⟨5322896562625690411126253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3548597708417126940750835 5322896562625690411126253)
                    ·
                      refine ⟨1996086210984633904172345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5322896562625690411126253 1996086210984633904172345)
                      ·
                        rfl

theorem cell23_3887364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 4, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 4, 1, 1, 2, 2, 1, 3].length) (baseStart_3887364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3887364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3887364 prefixEnd_3887364 := by exact prefixLift 3887364
  have htrace : WordTrace (prefixWord ++ tailWord_3887364) baseStart_3887364 baseEnd_3887364 := by
    simpa [prefixWord, tailWord_3887364, baseEnd_3887364] using wordTrace_append hprefix tailTrace_3887364
  have hstable : (prefixWord ++ tailWord_3887364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3887364).length < 2 ^ (prefixWord ++ tailWord_3887364).sum := by decide
  have hdescent : baseEnd_3887364 < baseStart_3887364 := by decide
  rcases family_descends (prefixWord ++ tailWord_3887364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3887483 : List Nat := [1, 1, 1, 1, 1, 8, 2, 2, 6]
def baseStart_3887483 : Nat := 118140960795 + 3887483 * 2 ^ 59
def prefixEnd_3887483 : Nat := 4983230072969 + 3 ^ 40 * 3887483 * 2
def baseEnd_3887483 : Nat := 221794146131390993176033

theorem tailTrace_3887483 : CollatzResearch.WordTrace tailWord_3887483 prefixEnd_3887483 221794146131390993176033 := by
  unfold tailWord_3887483
  simp only [CollatzResearch.WordTrace]
  refine ⟨141788153375320495083403103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94525435583546996722268735 141788153375320495083403103)
  ·
    refine ⟨212682230062980742625104655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141788153375320495083403103 212682230062980742625104655)
    ·
      refine ⟨319023345094471113937656983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212682230062980742625104655 319023345094471113937656983)
      ·
        refine ⟨478535017641706670906485475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 319023345094471113937656983 478535017641706670906485475)
        ·
          refine ⟨717802526462560006359728213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 478535017641706670906485475 717802526462560006359728213)
          ·
            refine ⟨8411748356983125074528065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 717802526462560006359728213 8411748356983125074528065)
            ·
              refine ⟨6308811267737343805896049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8411748356983125074528065 6308811267737343805896049)
              ·
                refine ⟨4731608450803007854422037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6308811267737343805896049 4731608450803007854422037)
                ·
                  refine ⟨221794146131390993176033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4731608450803007854422037 221794146131390993176033)
                  ·
                    rfl

theorem cell23_3887483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 2, 2, 6].length) (baseStart_3887483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3887483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3887483 prefixEnd_3887483 := by exact prefixLift 3887483
  have htrace : WordTrace (prefixWord ++ tailWord_3887483) baseStart_3887483 baseEnd_3887483 := by
    simpa [prefixWord, tailWord_3887483, baseEnd_3887483] using wordTrace_append hprefix tailTrace_3887483
  have hstable : (prefixWord ++ tailWord_3887483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3887483).length < 2 ^ (prefixWord ++ tailWord_3887483).sum := by decide
  have hdescent : baseEnd_3887483 < baseStart_3887483 := by decide
  rcases family_descends (prefixWord ++ tailWord_3887483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3887513 : List Nat := [1, 2, 1, 2, 1, 4, 2, 4, 1, 5]
def baseStart_3887513 : Nat := 118140960795 + 3887513 * 2 ^ 59
def prefixEnd_3887513 : Nat := 4983230072969 + 3 ^ 40 * 3887513 * 2
def baseEnd_3887513 : Nat := 665387573200717940403053

theorem tailTrace_3887513 : CollatzResearch.WordTrace tailWord_3887513 prefixEnd_3887513 665387573200717940403053 := by
  unfold tailWord_3887513
  simp only [CollatzResearch.WordTrace]
  refine ⟨141789247565211810206995193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94526165043474540137996795 141789247565211810206995193)
  ·
    refine ⟨106341935673908857655246395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141789247565211810206995193 106341935673908857655246395)
    ·
      refine ⟨159512903510863286482869593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106341935673908857655246395 159512903510863286482869593)
      ·
        refine ⟨119634677633147464862152195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159512903510863286482869593 119634677633147464862152195)
        ·
          refine ⟨179452016449721197293228293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119634677633147464862152195 179452016449721197293228293)
          ·
            refine ⟨33647253084322724492480305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 179452016449721197293228293 33647253084322724492480305)
            ·
              refine ⟨25235439813242043369360229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33647253084322724492480305 25235439813242043369360229)
              ·
                refine ⟨4731644964982883131755043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25235439813242043369360229 4731644964982883131755043)
                ·
                  refine ⟨7097467447474324697632565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4731644964982883131755043 7097467447474324697632565)
                  ·
                    refine ⟨665387573200717940403053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7097467447474324697632565 665387573200717940403053)
                    ·
                      rfl

theorem cell23_3887513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 2, 4, 1, 5].length) (baseStart_3887513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3887513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3887513 prefixEnd_3887513 := by exact prefixLift 3887513
  have htrace : WordTrace (prefixWord ++ tailWord_3887513) baseStart_3887513 baseEnd_3887513 := by
    simpa [prefixWord, tailWord_3887513, baseEnd_3887513] using wordTrace_append hprefix tailTrace_3887513
  have hstable : (prefixWord ++ tailWord_3887513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3887513).length < 2 ^ (prefixWord ++ tailWord_3887513).sum := by decide
  have hdescent : baseEnd_3887513 < baseStart_3887513 := by decide
  rcases family_descends (prefixWord ++ tailWord_3887513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3887520 : List Nat := [2, 1, 1, 4, 1, 4, 1, 1, 1, 5, 2]
def baseStart_3887520 : Nat := 118140960795 + 3887520 * 2 ^ 59
def prefixEnd_3887520 : Nat := 4983230072969 + 3 ^ 40 * 3887520 * 2
def baseEnd_3887520 : Nat := 1996166313966735293821627

theorem tailTrace_3887520 : CollatzResearch.WordTrace tailWord_3887520 prefixEnd_3887520 1996166313966735293821627 := by
  unfold tailWord_3887520
  simp only [CollatzResearch.WordTrace]
  refine ⟨70894751438093225201250007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94526335250790966935000009 70894751438093225201250007)
  ·
    refine ⟨106342127157139837801875011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70894751438093225201250007 106342127157139837801875011)
    ·
      refine ⟨159513190735709756702812517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106342127157139837801875011 159513190735709756702812517)
      ·
        refine ⟨29908723262945579381777347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 159513190735709756702812517 29908723262945579381777347)
        ·
          refine ⟨44863084894418369072666021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29908723262945579381777347 44863084894418369072666021)
          ·
            refine ⟨8411828417703444201124879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44863084894418369072666021 8411828417703444201124879)
            ·
              refine ⟨12617742626555166301687319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8411828417703444201124879 12617742626555166301687319)
              ·
                refine ⟨18926613939832749452530979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12617742626555166301687319 18926613939832749452530979)
                ·
                  refine ⟨28389920909749124178796469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18926613939832749452530979 28389920909749124178796469)
                  ·
                    refine ⟨2661555085288980391762169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 28389920909749124178796469 2661555085288980391762169)
                    ·
                      refine ⟨1996166313966735293821627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2661555085288980391762169 1996166313966735293821627)
                      ·
                        rfl

theorem cell23_3887520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 1, 1, 1, 5, 2].length) (baseStart_3887520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3887520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3887520 prefixEnd_3887520 := by exact prefixLift 3887520
  have htrace : WordTrace (prefixWord ++ tailWord_3887520) baseStart_3887520 baseEnd_3887520 := by
    simpa [prefixWord, tailWord_3887520, baseEnd_3887520] using wordTrace_append hprefix tailTrace_3887520
  have hstable : (prefixWord ++ tailWord_3887520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3887520).length < 2 ^ (prefixWord ++ tailWord_3887520).sum := by decide
  have hdescent : baseEnd_3887520 < baseStart_3887520 := by decide
  rcases family_descends (prefixWord ++ tailWord_3887520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3887560 : List Nat := [2, 1, 3, 1, 3, 4, 1, 1, 1, 6]
def baseStart_3887560 : Nat := 118140960795 + 3887560 * 2 ^ 59
def prefixEnd_3887560 : Nat := 4983230072969 + 3 ^ 40 * 3887560 * 2
def baseEnd_3887560 : Nat := 665395617730971712440481

theorem tailTrace_3887560 : CollatzResearch.WordTrace tailWord_3887560 prefixEnd_3887560 665395617730971712440481 := by
  unfold tailWord_3887560
  simp only [CollatzResearch.WordTrace]
  refine ⟨70895480898020768616978067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94527307864027691489304089 70895480898020768616978067)
  ·
    refine ⟨106343221347031152925467101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70895480898020768616978067 106343221347031152925467101)
    ·
      refine ⟨39878708005136682347050163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106343221347031152925467101 39878708005136682347050163)
      ·
        refine ⟨59818062007705023520575245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39878708005136682347050163 59818062007705023520575245)
        ·
          refine ⟨22431773252889383820215717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59818062007705023520575245 22431773252889383820215717)
          ·
            refine ⟨4205957484916759466290447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22431773252889383820215717 4205957484916759466290447)
            ·
              refine ⟨6308936227375139199435671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4205957484916759466290447 6308936227375139199435671)
              ·
                refine ⟨9463404341062708799153507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6308936227375139199435671 9463404341062708799153507)
                ·
                  refine ⟨14195106511594063198730261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9463404341062708799153507 14195106511594063198730261)
                  ·
                    refine ⟨665395617730971712440481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14195106511594063198730261 665395617730971712440481)
                    ·
                      rfl

theorem cell23_3887560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 4, 1, 1, 1, 6].length) (baseStart_3887560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3887560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3887560 prefixEnd_3887560 := by exact prefixLift 3887560
  have htrace : WordTrace (prefixWord ++ tailWord_3887560) baseStart_3887560 baseEnd_3887560 := by
    simpa [prefixWord, tailWord_3887560, baseEnd_3887560] using wordTrace_append hprefix tailTrace_3887560
  have hstable : (prefixWord ++ tailWord_3887560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3887560).length < 2 ^ (prefixWord ++ tailWord_3887560).sum := by decide
  have hdescent : baseEnd_3887560 < baseStart_3887560 := by decide
  rcases family_descends (prefixWord ++ tailWord_3887560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3887573 : List Nat := [1, 3, 2, 3, 1, 3, 1, 9]
def baseStart_3887573 : Nat := 118140960795 + 3887573 * 2 ^ 59
def prefixEnd_3887573 : Nat := 4983230072969 + 3 ^ 40 * 3887573 * 2
def baseEnd_3887573 : Nat := 73933093645978651350329

theorem tailTrace_3887573 : CollatzResearch.WordTrace tailWord_3887573 prefixEnd_3887573 73933093645978651350329 := by
  unfold tailWord_3887573
  simp only [CollatzResearch.WordTrace]
  refine ⟨141791435944994440454179373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94527623963329626969452915 141791435944994440454179373)
  ·
    refine ⟨53171788479372915170317265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 141791435944994440454179373 53171788479372915170317265)
    ·
      refine ⟨39878841359529686377737949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53171788479372915170317265 39878841359529686377737949)
      ·
        refine ⟨14954565509823632391651731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39878841359529686377737949 14954565509823632391651731)
        ·
          refine ⟨22431848264735448587477597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14954565509823632391651731 22431848264735448587477597)
          ·
            refine ⟨8411943099275793220304099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22431848264735448587477597 8411943099275793220304099)
            ·
              refine ⟨12617914648913689830456149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8411943099275793220304099 12617914648913689830456149)
              ·
                refine ⟨73933093645978651350329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 12617914648913689830456149 73933093645978651350329)
                ·
                  rfl

theorem cell23_3887573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 1, 9].length) (baseStart_3887573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3887573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3887573 prefixEnd_3887573 := by exact prefixLift 3887573
  have htrace : WordTrace (prefixWord ++ tailWord_3887573) baseStart_3887573 baseEnd_3887573 := by
    simpa [prefixWord, tailWord_3887573, baseEnd_3887573] using wordTrace_append hprefix tailTrace_3887573
  have hstable : (prefixWord ++ tailWord_3887573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3887573).length < 2 ^ (prefixWord ++ tailWord_3887573).sum := by decide
  have hdescent : baseEnd_3887573 < baseStart_3887573 := by decide
  rcases family_descends (prefixWord ++ tailWord_3887573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3887600 : List Nat := [2, 1, 1, 1, 3, 3, 1, 3, 4, 1, 3]
def baseStart_3887600 : Nat := 118140960795 + 3887600 * 2 ^ 59
def prefixEnd_3887600 : Nat := 4983230072969 + 3 ^ 40 * 3887600 * 2
def baseEnd_3887600 : Nat := 1996207392419094980821259

theorem tailTrace_3887600 : CollatzResearch.WordTrace tailWord_3887600 prefixEnd_3887600 1996207392419094980821259 := by
  unfold tailWord_3887600
  simp only [CollatzResearch.WordTrace]
  refine ⟨70896210357948312032706127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94528280477264416043608169 70896210357948312032706127)
  ·
    refine ⟨106344315536922468049059191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70896210357948312032706127 106344315536922468049059191)
    ·
      refine ⟨159516473305383702073588787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106344315536922468049059191 159516473305383702073588787)
      ·
        refine ⟨239274709958075553110383181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159516473305383702073588787 239274709958075553110383181)
        ·
          refine ⟨89728016234278332416393693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 239274709958075553110383181 89728016234278332416393693)
          ·
            refine ⟨33648006087854374656147635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 89728016234278332416393693 33648006087854374656147635)
            ·
              refine ⟨50472009131781561984221453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33648006087854374656147635 50472009131781561984221453)
              ·
                refine ⟨18927003424418085744083045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50472009131781561984221453 18927003424418085744083045)
                ·
                  refine ⟨3548813142078391077015571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18927003424418085744083045 3548813142078391077015571)
                  ·
                    refine ⟨5323219713117586615523357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3548813142078391077015571 5323219713117586615523357)
                    ·
                      refine ⟨1996207392419094980821259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5323219713117586615523357 1996207392419094980821259)
                      ·
                        rfl

theorem cell23_3887600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 3, 4, 1, 3].length) (baseStart_3887600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3887600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3887600 prefixEnd_3887600 := by exact prefixLift 3887600
  have htrace : WordTrace (prefixWord ++ tailWord_3887600) baseStart_3887600 baseEnd_3887600 := by
    simpa [prefixWord, tailWord_3887600, baseEnd_3887600] using wordTrace_append hprefix tailTrace_3887600
  have hstable : (prefixWord ++ tailWord_3887600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3887600).length < 2 ^ (prefixWord ++ tailWord_3887600).sum := by decide
  have hdescent : baseEnd_3887600 < baseStart_3887600 := by decide
  rcases family_descends (prefixWord ++ tailWord_3887600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3887601 : List Nat := [1, 2, 2, 2, 3, 1, 5, 2, 1, 2, 2]
def baseStart_3887601 : Nat := 118140960795 + 3887601 * 2 ^ 59
def prefixEnd_3887601 : Nat := 4983230072969 + 3 ^ 40 * 3887601 * 2
def baseEnd_3887601 : Nat := 1996207905899749476908755

theorem tailTrace_3887601 : CollatzResearch.WordTrace tailWord_3887601 prefixEnd_3887601 1996207905899749476908755 := by
  unfold tailWord_3887601
  simp only [CollatzResearch.WordTrace]
  refine ⟨141792457188893001236198657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94528304792595334157465771 141792457188893001236198657)
  ·
    refine ⟨106344342891669750927148993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141792457188893001236198657 106344342891669750927148993)
    ·
      refine ⟨79758257168752313195361745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106344342891669750927148993 79758257168752313195361745)
      ·
        refine ⟨59818692876564234896521309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79758257168752313195361745 59818692876564234896521309)
        ·
          refine ⟨22432009828711588086195491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59818692876564234896521309 22432009828711588086195491)
          ·
            refine ⟨33648014743067382129293237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22432009828711588086195491 33648014743067382129293237)
            ·
              refine ⟨3154501382162567074621241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 33648014743067382129293237 3154501382162567074621241)
              ·
                refine ⟨2365876036621925305965931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3154501382162567074621241 2365876036621925305965931)
                ·
                  refine ⟨3548814054932887958948897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2365876036621925305965931 3548814054932887958948897)
                  ·
                    refine ⟨2661610541199665969211673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3548814054932887958948897 2661610541199665969211673)
                    ·
                      refine ⟨1996207905899749476908755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2661610541199665969211673 1996207905899749476908755)
                      ·
                        rfl

theorem cell23_3887601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 5, 2, 1, 2, 2].length) (baseStart_3887601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3887601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3887601 prefixEnd_3887601 := by exact prefixLift 3887601
  have htrace : WordTrace (prefixWord ++ tailWord_3887601) baseStart_3887601 baseEnd_3887601 := by
    simpa [prefixWord, tailWord_3887601, baseEnd_3887601] using wordTrace_append hprefix tailTrace_3887601
  have hstable : (prefixWord ++ tailWord_3887601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3887601).length < 2 ^ (prefixWord ++ tailWord_3887601).sum := by decide
  have hdescent : baseEnd_3887601 < baseStart_3887601 := by decide
  rcases family_descends (prefixWord ++ tailWord_3887601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3887627 : List Nat := [1, 1, 1, 1, 7, 2, 1, 1, 3, 3, 2]
def baseStart_3887627 : Nat := 118140960795 + 3887627 * 2 ^ 59
def prefixEnd_3887627 : Nat := 4983230072969 + 3 ^ 40 * 3887627 * 2
def baseEnd_3887627 : Nat := 1996221256396766375183635

theorem tailTrace_3887627 : CollatzResearch.WordTrace tailWord_3887627 prefixEnd_3887627 1996221256396766375183635 := by
  unfold tailWord_3887627
  simp only [CollatzResearch.WordTrace]
  refine ⟨141793405486798807676645135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94528936991199205117763423 141793405486798807676645135)
  ·
    refine ⟨212690108230198211514967703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141793405486798807676645135 212690108230198211514967703)
    ·
      refine ⟨319035162345297317272451555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212690108230198211514967703 319035162345297317272451555)
      ·
        refine ⟨478552743517945975908677333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 319035162345297317272451555 478552743517945975908677333)
        ·
          refine ⟨11216079926201858810359625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 478552743517945975908677333 11216079926201858810359625)
          ·
            refine ⟨8412059944651394107769719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11216079926201858810359625 8412059944651394107769719)
            ·
              refine ⟨12618089916977091161654579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8412059944651394107769719 12618089916977091161654579)
              ·
                refine ⟨18927134875465636742481869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12618089916977091161654579 18927134875465636742481869)
                ·
                  refine ⟨7097675578299613778430701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18927134875465636742481869 7097675578299613778430701)
                  ·
                    refine ⟨2661628341862355166911513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7097675578299613778430701 2661628341862355166911513)
                    ·
                      refine ⟨1996221256396766375183635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2661628341862355166911513 1996221256396766375183635)
                      ·
                        rfl

theorem cell23_3887627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 1, 1, 3, 3, 2].length) (baseStart_3887627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3887627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3887627 prefixEnd_3887627 := by exact prefixLift 3887627
  have htrace : WordTrace (prefixWord ++ tailWord_3887627) baseStart_3887627 baseEnd_3887627 := by
    simpa [prefixWord, tailWord_3887627, baseEnd_3887627] using wordTrace_append hprefix tailTrace_3887627
  have hstable : (prefixWord ++ tailWord_3887627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3887627).length < 2 ^ (prefixWord ++ tailWord_3887627).sum := by decide
  have hdescent : baseEnd_3887627 < baseStart_3887627 := by decide
  rcases family_descends (prefixWord ++ tailWord_3887627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3887643 : List Nat := [1, 1, 1, 1, 1, 1, 3, 1, 6, 4, 3]
def baseStart_3887643 : Nat := 118140960795 + 3887643 * 2 ^ 59
def prefixEnd_3887643 : Nat := 4983230072969 + 3 ^ 40 * 3887643 * 2
def baseEnd_3887643 : Nat := 1996229472087238312583561

theorem tailTrace_3887643 : CollatzResearch.WordTrace tailWord_3887643 prefixEnd_3887643 1996229472087238312583561 := by
  unfold tailWord_3887643
  simp only [CollatzResearch.WordTrace]
  refine ⟨141793989054740842409227583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94529326036493894939485055 141793989054740842409227583)
  ·
    refine ⟨212690983582111263613841375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141793989054740842409227583 212690983582111263613841375)
    ·
      refine ⟨319036475373166895420762063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212690983582111263613841375 319036475373166895420762063)
      ·
        refine ⟨478554713059750343131143095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 319036475373166895420762063 478554713059750343131143095)
        ·
          refine ⟨717832069589625514696714643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 478554713059750343131143095 717832069589625514696714643)
          ·
            refine ⟨1076748104384438272045071965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 717832069589625514696714643 1076748104384438272045071965)
            ·
              refine ⟨403780539144164352016901987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1076748104384438272045071965 403780539144164352016901987)
              ·
                refine ⟨605670808716246528025352981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 403780539144164352016901987 605670808716246528025352981)
                ·
                  refine ⟨28390819158574056001188421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 605670808716246528025352981 28390819158574056001188421)
                  ·
                    refine ⟨5323278592232635500222829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28390819158574056001188421 5323278592232635500222829)
                    ·
                      refine ⟨1996229472087238312583561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5323278592232635500222829 1996229472087238312583561)
                      ·
                        rfl

theorem cell23_3887643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 6, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 6, 4, 3].length) (baseStart_3887643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3887643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3887643 prefixEnd_3887643 := by exact prefixLift 3887643
  have htrace : WordTrace (prefixWord ++ tailWord_3887643) baseStart_3887643 baseEnd_3887643 := by
    simpa [prefixWord, tailWord_3887643, baseEnd_3887643] using wordTrace_append hprefix tailTrace_3887643
  have hstable : (prefixWord ++ tailWord_3887643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3887643).length < 2 ^ (prefixWord ++ tailWord_3887643).sum := by decide
  have hdescent : baseEnd_3887643 < baseStart_3887643 := by decide
  rcases family_descends (prefixWord ++ tailWord_3887643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3887652 : List Nat := [2, 3, 1, 5, 2, 1, 2, 2, 1, 2, 2]
def baseStart_3887652 : Nat := 118140960795 + 3887652 * 2 ^ 59
def prefixEnd_3887652 : Nat := 4983230072969 + 3 ^ 40 * 3887652 * 2
def baseEnd_3887652 : Nat := 1996234093413128777371021

theorem tailTrace_3887652 : CollatzResearch.WordTrace tailWord_3887652 prefixEnd_3887652 1996234093413128777371021 := by
  unfold tailWord_3887652
  simp only [CollatzResearch.WordTrace]
  refine ⟨70897158655854118473152605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94529544874472157964203473 70897158655854118473152605)
  ·
    refine ⟨26586434495945294427432227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70897158655854118473152605 26586434495945294427432227)
    ·
      refine ⟨39879651743917941641148341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26586434495945294427432227 39879651743917941641148341)
      ·
        refine ⟨3738717350992307028857657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 39879651743917941641148341 3738717350992307028857657)
        ·
          refine ⟨2804038013244230271643243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3738717350992307028857657 2804038013244230271643243)
          ·
            refine ⟨4206057019866345407464865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2804038013244230271643243 4206057019866345407464865)
            ·
              refine ⟨3154542764899759055598649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4206057019866345407464865 3154542764899759055598649)
              ·
                refine ⟨2365907073674819291698987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3154542764899759055598649 2365907073674819291698987)
                ·
                  refine ⟨3548860610512228937548481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2365907073674819291698987 3548860610512228937548481)
                  ·
                    refine ⟨2661645457884171703161361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3548860610512228937548481 2661645457884171703161361)
                    ·
                      refine ⟨1996234093413128777371021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2661645457884171703161361 1996234093413128777371021)
                      ·
                        rfl

theorem cell23_3887652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 2, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 2, 1, 2, 2, 1, 2, 2].length) (baseStart_3887652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3887652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3887652 prefixEnd_3887652 := by exact prefixLift 3887652
  have htrace : WordTrace (prefixWord ++ tailWord_3887652) baseStart_3887652 baseEnd_3887652 := by
    simpa [prefixWord, tailWord_3887652, baseEnd_3887652] using wordTrace_append hprefix tailTrace_3887652
  have hstable : (prefixWord ++ tailWord_3887652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3887652).length < 2 ^ (prefixWord ++ tailWord_3887652).sum := by decide
  have hdescent : baseEnd_3887652 < baseStart_3887652 := by decide
  rcases family_descends (prefixWord ++ tailWord_3887652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3887674 : List Nat := [3, 1, 1, 1, 3, 3, 2, 3, 2, 2, 2]
def baseStart_3887674 : Nat := 118140960795 + 3887674 * 2 ^ 59
def prefixEnd_3887674 : Nat := 4983230072969 + 3 ^ 40 * 3887674 * 2
def baseEnd_3887674 : Nat := 1996245389987527691295919

theorem tailTrace_3887674 : CollatzResearch.WordTrace tailWord_3887674 prefixEnd_3887674 1996245389987527691295919 := by
  unfold tailWord_3887674
  simp only [CollatzResearch.WordTrace]
  refine ⟨35448779929407133675901519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94530079811752356469070717 35448779929407133675901519)
  ·
    refine ⟨53173169894110700513852279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35448779929407133675901519 53173169894110700513852279)
    ·
      refine ⟨79759754841166050770778419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53173169894110700513852279 79759754841166050770778419)
      ·
        refine ⟨119639632261749076156167629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79759754841166050770778419 119639632261749076156167629)
        ·
          refine ⟨44864862098155903558562861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 119639632261749076156167629 44864862098155903558562861)
          ·
            refine ⟨16824323286808463834461073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44864862098155903558562861 16824323286808463834461073)
            ·
              refine ⟨12618242465106347875845805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16824323286808463834461073 12618242465106347875845805)
              ·
                refine ⟨4731840924414880453442177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12618242465106347875845805 4731840924414880453442177)
                ·
                  refine ⟨3548880693311160340081633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4731840924414880453442177 3548880693311160340081633)
                  ·
                    refine ⟨2661660519983370255061225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3548880693311160340081633 2661660519983370255061225)
                    ·
                      refine ⟨1996245389987527691295919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2661660519983370255061225 1996245389987527691295919)
                      ·
                        rfl

theorem cell23_3887674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 2, 3, 2, 2, 2].length) (baseStart_3887674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3887674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3887674 prefixEnd_3887674 := by exact prefixLift 3887674
  have htrace : WordTrace (prefixWord ++ tailWord_3887674) baseStart_3887674 baseEnd_3887674 := by
    simpa [prefixWord, tailWord_3887674, baseEnd_3887674] using wordTrace_append hprefix tailTrace_3887674
  have hstable : (prefixWord ++ tailWord_3887674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3887674).length < 2 ^ (prefixWord ++ tailWord_3887674).sum := by decide
  have hdescent : baseEnd_3887674 < baseStart_3887674 := by decide
  rcases family_descends (prefixWord ++ tailWord_3887674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3887697 : List Nat := [1, 2, 2, 1, 3, 4, 2, 3, 5]
def baseStart_3887697 : Nat := 118140960795 + 3887697 * 2 ^ 59
def prefixEnd_3887697 : Nat := 4983230072969 + 3 ^ 40 * 3887697 * 2
def baseEnd_3887697 : Nat := 221806355560286789034257

theorem tailTrace_3887697 : CollatzResearch.WordTrace tailWord_3887697 prefixEnd_3887697 221806355560286789034257 := by
  unfold tailWord_3887697
  simp only [CollatzResearch.WordTrace]
  refine ⟨141795958596545209631693345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94530639064363473087795563 141795958596545209631693345)
  ·
    refine ⟨106346968947408907223770009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141795958596545209631693345 106346968947408907223770009)
    ·
      refine ⟨79760226710556680417827507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106346968947408907223770009 79760226710556680417827507)
      ·
        refine ⟨119640340065835020626741261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79760226710556680417827507 119640340065835020626741261)
        ·
          refine ⟨44865127524688132735027973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 119640340065835020626741261 44865127524688132735027973)
          ·
            refine ⟨8412211410879024887817745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44865127524688132735027973 8412211410879024887817745)
            ·
              refine ⟨6309158558159268665863309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8412211410879024887817745 6309158558159268665863309)
              ·
                refine ⟨2365934459309725749698741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6309158558159268665863309 2365934459309725749698741)
                ·
                  refine ⟨221806355560286789034257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2365934459309725749698741 221806355560286789034257)
                  ·
                    rfl

theorem cell23_3887697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 2, 3, 5].length) (baseStart_3887697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3887697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3887697 prefixEnd_3887697 := by exact prefixLift 3887697
  have htrace : WordTrace (prefixWord ++ tailWord_3887697) baseStart_3887697 baseEnd_3887697 := by
    simpa [prefixWord, tailWord_3887697, baseEnd_3887697] using wordTrace_append hprefix tailTrace_3887697
  have hstable : (prefixWord ++ tailWord_3887697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3887697).length < 2 ^ (prefixWord ++ tailWord_3887697).sum := by decide
  have hdescent : baseEnd_3887697 < baseStart_3887697 := by decide
  rcases family_descends (prefixWord ++ tailWord_3887697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3887708 : List Nat := [2, 2, 4, 1, 3, 2, 1, 2, 2, 2, 2]
def baseStart_3887708 : Nat := 118140960795 + 3887708 * 2 ^ 59
def prefixEnd_3887708 : Nat := 4983230072969 + 3 ^ 40 * 3887708 * 2
def baseEnd_3887708 : Nat := 1996262848329780558270763

theorem tailTrace_3887708 : CollatzResearch.WordTrace tailWord_3887708 prefixEnd_3887708 1996262848329780558270763 := by
  unfold tailWord_3887708
  simp only [CollatzResearch.WordTrace]
  refine ⟨70898179899752679255171889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94530906533003572340229185 70898179899752679255171889)
  ·
    refine ⟨53173634924814509441378917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70898179899752679255171889 53173634924814509441378917)
    ·
      refine ⟨9970056548402720520258547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 53173634924814509441378917 9970056548402720520258547)
      ·
        refine ⟨14955084822604080780387821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9970056548402720520258547 14955084822604080780387821)
        ·
          refine ⟨5608156808476530292645433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14955084822604080780387821 5608156808476530292645433)
          ·
            refine ⟨4206117606357397719484075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5608156808476530292645433 4206117606357397719484075)
            ·
              refine ⟨6309176409536096579226113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4206117606357397719484075 6309176409536096579226113)
              ·
                refine ⟨4731882307152072434419585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6309176409536096579226113 4731882307152072434419585)
                ·
                  refine ⟨3548911730364054325814689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4731882307152072434419585 3548911730364054325814689)
                  ·
                    refine ⟨2661683797773040744361017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3548911730364054325814689 2661683797773040744361017)
                    ·
                      refine ⟨1996262848329780558270763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2661683797773040744361017 1996262848329780558270763)
                      ·
                        rfl

theorem cell23_3887708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 2, 1, 2, 2, 2, 2].length) (baseStart_3887708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3887708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3887708 prefixEnd_3887708 := by exact prefixLift 3887708
  have htrace : WordTrace (prefixWord ++ tailWord_3887708) baseStart_3887708 baseEnd_3887708 := by
    simpa [prefixWord, tailWord_3887708, baseEnd_3887708] using wordTrace_append hprefix tailTrace_3887708
  have hstable : (prefixWord ++ tailWord_3887708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3887708).length < 2 ^ (prefixWord ++ tailWord_3887708).sum := by decide
  have hdescent : baseEnd_3887708 < baseStart_3887708 := by decide
  rcases family_descends (prefixWord ++ tailWord_3887708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3887714 : List Nat := [3, 3, 2, 3, 1, 1, 2, 1, 7]
def baseStart_3887714 : Nat := 118140960795 + 3887714 * 2 ^ 59
def prefixEnd_3887714 : Nat := 4983230072969 + 3 ^ 40 * 3887714 * 2
def baseEnd_3887714 : Nat := 221807325468189726088415

theorem tailTrace_3887714 : CollatzResearch.WordTrace tailWord_3887714 prefixEnd_3887714 221807325468189726088415 := by
  unfold tailWord_3887714
  simp only [CollatzResearch.WordTrace]
  refine ⟨35449144659370905383765549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94531052424989081023374797 35449144659370905383765549)
  ·
    refine ⟨13293429247264089518912081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35449144659370905383765549 13293429247264089518912081)
    ·
      refine ⟨9970071935448067139184061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13293429247264089518912081 9970071935448067139184061)
      ·
        refine ⟨3738776975793025177194023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9970071935448067139184061 3738776975793025177194023)
        ·
          refine ⟨5608165463689537765791035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3738776975793025177194023 5608165463689537765791035)
          ·
            refine ⟨8412248195534306648686553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5608165463689537765791035 8412248195534306648686553)
            ·
              refine ⟨6309186146650729986514915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8412248195534306648686553 6309186146650729986514915)
              ·
                refine ⟨9463779219976094979772373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6309186146650729986514915 9463779219976094979772373)
                ·
                  refine ⟨221807325468189726088415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9463779219976094979772373 221807325468189726088415)
                  ·
                    rfl

theorem cell23_3887714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 2, 1, 7].length) (baseStart_3887714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3887714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3887714 prefixEnd_3887714 := by exact prefixLift 3887714
  have htrace : WordTrace (prefixWord ++ tailWord_3887714) baseStart_3887714 baseEnd_3887714 := by
    simpa [prefixWord, tailWord_3887714, baseEnd_3887714] using wordTrace_append hprefix tailTrace_3887714
  have hstable : (prefixWord ++ tailWord_3887714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3887714).length < 2 ^ (prefixWord ++ tailWord_3887714).sum := by decide
  have hdescent : baseEnd_3887714 < baseStart_3887714 := by decide
  rcases family_descends (prefixWord ++ tailWord_3887714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3887743 : List Nat := [1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 6]
def baseStart_3887743 : Nat := 118140960795 + 3887743 * 2 ^ 59
def prefixEnd_3887743 : Nat := 4983230072969 + 3 ^ 40 * 3887743 * 2
def baseEnd_3887743 : Nat := 1996280820152687921333101

theorem tailTrace_3887743 : CollatzResearch.WordTrace tailWord_3887743 prefixEnd_3887743 1996280820152687921333101 := by
  unfold tailWord_3887743
  simp only [CollatzResearch.WordTrace]
  refine ⟨141797636354378559487867883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94531757569585706325245255 141797636354378559487867883)
  ·
    refine ⟨212696454531567839231801825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141797636354378559487867883 212696454531567839231801825)
    ·
      refine ⟨159522340898675879423851369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 212696454531567839231801825 159522340898675879423851369)
      ·
        refine ⟨119641755674006909567888527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159522340898675879423851369 119641755674006909567888527)
        ·
          refine ⟨179462633511010364351832791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119641755674006909567888527 179462633511010364351832791)
          ·
            refine ⟨269193950266515546527749187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 179462633511010364351832791 269193950266515546527749187)
            ·
              refine ⟨403790925399773319791623781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 269193950266515546527749187 403790925399773319791623781)
              ·
                refine ⟨75710798512457497460929459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 403790925399773319791623781 75710798512457497460929459)
                ·
                  refine ⟨113566197768686246191394189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 75710798512457497460929459 113566197768686246191394189)
                  ·
                    refine ⟨42587324163257342321772821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 113566197768686246191394189 42587324163257342321772821)
                    ·
                      refine ⟨1996280820152687921333101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 42587324163257342321772821 1996280820152687921333101)
                      ·
                        rfl

theorem cell23_3887743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 6].length) (baseStart_3887743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3887743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3887743 prefixEnd_3887743 := by exact prefixLift 3887743
  have htrace : WordTrace (prefixWord ++ tailWord_3887743) baseStart_3887743 baseEnd_3887743 := by
    simpa [prefixWord, tailWord_3887743, baseEnd_3887743] using wordTrace_append hprefix tailTrace_3887743
  have hstable : (prefixWord ++ tailWord_3887743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3887743).length < 2 ^ (prefixWord ++ tailWord_3887743).sum := by decide
  have hdescent : baseEnd_3887743 < baseStart_3887743 := by decide
  rcases family_descends (prefixWord ++ tailWord_3887743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3887764 : List Nat := [2, 4, 2, 2, 1, 2, 1, 2, 2, 1, 4]
def baseStart_3887764 : Nat := 118140960795 + 3887764 * 2 ^ 59
def prefixEnd_3887764 : Nat := 4983230072969 + 3 ^ 40 * 3887764 * 2
def baseEnd_3887764 : Nat := 1996291603246432339170505

theorem tailTrace_3887764 : CollatzResearch.WordTrace tailWord_3887764 prefixEnd_3887764 1996291603246432339170505 := by
  unfold tailWord_3887764
  simp only [CollatzResearch.WordTrace]
  refine ⟨70899201143651240037191173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94532268191534986716254897 70899201143651240037191173)
  ·
    refine ⟨13293600214434607506973345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 70899201143651240037191173 13293600214434607506973345)
    ·
      refine ⟨9970200160825955630230009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13293600214434607506973345 9970200160825955630230009)
      ·
        refine ⟨7477650120619466722672507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9970200160825955630230009 7477650120619466722672507)
        ·
          refine ⟨11216475180929200084008761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7477650120619466722672507 11216475180929200084008761)
          ·
            refine ⟨8412356385696900063006571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11216475180929200084008761 8412356385696900063006571)
            ·
              refine ⟨12618534578545350094509857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8412356385696900063006571 12618534578545350094509857)
              ·
                refine ⟨9463900933909012570882393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12618534578545350094509857 9463900933909012570882393)
                ·
                  refine ⟨7097925700431759428161795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9463900933909012570882393 7097925700431759428161795)
                  ·
                    refine ⟨10646888550647639142242693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7097925700431759428161795 10646888550647639142242693)
                    ·
                      refine ⟨1996291603246432339170505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10646888550647639142242693 1996291603246432339170505)
                      ·
                        rfl

theorem cell23_3887764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 1, 2, 2, 1, 4].length) (baseStart_3887764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3887764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3887764 prefixEnd_3887764 := by exact prefixLift 3887764
  have htrace : WordTrace (prefixWord ++ tailWord_3887764) baseStart_3887764 baseEnd_3887764 := by
    simpa [prefixWord, tailWord_3887764, baseEnd_3887764] using wordTrace_append hprefix tailTrace_3887764
  have hstable : (prefixWord ++ tailWord_3887764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3887764).length < 2 ^ (prefixWord ++ tailWord_3887764).sum := by decide
  have hdescent : baseEnd_3887764 < baseStart_3887764 := by decide
  rcases family_descends (prefixWord ++ tailWord_3887764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3887767 : List Nat := [1, 1, 3, 3, 2, 1, 3, 2, 2, 2, 3]
def baseStart_3887767 : Nat := 118140960795 + 3887767 * 2 ^ 59
def prefixEnd_3887767 : Nat := 4983230072969 + 3 ^ 40 * 3887767 * 2
def baseEnd_3887767 : Nat := 1996293143688395827432991

theorem tailTrace_3887767 : CollatzResearch.WordTrace tailWord_3887767 prefixEnd_3887767 1996293143688395827432991 := by
  unfold tailWord_3887767
  simp only [CollatzResearch.WordTrace]
  refine ⟨141798511706291611586741555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94532341137527741057827703 141798511706291611586741555)
  ·
    refine ⟨212697767559437417380112333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141798511706291611586741555 212697767559437417380112333)
    ·
      refine ⟨79761662834789031517542125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 212697767559437417380112333 79761662834789031517542125)
      ·
        refine ⟨29910623563045886819078297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79761662834789031517542125 29910623563045886819078297)
        ·
          refine ⟨22432967672284415114308723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29910623563045886819078297 22432967672284415114308723)
          ·
            refine ⟨33649451508426622671463085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22432967672284415114308723 33649451508426622671463085)
            ·
              refine ⟨12618544315659983501798657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33649451508426622671463085 12618544315659983501798657)
              ·
                refine ⟨9463908236744987626348993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12618544315659983501798657 9463908236744987626348993)
                ·
                  refine ⟨7097931177558740719761745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9463908236744987626348993 7097931177558740719761745)
                  ·
                    refine ⟨5323448383169055539821309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7097931177558740719761745 5323448383169055539821309)
                    ·
                      refine ⟨1996293143688395827432991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5323448383169055539821309 1996293143688395827432991)
                      ·
                        rfl

theorem cell23_3887767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 3, 2, 2, 2, 3].length) (baseStart_3887767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3887767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3887767 prefixEnd_3887767 := by exact prefixLift 3887767
  have htrace : WordTrace (prefixWord ++ tailWord_3887767) baseStart_3887767 baseEnd_3887767 := by
    simpa [prefixWord, tailWord_3887767, baseEnd_3887767] using wordTrace_append hprefix tailTrace_3887767
  have hstable : (prefixWord ++ tailWord_3887767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3887767).length < 2 ^ (prefixWord ++ tailWord_3887767).sum := by decide
  have hdescent : baseEnd_3887767 < baseStart_3887767 := by decide
  rcases family_descends (prefixWord ++ tailWord_3887767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3887821 : List Nat := [1, 6, 2, 1, 2, 1, 2, 2, 6]
def baseStart_3887821 : Nat := 118140960795 + 3887821 * 2 ^ 59
def prefixEnd_3887821 : Nat := 4983230072969 + 3 ^ 40 * 3887821 * 2
def baseEnd_3887821 : Nat := 221813430182637624017527

theorem tailTrace_3887821 : CollatzResearch.WordTrace tailWord_3887821 prefixEnd_3887821 221813430182637624017527 := by
  unfold tailWord_3887821
  simp only [CollatzResearch.WordTrace]
  refine ⟨141800481248095978809207317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94533654165397319206138211 141800481248095978809207317)
  ·
    refine ⟨6646897558504499006681593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 141800481248095978809207317 6646897558504499006681593)
    ·
      refine ⟨4985173168878374255011195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6646897558504499006681593 4985173168878374255011195)
      ·
        refine ⟨7477759753317561382516793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4985173168878374255011195 7477759753317561382516793)
        ·
          refine ⟨5608319814988171036887595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7477759753317561382516793 5608319814988171036887595)
          ·
            refine ⟨8412479722482256555331393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5608319814988171036887595 8412479722482256555331393)
            ·
              refine ⟨6309359791861692416498545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8412479722482256555331393 6309359791861692416498545)
              ·
                refine ⟨4732019843896269312373909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6309359791861692416498545 4732019843896269312373909)
                ·
                  refine ⟨221813430182637624017527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4732019843896269312373909 221813430182637624017527)
                  ·
                    rfl

theorem cell23_3887821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 2, 2, 6].length) (baseStart_3887821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3887821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3887821 prefixEnd_3887821 := by exact prefixLift 3887821
  have htrace : WordTrace (prefixWord ++ tailWord_3887821) baseStart_3887821 baseEnd_3887821 := by
    simpa [prefixWord, tailWord_3887821, baseEnd_3887821] using wordTrace_append hprefix tailTrace_3887821
  have hstable : (prefixWord ++ tailWord_3887821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3887821).length < 2 ^ (prefixWord ++ tailWord_3887821).sum := by decide
  have hdescent : baseEnd_3887821 < baseStart_3887821 := by decide
  rcases family_descends (prefixWord ++ tailWord_3887821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3887831 : List Nat := [1, 1, 3, 2, 1, 5, 1, 4, 1, 1, 3]
def baseStart_3887831 : Nat := 118140960795 + 3887831 * 2 ^ 59
def prefixEnd_3887831 : Nat := 4983230072969 + 3 ^ 40 * 3887831 * 2
def baseEnd_3887831 : Nat := 1996326006450283577032697

theorem tailTrace_3887831 : CollatzResearch.WordTrace tailWord_3887831 prefixEnd_3887831 1996326006450283577032697 := by
  unfold tailWord_3887831
  simp only [CollatzResearch.WordTrace]
  refine ⟨141800845978059750517071347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94533897318706500344714231 141800845978059750517071347)
  ·
    refine ⟨212701268967089625775607021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141800845978059750517071347 212701268967089625775607021)
    ·
      refine ⟨79762975862658609665852633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 212701268967089625775607021 79762975862658609665852633)
      ·
        refine ⟨59822231896993957249389475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79762975862658609665852633 59822231896993957249389475)
        ·
          refine ⟨89733347845490935874084213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59822231896993957249389475 89733347845490935874084213)
          ·
            refine ⟨8412501360514775238195395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 89733347845490935874084213 8412501360514775238195395)
            ·
              refine ⟨12618752040772162857293093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8412501360514775238195395 12618752040772162857293093)
              ·
                refine ⟨2366016007644780535742455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12618752040772162857293093 2366016007644780535742455)
                ·
                  refine ⟨3549024011467170803613683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2366016007644780535742455 3549024011467170803613683)
                  ·
                    refine ⟨5323536017200756205420525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3549024011467170803613683 5323536017200756205420525)
                    ·
                      refine ⟨1996326006450283577032697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5323536017200756205420525 1996326006450283577032697)
                      ·
                        rfl

theorem cell23_3887831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 1, 4, 1, 1, 3].length) (baseStart_3887831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3887831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3887831 prefixEnd_3887831 := by exact prefixLift 3887831
  have htrace : WordTrace (prefixWord ++ tailWord_3887831) baseStart_3887831 baseEnd_3887831 := by
    simpa [prefixWord, tailWord_3887831, baseEnd_3887831] using wordTrace_append hprefix tailTrace_3887831
  have hstable : (prefixWord ++ tailWord_3887831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3887831).length < 2 ^ (prefixWord ++ tailWord_3887831).sum := by decide
  have hdescent : baseEnd_3887831 < baseStart_3887831 := by decide
  rcases family_descends (prefixWord ++ tailWord_3887831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3887840 : List Nat := [2, 1, 1, 3, 1, 2, 1, 3, 3, 1, 5]
def baseStart_3887840 : Nat := 118140960795 + 3887840 * 2 ^ 59
def prefixEnd_3887840 : Nat := 4983230072969 + 3 ^ 40 * 3887840 * 2
def baseEnd_3887840 : Nat := 1996330627776174041820155

theorem tailTrace_3887840 : CollatzResearch.WordTrace tailWord_3887840 prefixEnd_3887840 1996330627776174041820155 := by
  unfold tailWord_3887840
  simp only [CollatzResearch.WordTrace]
  refine ⟨70900587117513572527074487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94534116156684763369432649 70900587117513572527074487)
  ·
    refine ⟨106350880676270358790611731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70900587117513572527074487 106350880676270358790611731)
    ·
      refine ⟨159526321014405538185917597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106350880676270358790611731 159526321014405538185917597)
      ·
        refine ⟨59822370380402076819719099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 159526321014405538185917597 59822370380402076819719099)
        ·
          refine ⟨89733555570603115229578649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59822370380402076819719099 89733555570603115229578649)
          ·
            refine ⟨67300166677952336422183987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89733555570603115229578649 67300166677952336422183987)
            ·
              refine ⟨100950250016928504633275981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67300166677952336422183987 100950250016928504633275981)
              ·
                refine ⟨37856343756348189237478493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 100950250016928504633275981 37856343756348189237478493)
                ·
                  refine ⟨14196128908630570964054435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37856343756348189237478493 14196128908630570964054435)
                  ·
                    refine ⟨21294193362945856446081653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14196128908630570964054435 21294193362945856446081653)
                    ·
                      refine ⟨1996330627776174041820155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21294193362945856446081653 1996330627776174041820155)
                      ·
                        rfl

theorem cell23_3887840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 3, 3, 1, 5].length) (baseStart_3887840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3887840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3887840 prefixEnd_3887840 := by exact prefixLift 3887840
  have htrace : WordTrace (prefixWord ++ tailWord_3887840) baseStart_3887840 baseEnd_3887840 := by
    simpa [prefixWord, tailWord_3887840, baseEnd_3887840] using wordTrace_append hprefix tailTrace_3887840
  have hstable : (prefixWord ++ tailWord_3887840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3887840).length < 2 ^ (prefixWord ++ tailWord_3887840).sum := by decide
  have hdescent : baseEnd_3887840 < baseStart_3887840 := by decide
  rcases family_descends (prefixWord ++ tailWord_3887840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3887857 : List Nat := [1, 2, 2, 2, 2, 2, 1, 3, 3, 2, 3]
def baseStart_3887857 : Nat := 118140960795 + 3887857 * 2 ^ 59
def prefixEnd_3887857 : Nat := 4983230072969 + 3 ^ 40 * 3887857 * 2
def baseEnd_3887857 : Nat := 1996339356947300475307577

theorem tailTrace_3887857 : CollatzResearch.WordTrace tailWord_3887857 prefixEnd_3887857 1996339356947300475307577 := by
  unfold tailWord_3887857
  simp only [CollatzResearch.WordTrace]
  refine ⟨141801794275965556957517825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94534529517310371305011883 141801794275965556957517825)
  ·
    refine ⟨106351345706974167718138369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141801794275965556957517825 106351345706974167718138369)
    ·
      refine ⟨79763509280230625788603777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106351345706974167718138369 79763509280230625788603777)
      ·
        refine ⟨59822631960172969341452833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79763509280230625788603777 59822631960172969341452833)
        ·
          refine ⟨44866973970129727006089625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59822631960172969341452833 44866973970129727006089625)
          ·
            refine ⟨33650230477597295254567219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44866973970129727006089625 33650230477597295254567219)
            ·
              refine ⟨50475345716395942881850829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33650230477597295254567219 50475345716395942881850829)
              ·
                refine ⟨18928254643648478580694061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50475345716395942881850829 18928254643648478580694061)
                ·
                  refine ⟨7098095491368179467760273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18928254643648478580694061 7098095491368179467760273)
                  ·
                    refine ⟨5323571618526134600820205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7098095491368179467760273 5323571618526134600820205)
                    ·
                      refine ⟨1996339356947300475307577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5323571618526134600820205 1996339356947300475307577)
                      ·
                        rfl

theorem cell23_3887857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 3, 3, 2, 3].length) (baseStart_3887857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3887857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3887857 prefixEnd_3887857 := by exact prefixLift 3887857
  have htrace : WordTrace (prefixWord ++ tailWord_3887857) baseStart_3887857 baseEnd_3887857 := by
    simpa [prefixWord, tailWord_3887857, baseEnd_3887857] using wordTrace_append hprefix tailTrace_3887857
  have hstable : (prefixWord ++ tailWord_3887857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3887857).length < 2 ^ (prefixWord ++ tailWord_3887857).sum := by decide
  have hdescent : baseEnd_3887857 < baseStart_3887857 := by decide
  rcases family_descends (prefixWord ++ tailWord_3887857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3887897 : List Nat := [1, 2, 1, 2, 1, 1, 1, 3, 2, 7, 2]
def baseStart_3887897 : Nat := 118140960795 + 3887897 * 2 ^ 59
def prefixEnd_3887897 : Nat := 4983230072969 + 3 ^ 40 * 3887897 * 2
def baseEnd_3887897 : Nat := 1996359896173480318807393

theorem tailTrace_3887897 : CollatzResearch.WordTrace tailWord_3887897 prefixEnd_3887897 1996359896173480318807393 := by
  unfold tailWord_3887897
  simp only [CollatzResearch.WordTrace]
  refine ⟨141803253195820643788973945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94535502130547095859315963 141803253195820643788973945)
  ·
    refine ⟨106352439896865482841730459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141803253195820643788973945 106352439896865482841730459)
    ·
      refine ⟨159528659845298224262595689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106352439896865482841730459 159528659845298224262595689)
      ·
        refine ⟨119646494883973668196946767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159528659845298224262595689 119646494883973668196946767)
        ·
          refine ⟨179469742325960502295420151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119646494883973668196946767 179469742325960502295420151)
          ·
            refine ⟨269204613488940753443130227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 179469742325960502295420151 269204613488940753443130227)
            ·
              refine ⟨403806920233411130164695341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 269204613488940753443130227 403806920233411130164695341)
              ·
                refine ⟨151427595087529173811760753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 403806920233411130164695341 151427595087529173811760753)
                ·
                  refine ⟨113570696315646880358820565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 151427595087529173811760753 113570696315646880358820565)
                  ·
                    refine ⟨2661813194897973758409857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 113570696315646880358820565 2661813194897973758409857)
                    ·
                      refine ⟨1996359896173480318807393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2661813194897973758409857 1996359896173480318807393)
                      ·
                        rfl

theorem cell23_3887897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 3, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 3, 2, 7, 2].length) (baseStart_3887897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3887897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3887897 prefixEnd_3887897 := by exact prefixLift 3887897
  have htrace : WordTrace (prefixWord ++ tailWord_3887897) baseStart_3887897 baseEnd_3887897 := by
    simpa [prefixWord, tailWord_3887897, baseEnd_3887897] using wordTrace_append hprefix tailTrace_3887897
  have hstable : (prefixWord ++ tailWord_3887897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3887897).length < 2 ^ (prefixWord ++ tailWord_3887897).sum := by decide
  have hdescent : baseEnd_3887897 < baseStart_3887897 := by decide
  rcases family_descends (prefixWord ++ tailWord_3887897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3887904 : List Nat := [2, 1, 1, 5, 1, 2, 3, 1, 1, 3, 3]
def baseStart_3887904 : Nat := 118140960795 + 3887904 * 2 ^ 59
def prefixEnd_3887904 : Nat := 4983230072969 + 3 ^ 40 * 3887904 * 2
def baseEnd_3887904 : Nat := 1996363490538061791419861

theorem tailTrace_3887904 : CollatzResearch.WordTrace tailWord_3887904 prefixEnd_3887904 1996363490538061791419861 := by
  unfold tailWord_3887904
  simp only [CollatzResearch.WordTrace]
  refine ⟨70901754253397641992239383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94535672337863522656319177 70901754253397641992239383)
  ·
    refine ⟨106352631380096462988359075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70901754253397641992239383 106352631380096462988359075)
    ·
      refine ⟨159528947070144694482538613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106352631380096462988359075 159528947070144694482538613)
      ·
        refine ⟨14955838787826065107737995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 159528947070144694482538613 14955838787826065107737995)
        ·
          refine ⟨22433758181739097661606993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14955838787826065107737995 22433758181739097661606993)
          ·
            refine ⟨16825318636304323246205245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22433758181739097661606993 16825318636304323246205245)
            ·
              refine ⟨6309494488614121217326967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16825318636304323246205245 6309494488614121217326967)
              ·
                refine ⟨9464241732921181825990451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6309494488614121217326967 9464241732921181825990451)
                ·
                  refine ⟨14196362599381772738985677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9464241732921181825990451 14196362599381772738985677)
                  ·
                    refine ⟨5323635974768164777119629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14196362599381772738985677 5323635974768164777119629)
                    ·
                      refine ⟨1996363490538061791419861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5323635974768164777119629 1996363490538061791419861)
                      ·
                        rfl

theorem cell23_3887904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 3, 1, 1, 3, 3].length) (baseStart_3887904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3887904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3887904 prefixEnd_3887904 := by exact prefixLift 3887904
  have htrace : WordTrace (prefixWord ++ tailWord_3887904) baseStart_3887904 baseEnd_3887904 := by
    simpa [prefixWord, tailWord_3887904, baseEnd_3887904] using wordTrace_append hprefix tailTrace_3887904
  have hstable : (prefixWord ++ tailWord_3887904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3887904).length < 2 ^ (prefixWord ++ tailWord_3887904).sum := by decide
  have hdescent : baseEnd_3887904 < baseStart_3887904 := by decide
  rcases family_descends (prefixWord ++ tailWord_3887904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3887920 : List Nat := [2, 1, 1, 1, 2, 2, 1, 4, 1, 8]
def baseStart_3887920 : Nat := 118140960795 + 3887920 * 2 ^ 59
def prefixEnd_3887920 : Nat := 4983230072969 + 3 ^ 40 * 3887920 * 2
def baseEnd_3887920 : Nat := 665457235409511242939929

theorem tailTrace_3887920 : CollatzResearch.WordTrace tailWord_3887920 prefixEnd_3887920 665457235409511242939929 := by
  unfold tailWord_3887920
  simp only [CollatzResearch.WordTrace]
  refine ⟨70902046037368659358530607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94536061383158212478040809 70902046037368659358530607)
  ·
    refine ⟨106353069056052989037795911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70902046037368659358530607 106353069056052989037795911)
    ·
      refine ⟨159529603584079483556693867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106353069056052989037795911 159529603584079483556693867)
      ·
        refine ⟨239294405376119225335040801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159529603584079483556693867 239294405376119225335040801)
        ·
          refine ⟨179470804032089419001280601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 239294405376119225335040801 179470804032089419001280601)
          ·
            refine ⟨134603103024067064250960451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 179470804032089419001280601 134603103024067064250960451)
            ·
              refine ⟨201904654536100596376440677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 134603103024067064250960451 201904654536100596376440677)
              ·
                refine ⟨37857122725518861820582627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 201904654536100596376440677 37857122725518861820582627)
                ·
                  refine ⟨56785684088278292730873941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37857122725518861820582627 56785684088278292730873941)
                  ·
                    refine ⟨665457235409511242939929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 56785684088278292730873941 665457235409511242939929)
                    ·
                      rfl

theorem cell23_3887920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 4, 1, 8].length) (baseStart_3887920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3887920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3887920 prefixEnd_3887920 := by exact prefixLift 3887920
  have htrace : WordTrace (prefixWord ++ tailWord_3887920) baseStart_3887920 baseEnd_3887920 := by
    simpa [prefixWord, tailWord_3887920, baseEnd_3887920] using wordTrace_append hprefix tailTrace_3887920
  have hstable : (prefixWord ++ tailWord_3887920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3887920).length < 2 ^ (prefixWord ++ tailWord_3887920).sum := by decide
  have hdescent : baseEnd_3887920 < baseStart_3887920 := by decide
  rcases family_descends (prefixWord ++ tailWord_3887920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3887957 : List Nat := [1, 3, 2, 2, 2, 1, 2, 1, 1, 4, 4]
def baseStart_3887957 : Nat := 118140960795 + 3887957 * 2 ^ 59
def prefixEnd_3887957 : Nat := 4983230072969 + 3 ^ 40 * 3887957 * 2
def baseEnd_3887957 : Nat := 1996390705012750084057117

theorem tailTrace_3887957 : CollatzResearch.WordTrace tailWord_3887957 prefixEnd_3887957 1996390705012750084057117 := by
  unfold tailWord_3887957
  simp only [CollatzResearch.WordTrace]
  refine ⟨141805441575603274036158125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94536961050402182690772083 141805441575603274036158125)
  ·
    refine ⟨53177040590851227763559297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 141805441575603274036158125 53177040590851227763559297)
    ·
      refine ⟨39882780443138420822669473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53177040590851227763559297 39882780443138420822669473)
      ·
        refine ⟨29912085332353815617002105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39882780443138420822669473 29912085332353815617002105)
        ·
          refine ⟨22434063999265361712751579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29912085332353815617002105 22434063999265361712751579)
          ·
            refine ⟨33651095998898042569127369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22434063999265361712751579 33651095998898042569127369)
            ·
              refine ⟨25238321999173531926845527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33651095998898042569127369 25238321999173531926845527)
              ·
                refine ⟨37857482998760297890268291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25238321999173531926845527 37857482998760297890268291)
                ·
                  refine ⟨56786224498140446835402437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37857482998760297890268291 56786224498140446835402437)
                  ·
                    refine ⟨10647417093401333781637957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 56786224498140446835402437 10647417093401333781637957)
                    ·
                      refine ⟨1996390705012750084057117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10647417093401333781637957 1996390705012750084057117)
                      ·
                        rfl

theorem cell23_3887957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 2, 1, 1, 4, 4].length) (baseStart_3887957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3887957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3887957 prefixEnd_3887957 := by exact prefixLift 3887957
  have htrace : WordTrace (prefixWord ++ tailWord_3887957) baseStart_3887957 baseEnd_3887957 := by
    simpa [prefixWord, tailWord_3887957, baseEnd_3887957] using wordTrace_append hprefix tailTrace_3887957
  have hstable : (prefixWord ++ tailWord_3887957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3887957).length < 2 ^ (prefixWord ++ tailWord_3887957).sum := by decide
  have hdescent : baseEnd_3887957 < baseStart_3887957 := by decide
  rcases family_descends (prefixWord ++ tailWord_3887957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3887964 : List Nat := [2, 2, 4, 2, 1, 1, 1, 2, 2, 1, 5]
def baseStart_3887964 : Nat := 118140960795 + 3887964 * 2 ^ 59
def prefixEnd_3887964 : Nat := 4983230072969 + 3 ^ 40 * 3887964 * 2
def baseEnd_3887964 : Nat := 1996394299377331556669585

theorem tailTrace_3887964 : CollatzResearch.WordTrace tailWord_3887964 prefixEnd_3887964 1996394299377331556669585 := by
  unfold tailWord_3887964
  simp only [CollatzResearch.WordTrace]
  refine ⟨70902848443288957115831473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94537131257718609487775297 70902848443288957115831473)
  ·
    refine ⟨53177136332466717836873605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70902848443288957115831473 53177136332466717836873605)
    ·
      refine ⟨9970713062337509594413801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 53177136332466717836873605 9970713062337509594413801)
      ·
        refine ⟨7478034796753132195810351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9970713062337509594413801 7478034796753132195810351)
        ·
          refine ⟨11217052195129698293715527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7478034796753132195810351 11217052195129698293715527)
          ·
            refine ⟨16825578292694547440573291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11217052195129698293715527 16825578292694547440573291)
            ·
              refine ⟨25238367439041821160859937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16825578292694547440573291 25238367439041821160859937)
              ·
                refine ⟨18928775579281365870644953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25238367439041821160859937 18928775579281365870644953)
                ·
                  refine ⟨14196581684461024402983715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18928775579281365870644953 14196581684461024402983715)
                  ·
                    refine ⟨21294872526691536604475573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14196581684461024402983715 21294872526691536604475573)
                    ·
                      refine ⟨1996394299377331556669585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21294872526691536604475573 1996394299377331556669585)
                      ·
                        rfl

theorem cell23_3887964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 1, 2, 2, 1, 5].length) (baseStart_3887964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3887964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3887964 prefixEnd_3887964 := by exact prefixLift 3887964
  have htrace : WordTrace (prefixWord ++ tailWord_3887964) baseStart_3887964 baseEnd_3887964 := by
    simpa [prefixWord, tailWord_3887964, baseEnd_3887964] using wordTrace_append hprefix tailTrace_3887964
  have hstable : (prefixWord ++ tailWord_3887964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3887964).length < 2 ^ (prefixWord ++ tailWord_3887964).sum := by decide
  have hdescent : baseEnd_3887964 < baseStart_3887964 := by decide
  rcases family_descends (prefixWord ++ tailWord_3887964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3887977 : List Nat := [1, 2, 1, 1, 1, 3, 1, 1, 6, 3, 3]
def baseStart_3887977 : Nat := 118140960795 + 3887977 * 2 ^ 59
def prefixEnd_3887977 : Nat := 4983230072969 + 3 ^ 40 * 3887977 * 2
def baseEnd_3887977 : Nat := 1996400974625840005807025

theorem tailTrace_3887977 : CollatzResearch.WordTrace tailWord_3887977 prefixEnd_3887977 1996400974625840005807025 := by
  unfold tailWord_3887977
  simp only [CollatzResearch.WordTrace]
  refine ⟨141806171035530817451886185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94537447357020544967924123 141806171035530817451886185)
  ·
    refine ⟨106354628276648113088914639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141806171035530817451886185 106354628276648113088914639)
    ·
      refine ⟨159531942414972169633371959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106354628276648113088914639 159531942414972169633371959)
      ·
        refine ⟨239297913622458254450057939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159531942414972169633371959 239297913622458254450057939)
        ·
          refine ⟨358946870433687381675086909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 239297913622458254450057939 358946870433687381675086909)
          ·
            refine ⟨134605076412632768128157591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 358946870433687381675086909 134605076412632768128157591)
            ·
              refine ⟨201907614618949152192236387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 134605076412632768128157591 201907614618949152192236387)
              ·
                refine ⟨302861421928423728288354581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 201907614618949152192236387 302861421928423728288354581)
                ·
                  refine ⟨14196629152894862263516621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 302861421928423728288354581 14196629152894862263516621)
                  ·
                    refine ⟨5323735932335573348818733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14196629152894862263516621 5323735932335573348818733)
                    ·
                      refine ⟨1996400974625840005807025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5323735932335573348818733 1996400974625840005807025)
                      ·
                        rfl

theorem cell23_3887977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 1, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 1, 6, 3, 3].length) (baseStart_3887977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3887977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3887977 prefixEnd_3887977 := by exact prefixLift 3887977
  have htrace : WordTrace (prefixWord ++ tailWord_3887977) baseStart_3887977 baseEnd_3887977 := by
    simpa [prefixWord, tailWord_3887977, baseEnd_3887977] using wordTrace_append hprefix tailTrace_3887977
  have hstable : (prefixWord ++ tailWord_3887977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3887977).length < 2 ^ (prefixWord ++ tailWord_3887977).sum := by decide
  have hdescent : baseEnd_3887977 < baseStart_3887977 := by decide
  rcases family_descends (prefixWord ++ tailWord_3887977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3888017 : List Nat := [1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 4]
def baseStart_3888017 : Nat := 118140960795 + 3888017 * 2 ^ 59
def prefixEnd_3888017 : Nat := 4983230072969 + 3 ^ 40 * 3888017 * 2
def baseEnd_3888017 : Nat := 1996421513852019849306841

theorem tailTrace_3888017 : CollatzResearch.WordTrace tailWord_3888017 prefixEnd_3888017 1996421513852019849306841 := by
  unfold tailWord_3888017
  simp only [CollatzResearch.WordTrace]
  refine ⟨141807629955385904283342305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94538419970257269522228203 141807629955385904283342305)
  ·
    refine ⟨106355722466539428212506729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141807629955385904283342305 106355722466539428212506729)
    ·
      refine ⟨79766791849904571159380047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106355722466539428212506729 79766791849904571159380047)
      ·
        refine ⟨119650187774856856739070071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79766791849904571159380047 119650187774856856739070071)
        ·
          refine ⟨179475281662285285108605107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119650187774856856739070071 179475281662285285108605107)
          ·
            refine ⟨269212922493427927662907661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 179475281662285285108605107 269212922493427927662907661)
            ·
              refine ⟨100954845935035472873590373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 269212922493427927662907661 100954845935035472873590373)
              ·
                refine ⟨18929033612819151163798195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 100954845935035472873590373 18929033612819151163798195)
                ·
                  refine ⟨28393550419228726745697293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18929033612819151163798195 28393550419228726745697293)
                  ·
                    refine ⟨10647581407210772529636485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28393550419228726745697293 10647581407210772529636485)
                    ·
                      refine ⟨1996421513852019849306841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10647581407210772529636485 1996421513852019849306841)
                      ·
                        rfl

theorem cell23_3888017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 4].length) (baseStart_3888017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3888017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3888017 prefixEnd_3888017 := by exact prefixLift 3888017
  have htrace : WordTrace (prefixWord ++ tailWord_3888017) baseStart_3888017 baseEnd_3888017 := by
    simpa [prefixWord, tailWord_3888017, baseEnd_3888017] using wordTrace_append hprefix tailTrace_3888017
  have hstable : (prefixWord ++ tailWord_3888017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3888017).length < 2 ^ (prefixWord ++ tailWord_3888017).sum := by decide
  have hdescent : baseEnd_3888017 < baseStart_3888017 := by decide
  rcases family_descends (prefixWord ++ tailWord_3888017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3888031 : List Nat := [1, 1, 2, 5, 2, 3, 1, 1, 2, 5]
def baseStart_3888031 : Nat := 118140960795 + 3888031 * 2 ^ 59
def prefixEnd_3888031 : Nat := 4983230072969 + 3 ^ 40 * 3888031 * 2
def baseEnd_3888031 : Nat := 665476234193727598177259

theorem tailTrace_3888031 : CollatzResearch.WordTrace tailWord_3888031 prefixEnd_3888031 665476234193727598177259 := by
  unfold tailWord_3888031
  simp only [CollatzResearch.WordTrace]
  refine ⟨141808140577335184674351947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94538760384890123116234631 141808140577335184674351947)
  ·
    refine ⟨212712210866002777011527921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141808140577335184674351947 212712210866002777011527921)
    ·
      refine ⟨159534158149502082758645941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 212712210866002777011527921 159534158149502082758645941)
      ·
        refine ⟨14956327326515820258623057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 159534158149502082758645941 14956327326515820258623057)
        ·
          refine ⟨11217245494886865193967293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14956327326515820258623057 11217245494886865193967293)
          ·
            refine ⟨4206467060582574447737735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11217245494886865193967293 4206467060582574447737735)
            ·
              refine ⟨6309700590873861671606603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4206467060582574447737735 6309700590873861671606603)
              ·
                refine ⟨9464550886310792507409905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6309700590873861671606603 9464550886310792507409905)
                ·
                  refine ⟨7098413164733094380557429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9464550886310792507409905 7098413164733094380557429)
                  ·
                    refine ⟨665476234193727598177259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7098413164733094380557429 665476234193727598177259)
                    ·
                      rfl

theorem cell23_3888031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 3, 1, 1, 2, 5].length) (baseStart_3888031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3888031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3888031 prefixEnd_3888031 := by exact prefixLift 3888031
  have htrace : WordTrace (prefixWord ++ tailWord_3888031) baseStart_3888031 baseEnd_3888031 := by
    simpa [prefixWord, tailWord_3888031, baseEnd_3888031] using wordTrace_append hprefix tailTrace_3888031
  have hstable : (prefixWord ++ tailWord_3888031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3888031).length < 2 ^ (prefixWord ++ tailWord_3888031).sum := by decide
  have hdescent : baseEnd_3888031 < baseStart_3888031 := by decide
  rcases family_descends (prefixWord ++ tailWord_3888031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3888095 : List Nat := [1, 1, 2, 3, 5, 2, 1, 3, 1, 4]
def baseStart_3888095 : Nat := 118140960795 + 3888095 * 2 ^ 59
def prefixEnd_3888095 : Nat := 4983230072969 + 3 ^ 40 * 3888095 * 2
def baseEnd_3888095 : Nat := 665487188447690181377161

theorem tailTrace_3888095 : CollatzResearch.WordTrace tailWord_3888095 prefixEnd_3888095 665487188447690181377161 := by
  unfold tailWord_3888095
  simp only [CollatzResearch.WordTrace]
  refine ⟨141810474849103323604681739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94540316566068882403121159 141810474849103323604681739)
  ·
    refine ⟨212715712273654985407022609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141810474849103323604681739 212715712273654985407022609)
    ·
      refine ⟨159536784205241239055266957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 212715712273654985407022609 159536784205241239055266957)
      ·
        refine ⟨59826294076965464645725109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 159536784205241239055266957 59826294076965464645725109)
        ·
          refine ⟨5608715069715512310536729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 59826294076965464645725109 5608715069715512310536729)
          ·
            refine ⟨4206536302286634232902547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5608715069715512310536729 4206536302286634232902547)
            ·
              refine ⟨6309804453429951349353821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4206536302286634232902547 6309804453429951349353821)
              ·
                refine ⟨2366176670036231756007683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6309804453429951349353821 2366176670036231756007683)
                ·
                  refine ⟨3549265005054347634011525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2366176670036231756007683 3549265005054347634011525)
                  ·
                    refine ⟨665487188447690181377161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3549265005054347634011525 665487188447690181377161)
                    ·
                      rfl

theorem cell23_3888095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 2, 1, 3, 1, 4].length) (baseStart_3888095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3888095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3888095 prefixEnd_3888095 := by exact prefixLift 3888095
  have htrace : WordTrace (prefixWord ++ tailWord_3888095) baseStart_3888095 baseEnd_3888095 := by
    simpa [prefixWord, tailWord_3888095, baseEnd_3888095] using wordTrace_append hprefix tailTrace_3888095
  have hstable : (prefixWord ++ tailWord_3888095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3888095).length < 2 ^ (prefixWord ++ tailWord_3888095).sum := by decide
  have hdescent : baseEnd_3888095 < baseStart_3888095 := by decide
  rcases family_descends (prefixWord ++ tailWord_3888095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3888111 : List Nat := [1, 1, 2, 1, 4, 3, 1, 1, 4, 3, 2]
def baseStart_3888111 : Nat := 118140960795 + 3888111 * 2 ^ 59
def prefixEnd_3888111 : Nat := 4983230072969 + 3 ^ 40 * 3888111 * 2
def baseEnd_3888111 : Nat := 1996469781033542481531409

theorem tailTrace_3888111 : CollatzResearch.WordTrace tailWord_3888111 prefixEnd_3888111 1996469781033542481531409 := by
  unfold tailWord_3888111
  simp only [CollatzResearch.WordTrace]
  refine ⟨141811058417045358337264187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94540705611363572224842791 141811058417045358337264187)
  ·
    refine ⟨212716587625568037505896281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141811058417045358337264187 212716587625568037505896281)
    ·
      refine ⟨159537440719176028129422211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 212716587625568037505896281 159537440719176028129422211)
      ·
        refine ⟨239306161078764042194133317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159537440719176028129422211 239306161078764042194133317)
        ·
          refine ⟨44869905202268257911399997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 239306161078764042194133317 44869905202268257911399997)
          ·
            refine ⟨16826214450850596716774999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44869905202268257911399997 16826214450850596716774999)
            ·
              refine ⟨25239321676275895075162499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16826214450850596716774999 25239321676275895075162499)
              ·
                refine ⟨37858982514413842612743749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25239321676275895075162499 37858982514413842612743749)
                ·
                  refine ⟨7098559221452595489889453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37858982514413842612743749 7098559221452595489889453)
                  ·
                    refine ⟨2661959708044723308708545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7098559221452595489889453 2661959708044723308708545)
                    ·
                      refine ⟨1996469781033542481531409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2661959708044723308708545 1996469781033542481531409)
                      ·
                        rfl

theorem cell23_3888111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 1, 1, 4, 3, 2].length) (baseStart_3888111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3888111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3888111 prefixEnd_3888111 := by exact prefixLift 3888111
  have htrace : WordTrace (prefixWord ++ tailWord_3888111) baseStart_3888111 baseEnd_3888111 := by
    simpa [prefixWord, tailWord_3888111, baseEnd_3888111] using wordTrace_append hprefix tailTrace_3888111
  have hstable : (prefixWord ++ tailWord_3888111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3888111).length < 2 ^ (prefixWord ++ tailWord_3888111).sum := by decide
  have hdescent : baseEnd_3888111 < baseStart_3888111 := by decide
  rcases family_descends (prefixWord ++ tailWord_3888111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3888138 : List Nat := [3, 1, 2, 2, 3, 3, 1, 2, 1, 5]
def baseStart_3888138 : Nat := 118140960795 + 3888138 * 2 ^ 59
def prefixEnd_3888138 : Nat := 4983230072969 + 3 ^ 40 * 3888138 * 2
def baseEnd_3888138 : Nat := 665494548337071291964595

theorem tailTrace_3888138 : CollatzResearch.WordTrace tailWord_3888138 prefixEnd_3888138 665494548337071291964595 := by
  unfold tailWord_3888138
  simp only [CollatzResearch.WordTrace]
  refine ⟨35453010796986885487124267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94541362125298361298998045 35453010796986885487124267)
  ·
    refine ⟨53179516195480328230686401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35453010796986885487124267 53179516195480328230686401)
    ·
      refine ⟨39884637146610246173014801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53179516195480328230686401 39884637146610246173014801)
      ·
        refine ⟨29913477859957684629761101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39884637146610246173014801 29913477859957684629761101)
        ·
          refine ⟨11217554197484131736160413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29913477859957684629761101 11217554197484131736160413)
          ·
            refine ⟨4206582824056549401060155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11217554197484131736160413 4206582824056549401060155)
            ·
              refine ⟨6309874236084824101590233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4206582824056549401060155 6309874236084824101590233)
              ·
                refine ⟨4732405677063618076192675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6309874236084824101590233 4732405677063618076192675)
                ·
                  refine ⟨7098608515595427114289013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4732405677063618076192675 7098608515595427114289013)
                  ·
                    refine ⟨665494548337071291964595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7098608515595427114289013 665494548337071291964595)
                    ·
                      rfl

theorem cell23_3888138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 3, 1, 2, 1, 5].length) (baseStart_3888138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3888138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3888138 prefixEnd_3888138 := by exact prefixLift 3888138
  have htrace : WordTrace (prefixWord ++ tailWord_3888138) baseStart_3888138 baseEnd_3888138 := by
    simpa [prefixWord, tailWord_3888138, baseEnd_3888138] using wordTrace_append hprefix tailTrace_3888138
  have hstable : (prefixWord ++ tailWord_3888138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3888138).length < 2 ^ (prefixWord ++ tailWord_3888138).sum := by decide
  have hdescent : baseEnd_3888138 < baseStart_3888138 := by decide
  rcases family_descends (prefixWord ++ tailWord_3888138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3888151 : List Nat := [1, 1, 3, 5, 1, 2, 1, 2, 1, 6]
def baseStart_3888151 : Nat := 118140960795 + 3888151 * 2 ^ 59
def prefixEnd_3888151 : Nat := 4983230072969 + 3 ^ 40 * 3888151 * 2
def baseEnd_3888151 : Nat := 665496773419907441677075

theorem tailTrace_3888151 : CollatzResearch.WordTrace tailWord_3888151 prefixEnd_3888151 665496773419907441677075 := by
  unfold tailWord_3888151
  simp only [CollatzResearch.WordTrace]
  refine ⟨141812517336900445168720307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94541678224600296779146871 141812517336900445168720307)
  ·
    refine ⟨212718776005350667753080461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141812517336900445168720307 212718776005350667753080461)
    ·
      refine ⟨79769541002006500407405173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 212718776005350667753080461 79769541002006500407405173)
      ·
        refine ⟨7478394468938109413194235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 79769541002006500407405173 7478394468938109413194235)
        ·
          refine ⟨11217591703407164119791353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7478394468938109413194235 11217591703407164119791353)
          ·
            refine ⟨8413193777555373089843515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11217591703407164119791353 8413193777555373089843515)
            ·
              refine ⟨12619790666333059634765273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8413193777555373089843515 12619790666333059634765273)
              ·
                refine ⟨9464842999749794726073955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12619790666333059634765273 9464842999749794726073955)
                ·
                  refine ⟨14197264499624692089110933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9464842999749794726073955 14197264499624692089110933)
                  ·
                    refine ⟨665496773419907441677075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14197264499624692089110933 665496773419907441677075)
                    ·
                      rfl

theorem cell23_3888151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 1, 2, 1, 6].length) (baseStart_3888151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3888151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3888151 prefixEnd_3888151 := by exact prefixLift 3888151
  have htrace : WordTrace (prefixWord ++ tailWord_3888151) baseStart_3888151 baseEnd_3888151 := by
    simpa [prefixWord, tailWord_3888151, baseEnd_3888151] using wordTrace_append hprefix tailTrace_3888151
  have hstable : (prefixWord ++ tailWord_3888151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3888151).length < 2 ^ (prefixWord ++ tailWord_3888151).sum := by decide
  have hdescent : baseEnd_3888151 < baseStart_3888151 := by decide
  rcases family_descends (prefixWord ++ tailWord_3888151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3888161 : List Nat := [1, 2, 3, 2, 3, 1, 3, 1, 1, 1, 5]
def baseStart_3888161 : Nat := 118140960795 + 3888161 * 2 ^ 59
def prefixEnd_3888161 : Nat := 4983230072969 + 3 ^ 40 * 3888161 * 2
def baseEnd_3888161 : Nat := 1996495455066267285906179

theorem tailTrace_3888161 : CollatzResearch.WordTrace tailWord_3888161 prefixEnd_3888161 1996495455066267285906179 := by
  unfold tailWord_3888161
  simp only [CollatzResearch.WordTrace]
  refine ⟨141812882066864216876584337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94541921377909477917722891 141812882066864216876584337)
  ·
    refine ⟨106359661550148162657438253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141812882066864216876584337 106359661550148162657438253)
    ·
      refine ⟨39884873081305560996539345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106359661550148162657438253 39884873081305560996539345)
      ·
        refine ⟨29913654810979170747404509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39884873081305560996539345 29913654810979170747404509)
        ·
          refine ⟨11217620554117189030276691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29913654810979170747404509 11217620554117189030276691)
          ·
            refine ⟨16826430831175783545415037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11217620554117189030276691 16826430831175783545415037)
            ·
              refine ⟨6309911561690918829530639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16826430831175783545415037 6309911561690918829530639)
              ·
                refine ⟨9464867342536378244295959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6309911561690918829530639 9464867342536378244295959)
                ·
                  refine ⟨14197301013804567366443939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9464867342536378244295959 14197301013804567366443939)
                  ·
                    refine ⟨21295951520706851049665909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14197301013804567366443939 21295951520706851049665909)
                    ·
                      refine ⟨1996495455066267285906179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21295951520706851049665909 1996495455066267285906179)
                      ·
                        rfl

theorem cell23_3888161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 3, 1, 1, 1, 5].length) (baseStart_3888161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3888161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3888161 prefixEnd_3888161 := by exact prefixLift 3888161
  have htrace : WordTrace (prefixWord ++ tailWord_3888161) baseStart_3888161 baseEnd_3888161 := by
    simpa [prefixWord, tailWord_3888161, baseEnd_3888161] using wordTrace_append hprefix tailTrace_3888161
  have hstable : (prefixWord ++ tailWord_3888161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3888161).length < 2 ^ (prefixWord ++ tailWord_3888161).sum := by decide
  have hdescent : baseEnd_3888161 < baseStart_3888161 := by decide
  rcases family_descends (prefixWord ++ tailWord_3888161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3888164 : List Nat := [2, 3, 1, 4, 1, 12]
def baseStart_3888164 : Nat := 118140960795 + 3888164 * 2 ^ 59
def prefixEnd_3888164 : Nat := 4983230072969 + 3 ^ 40 * 3888164 * 2
def baseEnd_3888164 : Nat := 8216037018552390017155

theorem tailTrace_3888164 : CollatzResearch.WordTrace tailWord_3888164 prefixEnd_3888164 8216037018552390017155 := by
  unfold tailWord_3888164
  simp only [CollatzResearch.WordTrace]
  refine ⟨70906495742926674194471773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94541994323902232259295697 70906495742926674194471773)
  ·
    refine ⟨26589935903597502822926915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70906495742926674194471773 26589935903597502822926915)
    ·
      refine ⟨39884903855396254234390373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26589935903597502822926915 39884903855396254234390373)
      ·
        refine ⟨7478419472886797668948195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39884903855396254234390373 7478419472886797668948195)
        ·
          refine ⟨11217629209330196503422293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7478419472886797668948195 11217629209330196503422293)
          ·
            refine ⟨8216037018552390017155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 11217629209330196503422293 8216037018552390017155)
            ·
              rfl

theorem cell23_3888164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 12].length) (baseStart_3888164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3888164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3888164 prefixEnd_3888164 := by exact prefixLift 3888164
  have htrace : WordTrace (prefixWord ++ tailWord_3888164) baseStart_3888164 baseEnd_3888164 := by
    simpa [prefixWord, tailWord_3888164, baseEnd_3888164] using wordTrace_append hprefix tailTrace_3888164
  have hstable : (prefixWord ++ tailWord_3888164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3888164).length < 2 ^ (prefixWord ++ tailWord_3888164).sum := by decide
  have hdescent : baseEnd_3888164 < baseStart_3888164 := by decide
  rcases family_descends (prefixWord ++ tailWord_3888164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3888191 : List Nat := [1, 1, 2, 2, 3, 1, 1, 2, 6, 1, 3]
def baseStart_3888191 : Nat := 118140960795 + 3888191 * 2 ^ 59
def prefixEnd_3888191 : Nat := 4983230072969 + 3 ^ 40 * 3888191 * 2
def baseEnd_3888191 : Nat := 1996510859485902168531041

theorem tailTrace_3888191 : CollatzResearch.WordTrace tailWord_3888191 prefixEnd_3888191 1996510859485902168531041 := by
  unfold tailWord_3888191
  simp only [CollatzResearch.WordTrace]
  refine ⟨141813976256755532000176427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94542650837837021333450951 141813976256755532000176427)
  ·
    refine ⟨212720964385133298000264641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141813976256755532000176427 212720964385133298000264641)
    ·
      refine ⟨159540723288849973500198481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 212720964385133298000264641 159540723288849973500198481)
      ·
        refine ⟨119655542466637480125148861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159540723288849973500198481 119655542466637480125148861)
        ·
          refine ⟨44870828424989055046930823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 119655542466637480125148861 44870828424989055046930823)
          ·
            refine ⟨67306242637483582570396235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44870828424989055046930823 67306242637483582570396235)
            ·
              refine ⟨100959363956225373855594353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67306242637483582570396235 100959363956225373855594353)
              ·
                refine ⟨75719522967169030391695765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 100959363956225373855594353 75719522967169030391695765)
                ·
                  refine ⟨3549352639086048299610739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 75719522967169030391695765 3549352639086048299610739)
                  ·
                    refine ⟨5324028958629072449416109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3549352639086048299610739 5324028958629072449416109)
                    ·
                      refine ⟨1996510859485902168531041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5324028958629072449416109 1996510859485902168531041)
                      ·
                        rfl

theorem cell23_3888191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 2, 6, 1, 3].length) (baseStart_3888191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3888191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3888191 prefixEnd_3888191 := by exact prefixLift 3888191
  have htrace : WordTrace (prefixWord ++ tailWord_3888191) baseStart_3888191 baseEnd_3888191 := by
    simpa [prefixWord, tailWord_3888191, baseEnd_3888191] using wordTrace_append hprefix tailTrace_3888191
  have hstable : (prefixWord ++ tailWord_3888191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3888191).length < 2 ^ (prefixWord ++ tailWord_3888191).sum := by decide
  have hdescent : baseEnd_3888191 < baseStart_3888191 := by decide
  rcases family_descends (prefixWord ++ tailWord_3888191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3888204 : List Nat := [2, 2, 1, 3, 1, 1, 1, 3, 2, 2, 5]
def baseStart_3888204 : Nat := 118140960795 + 3888204 * 2 ^ 59
def prefixEnd_3888204 : Nat := 4983230072969 + 3 ^ 40 * 3888204 * 2
def baseEnd_3888204 : Nat := 1996517534734410617668481

theorem tailTrace_3888204 : CollatzResearch.WordTrace tailWord_3888204 prefixEnd_3888204 1996517534734410617668481 := by
  unfold tailWord_3888204
  simp only [CollatzResearch.WordTrace]
  refine ⟨70907225202854217610199833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94542966937138956813599777 70907225202854217610199833)
  ·
    refine ⟨53180418902140663207649875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70907225202854217610199833 53180418902140663207649875)
    ·
      refine ⟨79770628353210994811474813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53180418902140663207649875 79770628353210994811474813)
      ·
        refine ⟨29913985632454123054303055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79770628353210994811474813 29913985632454123054303055)
        ·
          refine ⟨44870978448681184581454583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29913985632454123054303055 44870978448681184581454583)
          ·
            refine ⟨67306467673021776872181875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44870978448681184581454583 67306467673021776872181875)
            ·
              refine ⟨100959701509532665308272813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67306467673021776872181875 100959701509532665308272813)
              ·
                refine ⟨37859888066074749490602305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 100959701509532665308272813 37859888066074749490602305)
                ·
                  refine ⟨28394916049556062117951729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37859888066074749490602305 28394916049556062117951729)
                  ·
                    refine ⟨21296187037167046588463797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28394916049556062117951729 21296187037167046588463797)
                    ·
                      refine ⟨1996517534734410617668481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21296187037167046588463797 1996517534734410617668481)
                      ·
                        rfl

theorem cell23_3888204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 3, 2, 2, 5].length) (baseStart_3888204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3888204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3888204 prefixEnd_3888204 := by exact prefixLift 3888204
  have htrace : WordTrace (prefixWord ++ tailWord_3888204) baseStart_3888204 baseEnd_3888204 := by
    simpa [prefixWord, tailWord_3888204, baseEnd_3888204] using wordTrace_append hprefix tailTrace_3888204
  have hstable : (prefixWord ++ tailWord_3888204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3888204).length < 2 ^ (prefixWord ++ tailWord_3888204).sum := by decide
  have hdescent : baseEnd_3888204 < baseStart_3888204 := by decide
  rcases family_descends (prefixWord ++ tailWord_3888204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3888224 : List Nat := [2, 1, 1, 3, 2, 2, 1, 1, 4, 6]
def baseStart_3888224 : Nat := 118140960795 + 3888224 * 2 ^ 59
def prefixEnd_3888224 : Nat := 4983230072969 + 3 ^ 40 * 3888224 * 2
def baseEnd_3888224 : Nat := 665509268115833513139463

theorem tailTrace_3888224 : CollatzResearch.WordTrace tailWord_3888224 prefixEnd_3888224 665509268115833513139463 := by
  unfold tailWord_3888224
  simp only [CollatzResearch.WordTrace]
  refine ⟨70907589932817989318063863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94543453243757319090751817 70907589932817989318063863)
  ·
    refine ⟨106361384899226983977095795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70907589932817989318063863 106361384899226983977095795)
    ·
      refine ⟨159542077348840475965643693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106361384899226983977095795 159542077348840475965643693)
      ·
        refine ⟨59828279005815178487116385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 159542077348840475965643693 59828279005815178487116385)
        ·
          refine ⟨44871209254361383865337289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59828279005815178487116385 44871209254361383865337289)
          ·
            refine ⟨33653406940771037899002967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44871209254361383865337289 33653406940771037899002967)
            ·
              refine ⟨50480110411156556848504451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33653406940771037899002967 50480110411156556848504451)
              ·
                refine ⟨75720165616734835272756677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50480110411156556848504451 75720165616734835272756677)
                ·
                  refine ⟨14197531053137781613641877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 75720165616734835272756677 14197531053137781613641877)
                  ·
                    refine ⟨665509268115833513139463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14197531053137781613641877 665509268115833513139463)
                    ·
                      rfl

theorem cell23_3888224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 1, 4, 6].length) (baseStart_3888224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3888224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3888224 prefixEnd_3888224 := by exact prefixLift 3888224
  have htrace : WordTrace (prefixWord ++ tailWord_3888224) baseStart_3888224 baseEnd_3888224 := by
    simpa [prefixWord, tailWord_3888224, baseEnd_3888224] using wordTrace_append hprefix tailTrace_3888224
  have hstable : (prefixWord ++ tailWord_3888224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3888224).length < 2 ^ (prefixWord ++ tailWord_3888224).sum := by decide
  have hdescent : baseEnd_3888224 < baseStart_3888224 := by decide
  rcases family_descends (prefixWord ++ tailWord_3888224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3888248 : List Nat := [2, 1, 2, 1, 1, 1, 7, 1, 1, 4, 2]
def baseStart_3888248 : Nat := 118140960795 + 3888248 * 2 ^ 59
def prefixEnd_3888248 : Nat := 4983230072969 + 3 ^ 40 * 3888248 * 2
def baseEnd_3888248 : Nat := 1996540127883208445518279

theorem tailTrace_3888248 : CollatzResearch.WordTrace tailWord_3888248 prefixEnd_3888248 1996540127883208445518279 := by
  unfold tailWord_3888248
  simp only [CollatzResearch.WordTrace]
  refine ⟨70908027608774515367500699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94544036811699353823334265 70908027608774515367500699)
  ·
    refine ⟨106362041413161773051251049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70908027608774515367500699 106362041413161773051251049)
    ·
      refine ⟨79771531059871329788438287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106362041413161773051251049 79771531059871329788438287)
      ·
        refine ⟨119657296589806994682657431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79771531059871329788438287 119657296589806994682657431)
        ·
          refine ⟨179485944884710492023986147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119657296589806994682657431 179485944884710492023986147)
          ·
            refine ⟨269228917327065738035979221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 179485944884710492023986147 269228917327065738035979221)
            ·
              refine ⟨6310052749853103235218263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 269228917327065738035979221 6310052749853103235218263)
              ·
                refine ⟨9465079124779654852827395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6310052749853103235218263 9465079124779654852827395)
                ·
                  refine ⟨14197618687169482279241093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9465079124779654852827395 14197618687169482279241093)
                  ·
                    refine ⟨2662053503844277927357705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14197618687169482279241093 2662053503844277927357705)
                    ·
                      refine ⟨1996540127883208445518279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2662053503844277927357705 1996540127883208445518279)
                      ·
                        rfl

theorem cell23_3888248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 7, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 7, 1, 1, 4, 2].length) (baseStart_3888248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3888248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3888248 prefixEnd_3888248 := by exact prefixLift 3888248
  have htrace : WordTrace (prefixWord ++ tailWord_3888248) baseStart_3888248 baseEnd_3888248 := by
    simpa [prefixWord, tailWord_3888248, baseEnd_3888248] using wordTrace_append hprefix tailTrace_3888248
  have hstable : (prefixWord ++ tailWord_3888248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3888248).length < 2 ^ (prefixWord ++ tailWord_3888248).sum := by decide
  have hdescent : baseEnd_3888248 < baseStart_3888248 := by decide
  rcases family_descends (prefixWord ++ tailWord_3888248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3888318 : List Nat := [4, 2, 1, 1, 3, 1, 1, 3, 2, 5]
def baseStart_3888318 : Nat := 118140960795 + 3888318 * 2 ^ 59
def prefixEnd_3888318 : Nat := 4983230072969 + 3 ^ 40 * 3888318 * 2
def baseEnd_3888318 : Nat := 665525357176341057214319

theorem tailTrace_3888318 : CollatzResearch.WordTrace tailWord_3888318 prefixEnd_3888318 665525357176341057214319 := by
  unfold tailWord_3888318
  simp only [CollatzResearch.WordTrace]
  refine ⟨17727326040911929086256201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 94545738884863621793366405 17727326040911929086256201)
  ·
    refine ⟨13295494530683946814692151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17727326040911929086256201 13295494530683946814692151)
    ·
      refine ⟨19943241796025920222038227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13295494530683946814692151 19943241796025920222038227)
      ·
        refine ⟨29914862694038880333057341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19943241796025920222038227 29914862694038880333057341)
        ·
          refine ⟨11218073510264580124896503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29914862694038880333057341 11218073510264580124896503)
          ·
            refine ⟨16827110265396870187344755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11218073510264580124896503 16827110265396870187344755)
            ·
              refine ⟨25240665398095305281017133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16827110265396870187344755 25240665398095305281017133)
              ·
                refine ⟨9465249524285739480381425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25240665398095305281017133 9465249524285739480381425)
                ·
                  refine ⟨7098937143214304610286069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9465249524285739480381425 7098937143214304610286069)
                  ·
                    refine ⟨665525357176341057214319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7098937143214304610286069 665525357176341057214319)
                    ·
                      rfl

theorem cell23_3888318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 1, 3, 2, 5].length) (baseStart_3888318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3888318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3888318 prefixEnd_3888318 := by exact prefixLift 3888318
  have htrace : WordTrace (prefixWord ++ tailWord_3888318) baseStart_3888318 baseEnd_3888318 := by
    simpa [prefixWord, tailWord_3888318, baseEnd_3888318] using wordTrace_append hprefix tailTrace_3888318
  have hstable : (prefixWord ++ tailWord_3888318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3888318).length < 2 ^ (prefixWord ++ tailWord_3888318).sum := by decide
  have hdescent : baseEnd_3888318 < baseStart_3888318 := by decide
  rcases family_descends (prefixWord ++ tailWord_3888318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3888331 : List Nat := [1, 1, 1, 1, 3, 2, 2, 1, 7, 4]
def baseStart_3888331 : Nat := 118140960795 + 3888331 * 2 ^ 59
def prefixEnd_3888331 : Nat := 4983230072969 + 3 ^ 40 * 3888331 * 2
def baseEnd_3888331 : Nat := 665527582259177206926799

theorem tailTrace_3888331 : CollatzResearch.WordTrace tailWord_3888331 prefixEnd_3888331 665527582259177206926799 := by
  unfold tailWord_3888331
  simp only [CollatzResearch.WordTrace]
  refine ⟨141819082476248335910272847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94546054984165557273515231 141819082476248335910272847)
  ·
    refine ⟨212728623714372503865409271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141819082476248335910272847 212728623714372503865409271)
    ·
      refine ⟨319092935571558755798113907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212728623714372503865409271 319092935571558755798113907)
      ·
        refine ⟨478639403357338133697170861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 319092935571558755798113907 478639403357338133697170861)
        ·
          refine ⟨179489776259001800136439073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 478639403357338133697170861 179489776259001800136439073)
          ·
            refine ⟨134617332194251350102329305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 179489776259001800136439073 134617332194251350102329305)
            ·
              refine ⟨100962999145688512576746979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 134617332194251350102329305 100962999145688512576746979)
              ·
                refine ⟨151444498718532768865120469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100962999145688512576746979 151444498718532768865120469)
                ·
                  refine ⟨3549480438715611770276261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 151444498718532768865120469 3549480438715611770276261)
                  ·
                    refine ⟨665527582259177206926799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3549480438715611770276261 665527582259177206926799)
                    ·
                      rfl

theorem cell23_3888331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 1, 7, 4].length) (baseStart_3888331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3888331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3888331 prefixEnd_3888331 := by exact prefixLift 3888331
  have htrace : WordTrace (prefixWord ++ tailWord_3888331) baseStart_3888331 baseEnd_3888331 := by
    simpa [prefixWord, tailWord_3888331, baseEnd_3888331] using wordTrace_append hprefix tailTrace_3888331
  have hstable : (prefixWord ++ tailWord_3888331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3888331).length < 2 ^ (prefixWord ++ tailWord_3888331).sum := by decide
  have hdescent : baseEnd_3888331 < baseStart_3888331 := by decide
  rcases family_descends (prefixWord ++ tailWord_3888331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3888338 : List Nat := [3, 2, 2, 2, 1, 1, 1, 4, 2, 1, 4]
def baseStart_3888338 : Nat := 118140960795 + 3888338 * 2 ^ 59
def prefixEnd_3888338 : Nat := 4983230072969 + 3 ^ 40 * 3888338 * 2
def baseEnd_3888338 : Nat := 1996586341142113093392865

theorem tailTrace_3888338 : CollatzResearch.WordTrace tailWord_3888338 prefixEnd_3888338 1996586341142113093392865 := by
  unfold tailWord_3888338
  simp only [CollatzResearch.WordTrace]
  refine ⟨35454834446805744026444417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94546225191481984070518445 35454834446805744026444417)
  ·
    refine ⟨26591125835104308019833313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35454834446805744026444417 26591125835104308019833313)
    ·
      refine ⟨19943344376328231014874985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26591125835104308019833313 19943344376328231014874985)
      ·
        refine ⟨14957508282246173261156239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19943344376328231014874985 14957508282246173261156239)
        ·
          refine ⟨22436262423369259891734359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14957508282246173261156239 22436262423369259891734359)
          ·
            refine ⟨33654393635053889837601539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22436262423369259891734359 33654393635053889837601539)
            ·
              refine ⟨50481590452580834756402309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33654393635053889837601539 50481590452580834756402309)
              ·
                refine ⟨9465298209858906516825433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50481590452580834756402309 9465298209858906516825433)
                ·
                  refine ⟨7098973657394179887619075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9465298209858906516825433 7098973657394179887619075)
                  ·
                    refine ⟨10648460486091269831428613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7098973657394179887619075 10648460486091269831428613)
                    ·
                      refine ⟨1996586341142113093392865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10648460486091269831428613 1996586341142113093392865)
                      ·
                        rfl

theorem cell23_3888338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 4, 2, 1, 4].length) (baseStart_3888338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3888338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3888338 prefixEnd_3888338 := by exact prefixLift 3888338
  have htrace : WordTrace (prefixWord ++ tailWord_3888338) baseStart_3888338 baseEnd_3888338 := by
    simpa [prefixWord, tailWord_3888338, baseEnd_3888338] using wordTrace_append hprefix tailTrace_3888338
  have hstable : (prefixWord ++ tailWord_3888338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3888338).length < 2 ^ (prefixWord ++ tailWord_3888338).sum := by decide
  have hdescent : baseEnd_3888338 < baseStart_3888338 := by decide
  rcases family_descends (prefixWord ++ tailWord_3888338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3888365 : List Nat := [1, 5, 1, 2, 2, 2, 1, 2, 3, 4]
def baseStart_3888365 : Nat := 118140960795 + 3888365 * 2 ^ 59
def prefixEnd_3888365 : Nat := 4983230072969 + 3 ^ 40 * 3888365 * 2
def baseEnd_3888365 : Nat := 665533401706594829251747

theorem tailTrace_3888365 : CollatzResearch.WordTrace tailWord_3888365 prefixEnd_3888365 665533401706594829251747 := by
  unfold tailWord_3888365
  simp only [CollatzResearch.WordTrace]
  refine ⟨141820322558125159717010549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94546881705416773144673699 141820322558125159717010549)
  ·
    refine ⟨13295655239824233723469739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 141820322558125159717010549 13295655239824233723469739)
    ·
      refine ⟨19943482859736350585204609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13295655239824233723469739 19943482859736350585204609)
      ·
        refine ⟨14957612144802262938903457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19943482859736350585204609 14957612144802262938903457)
        ·
          refine ⟨11218209108601697204177593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14957612144802262938903457 11218209108601697204177593)
          ·
            refine ⟨8413656831451272903133195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11218209108601697204177593 8413656831451272903133195)
            ·
              refine ⟨12620485247176909354699793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8413656831451272903133195 12620485247176909354699793)
              ·
                refine ⟨9465363935382682016024845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12620485247176909354699793 9465363935382682016024845)
                ·
                  refine ⟨3549511475768505756009317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9465363935382682016024845 3549511475768505756009317)
                  ·
                    refine ⟨665533401706594829251747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3549511475768505756009317 665533401706594829251747)
                    ·
                      rfl

theorem cell23_3888365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 1, 2, 3, 4].length) (baseStart_3888365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3888365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3888365 prefixEnd_3888365 := by exact prefixLift 3888365
  have htrace : WordTrace (prefixWord ++ tailWord_3888365) baseStart_3888365 baseEnd_3888365 := by
    simpa [prefixWord, tailWord_3888365, baseEnd_3888365] using wordTrace_append hprefix tailTrace_3888365
  have hstable : (prefixWord ++ tailWord_3888365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3888365).length < 2 ^ (prefixWord ++ tailWord_3888365).sum := by decide
  have hdescent : baseEnd_3888365 < baseStart_3888365 := by decide
  rcases family_descends (prefixWord ++ tailWord_3888365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3888382 : List Nat := [4, 2, 2, 1, 1, 2, 1, 5, 1, 4]
def baseStart_3888382 : Nat := 118140960795 + 3888382 * 2 ^ 59
def prefixEnd_3888382 : Nat := 4983230072969 + 3 ^ 40 * 3888382 * 2
def baseEnd_3888382 : Nat := 665536311430303640414221

theorem tailTrace_3888382 : CollatzResearch.WordTrace tailWord_3888382 prefixEnd_3888382 665536311430303640414221 := by
  unfold tailWord_3888382
  simp only [CollatzResearch.WordTrace]
  refine ⟨17727617824882946452547425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 94547295066042381080252933 17727617824882946452547425)
  ·
    refine ⟨13295713368662209839410569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17727617824882946452547425 13295713368662209839410569)
    ·
      refine ⟨9971785026496657379557927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13295713368662209839410569 9971785026496657379557927)
      ·
        refine ⟨14957677539744986069336891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9971785026496657379557927 14957677539744986069336891)
        ·
          refine ⟨22436516309617479104005337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14957677539744986069336891 22436516309617479104005337)
          ·
            refine ⟨16827387232213109328004003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22436516309617479104005337 16827387232213109328004003)
            ·
              refine ⟨25241080848319663992006005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16827387232213109328004003 25241080848319663992006005)
              ·
                refine ⟨2366351329529968499250563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25241080848319663992006005 2366351329529968499250563)
                ·
                  refine ⟨3549526994294952748875845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2366351329529968499250563 3549526994294952748875845)
                  ·
                    refine ⟨665536311430303640414221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3549526994294952748875845 665536311430303640414221)
                    ·
                      rfl

theorem cell23_3888382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 1, 5, 1, 4].length) (baseStart_3888382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3888382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3888382 prefixEnd_3888382 := by exact prefixLift 3888382
  have htrace : WordTrace (prefixWord ++ tailWord_3888382) baseStart_3888382 baseEnd_3888382 := by
    simpa [prefixWord, tailWord_3888382, baseEnd_3888382] using wordTrace_append hprefix tailTrace_3888382
  have hstable : (prefixWord ++ tailWord_3888382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3888382).length < 2 ^ (prefixWord ++ tailWord_3888382).sum := by decide
  have hdescent : baseEnd_3888382 < baseStart_3888382 := by decide
  rcases family_descends (prefixWord ++ tailWord_3888382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3888428 : List Nat := [2, 2, 1, 1, 1, 3, 1, 1, 1, 8, 2]
def baseStart_3888428 : Nat := 118140960795 + 3888428 * 2 ^ 59
def prefixEnd_3888428 : Nat := 4983230072969 + 3 ^ 40 * 3888428 * 2
def baseEnd_3888428 : Nat := 1996632554401017741267451

theorem tailTrace_3888428 : CollatzResearch.WordTrace tailWord_3888428 prefixEnd_3888428 1996632554401017741267451 := by
  unfold tailWord_3888428
  simp only [CollatzResearch.WordTrace]
  refine ⟨70911310178448460738276969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94548413571264614317702625 70911310178448460738276969)
  ·
    refine ⟨53183482633836345553707727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70911310178448460738276969 53183482633836345553707727)
    ·
      refine ⟨79775223950754518330561591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53183482633836345553707727 79775223950754518330561591)
      ·
        refine ⟨119662835926131777495842387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79775223950754518330561591 119662835926131777495842387)
        ·
          refine ⟨179494253889197666243763581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119662835926131777495842387 179494253889197666243763581)
          ·
            refine ⟨67310345208449124841411343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 179494253889197666243763581 67310345208449124841411343)
            ·
              refine ⟨100965517812673687262117015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67310345208449124841411343 100965517812673687262117015)
              ·
                refine ⟨151448276719010530893175523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100965517812673687262117015 151448276719010530893175523)
                ·
                  refine ⟨227172415078515796339763285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 151448276719010530893175523 227172415078515796339763285)
                  ·
                    refine ⟨2662176739201356988356601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 227172415078515796339763285 2662176739201356988356601)
                    ·
                      refine ⟨1996632554401017741267451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2662176739201356988356601 1996632554401017741267451)
                      ·
                        rfl

theorem cell23_3888428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 8, 2].length) (baseStart_3888428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3888428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3888428 prefixEnd_3888428 := by exact prefixLift 3888428
  have htrace : WordTrace (prefixWord ++ tailWord_3888428) baseStart_3888428 baseEnd_3888428 := by
    simpa [prefixWord, tailWord_3888428, baseEnd_3888428] using wordTrace_append hprefix tailTrace_3888428
  have hstable : (prefixWord ++ tailWord_3888428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3888428).length < 2 ^ (prefixWord ++ tailWord_3888428).sum := by decide
  have hdescent : baseEnd_3888428 < baseStart_3888428 := by decide
  rcases family_descends (prefixWord ++ tailWord_3888428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3888431 : List Nat := [1, 1, 2, 1, 2, 1, 3, 1, 5, 1, 5]
def baseStart_3888431 : Nat := 118140960795 + 3888431 * 2 ^ 59
def prefixEnd_3888431 : Nat := 4983230072969 + 3 ^ 40 * 3888431 * 2
def baseEnd_3888431 : Nat := 1996634094842981229529937

theorem tailTrace_3888431 : CollatzResearch.WordTrace tailWord_3888431 prefixEnd_3888431 1996634094842981229529937 := by
  unfold tailWord_3888431
  simp only [CollatzResearch.WordTrace]
  refine ⟨141822729775886052988913147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94548486517257368659275431 141822729775886052988913147)
  ·
    refine ⟨212734094663829079483369721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141822729775886052988913147 212734094663829079483369721)
    ·
      refine ⟨159550570997871809612527291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 212734094663829079483369721 159550570997871809612527291)
      ·
        refine ⟨239325856496807714418790937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159550570997871809612527291 239325856496807714418790937)
        ·
          refine ⟨179494392372605785814093203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 239325856496807714418790937 179494392372605785814093203)
          ·
            refine ⟨269241588558908678721139805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 179494392372605785814093203 269241588558908678721139805)
            ·
              refine ⟨100965595709590754520427427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 269241588558908678721139805 100965595709590754520427427)
              ·
                refine ⟨151448393564386131780641141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100965595709590754520427427 151448393564386131780641141)
                ·
                  refine ⟨14198286896661199854435107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 151448393564386131780641141 14198286896661199854435107)
                  ·
                    refine ⟨21297430344991799781652661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14198286896661199854435107 21297430344991799781652661)
                    ·
                      refine ⟨1996634094842981229529937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21297430344991799781652661 1996634094842981229529937)
                      ·
                        rfl

theorem cell23_3888431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 1, 5, 1, 5].length) (baseStart_3888431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3888431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3888431 prefixEnd_3888431 := by exact prefixLift 3888431
  have htrace : WordTrace (prefixWord ++ tailWord_3888431) baseStart_3888431 baseEnd_3888431 := by
    simpa [prefixWord, tailWord_3888431, baseEnd_3888431] using wordTrace_append hprefix tailTrace_3888431
  have hstable : (prefixWord ++ tailWord_3888431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3888431).length < 2 ^ (prefixWord ++ tailWord_3888431).sum := by decide
  have hdescent : baseEnd_3888431 < baseStart_3888431 := by decide
  rcases family_descends (prefixWord ++ tailWord_3888431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3888448 : List Nat := [2, 1, 1, 2, 2, 1, 6, 1, 1, 1, 5]
def baseStart_3888448 : Nat := 118140960795 + 3888448 * 2 ^ 59
def prefixEnd_3888448 : Nat := 4983230072969 + 3 ^ 40 * 3888448 * 2
def baseEnd_3888448 : Nat := 1996642824014107663017359

theorem tailTrace_3888448 : CollatzResearch.WordTrace tailWord_3888448 prefixEnd_3888448 1996642824014107663017359 := by
  unfold tailWord_3888448
  simp only [CollatzResearch.WordTrace]
  refine ⟨70911674908412232446140999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94548899877882976594854665 70911674908412232446140999)
  ·
    refine ⟨106367512362618348669211499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70911674908412232446140999 106367512362618348669211499)
    ·
      refine ⟨159551268543927523003817249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106367512362618348669211499 159551268543927523003817249)
      ·
        refine ⟨119663451407945642252862937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159551268543927523003817249 119663451407945642252862937)
        ·
          refine ⟨89747588555959231689647203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119663451407945642252862937 89747588555959231689647203)
          ·
            refine ⟨134621382833938847534470805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89747588555959231689647203 134621382833938847534470805)
            ·
              refine ⟨6310377320340883478178319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 134621382833938847534470805 6310377320340883478178319)
              ·
                refine ⟨9465565980511325217267479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6310377320340883478178319 9465565980511325217267479)
                ·
                  refine ⟨14198348970766987825901219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9465565980511325217267479 14198348970766987825901219)
                  ·
                    refine ⟨21297523456150481738851829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14198348970766987825901219 21297523456150481738851829)
                    ·
                      refine ⟨1996642824014107663017359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21297523456150481738851829 1996642824014107663017359)
                      ·
                        rfl

theorem cell23_3888448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 6, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 6, 1, 1, 1, 5].length) (baseStart_3888448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3888448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3888448 prefixEnd_3888448 := by exact prefixLift 3888448
  have htrace : WordTrace (prefixWord ++ tailWord_3888448) baseStart_3888448 baseEnd_3888448 := by
    simpa [prefixWord, tailWord_3888448, baseEnd_3888448] using wordTrace_append hprefix tailTrace_3888448
  have hstable : (prefixWord ++ tailWord_3888448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3888448).length < 2 ^ (prefixWord ++ tailWord_3888448).sum := by decide
  have hdescent : baseEnd_3888448 < baseStart_3888448 := by decide
  rcases family_descends (prefixWord ++ tailWord_3888448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3888468 : List Nat := [2, 4, 1, 1, 2, 1, 4, 8]
def baseStart_3888468 : Nat := 118140960795 + 3888468 * 2 ^ 59
def prefixEnd_3888468 : Nat := 4983230072969 + 3 ^ 40 * 3888468 * 2
def baseEnd_3888468 : Nat := 73950114578785095732121

theorem tailTrace_3888468 : CollatzResearch.WordTrace tailWord_3888468 prefixEnd_3888468 73950114578785095732121 := by
  unfold tailWord_3888468
  simp only [CollatzResearch.WordTrace]
  refine ⟨70912039638376004154005029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94549386184501338872006705 70912039638376004154005029)
  ·
    refine ⟨13296007432195500778875943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 70912039638376004154005029 13296007432195500778875943)
    ·
      refine ⟨19944011148293251168313915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13296007432195500778875943 19944011148293251168313915)
      ·
        refine ⟨29916016722439876752470873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19944011148293251168313915 29916016722439876752470873)
        ·
          refine ⟨22437012541829907564353155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29916016722439876752470873 22437012541829907564353155)
          ·
            refine ⟨33655518812744861346529733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22437012541829907564353155 33655518812744861346529733)
            ·
              refine ⟨6310409777389661502474325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33655518812744861346529733 6310409777389661502474325)
              ·
                refine ⟨73950114578785095732121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6310409777389661502474325 73950114578785095732121)
                ·
                  rfl

theorem cell23_3888468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 4, 8].length) (baseStart_3888468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3888468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3888468 prefixEnd_3888468 := by exact prefixLift 3888468
  have htrace : WordTrace (prefixWord ++ tailWord_3888468) baseStart_3888468 baseEnd_3888468 := by
    simpa [prefixWord, tailWord_3888468, baseEnd_3888468] using wordTrace_append hprefix tailTrace_3888468
  have hstable : (prefixWord ++ tailWord_3888468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3888468).length < 2 ^ (prefixWord ++ tailWord_3888468).sum := by decide
  have hdescent : baseEnd_3888468 < baseStart_3888468 := by decide
  rcases family_descends (prefixWord ++ tailWord_3888468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3888548 : List Nat := [2, 3, 1, 2, 1, 1, 1, 1, 3, 4, 4]
def baseStart_3888548 : Nat := 118140960795 + 3888548 * 2 ^ 59
def prefixEnd_3888548 : Nat := 4983230072969 + 3 ^ 40 * 3888548 * 2
def baseEnd_3888548 : Nat := 1996694172079557271766899

theorem tailTrace_3888548 : CollatzResearch.WordTrace tailWord_3888548 prefixEnd_3888548 1996694172079557271766899 := by
  unfold tailWord_3888548
  simp only [CollatzResearch.WordTrace]
  refine ⟨70913498558231090985461149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94551331410974787980614865 70913498558231090985461149)
  ·
    refine ⟨26592561959336659119547931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70913498558231090985461149 26592561959336659119547931)
    ·
      refine ⟨39888842939004988679321897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26592561959336659119547931 39888842939004988679321897)
      ·
        refine ⟨29916632204253741509491423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39888842939004988679321897 29916632204253741509491423)
        ·
          refine ⟨44874948306380612264237135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29916632204253741509491423 44874948306380612264237135)
          ·
            refine ⟨67312422459570918396355703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44874948306380612264237135 67312422459570918396355703)
            ·
              refine ⟨100968633689356377594533555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67312422459570918396355703 100968633689356377594533555)
              ·
                refine ⟨151452950534034566391800333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100968633689356377594533555 151452950534034566391800333)
                ·
                  refine ⟨56794856450262962396925125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 151452950534034566391800333 56794856450262962396925125)
                  ·
                    refine ⟨10649035584424305449423461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 56794856450262962396925125 10649035584424305449423461)
                    ·
                      refine ⟨1996694172079557271766899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10649035584424305449423461 1996694172079557271766899)
                      ·
                        rfl

theorem cell23_3888548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 1, 3, 4, 4].length) (baseStart_3888548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3888548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3888548 prefixEnd_3888548 := by exact prefixLift 3888548
  have htrace : WordTrace (prefixWord ++ tailWord_3888548) baseStart_3888548 baseEnd_3888548 := by
    simpa [prefixWord, tailWord_3888548, baseEnd_3888548] using wordTrace_append hprefix tailTrace_3888548
  have hstable : (prefixWord ++ tailWord_3888548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3888548).length < 2 ^ (prefixWord ++ tailWord_3888548).sum := by decide
  have hdescent : baseEnd_3888548 < baseStart_3888548 := by decide
  rcases family_descends (prefixWord ++ tailWord_3888548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3888565 : List Nat := [1, 3, 3, 2, 2, 1, 1, 2, 2, 2, 4]
def baseStart_3888565 : Nat := 118140960795 + 3888565 * 2 ^ 59
def prefixEnd_3888565 : Nat := 4983230072969 + 3 ^ 40 * 3888565 * 2
def baseEnd_3888565 : Nat := 1996702901250683705254321

theorem tailTrace_3888565 : CollatzResearch.WordTrace tailWord_3888565 prefixEnd_3888565 1996702901250683705254321 := by
  unfold tailWord_3888565
  simp only [CollatzResearch.WordTrace]
  refine ⟨141827617157400593874291149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94551744771600395916194099 141827617157400593874291149)
  ·
    refine ⟨53185356434025222702859181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 141827617157400593874291149 53185356434025222702859181)
    ·
      refine ⟨19944508662759458513572193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53185356434025222702859181 19944508662759458513572193)
      ·
        refine ⟨14958381497069593885179145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19944508662759458513572193 14958381497069593885179145)
        ·
          refine ⟨11218786122802195413884359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14958381497069593885179145 11218786122802195413884359)
          ·
            refine ⟨16828179184203293120826539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11218786122802195413884359 16828179184203293120826539)
            ·
              refine ⟨25242268776304939681239809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16828179184203293120826539 25242268776304939681239809)
              ·
                refine ⟨18931701582228704760929857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25242268776304939681239809 18931701582228704760929857)
                ·
                  refine ⟨14198776186671528570697393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18931701582228704760929857 14198776186671528570697393)
                  ·
                    refine ⟨10649082140003646428023045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14198776186671528570697393 10649082140003646428023045)
                    ·
                      refine ⟨1996702901250683705254321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10649082140003646428023045 1996702901250683705254321)
                      ·
                        rfl

theorem cell23_3888565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 1, 2, 2, 2, 4].length) (baseStart_3888565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3888565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3888565 prefixEnd_3888565 := by exact prefixLift 3888565
  have htrace : WordTrace (prefixWord ++ tailWord_3888565) baseStart_3888565 baseEnd_3888565 := by
    simpa [prefixWord, tailWord_3888565, baseEnd_3888565] using wordTrace_append hprefix tailTrace_3888565
  have hstable : (prefixWord ++ tailWord_3888565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3888565).length < 2 ^ (prefixWord ++ tailWord_3888565).sum := by decide
  have hdescent : baseEnd_3888565 < baseStart_3888565 := by decide
  rcases family_descends (prefixWord ++ tailWord_3888565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3888569 : List Nat := [1, 2, 1, 4, 4, 1, 1, 1, 4, 2, 2]
def baseStart_3888569 : Nat := 118140960795 + 3888569 * 2 ^ 59
def prefixEnd_3888569 : Nat := 4983230072969 + 3 ^ 40 * 3888569 * 2
def baseEnd_3888569 : Nat := 1996704955173301689604303

theorem tailTrace_3888569 : CollatzResearch.WordTrace tailWord_3888569 prefixEnd_3888569 1996704955173301689604303 := by
  unfold tailWord_3888569
  simp only [CollatzResearch.WordTrace]
  refine ⟨141827763049386102557436761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94551842032924068371624507 141827763049386102557436761)
  ·
    refine ⟨106370822287039576918077571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141827763049386102557436761 106370822287039576918077571)
    ·
      refine ⟨159556233430559365377116357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106370822287039576918077571 159556233430559365377116357)
      ·
        refine ⟨29916793768229881008209317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 159556233430559365377116357 29916793768229881008209317)
        ·
          refine ⟨5609398831543102689039247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29916793768229881008209317 5609398831543102689039247)
          ·
            refine ⟨8414098247314654033558871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5609398831543102689039247 8414098247314654033558871)
            ·
              refine ⟨12621147370971981050338307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8414098247314654033558871 12621147370971981050338307)
              ·
                refine ⟨18931721056457971575507461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12621147370971981050338307 18931721056457971575507461)
                ·
                  refine ⟨3549697698085869670407649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18931721056457971575507461 3549697698085869670407649)
                  ·
                    refine ⟨2662273273564402252805737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3549697698085869670407649 2662273273564402252805737)
                    ·
                      refine ⟨1996704955173301689604303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2662273273564402252805737 1996704955173301689604303)
                      ·
                        rfl

theorem cell23_3888569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 1, 1, 4, 2, 2].length) (baseStart_3888569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3888569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3888569 prefixEnd_3888569 := by exact prefixLift 3888569
  have htrace : WordTrace (prefixWord ++ tailWord_3888569) baseStart_3888569 baseEnd_3888569 := by
    simpa [prefixWord, tailWord_3888569, baseEnd_3888569] using wordTrace_append hprefix tailTrace_3888569
  have hstable : (prefixWord ++ tailWord_3888569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3888569).length < 2 ^ (prefixWord ++ tailWord_3888569).sum := by decide
  have hdescent : baseEnd_3888569 < baseStart_3888569 := by decide
  rcases family_descends (prefixWord ++ tailWord_3888569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3888586 : List Nat := [3, 1, 2, 1, 2, 4, 3, 1, 2, 2, 2]
def baseStart_3888586 : Nat := 118140960795 + 3888586 * 2 ^ 59
def prefixEnd_3888586 : Nat := 4983230072969 + 3 ^ 40 * 3888586 * 2
def baseEnd_3888586 : Nat := 1996713684344428123091725

theorem tailTrace_3888586 : CollatzResearch.WordTrace tailWord_3888586 prefixEnd_3888586 1996713684344428123091725 := by
  unfold tailWord_3888586
  simp only [CollatzResearch.WordTrace]
  refine ⟨35457095772581128615201403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94552255393549676307203741 35457095772581128615201403)
  ·
    refine ⟨53185643658871692922802105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35457095772581128615201403 53185643658871692922802105)
    ·
      refine ⟨39889232744153769692101579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53185643658871692922802105 39889232744153769692101579)
      ·
        refine ⟨59833849116230654538152369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39889232744153769692101579 59833849116230654538152369)
        ·
          refine ⟨44875386837172990903614277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59833849116230654538152369 44875386837172990903614277)
          ·
            refine ⟨8414135031969935794427677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44875386837172990903614277 8414135031969935794427677)
            ·
              refine ⟨3155300636988725922910379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8414135031969935794427677 3155300636988725922910379)
              ·
                refine ⟨4732950955483088884365569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3155300636988725922910379 4732950955483088884365569)
                ·
                  refine ⟨3549713216612316663274177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4732950955483088884365569 3549713216612316663274177)
                  ·
                    refine ⟨2662284912459237497455633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3549713216612316663274177 2662284912459237497455633)
                    ·
                      refine ⟨1996713684344428123091725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2662284912459237497455633 1996713684344428123091725)
                      ·
                        rfl

theorem cell23_3888586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 3, 1, 2, 2, 2].length) (baseStart_3888586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3888586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3888586 prefixEnd_3888586 := by exact prefixLift 3888586
  have htrace : WordTrace (prefixWord ++ tailWord_3888586) baseStart_3888586 baseEnd_3888586 := by
    simpa [prefixWord, tailWord_3888586, baseEnd_3888586] using wordTrace_append hprefix tailTrace_3888586
  have hstable : (prefixWord ++ tailWord_3888586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3888586).length < 2 ^ (prefixWord ++ tailWord_3888586).sum := by decide
  have hdescent : baseEnd_3888586 < baseStart_3888586 := by decide
  rcases family_descends (prefixWord ++ tailWord_3888586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3888605 : List Nat := [1, 4, 3, 1, 1, 2, 2, 1, 1, 7]
def baseStart_3888605 : Nat := 118140960795 + 3888605 * 2 ^ 59
def prefixEnd_3888605 : Nat := 4983230072969 + 3 ^ 40 * 3888605 * 2
def baseEnd_3888605 : Nat := 665574480158954516251379

theorem tailTrace_3888605 : CollatzResearch.WordTrace tailWord_3888605 prefixEnd_3888605 665574480158954516251379 := by
  unfold tailWord_3888605
  simp only [CollatzResearch.WordTrace]
  refine ⟨141829076077255680705747269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94552717384837120470498179 141829076077255680705747269)
  ·
    refine ⟨26592951764485440132327613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 141829076077255680705747269 26592951764485440132327613)
    ·
      refine ⟨9972356911682040049622855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26592951764485440132327613 9972356911682040049622855)
      ·
        refine ⟨14958535367523060074434283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9972356911682040049622855 14958535367523060074434283)
        ·
          refine ⟨22437803051284590111651425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14958535367523060074434283 22437803051284590111651425)
          ·
            refine ⟨16828352288463442583738569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22437803051284590111651425 16828352288463442583738569)
            ·
              refine ⟨12621264216347581937803927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16828352288463442583738569 12621264216347581937803927)
              ·
                refine ⟨18931896324521372906705891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12621264216347581937803927 18931896324521372906705891)
                ·
                  refine ⟨28397844486782059360058837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18931896324521372906705891 28397844486782059360058837)
                  ·
                    refine ⟨665574480158954516251379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 28397844486782059360058837 665574480158954516251379)
                    ·
                      rfl

theorem cell23_3888605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 2, 1, 1, 7].length) (baseStart_3888605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3888605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3888605 prefixEnd_3888605 := by exact prefixLift 3888605
  have htrace : WordTrace (prefixWord ++ tailWord_3888605) baseStart_3888605 baseEnd_3888605 := by
    simpa [prefixWord, tailWord_3888605, baseEnd_3888605] using wordTrace_append hprefix tailTrace_3888605
  have hstable : (prefixWord ++ tailWord_3888605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3888605).length < 2 ^ (prefixWord ++ tailWord_3888605).sum := by decide
  have hdescent : baseEnd_3888605 < baseStart_3888605 := by decide
  rcases family_descends (prefixWord ++ tailWord_3888605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3888625 : List Nat := [1, 2, 2, 2, 3, 2, 1, 1, 4, 1, 4]
def baseStart_3888625 : Nat := 118140960795 + 3888625 * 2 ^ 59
def prefixEnd_3888625 : Nat := 4983230072969 + 3 ^ 40 * 3888625 * 2
def baseEnd_3888625 : Nat := 1996733710089953470504045

theorem tailTrace_3888625 : CollatzResearch.WordTrace tailWord_3888625 prefixEnd_3888625 1996733710089953470504045 := by
  unfold tailWord_3888625
  simp only [CollatzResearch.WordTrace]
  refine ⟨141829805537183224121475329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94553203691455482747650219 141829805537183224121475329)
  ·
    refine ⟨106372354152887418091106497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141829805537183224121475329 106372354152887418091106497)
    ·
      refine ⟨79779265614665563568329873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106372354152887418091106497 79779265614665563568329873)
      ·
        refine ⟨59834449210999172676247405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79779265614665563568329873 59834449210999172676247405)
        ·
          refine ⟨22437918454124689753592777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59834449210999172676247405 22437918454124689753592777)
          ·
            refine ⟨16828438840593517315194583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22437918454124689753592777 16828438840593517315194583)
            ·
              refine ⟨25242658260890275972791875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16828438840593517315194583 25242658260890275972791875)
              ·
                refine ⟨37863987391335413959187813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25242658260890275972791875 37863987391335413959187813)
                ·
                  refine ⟨7099497635875390117347715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37863987391335413959187813 7099497635875390117347715)
                  ·
                    refine ⟨10649246453813085176021573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7099497635875390117347715 10649246453813085176021573)
                    ·
                      refine ⟨1996733710089953470504045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10649246453813085176021573 1996733710089953470504045)
                      ·
                        rfl

theorem cell23_3888625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 1, 1, 4, 1, 4].length) (baseStart_3888625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3888625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3888625 prefixEnd_3888625 := by exact prefixLift 3888625
  have htrace : WordTrace (prefixWord ++ tailWord_3888625) baseStart_3888625 baseEnd_3888625 := by
    simpa [prefixWord, tailWord_3888625, baseEnd_3888625] using wordTrace_append hprefix tailTrace_3888625
  have hstable : (prefixWord ++ tailWord_3888625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3888625).length < 2 ^ (prefixWord ++ tailWord_3888625).sum := by decide
  have hdescent : baseEnd_3888625 < baseStart_3888625 := by decide
  rcases family_descends (prefixWord ++ tailWord_3888625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3888645 : List Nat := [1, 3, 1, 1, 2, 2, 1, 1, 6, 2, 3]
def baseStart_3888645 : Nat := 118140960795 + 3888645 * 2 ^ 59
def prefixEnd_3888645 : Nat := 4983230072969 + 3 ^ 40 * 3888645 * 2
def baseEnd_3888645 : Nat := 1996743979703043392253953

theorem tailTrace_3888645 : CollatzResearch.WordTrace tailWord_3888645 prefixEnd_3888645 1996743979703043392253953 := by
  unfold tailWord_3888645
  simp only [CollatzResearch.WordTrace]
  refine ⟨141830534997110767537203389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94553689998073845024802259 141830534997110767537203389)
  ·
    refine ⟨53186450623916537826451271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 141830534997110767537203389 53186450623916537826451271)
    ·
      refine ⟨79779675935874806739676907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53186450623916537826451271 79779675935874806739676907)
      ·
        refine ⟨119669513903812210109515361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79779675935874806739676907 119669513903812210109515361)
        ·
          refine ⟨89752135427859157582136521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119669513903812210109515361 89752135427859157582136521)
          ·
            refine ⟨67314101570894368186602391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89752135427859157582136521 67314101570894368186602391)
            ·
              refine ⟨100971152356341552279903587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67314101570894368186602391 100971152356341552279903587)
              ·
                refine ⟨151456728534512328419855381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100971152356341552279903587 151456728534512328419855381)
                ·
                  refine ⟨7099534150055265394680721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 151456728534512328419855381 7099534150055265394680721)
                  ·
                    refine ⟨5324650612541449046010541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7099534150055265394680721 5324650612541449046010541)
                    ·
                      refine ⟨1996743979703043392253953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5324650612541449046010541 1996743979703043392253953)
                      ·
                        rfl

theorem cell23_3888645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 1, 6, 2, 3].length) (baseStart_3888645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3888645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3888645 prefixEnd_3888645 := by exact prefixLift 3888645
  have htrace : WordTrace (prefixWord ++ tailWord_3888645) baseStart_3888645 baseEnd_3888645 := by
    simpa [prefixWord, tailWord_3888645, baseEnd_3888645] using wordTrace_append hprefix tailTrace_3888645
  have hstable : (prefixWord ++ tailWord_3888645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3888645).length < 2 ^ (prefixWord ++ tailWord_3888645).sum := by decide
  have hdescent : baseEnd_3888645 < baseStart_3888645 := by decide
  rcases family_descends (prefixWord ++ tailWord_3888645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3888669 : List Nat := [1, 4, 2, 2, 1, 1, 2, 5, 1, 4]
def baseStart_3888669 : Nat := 118140960795 + 3888669 * 2 ^ 59
def prefixEnd_3888669 : Nat := 4983230072969 + 3 ^ 40 * 3888669 * 2
def baseEnd_3888669 : Nat := 665585434412917099451281

theorem tailTrace_3888669 : CollatzResearch.WordTrace tailWord_3888669 prefixEnd_3888669 665585434412917099451281 := by
  unfold tailWord_3888669
  simp only [CollatzResearch.WordTrace]
  refine ⟨141831410349023819636077061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94554273566015879757384707 141831410349023819636077061)
  ·
    refine ⟨26593389440441966181764449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 141831410349023819636077061 26593389440441966181764449)
    ·
      refine ⟨19945042080331474636323337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26593389440441966181764449 19945042080331474636323337)
      ·
        refine ⟨14958781560248605977242503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19945042080331474636323337 14958781560248605977242503)
        ·
          refine ⟨22438172340372908965863755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14958781560248605977242503 22438172340372908965863755)
          ·
            refine ⟨33657258510559363448795633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22438172340372908965863755 33657258510559363448795633)
            ·
              refine ⟨25242943882919522586596725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33657258510559363448795633 25242943882919522586596725)
              ·
                refine ⟨2366525989023705242493443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25242943882919522586596725 2366525989023705242493443)
                ·
                  refine ⟨3549788983535557863740165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2366525989023705242493443 3549788983535557863740165)
                  ·
                    refine ⟨665585434412917099451281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3549788983535557863740165 665585434412917099451281)
                    ·
                      rfl

theorem cell23_3888669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 2, 5, 1, 4].length) (baseStart_3888669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3888669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3888669 prefixEnd_3888669 := by exact prefixLift 3888669
  have htrace : WordTrace (prefixWord ++ tailWord_3888669) baseStart_3888669 baseEnd_3888669 := by
    simpa [prefixWord, tailWord_3888669, baseEnd_3888669] using wordTrace_append hprefix tailTrace_3888669
  have hstable : (prefixWord ++ tailWord_3888669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3888669).length < 2 ^ (prefixWord ++ tailWord_3888669).sum := by decide
  have hdescent : baseEnd_3888669 < baseStart_3888669 := by decide
  rcases family_descends (prefixWord ++ tailWord_3888669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3888682 : List Nat := [3, 1, 4, 1, 1, 1, 4, 2, 6]
def baseStart_3888682 : Nat := 118140960795 + 3888682 * 2 ^ 59
def prefixEnd_3888682 : Nat := 4983230072969 + 3 ^ 40 * 3888682 * 2
def baseEnd_3888682 : Nat := 221862553165251083054587

theorem tailTrace_3888682 : CollatzResearch.WordTrace tailWord_3888682 prefixEnd_3888682 221862553165251083054587 := by
  unfold tailWord_3888682
  simp only [CollatzResearch.WordTrace]
  refine ⟨35457971124494180714075075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94554589665317815237533533 35457971124494180714075075)
  ·
    refine ⟨53186956686741271071112613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35457971124494180714075075 53186956686741271071112613)
    ·
      refine ⟨9972554378763988325833615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 53186956686741271071112613 9972554378763988325833615)
      ·
        refine ⟨14958831568145982488750423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9972554378763988325833615 14958831568145982488750423)
        ·
          refine ⟨22438247352218973733125635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14958831568145982488750423 22438247352218973733125635)
          ·
            refine ⟨33657371028328460599688453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22438247352218973733125635 33657371028328460599688453)
            ·
              refine ⟨6310757067811586362441585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33657371028328460599688453 6310757067811586362441585)
              ·
                refine ⟨4733067800858689771831189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6310757067811586362441585 4733067800858689771831189)
                ·
                  refine ⟨221862553165251083054587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4733067800858689771831189 221862553165251083054587)
                  ·
                    rfl

theorem cell23_3888682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 4, 2, 6].length) (baseStart_3888682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3888682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3888682 prefixEnd_3888682 := by exact prefixLift 3888682
  have htrace : WordTrace (prefixWord ++ tailWord_3888682) baseStart_3888682 baseEnd_3888682 := by
    simpa [prefixWord, tailWord_3888682, baseEnd_3888682] using wordTrace_append hprefix tailTrace_3888682
  have hstable : (prefixWord ++ tailWord_3888682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3888682).length < 2 ^ (prefixWord ++ tailWord_3888682).sum := by decide
  have hdescent : baseEnd_3888682 < baseStart_3888682 := by decide
  rcases family_descends (prefixWord ++ tailWord_3888682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3888686 : List Nat := [4, 1, 3, 1, 2, 2, 1, 4, 1, 4]
def baseStart_3888686 : Nat := 118140960795 + 3888686 * 2 ^ 59
def prefixEnd_3888686 : Nat := 4983230072969 + 3 ^ 40 * 3888686 * 2
def baseEnd_3888686 : Nat := 665588344136625910613755

theorem tailTrace_3888686 : CollatzResearch.WordTrace tailWord_3888686 prefixEnd_3888686 665588344136625910613755 := by
  unfold tailWord_3888686
  simp only [CollatzResearch.WordTrace]
  refine ⟨17729003798745278942430739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 94554686926641487692963941 17729003798745278942430739)
  ·
    refine ⟨26593505698117918413646109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17729003798745278942430739 26593505698117918413646109)
    ·
      refine ⟨9972564636794219405117291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26593505698117918413646109 9972564636794219405117291)
      ·
        refine ⟨14958846955191329107675937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9972564636794219405117291 14958846955191329107675937)
        ·
          refine ⟨11219135216393496830756953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14958846955191329107675937 11219135216393496830756953)
          ·
            refine ⟨8414351412295122623067715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11219135216393496830756953 8414351412295122623067715)
            ·
              refine ⟨12621527118442683934601573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8414351412295122623067715 12621527118442683934601573)
              ·
                refine ⟨2366536334708003237737795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12621527118442683934601573 2366536334708003237737795)
                ·
                  refine ⟨3549804502062004856606693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2366536334708003237737795 3549804502062004856606693)
                  ·
                    refine ⟨665588344136625910613755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3549804502062004856606693 665588344136625910613755)
                    ·
                      rfl

theorem cell23_3888686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 1, 4, 1, 4].length) (baseStart_3888686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3888686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3888686 prefixEnd_3888686 := by exact prefixLift 3888686
  have htrace : WordTrace (prefixWord ++ tailWord_3888686) baseStart_3888686 baseEnd_3888686 := by
    simpa [prefixWord, tailWord_3888686, baseEnd_3888686] using wordTrace_append hprefix tailTrace_3888686
  have hstable : (prefixWord ++ tailWord_3888686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3888686).length < 2 ^ (prefixWord ++ tailWord_3888686).sum := by decide
  have hdescent : baseEnd_3888686 < baseStart_3888686 := by decide
  rcases family_descends (prefixWord ++ tailWord_3888686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3888695 : List Nat := [1, 1, 3, 1, 2, 4, 1, 2, 3, 5]
def baseStart_3888695 : Nat := 118140960795 + 3888695 * 2 ^ 59
def prefixEnd_3888695 : Nat := 4983230072969 + 3 ^ 40 * 3888695 * 2
def baseEnd_3888695 : Nat := 665589884578589398876241

theorem tailTrace_3888695 : CollatzResearch.WordTrace tailWord_3888695 prefixEnd_3888695 665589884578589398876241 := by
  unfold tailWord_3888695
  simp only [CollatzResearch.WordTrace]
  refine ⟨141832358646929626076523539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94554905764619750717682359 141832358646929626076523539)
  ·
    refine ⟨212748537970394439114785309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141832358646929626076523539 212748537970394439114785309)
    ·
      refine ⟨79780701738897914668044491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 212748537970394439114785309 79780701738897914668044491)
      ·
        refine ⟨119671052608346872002066737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79780701738897914668044491 119671052608346872002066737)
        ·
          refine ⟨89753289456260154001550053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119671052608346872002066737 89753289456260154001550053)
          ·
            refine ⟨16828741773048778875290635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 89753289456260154001550053 16828741773048778875290635)
            ·
              refine ⟨25243112659573168312935953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16828741773048778875290635 25243112659573168312935953)
              ·
                refine ⟨18932334494679876234701965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25243112659573168312935953 18932334494679876234701965)
                ·
                  refine ⟨7099625435504953588013237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18932334494679876234701965 7099625435504953588013237)
                  ·
                    refine ⟨665589884578589398876241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7099625435504953588013237 665589884578589398876241)
                    ·
                      rfl

theorem cell23_3888695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 1, 2, 3, 5].length) (baseStart_3888695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3888695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3888695 prefixEnd_3888695 := by exact prefixLift 3888695
  have htrace : WordTrace (prefixWord ++ tailWord_3888695) baseStart_3888695 baseEnd_3888695 := by
    simpa [prefixWord, tailWord_3888695, baseEnd_3888695] using wordTrace_append hprefix tailTrace_3888695
  have hstable : (prefixWord ++ tailWord_3888695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3888695).length < 2 ^ (prefixWord ++ tailWord_3888695).sum := by decide
  have hdescent : baseEnd_3888695 < baseStart_3888695 := by decide
  rcases family_descends (prefixWord ++ tailWord_3888695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3888705 : List Nat := [1, 2, 5, 1, 1, 1, 1, 1, 2, 1, 7]
def baseStart_3888705 : Nat := 118140960795 + 3888705 * 2 ^ 59
def prefixEnd_3888705 : Nat := 4983230072969 + 3 ^ 40 * 3888705 * 2
def baseEnd_3888705 : Nat := 1996774788542313157503677

theorem tailTrace_3888705 : CollatzResearch.WordTrace tailWord_3888705 prefixEnd_3888705 1996774788542313157503677 := by
  unfold tailWord_3888705
  simp only [CollatzResearch.WordTrace]
  refine ⟨141832723376893397784387569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94555148917928931856258379 141832723376893397784387569)
  ·
    refine ⟨106374542532670048338290677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141832723376893397784387569 106374542532670048338290677)
    ·
      refine ⟨9972613362437817031714751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 106374542532670048338290677 9972613362437817031714751)
      ·
        refine ⟨14958920043656725547572127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9972613362437817031714751 14958920043656725547572127)
        ·
          refine ⟨22438380065485088321358191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14958920043656725547572127 22438380065485088321358191)
          ·
            refine ⟨33657570098227632482037287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22438380065485088321358191 33657570098227632482037287)
            ·
              refine ⟨50486355147341448723055931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33657570098227632482037287 50486355147341448723055931)
              ·
                refine ⟨75729532721012173084583897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50486355147341448723055931 75729532721012173084583897)
                ·
                  refine ⟨56797149540759129813437923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 75729532721012173084583897 56797149540759129813437923)
                  ·
                    refine ⟨85195724311138694720156885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 56797149540759129813437923 85195724311138694720156885)
                    ·
                      refine ⟨1996774788542313157503677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 85195724311138694720156885 1996774788542313157503677)
                      ·
                        rfl

theorem cell23_3888705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 1, 2, 1, 7].length) (baseStart_3888705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3888705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3888705 prefixEnd_3888705 := by exact prefixLift 3888705
  have htrace : WordTrace (prefixWord ++ tailWord_3888705) baseStart_3888705 baseEnd_3888705 := by
    simpa [prefixWord, tailWord_3888705, baseEnd_3888705] using wordTrace_append hprefix tailTrace_3888705
  have hstable : (prefixWord ++ tailWord_3888705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3888705).length < 2 ^ (prefixWord ++ tailWord_3888705).sum := by decide
  have hdescent : baseEnd_3888705 < baseStart_3888705 := by decide
  rcases family_descends (prefixWord ++ tailWord_3888705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3888733 : List Nat := [1, 4, 4, 2, 2, 1, 1, 2, 6]
def baseStart_3888733 : Nat := 118140960795 + 3888733 * 2 ^ 59
def prefixEnd_3888733 : Nat := 4983230072969 + 3 ^ 40 * 3888733 * 2
def baseEnd_3888733 : Nat := 221865462888959894217061

theorem tailTrace_3888733 : CollatzResearch.WordTrace tailWord_3888733 prefixEnd_3888733 221865462888959894217061 := by
  unfold tailWord_3888733
  simp only [CollatzResearch.WordTrace]
  refine ⟨141833744620791958566406853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94555829747194639044271235 141833744620791958566406853)
  ·
    refine ⟨26593827116398492231201285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 141833744620791958566406853 26593827116398492231201285)
    ·
      refine ⟨4986342584324717293350241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26593827116398492231201285 4986342584324717293350241)
      ·
        refine ⟨3739756938243537970012681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4986342584324717293350241 3739756938243537970012681)
        ·
          refine ⟨2804817703682653477509511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3739756938243537970012681 2804817703682653477509511)
          ·
            refine ⟨4207226555523980216264267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2804817703682653477509511 4207226555523980216264267)
            ·
              refine ⟨6310839833285970324396401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4207226555523980216264267 6310839833285970324396401)
              ·
                refine ⟨4733129874964477743297301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6310839833285970324396401 4733129874964477743297301)
                ·
                  refine ⟨221865462888959894217061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4733129874964477743297301 221865462888959894217061)
                  ·
                    rfl

theorem cell23_3888733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 2, 1, 1, 2, 6].length) (baseStart_3888733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3888733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3888733 prefixEnd_3888733 := by exact prefixLift 3888733
  have htrace : WordTrace (prefixWord ++ tailWord_3888733) baseStart_3888733 baseEnd_3888733 := by
    simpa [prefixWord, tailWord_3888733, baseEnd_3888733] using wordTrace_append hprefix tailTrace_3888733
  have hstable : (prefixWord ++ tailWord_3888733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3888733).length < 2 ^ (prefixWord ++ tailWord_3888733).sum := by decide
  have hdescent : baseEnd_3888733 < baseStart_3888733 := by decide
  rcases family_descends (prefixWord ++ tailWord_3888733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3888745 : List Nat := [1, 2, 1, 1, 1, 4, 2, 2, 3, 2, 4]
def baseStart_3888745 : Nat := 118140960795 + 3888745 * 2 ^ 59
def prefixEnd_3888745 : Nat := 4983230072969 + 3 ^ 40 * 3888745 * 2
def baseEnd_3888745 : Nat := 1996795327768493001003493

theorem tailTrace_3888745 : CollatzResearch.WordTrace tailWord_3888745 prefixEnd_3888745 1996795327768493001003493 := by
  unfold tailWord_3888745
  simp only [CollatzResearch.WordTrace]
  refine ⟨141834182296748484615843689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94556121531165656410562459 141834182296748484615843689)
  ·
    refine ⟨106375636722561363461882767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141834182296748484615843689 106375636722561363461882767)
    ·
      refine ⟨159563455083842045192824151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106375636722561363461882767 159563455083842045192824151)
      ·
        refine ⟨239345182625763067789236227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159563455083842045192824151 239345182625763067789236227)
        ·
          refine ⟨359017773938644601683854341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 239345182625763067789236227 359017773938644601683854341)
          ·
            refine ⟨67315832613495862815722689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 359017773938644601683854341 67315832613495862815722689)
            ·
              refine ⟨50486874460121897111792017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67315832613495862815722689 50486874460121897111792017)
              ·
                refine ⟨37865155845091422833844013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50486874460121897111792017 37865155845091422833844013)
                ·
                  refine ⟨14199433441909283562691505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37865155845091422833844013 14199433441909283562691505)
                  ·
                    refine ⟨10649575081431962672018629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14199433441909283562691505 10649575081431962672018629)
                    ·
                      refine ⟨1996795327768493001003493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10649575081431962672018629 1996795327768493001003493)
                      ·
                        rfl

theorem cell23_3888745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 2, 3, 2, 4].length) (baseStart_3888745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3888745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3888745 prefixEnd_3888745 := by exact prefixLift 3888745
  have htrace : WordTrace (prefixWord ++ tailWord_3888745) baseStart_3888745 baseEnd_3888745 := by
    simpa [prefixWord, tailWord_3888745, baseEnd_3888745] using wordTrace_append hprefix tailTrace_3888745
  have hstable : (prefixWord ++ tailWord_3888745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3888745).length < 2 ^ (prefixWord ++ tailWord_3888745).sum := by decide
  have hdescent : baseEnd_3888745 < baseStart_3888745 := by decide
  rcases family_descends (prefixWord ++ tailWord_3888745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3888752 : List Nat := [2, 1, 1, 1, 6, 2, 1, 2, 1, 1, 5]
def baseStart_3888752 : Nat := 118140960795 + 3888752 * 2 ^ 59
def prefixEnd_3888752 : Nat := 4983230072969 + 3 ^ 40 * 3888752 * 2
def baseEnd_3888752 : Nat := 1996798922133074473615961

theorem tailTrace_3888752 : CollatzResearch.WordTrace tailWord_3888752 prefixEnd_3888752 1996798922133074473615961 := by
  unfold tailWord_3888752
  simp only [CollatzResearch.WordTrace]
  refine ⟨70917218803861562405674255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94556291738482083207565673 70917218803861562405674255)
  ·
    refine ⟨106375828205792343608511383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70917218803861562405674255 106375828205792343608511383)
    ·
      refine ⟨159563742308688515412767075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106375828205792343608511383 159563742308688515412767075)
      ·
        refine ⟨239345613463032773119150613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159563742308688515412767075 239345613463032773119150613)
        ·
          refine ⟨11219325631079661239960185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 239345613463032773119150613 11219325631079661239960185)
          ·
            refine ⟨8414494223309745929970139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11219325631079661239960185 8414494223309745929970139)
            ·
              refine ⟨12621741334964618894955209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8414494223309745929970139 12621741334964618894955209)
              ·
                refine ⟨9466306001223464171216407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12621741334964618894955209 9466306001223464171216407)
                ·
                  refine ⟨14199459001835196256824611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9466306001223464171216407 14199459001835196256824611)
                  ·
                    refine ⟨21299188502752794385236917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14199459001835196256824611 21299188502752794385236917)
                    ·
                      refine ⟨1996798922133074473615961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21299188502752794385236917 1996798922133074473615961)
                      ·
                        rfl

theorem cell23_3888752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 1, 2, 1, 1, 5].length) (baseStart_3888752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3888752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3888752 prefixEnd_3888752 := by exact prefixLift 3888752
  have htrace : WordTrace (prefixWord ++ tailWord_3888752) baseStart_3888752 baseEnd_3888752 := by
    simpa [prefixWord, tailWord_3888752, baseEnd_3888752] using wordTrace_append hprefix tailTrace_3888752
  have hstable : (prefixWord ++ tailWord_3888752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3888752).length < 2 ^ (prefixWord ++ tailWord_3888752).sum := by decide
  have hdescent : baseEnd_3888752 < baseStart_3888752 := by decide
  rcases family_descends (prefixWord ++ tailWord_3888752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3888769 : List Nat := [1, 2, 4, 2, 1, 2, 1, 4, 1, 2, 3]
def baseStart_3888769 : Nat := 118140960795 + 3888769 * 2 ^ 59
def prefixEnd_3888769 : Nat := 4983230072969 + 3 ^ 40 * 3888769 * 2
def baseEnd_3888769 : Nat := 1996807651304200907103383

theorem tailTrace_3888769 : CollatzResearch.WordTrace tailWord_3888769 prefixEnd_3888769 1996807651304200907103383 := by
  unfold tailWord_3888769
  simp only [CollatzResearch.WordTrace]
  refine ⟨141835057648661536714717361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94556705099107691143144907 141835057648661536714717361)
  ·
    refine ⟨106376293236496152536038021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141835057648661536714717361 106376293236496152536038021)
    ·
      refine ⟨19945554981843028600507129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 106376293236496152536038021 19945554981843028600507129)
      ·
        refine ⟨14959166236382271450380347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19945554981843028600507129 14959166236382271450380347)
        ·
          refine ⟨22438749354573407175570521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14959166236382271450380347 22438749354573407175570521)
          ·
            refine ⟨16829062015930055381677891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22438749354573407175570521 16829062015930055381677891)
            ·
              refine ⟨25243593023895083072516837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16829062015930055381677891 25243593023895083072516837)
              ·
                refine ⟨4733173691980328076096907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25243593023895083072516837 4733173691980328076096907)
                ·
                  refine ⟨7099760537970492114145361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4733173691980328076096907 7099760537970492114145361)
                  ·
                    refine ⟨5324820403477869085609021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7099760537970492114145361 5324820403477869085609021)
                    ·
                      refine ⟨1996807651304200907103383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5324820403477869085609021 1996807651304200907103383)
                      ·
                        rfl

theorem cell23_3888769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 1, 4, 1, 2, 3].length) (baseStart_3888769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3888769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3888769 prefixEnd_3888769 := by exact prefixLift 3888769
  have htrace : WordTrace (prefixWord ++ tailWord_3888769) baseStart_3888769 baseEnd_3888769 := by
    simpa [prefixWord, tailWord_3888769, baseEnd_3888769] using wordTrace_append hprefix tailTrace_3888769
  have hstable : (prefixWord ++ tailWord_3888769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3888769).length < 2 ^ (prefixWord ++ tailWord_3888769).sum := by decide
  have hdescent : baseEnd_3888769 < baseStart_3888769 := by decide
  rcases family_descends (prefixWord ++ tailWord_3888769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3888772 : List Nat := [2, 3, 2, 1, 4, 1, 1, 9]
def baseStart_3888772 : Nat := 118140960795 + 3888772 * 2 ^ 59
def prefixEnd_3888772 : Nat := 4983230072969 + 3 ^ 40 * 3888772 * 2
def baseEnd_3888772 : Nat := 73955895990598681309847

theorem tailTrace_3888772 : CollatzResearch.WordTrace tailWord_3888772 prefixEnd_3888772 73955895990598681309847 := by
  unfold tailWord_3888772
  simp only [CollatzResearch.WordTrace]
  refine ⟨70917583533825334113538285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94556778045100445484717713 70917583533825334113538285)
  ·
    refine ⟨26594093825184500292576857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70917583533825334113538285 26594093825184500292576857)
    ·
      refine ⟨19945570368888375219432643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26594093825184500292576857 19945570368888375219432643)
      ·
        refine ⟨29918355553332562829148965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19945570368888375219432643 29918355553332562829148965)
        ·
          refine ⟨5609691666249855530465431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29918355553332562829148965 5609691666249855530465431)
          ·
            refine ⟨8414537499374783295698147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5609691666249855530465431 8414537499374783295698147)
            ·
              refine ⟨12621806249062174943547221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8414537499374783295698147 12621806249062174943547221)
              ·
                refine ⟨73955895990598681309847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 12621806249062174943547221 73955895990598681309847)
                ·
                  rfl

theorem cell23_3888772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 1, 9].length) (baseStart_3888772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3888772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3888772 prefixEnd_3888772 := by exact prefixLift 3888772
  have htrace : WordTrace (prefixWord ++ tailWord_3888772) baseStart_3888772 baseEnd_3888772 := by
    simpa [prefixWord, tailWord_3888772, baseEnd_3888772] using wordTrace_append hprefix tailTrace_3888772
  have hstable : (prefixWord ++ tailWord_3888772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3888772).length < 2 ^ (prefixWord ++ tailWord_3888772).sum := by decide
  have hdescent : baseEnd_3888772 < baseStart_3888772 := by decide
  rcases family_descends (prefixWord ++ tailWord_3888772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3888800 : List Nat := [2, 1, 1, 4, 3, 2, 3, 2, 1, 2, 2]
def baseStart_3888800 : Nat := 118140960795 + 3888800 * 2 ^ 59
def prefixEnd_3888800 : Nat := 4983230072969 + 3 ^ 40 * 3888800 * 2
def baseEnd_3888800 : Nat := 1996823569204490285815741

theorem tailTrace_3888800 : CollatzResearch.WordTrace tailWord_3888800 prefixEnd_3888800 1996823569204490285815741 := by
  unfold tailWord_3888800
  simp only [CollatzResearch.WordTrace]
  refine ⟨70918094155774614504547927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94557458874366152672730569 70918094155774614504547927)
  ·
    refine ⟨106377141233661921756821891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70918094155774614504547927 106377141233661921756821891)
    ·
      refine ⟨159565711850492882635232837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106377141233661921756821891 159565711850492882635232837)
      ·
        refine ⟨29918570971967415494106157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 159565711850492882635232837 29918570971967415494106157)
        ·
          refine ⟨11219464114487780810289809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29918570971967415494106157 11219464114487780810289809)
          ·
            refine ⟨8414598085865835607717357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11219464114487780810289809 8414598085865835607717357)
            ·
              refine ⟨3155474282199688352894009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8414598085865835607717357 3155474282199688352894009)
              ·
                refine ⟨2366605711649766264670507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3155474282199688352894009 2366605711649766264670507)
                ·
                  refine ⟨3549908567474649397005761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2366605711649766264670507 3549908567474649397005761)
                  ·
                    refine ⟨2662431425605987047754321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3549908567474649397005761 2662431425605987047754321)
                    ·
                      refine ⟨1996823569204490285815741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2662431425605987047754321 1996823569204490285815741)
                      ·
                        rfl

theorem cell23_3888800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 3, 2, 1, 2, 2].length) (baseStart_3888800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3888800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3888800 prefixEnd_3888800 := by exact prefixLift 3888800
  have htrace : WordTrace (prefixWord ++ tailWord_3888800) baseStart_3888800 baseEnd_3888800 := by
    simpa [prefixWord, tailWord_3888800, baseEnd_3888800] using wordTrace_append hprefix tailTrace_3888800
  have hstable : (prefixWord ++ tailWord_3888800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3888800).length < 2 ^ (prefixWord ++ tailWord_3888800).sum := by decide
  have hdescent : baseEnd_3888800 < baseStart_3888800 := by decide
  rcases family_descends (prefixWord ++ tailWord_3888800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3888815 : List Nat := [1, 1, 2, 1, 2, 4, 2, 1, 1, 8]
def baseStart_3888815 : Nat := 118140960795 + 3888815 * 2 ^ 59
def prefixEnd_3888815 : Nat := 4983230072969 + 3 ^ 40 * 3888815 * 2
def baseEnd_3888815 : Nat := 665610423804769242376057

theorem tailTrace_3888815 : CollatzResearch.WordTrace tailWord_3888815 prefixEnd_3888815 665610423804769242376057 := by
  unfold tailWord_3888815
  simp only [CollatzResearch.WordTrace]
  refine ⟨141836735406494886570891899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94557823604329924380594599 141836735406494886570891899)
  ·
    refine ⟨212755103109742329856337849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141836735406494886570891899 212755103109742329856337849)
    ·
      refine ⟨159566327332306747392253387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 212755103109742329856337849 159566327332306747392253387)
      ·
        refine ⟨239349490998460121088380081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159566327332306747392253387 239349490998460121088380081)
        ·
          refine ⟨179512118248845090816285061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 239349490998460121088380081 179512118248845090816285061)
          ·
            refine ⟨33658522171658454528053449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 179512118248845090816285061 33658522171658454528053449)
            ·
              refine ⟨25243891628743840896040087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33658522171658454528053449 25243891628743840896040087)
              ·
                refine ⟨37865837443115761344060131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25243891628743840896040087 37865837443115761344060131)
                ·
                  refine ⟨56798756164673642016090197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37865837443115761344060131 56798756164673642016090197)
                  ·
                    refine ⟨665610423804769242376057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 56798756164673642016090197 665610423804769242376057)
                    ·
                      rfl

theorem cell23_3888815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 2, 1, 1, 8].length) (baseStart_3888815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3888815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3888815 prefixEnd_3888815 := by exact prefixLift 3888815
  have htrace : WordTrace (prefixWord ++ tailWord_3888815) baseStart_3888815 baseEnd_3888815 := by
    simpa [prefixWord, tailWord_3888815, baseEnd_3888815] using wordTrace_append hprefix tailTrace_3888815
  have hstable : (prefixWord ++ tailWord_3888815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3888815).length < 2 ^ (prefixWord ++ tailWord_3888815).sum := by decide
  have hdescent : baseEnd_3888815 < baseStart_3888815 := by decide
  rcases family_descends (prefixWord ++ tailWord_3888815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3888816 : List Nat := [2, 1, 1, 1, 2, 1, 8, 1, 2, 1, 3]
def baseStart_3888816 : Nat := 118140960795 + 3888816 * 2 ^ 59
def prefixEnd_3888816 : Nat := 4983230072969 + 3 ^ 40 * 3888816 * 2
def baseEnd_3888816 : Nat := 1996831784894962223215667

theorem tailTrace_3888816 : CollatzResearch.WordTrace tailWord_3888816 prefixEnd_3888816 1996831784894962223215667 := by
  unfold tailWord_3888816
  simp only [CollatzResearch.WordTrace]
  refine ⟨70918385939745631870839151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94557847919660842494452201 70918385939745631870839151)
  ·
    refine ⟨106377578909618447806258727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70918385939745631870839151 106377578909618447806258727)
    ·
      refine ⟨159566368364427671709388091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106377578909618447806258727 159566368364427671709388091)
      ·
        refine ⟨239349552546641507564082137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159566368364427671709388091 239349552546641507564082137)
        ·
          refine ⟨179512164409981130673061603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 239349552546641507564082137 179512164409981130673061603)
          ·
            refine ⟨269268246614971696009592405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 179512164409981130673061603 269268246614971696009592405)
            ·
              refine ⟨3155487265019199562612411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 269268246614971696009592405 3155487265019199562612411)
              ·
                refine ⟨4733230897528799343918617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3155487265019199562612411 4733230897528799343918617)
                ·
                  refine ⟨3549923173146599507938963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4733230897528799343918617 3549923173146599507938963)
                  ·
                    refine ⟨5324884759719899261908445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3549923173146599507938963 5324884759719899261908445)
                    ·
                      refine ⟨1996831784894962223215667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5324884759719899261908445 1996831784894962223215667)
                      ·
                        rfl

theorem cell23_3888816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 8, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 8, 1, 2, 1, 3].length) (baseStart_3888816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3888816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3888816 prefixEnd_3888816 := by exact prefixLift 3888816
  have htrace : WordTrace (prefixWord ++ tailWord_3888816) baseStart_3888816 baseEnd_3888816 := by
    simpa [prefixWord, tailWord_3888816, baseEnd_3888816] using wordTrace_append hprefix tailTrace_3888816
  have hstable : (prefixWord ++ tailWord_3888816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3888816).length < 2 ^ (prefixWord ++ tailWord_3888816).sum := by decide
  have hdescent : baseEnd_3888816 < baseStart_3888816 := by decide
  rcases family_descends (prefixWord ++ tailWord_3888816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3888826 : List Nat := [3, 1, 1, 1, 2, 4, 3, 2, 1, 3, 2]
def baseStart_3888826 : Nat := 118140960795 + 3888826 * 2 ^ 59
def prefixEnd_3888826 : Nat := 4983230072969 + 3 ^ 40 * 3888826 * 2
def baseEnd_3888826 : Nat := 1996836919701507184090621

theorem tailTrace_3888826 : CollatzResearch.WordTrace tailWord_3888826 prefixEnd_3888826 1996836919701507184090621 := by
  unfold tailWord_3888826
  simp only [CollatzResearch.WordTrace]
  refine ⟨35459284152363758862385583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94558091072970023633028221 35459284152363758862385583)
  ·
    refine ⟨53188926228545638293578375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35459284152363758862385583 53188926228545638293578375)
    ·
      refine ⟨79783389342818457440367563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53188926228545638293578375 79783389342818457440367563)
      ·
        refine ⟨119675084014227686160551345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79783389342818457440367563 119675084014227686160551345)
        ·
          refine ⟨89756313010670764620413509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119675084014227686160551345 89756313010670764620413509)
          ·
            refine ⟨16829308689500768366327533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 89756313010670764620413509 16829308689500768366327533)
            ·
              refine ⟨6310990758562788137372825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16829308689500768366327533 6310990758562788137372825)
              ·
                refine ⟨4733243068922091103029619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6310990758562788137372825 4733243068922091103029619)
                ·
                  refine ⟨7099864603383136654544429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4733243068922091103029619 7099864603383136654544429)
                  ·
                    refine ⟨2662449226268676245454161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7099864603383136654544429 2662449226268676245454161)
                    ·
                      refine ⟨1996836919701507184090621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2662449226268676245454161 1996836919701507184090621)
                      ·
                        rfl

theorem cell23_3888826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 3, 2, 1, 3, 2].length) (baseStart_3888826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3888826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3888826 prefixEnd_3888826 := by exact prefixLift 3888826
  have htrace : WordTrace (prefixWord ++ tailWord_3888826) baseStart_3888826 baseEnd_3888826 := by
    simpa [prefixWord, tailWord_3888826, baseEnd_3888826] using wordTrace_append hprefix tailTrace_3888826
  have hstable : (prefixWord ++ tailWord_3888826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3888826).length < 2 ^ (prefixWord ++ tailWord_3888826).sum := by decide
  have hdescent : baseEnd_3888826 < baseStart_3888826 := by decide
  rcases family_descends (prefixWord ++ tailWord_3888826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3888839 : List Nat := [1, 1, 4, 1, 1, 1, 5, 2, 1, 4, 2]
def baseStart_3888839 : Nat := 118140960795 + 3888839 * 2 ^ 59
def prefixEnd_3888839 : Nat := 4983230072969 + 3 ^ 40 * 3888839 * 2
def baseEnd_3888839 : Nat := 1996843594950015633228061

theorem tailTrace_3888839 : CollatzResearch.WordTrace tailWord_3888839 prefixEnd_3888839 1996843594950015633228061 := by
  unfold tailWord_3888839
  simp only [CollatzResearch.WordTrace]
  refine ⟨141837610758407938669765571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94558407172271959113177047 141837610758407938669765571)
  ·
    refine ⟨212756416137611908004648357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141837610758407938669765571 212756416137611908004648357)
    ·
      refine ⟨39891828025802232750871567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 212756416137611908004648357 39891828025802232750871567)
      ·
        refine ⟨59837742038703349126307351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39891828025802232750871567 59837742038703349126307351)
        ·
          refine ⟨89756613058055023689461027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59837742038703349126307351 89756613058055023689461027)
          ·
            refine ⟨134634919587082535534191541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89756613058055023689461027 134634919587082535534191541)
            ·
              refine ⟨12622023711288987706330457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 134634919587082535534191541 12622023711288987706330457)
              ·
                refine ⟨9466517783466740779747843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12622023711288987706330457 9466517783466740779747843)
                ·
                  refine ⟨14199776675200111169621765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9466517783466740779747843 14199776675200111169621765)
                  ·
                    refine ⟨2662458126600020844304081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14199776675200111169621765 2662458126600020844304081)
                    ·
                      refine ⟨1996843594950015633228061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2662458126600020844304081 1996843594950015633228061)
                      ·
                        rfl

theorem cell23_3888839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 5, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 5, 2, 1, 4, 2].length) (baseStart_3888839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3888839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3888839 prefixEnd_3888839 := by exact prefixLift 3888839
  have htrace : WordTrace (prefixWord ++ tailWord_3888839) baseStart_3888839 baseEnd_3888839 := by
    simpa [prefixWord, tailWord_3888839, baseEnd_3888839] using wordTrace_append hprefix tailTrace_3888839
  have hstable : (prefixWord ++ tailWord_3888839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3888839).length < 2 ^ (prefixWord ++ tailWord_3888839).sum := by decide
  have hdescent : baseEnd_3888839 < baseStart_3888839 := by decide
  rcases family_descends (prefixWord ++ tailWord_3888839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3888892 : List Nat := [2, 2, 2, 1, 3, 1, 3, 1, 1, 7]
def baseStart_3888892 : Nat := 118140960795 + 3888892 * 2 ^ 59
def prefixEnd_3888892 : Nat := 4983230072969 + 3 ^ 40 * 3888892 * 2
def baseEnd_3888892 : Nat := 665623603141567975288439

theorem tailTrace_3888892 : CollatzResearch.WordTrace tailWord_3888892 prefixEnd_3888892 665623603141567975288439 := by
  unfold tailWord_3888892
  simp only [CollatzResearch.WordTrace]
  refine ⟨70919771913607964360722465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94559695884810619147629953 70919771913607964360722465)
  ·
    refine ⟨53189828935205973270541849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70919771913607964360722465 53189828935205973270541849)
    ·
      refine ⟨39892371701404479952906387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53189828935205973270541849 39892371701404479952906387)
      ·
        refine ⟨59838557552106719929359581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39892371701404479952906387 59838557552106719929359581)
        ·
          refine ⟨22439459082040019973509843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59838557552106719929359581 22439459082040019973509843)
          ·
            refine ⟨33659188623060029960264765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22439459082040019973509843 33659188623060029960264765)
            ·
              refine ⟨12622195733647511235099287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33659188623060029960264765 12622195733647511235099287)
              ·
                refine ⟨18933293600471266852648931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12622195733647511235099287 18933293600471266852648931)
                ·
                  refine ⟨28399940400706900278973397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18933293600471266852648931 28399940400706900278973397)
                  ·
                    refine ⟨665623603141567975288439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 28399940400706900278973397 665623603141567975288439)
                    ·
                      rfl

theorem cell23_3888892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 3, 1, 1, 7].length) (baseStart_3888892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3888892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3888892 prefixEnd_3888892 := by exact prefixLift 3888892
  have htrace : WordTrace (prefixWord ++ tailWord_3888892) baseStart_3888892 baseEnd_3888892 := by
    simpa [prefixWord, tailWord_3888892, baseEnd_3888892] using wordTrace_append hprefix tailTrace_3888892
  have hstable : (prefixWord ++ tailWord_3888892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3888892).length < 2 ^ (prefixWord ++ tailWord_3888892).sum := by decide
  have hdescent : baseEnd_3888892 < baseStart_3888892 := by decide
  rcases family_descends (prefixWord ++ tailWord_3888892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3888952 : List Nat := [2, 1, 2, 1, 3, 3, 1, 2, 8]
def baseStart_3888952 : Nat := 118140960795 + 3888952 * 2 ^ 59
def prefixEnd_3888952 : Nat := 4983230072969 + 3 ^ 40 * 3888952 * 2
def baseEnd_3888952 : Nat := 221877957584885965679449

theorem tailTrace_3888952 : CollatzResearch.WordTrace tailWord_3888952 prefixEnd_3888952 221877957584885965679449 := by
  unfold tailWord_3888952
  simp only [CollatzResearch.WordTrace]
  refine ⟨70920866103499279484314555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94561154804665705979086073 70920866103499279484314555)
  ·
    refine ⟨106381299155248919226471833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70920866103499279484314555 106381299155248919226471833)
    ·
      refine ⟨79785974366436689419853875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106381299155248919226471833 79785974366436689419853875)
      ·
        refine ⟨119678961549655034129780813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79785974366436689419853875 119678961549655034129780813)
        ·
          refine ⟨44879610581120637798667805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 119678961549655034129780813 44879610581120637798667805)
          ·
            refine ⟨16829853967920239174500427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44879610581120637798667805 16829853967920239174500427)
            ·
              refine ⟨25244780951880358761750641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16829853967920239174500427 25244780951880358761750641)
              ·
                refine ⟨18933585713910269071312981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25244780951880358761750641 18933585713910269071312981)
                ·
                  refine ⟨221877957584885965679449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 18933585713910269071312981 221877957584885965679449)
                  ·
                    rfl

theorem cell23_3888952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 1, 2, 8].length) (baseStart_3888952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3888952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3888952 prefixEnd_3888952 := by exact prefixLift 3888952
  have htrace : WordTrace (prefixWord ++ tailWord_3888952) baseStart_3888952 baseEnd_3888952 := by
    simpa [prefixWord, tailWord_3888952, baseEnd_3888952] using wordTrace_append hprefix tailTrace_3888952
  have hstable : (prefixWord ++ tailWord_3888952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3888952).length < 2 ^ (prefixWord ++ tailWord_3888952).sum := by decide
  have hdescent : baseEnd_3888952 < baseStart_3888952 := by decide
  rcases family_descends (prefixWord ++ tailWord_3888952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3888973 : List Nat := [1, 6, 1, 2, 1, 1, 3, 1, 3, 4]
def baseStart_3888973 : Nat := 118140960795 + 3888973 * 2 ^ 59
def prefixEnd_3888973 : Nat := 4983230072969 + 3 ^ 40 * 3888973 * 2
def baseEnd_3888973 : Nat := 665637467119239369650815

theorem tailTrace_3888973 : CollatzResearch.WordTrace tailWord_3888973 prefixEnd_3888973 665637467119239369650815 := by
  unfold tailWord_3888973
  simp only [CollatzResearch.WordTrace]
  refine ⟨141842498139922479555143573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94561665426614986370095715 141842498139922479555143573)
  ·
    refine ⟨6648867100308866229147355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 141842498139922479555143573 6648867100308866229147355)
    ·
      refine ⟨9973300650463299343721033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6648867100308866229147355 9973300650463299343721033)
      ·
        refine ⟨7479975487847474507790775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9973300650463299343721033 7479975487847474507790775)
        ·
          refine ⟨11219963231771211761686163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7479975487847474507790775 11219963231771211761686163)
          ·
            refine ⟨16829944847656817642529245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11219963231771211761686163 16829944847656817642529245)
            ·
              refine ⟨6311229317871306615948467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16829944847656817642529245 6311229317871306615948467)
              ·
                refine ⟨9466843976806959923922701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6311229317871306615948467 9466843976806959923922701)
                ·
                  refine ⟨3550066491302609971471013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9466843976806959923922701 3550066491302609971471013)
                  ·
                    refine ⟨665637467119239369650815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3550066491302609971471013 665637467119239369650815)
                    ·
                      rfl

theorem cell23_3888973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 3, 1, 3, 4].length) (baseStart_3888973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3888973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3888973 prefixEnd_3888973 := by exact prefixLift 3888973
  have htrace : WordTrace (prefixWord ++ tailWord_3888973) baseStart_3888973 baseEnd_3888973 := by
    simpa [prefixWord, tailWord_3888973, baseEnd_3888973] using wordTrace_append hprefix tailTrace_3888973
  have hstable : (prefixWord ++ tailWord_3888973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3888973).length < 2 ^ (prefixWord ++ tailWord_3888973).sum := by decide
  have hdescent : baseEnd_3888973 < baseStart_3888973 := by decide
  rcases family_descends (prefixWord ++ tailWord_3888973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3888999 : List Nat := [1, 1, 5, 1, 2, 1, 3, 1, 3, 5]
def baseStart_3888999 : Nat := 118140960795 + 3888999 * 2 ^ 59
def prefixEnd_3888999 : Nat := 4983230072969 + 3 ^ 40 * 3888999 * 2
def baseEnd_3888999 : Nat := 665641917284911669075775

theorem tailTrace_3888999 : CollatzResearch.WordTrace tailWord_3888999 prefixEnd_3888999 665641917284911669075775 := by
  unfold tailWord_3888999
  simp only [CollatzResearch.WordTrace]
  refine ⟨141843446437828285995590051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94562297625218857330393367 141843446437828285995590051)
  ·
    refine ⟨212765169656742428993385077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141843446437828285995590051 212765169656742428993385077)
    ·
      refine ⟨19946734655319602718129851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 212765169656742428993385077 19946734655319602718129851)
      ·
        refine ⟨29920101982979404077194777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19946734655319602718129851 29920101982979404077194777)
        ·
          refine ⟨22440076487234553057896083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29920101982979404077194777 22440076487234553057896083)
          ·
            refine ⟨33660114730851829586844125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22440076487234553057896083 33660114730851829586844125)
            ·
              refine ⟨12622543024069436095066547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33660114730851829586844125 12622543024069436095066547)
              ·
                refine ⟨18933814536104154142599821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12622543024069436095066547 18933814536104154142599821)
                ·
                  refine ⟨7100180451039057803474933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18933814536104154142599821 7100180451039057803474933)
                  ·
                    refine ⟨665641917284911669075775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7100180451039057803474933 665641917284911669075775)
                    ·
                      rfl

theorem cell23_3888999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 3, 1, 3, 5].length) (baseStart_3888999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3888999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3888999 prefixEnd_3888999 := by exact prefixLift 3888999
  have htrace : WordTrace (prefixWord ++ tailWord_3888999) baseStart_3888999 baseEnd_3888999 := by
    simpa [prefixWord, tailWord_3888999, baseEnd_3888999] using wordTrace_append hprefix tailTrace_3888999
  have hstable : (prefixWord ++ tailWord_3888999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3888999).length < 2 ^ (prefixWord ++ tailWord_3888999).sum := by decide
  have hdescent : baseEnd_3888999 < baseStart_3888999 := by decide
  rcases family_descends (prefixWord ++ tailWord_3888999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3889049 : List Nat := [1, 2, 1, 2, 1, 3, 3, 3, 1, 2, 4]
def baseStart_3889049 : Nat := 118140960795 + 3889049 * 2 ^ 59
def prefixEnd_3889049 : Nat := 4983230072969 + 3 ^ 40 * 3889049 * 2
def baseEnd_3889049 : Nat := 1996951425887459811602095

theorem tailTrace_3889049 : CollatzResearch.WordTrace tailWord_3889049 prefixEnd_3889049 1996951425887459811602095 := by
  unfold tailWord_3889049
  simp only [CollatzResearch.WordTrace]
  refine ⟨141845270087647144534910201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94563513391764763023273467 141845270087647144534910201)
  ·
    refine ⟨106383952565735358401182651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141845270087647144534910201 106383952565735358401182651)
    ·
      refine ⟨159575928848603037601773977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106383952565735358401182651 159575928848603037601773977)
      ·
        refine ⟨119681946636452278201330483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159575928848603037601773977 119681946636452278201330483)
        ·
          refine ⟨179522919954678417301995725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119681946636452278201330483 179522919954678417301995725)
          ·
            refine ⟨67321094983004406488248397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 179522919954678417301995725 67321094983004406488248397)
            ·
              refine ⟨25245410618626652433093149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67321094983004406488248397 25245410618626652433093149)
              ·
                refine ⟨9467028981984994662409931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25245410618626652433093149 9467028981984994662409931)
                ·
                  refine ⟨14200543472977491993614897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9467028981984994662409931 14200543472977491993614897)
                  ·
                    refine ⟨10650407604733118995211173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14200543472977491993614897 10650407604733118995211173)
                    ·
                      refine ⟨1996951425887459811602095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10650407604733118995211173 1996951425887459811602095)
                      ·
                        rfl

theorem cell23_3889049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 3, 3, 1, 2, 4].length) (baseStart_3889049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3889049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3889049 prefixEnd_3889049 := by exact prefixLift 3889049
  have htrace : WordTrace (prefixWord ++ tailWord_3889049) baseStart_3889049 baseEnd_3889049 := by
    simpa [prefixWord, tailWord_3889049, baseEnd_3889049] using wordTrace_append hprefix tailTrace_3889049
  have hstable : (prefixWord ++ tailWord_3889049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3889049).length < 2 ^ (prefixWord ++ tailWord_3889049).sum := by decide
  have hdescent : baseEnd_3889049 < baseStart_3889049 := by decide
  rcases family_descends (prefixWord ++ tailWord_3889049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3889053 : List Nat := [1, 4, 2, 1, 2, 2, 1, 1, 5, 2, 2]
def baseStart_3889053 : Nat := 118140960795 + 3889053 * 2 ^ 59
def prefixEnd_3889053 : Nat := 4983230072969 + 3 ^ 40 * 3889053 * 2
def baseEnd_3889053 : Nat := 1996953479810077795952077

theorem tailTrace_3889053 : CollatzResearch.WordTrace tailWord_3889053 prefixEnd_3889053 1996953479810077795952077 := by
  unfold tailWord_3889053
  simp only [CollatzResearch.WordTrace]
  refine ⟨141845415979632653218055813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94563610653088435478703875 141845415979632653218055813)
  ·
    refine ⟨26596015496181122478385465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 141845415979632653218055813 26596015496181122478385465)
    ·
      refine ⟨19947011622135841858789099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26596015496181122478385465 19947011622135841858789099)
      ·
        refine ⟨29920517433203762788183649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19947011622135841858789099 29920517433203762788183649)
        ·
          refine ⟨22440388074902822091137737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29920517433203762788183649 22440388074902822091137737)
          ·
            refine ⟨16830291056177116568353303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22440388074902822091137737 16830291056177116568353303)
            ·
              refine ⟨25245436584265674852529955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16830291056177116568353303 25245436584265674852529955)
              ·
                refine ⟨37868154876398512278794933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25245436584265674852529955 37868154876398512278794933)
                ·
                  refine ⟨3550139519662360526137025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 37868154876398512278794933 3550139519662360526137025)
                  ·
                    refine ⟨2662604639746770394602769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3550139519662360526137025 2662604639746770394602769)
                    ·
                      refine ⟨1996953479810077795952077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2662604639746770394602769 1996953479810077795952077)
                      ·
                        rfl

theorem cell23_3889053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 1, 1, 5, 2, 2].length) (baseStart_3889053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3889053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3889053 prefixEnd_3889053 := by exact prefixLift 3889053
  have htrace : WordTrace (prefixWord ++ tailWord_3889053) baseStart_3889053 baseEnd_3889053 := by
    simpa [prefixWord, tailWord_3889053, baseEnd_3889053] using wordTrace_append hprefix tailTrace_3889053
  have hstable : (prefixWord ++ tailWord_3889053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3889053).length < 2 ^ (prefixWord ++ tailWord_3889053).sum := by decide
  have hdescent : baseEnd_3889053 < baseStart_3889053 := by decide
  rcases family_descends (prefixWord ++ tailWord_3889053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3889056 : List Nat := [2, 1, 1, 4, 1, 1, 1, 6, 1, 2, 3]
def baseStart_3889056 : Nat := 118140960795 + 3889056 * 2 ^ 59
def prefixEnd_3889056 : Nat := 4983230072969 + 3 ^ 40 * 3889056 * 2
def baseEnd_3889056 : Nat := 1996955020252041284214563

theorem tailTrace_3889056 : CollatzResearch.WordTrace tailWord_3889056 prefixEnd_3889056 1996955020252041284214563 := by
  unfold tailWord_3889056
  simp only [CollatzResearch.WordTrace]
  refine ⟨70922762699310892365207511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94563683599081189820276681 70922762699310892365207511)
  ·
    refine ⟨106384144048966338547811267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70922762699310892365207511 106384144048966338547811267)
    ·
      refine ⟨159576216073449507821716901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106384144048966338547811267 159576216073449507821716901)
      ·
        refine ⟨29920540513771782716571919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 159576216073449507821716901 29920540513771782716571919)
        ·
          refine ⟨44880810770657674074857879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29920540513771782716571919 44880810770657674074857879)
          ·
            refine ⟨67321216155986511112286819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44880810770657674074857879 67321216155986511112286819)
            ·
              refine ⟨100981824233979766668430229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67321216155986511112286819 100981824233979766668430229)
              ·
                refine ⟨4733523010967801562582667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 100981824233979766668430229 4733523010967801562582667)
                ·
                  refine ⟨7100284516451702343874001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4733523010967801562582667 7100284516451702343874001)
                  ·
                    refine ⟨5325213387338776757905501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7100284516451702343874001 5325213387338776757905501)
                    ·
                      refine ⟨1996955020252041284214563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5325213387338776757905501 1996955020252041284214563)
                      ·
                        rfl

theorem cell23_3889056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 6, 1, 2, 3].length) (baseStart_3889056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3889056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3889056 prefixEnd_3889056 := by exact prefixLift 3889056
  have htrace : WordTrace (prefixWord ++ tailWord_3889056) baseStart_3889056 baseEnd_3889056 := by
    simpa [prefixWord, tailWord_3889056, baseEnd_3889056] using wordTrace_append hprefix tailTrace_3889056
  have hstable : (prefixWord ++ tailWord_3889056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3889056).length < 2 ^ (prefixWord ++ tailWord_3889056).sum := by decide
  have hdescent : baseEnd_3889056 < baseStart_3889056 := by decide
  rcases family_descends (prefixWord ++ tailWord_3889056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3889057 : List Nat := [1, 2, 3, 4, 3, 1, 1, 1, 2, 3, 2]
def baseStart_3889057 : Nat := 118140960795 + 3889057 * 2 ^ 59
def prefixEnd_3889057 : Nat := 4983230072969 + 3 ^ 40 * 3889057 * 2
def baseEnd_3889057 : Nat := 1996955533732695780302059

theorem tailTrace_3889057 : CollatzResearch.WordTrace tailWord_3889057 prefixEnd_3889057 1996955533732695780302059 := by
  unfold tailWord_3889057
  simp only [CollatzResearch.WordTrace]
  refine ⟨141845561871618161901201425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94563707914412107934134283 141845561871618161901201425)
  ·
    refine ⟨106384171403713621425901069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141845561871618161901201425 106384171403713621425901069)
    ·
      refine ⟨39894064276392608034712901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106384171403713621425901069 39894064276392608034712901)
      ·
        refine ⟨7480137051823614006508669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39894064276392608034712901 7480137051823614006508669)
        ·
          refine ⟨2805051394433855252440751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7480137051823614006508669 2805051394433855252440751)
          ·
            refine ⟨4207577091650782878661127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2805051394433855252440751 4207577091650782878661127)
            ·
              refine ⟨6311365637476174317991691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4207577091650782878661127 6311365637476174317991691)
              ·
                refine ⟨9467048456214261476987537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6311365637476174317991691 9467048456214261476987537)
                ·
                  refine ⟨7100286342160696107740653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9467048456214261476987537 7100286342160696107740653)
                  ·
                    refine ⟨2662607378310261040402745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7100286342160696107740653 2662607378310261040402745)
                    ·
                      refine ⟨1996955533732695780302059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2662607378310261040402745 1996955533732695780302059)
                      ·
                        rfl

theorem cell23_3889057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 3, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 3, 1, 1, 1, 2, 3, 2].length) (baseStart_3889057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3889057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3889057 prefixEnd_3889057 := by exact prefixLift 3889057
  have htrace : WordTrace (prefixWord ++ tailWord_3889057) baseStart_3889057 baseEnd_3889057 := by
    simpa [prefixWord, tailWord_3889057, baseEnd_3889057] using wordTrace_append hprefix tailTrace_3889057
  have hstable : (prefixWord ++ tailWord_3889057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3889057).length < 2 ^ (prefixWord ++ tailWord_3889057).sum := by decide
  have hdescent : baseEnd_3889057 < baseStart_3889057 := by decide
  rcases family_descends (prefixWord ++ tailWord_3889057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3889064 : List Nat := [2, 1, 6, 2, 1, 1, 2, 3, 1, 1, 3]
def baseStart_3889064 : Nat := 118140960795 + 3889064 * 2 ^ 59
def prefixEnd_3889064 : Nat := 4983230072969 + 3 ^ 40 * 3889064 * 2
def baseEnd_3889064 : Nat := 1996959128097277252914527

theorem tailTrace_3889064 : CollatzResearch.WordTrace tailWord_3889064 prefixEnd_3889064 1996959128097277252914527 := by
  unfold tailWord_3889064
  simp only [CollatzResearch.WordTrace]
  refine ⟨70922908591296401048353123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94563878121728534731137497 70922908591296401048353123)
  ·
    refine ⟨106384362886944601572529685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70922908591296401048353123 106384362886944601572529685)
    ·
      refine ⟨4986767010325528198712329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 106384362886944601572529685 4986767010325528198712329)
      ·
        refine ⟨3740075257744146149034247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4986767010325528198712329 3740075257744146149034247)
        ·
          refine ⟨5610112886616219223551371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3740075257744146149034247 5610112886616219223551371)
          ·
            refine ⟨8415169329924328835327057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5610112886616219223551371 8415169329924328835327057)
            ·
              refine ⟨6311376997443246626495293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8415169329924328835327057 6311376997443246626495293)
              ·
                refine ⟨2366766374041217484935735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6311376997443246626495293 2366766374041217484935735)
                ·
                  refine ⟨3550149561061826227403603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2366766374041217484935735 3550149561061826227403603)
                  ·
                    refine ⟨5325224341592739341105405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3550149561061826227403603 5325224341592739341105405)
                    ·
                      refine ⟨1996959128097277252914527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5325224341592739341105405 1996959128097277252914527)
                      ·
                        rfl

theorem cell23_3889064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 2, 3, 1, 1, 3].length) (baseStart_3889064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3889064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3889064 prefixEnd_3889064 := by exact prefixLift 3889064
  have htrace : WordTrace (prefixWord ++ tailWord_3889064) baseStart_3889064 baseEnd_3889064 := by
    simpa [prefixWord, tailWord_3889064, baseEnd_3889064] using wordTrace_append hprefix tailTrace_3889064
  have hstable : (prefixWord ++ tailWord_3889064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3889064).length < 2 ^ (prefixWord ++ tailWord_3889064).sum := by decide
  have hdescent : baseEnd_3889064 < baseStart_3889064 := by decide
  rcases family_descends (prefixWord ++ tailWord_3889064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3889073 : List Nat := [1, 2, 2, 4, 2, 2, 1, 3, 1, 2, 3]
def baseStart_3889073 : Nat := 118140960795 + 3889073 * 2 ^ 59
def prefixEnd_3889073 : Nat := 4983230072969 + 3 ^ 40 * 3889073 * 2
def baseEnd_3889073 : Nat := 1996963749423167717701985

theorem tailTrace_3889073 : CollatzResearch.WordTrace tailWord_3889073 prefixEnd_3889073 1996963749423167717701985 := by
  unfold tailWord_3889073
  simp only [CollatzResearch.WordTrace]
  refine ⟨141846145439560196633783873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94564096959706797755855915 141846145439560196633783873)
  ·
    refine ⟨106384609079670147475337905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141846145439560196633783873 106384609079670147475337905)
    ·
      refine ⟨79788456809752610606503429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106384609079670147475337905 79788456809752610606503429)
      ·
        refine ⟨14960335651828614488719393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 79788456809752610606503429 14960335651828614488719393)
        ·
          refine ⟨11220251738871460866539545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14960335651828614488719393 11220251738871460866539545)
          ·
            refine ⟨8415188804153595649904659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11220251738871460866539545 8415188804153595649904659)
            ·
              refine ⟨12622783206230393474856989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8415188804153595649904659 12622783206230393474856989)
              ·
                refine ⟨4733543702336397553071371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12622783206230393474856989 4733543702336397553071371)
                ·
                  refine ⟨7100315553504596329607057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4733543702336397553071371 7100315553504596329607057)
                  ·
                    refine ⟨5325236665128447247205293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7100315553504596329607057 5325236665128447247205293)
                    ·
                      refine ⟨1996963749423167717701985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5325236665128447247205293 1996963749423167717701985)
                      ·
                        rfl

theorem cell23_3889073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 1, 3, 1, 2, 3].length) (baseStart_3889073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3889073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3889073 prefixEnd_3889073 := by exact prefixLift 3889073
  have htrace : WordTrace (prefixWord ++ tailWord_3889073) baseStart_3889073 baseEnd_3889073 := by
    simpa [prefixWord, tailWord_3889073, baseEnd_3889073] using wordTrace_append hprefix tailTrace_3889073
  have hstable : (prefixWord ++ tailWord_3889073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3889073).length < 2 ^ (prefixWord ++ tailWord_3889073).sum := by decide
  have hdescent : baseEnd_3889073 < baseStart_3889073 := by decide
  rcases family_descends (prefixWord ++ tailWord_3889073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3889110 : List Nat := [5, 2, 1, 1, 3, 2, 2, 7]
def baseStart_3889110 : Nat := 118140960795 + 3889110 * 2 ^ 59
def prefixEnd_3889110 : Nat := 4983230072969 + 3 ^ 40 * 3889110 * 2
def baseEnd_3889110 : Nat := 73962324007680891590345

theorem tailTrace_3889110 : CollatzResearch.WordTrace tailWord_3889110 prefixEnd_3889110 73962324007680891590345 := by
  unfold tailWord_3889110
  simp only [CollatzResearch.WordTrace]
  refine ⟨8865468433776634497055049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 94564996626950767968587189 8865468433776634497055049)
  ·
    refine ⟨6649101325332475872791287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8865468433776634497055049 6649101325332475872791287)
    ·
      refine ⟨9973651987998713809186931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6649101325332475872791287 9973651987998713809186931)
      ·
        refine ⟨14960477981998070713780397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9973651987998713809186931 14960477981998070713780397)
        ·
          refine ⟨5610179243249276517667649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14960477981998070713780397 5610179243249276517667649)
          ·
            refine ⟨4207634432436957388250737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5610179243249276517667649 4207634432436957388250737)
            ·
              refine ⟨3155725824327718041188053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4207634432436957388250737 3155725824327718041188053)
              ·
                refine ⟨73962324007680891590345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3155725824327718041188053 73962324007680891590345)
                ·
                  rfl

theorem cell23_3889110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 2, 2, 7].length) (baseStart_3889110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3889110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3889110 prefixEnd_3889110 := by exact prefixLift 3889110
  have htrace : WordTrace (prefixWord ++ tailWord_3889110) baseStart_3889110 baseEnd_3889110 := by
    simpa [prefixWord, tailWord_3889110, baseEnd_3889110] using wordTrace_append hprefix tailTrace_3889110
  have hstable : (prefixWord ++ tailWord_3889110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3889110).length < 2 ^ (prefixWord ++ tailWord_3889110).sum := by decide
  have hdescent : baseEnd_3889110 < baseStart_3889110 := by decide
  rcases family_descends (prefixWord ++ tailWord_3889110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3889139 : List Nat := [1, 1, 1, 2, 2, 2, 1, 3, 4, 2, 4]
def baseStart_3889139 : Nat := 118140960795 + 3889139 * 2 ^ 59
def prefixEnd_3889139 : Nat := 4983230072969 + 3 ^ 40 * 3889139 * 2
def baseEnd_3889139 : Nat := 1996997639146364459476681

theorem tailTrace_3889139 : CollatzResearch.WordTrace tailWord_3889139 prefixEnd_3889139 1996997639146364459476681 := by
  unfold tailWord_3889139
  simp only [CollatzResearch.WordTrace]
  refine ⟨141848552657321089905686471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94565701771547393270457647 141848552657321089905686471)
  ·
    refine ⟨212772828985981634858529707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141848552657321089905686471 212772828985981634858529707)
    ·
      refine ⟨319159243478972452287794561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212772828985981634858529707 319159243478972452287794561)
      ·
        refine ⟨239369432609229339215845921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 319159243478972452287794561 239369432609229339215845921)
        ·
          refine ⟨179527074456922004411884441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 239369432609229339215845921 179527074456922004411884441)
          ·
            refine ⟨134645305842691503308913331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 179527074456922004411884441 134645305842691503308913331)
            ·
              refine ⟨201967958764037254963369997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 134645305842691503308913331 201967958764037254963369997)
              ·
                refine ⟨75737984536513970611263749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 201967958764037254963369997 75737984536513970611263749)
                ·
                  refine ⟨14200872100596369489611953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 75737984536513970611263749 14200872100596369489611953)
                  ·
                    refine ⟨10650654075447277117208965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14200872100596369489611953 10650654075447277117208965)
                    ·
                      refine ⟨1996997639146364459476681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10650654075447277117208965 1996997639146364459476681)
                      ·
                        rfl

theorem cell23_3889139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 3, 4, 2, 4].length) (baseStart_3889139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3889139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3889139 prefixEnd_3889139 := by exact prefixLift 3889139
  have htrace : WordTrace (prefixWord ++ tailWord_3889139) baseStart_3889139 baseEnd_3889139 := by
    simpa [prefixWord, tailWord_3889139, baseEnd_3889139] using wordTrace_append hprefix tailTrace_3889139
  have hstable : (prefixWord ++ tailWord_3889139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3889139).length < 2 ^ (prefixWord ++ tailWord_3889139).sum := by decide
  have hdescent : baseEnd_3889139 < baseStart_3889139 := by decide
  rcases family_descends (prefixWord ++ tailWord_3889139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3889158 : List Nat := [6, 2, 1, 2, 2, 1, 1, 2, 1, 2, 3]
def baseStart_3889158 : Nat := 118140960795 + 3889158 * 2 ^ 59
def prefixEnd_3889158 : Nat := 4983230072969 + 3 ^ 40 * 3889158 * 2
def baseEnd_3889158 : Nat := 1997007395278799885139095

theorem tailTrace_3889158 : CollatzResearch.WordTrace tailWord_3889158 prefixEnd_3889158 1997007395278799885139095 := by
  unfold tailWord_3889158
  simp only [CollatzResearch.WordTrace]
  refine ⟨4432788926382883004707129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 94566163762834837433752085 4432788926382883004707129)
  ·
    refine ⟨3324591694787162253530347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4432788926382883004707129 3324591694787162253530347)
    ·
      refine ⟨4986887542180743380295521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3324591694787162253530347 4986887542180743380295521)
      ·
        refine ⟨3740165656635557535221641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4986887542180743380295521 3740165656635557535221641)
        ·
          refine ⟨2805124242476668151416231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3740165656635557535221641 2805124242476668151416231)
          ·
            refine ⟨4207686363715002227124347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2805124242476668151416231 4207686363715002227124347)
            ·
              refine ⟨6311529545572503340686521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4207686363715002227124347 6311529545572503340686521)
              ·
                refine ⟨4733647159179377505514891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6311529545572503340686521 4733647159179377505514891)
                ·
                  refine ⟨7100470738769066258272337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4733647159179377505514891 7100470738769066258272337)
                  ·
                    refine ⟨5325353054076799693704253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7100470738769066258272337 5325353054076799693704253)
                    ·
                      refine ⟨1997007395278799885139095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5325353054076799693704253 1997007395278799885139095)
                      ·
                        rfl

theorem cell23_3889158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 2, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 2, 1, 1, 2, 1, 2, 3].length) (baseStart_3889158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3889158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3889158 prefixEnd_3889158 := by exact prefixLift 3889158
  have htrace : WordTrace (prefixWord ++ tailWord_3889158) baseStart_3889158 baseEnd_3889158 := by
    simpa [prefixWord, tailWord_3889158, baseEnd_3889158] using wordTrace_append hprefix tailTrace_3889158
  have hstable : (prefixWord ++ tailWord_3889158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3889158).length < 2 ^ (prefixWord ++ tailWord_3889158).sum := by decide
  have hdescent : baseEnd_3889158 < baseStart_3889158 := by decide
  rcases family_descends (prefixWord ++ tailWord_3889158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3889160 : List Nat := [2, 1, 3, 2, 1, 2, 3, 3, 2, 2, 2]
def baseStart_3889160 : Nat := 118140960795 + 3889160 * 2 ^ 59
def prefixEnd_3889160 : Nat := 4983230072969 + 3 ^ 40 * 3889160 * 2
def baseEnd_3889160 : Nat := 1997008422240108877314085

theorem tailTrace_3889160 : CollatzResearch.WordTrace tailWord_3889160 prefixEnd_3889160 1997008422240108877314085 := by
  unfold tailWord_3889160
  simp only [CollatzResearch.WordTrace]
  refine ⟨70924659295122505246100467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94566212393496673661467289 70924659295122505246100467)
  ·
    refine ⟨106386988942683757869150701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70924659295122505246100467 106386988942683757869150701)
    ·
      refine ⟨39895120853506409200931513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106386988942683757869150701 39895120853506409200931513)
      ·
        refine ⟨29921340640129806900698635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39895120853506409200931513 29921340640129806900698635)
        ·
          refine ⟨44882010960194710351047953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29921340640129806900698635 44882010960194710351047953)
          ·
            refine ⟨33661508220146032763285965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44882010960194710351047953 33661508220146032763285965)
            ·
              refine ⟨12623065582554762286232237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33661508220146032763285965 12623065582554762286232237)
              ·
                refine ⟨4733649593458035857337089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12623065582554762286232237 4733649593458035857337089)
                ·
                  refine ⟨3550237195093526893002817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4733649593458035857337089 3550237195093526893002817)
                  ·
                    refine ⟨2662677896320145169752113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3550237195093526893002817 2662677896320145169752113)
                    ·
                      refine ⟨1997008422240108877314085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2662677896320145169752113 1997008422240108877314085)
                      ·
                        rfl

theorem cell23_3889160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 3, 3, 2, 2, 2].length) (baseStart_3889160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3889160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3889160 prefixEnd_3889160 := by exact prefixLift 3889160
  have htrace : WordTrace (prefixWord ++ tailWord_3889160) baseStart_3889160 baseEnd_3889160 := by
    simpa [prefixWord, tailWord_3889160, baseEnd_3889160] using wordTrace_append hprefix tailTrace_3889160
  have hstable : (prefixWord ++ tailWord_3889160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3889160).length < 2 ^ (prefixWord ++ tailWord_3889160).sum := by decide
  have hdescent : baseEnd_3889160 < baseStart_3889160 := by decide
  rcases family_descends (prefixWord ++ tailWord_3889160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3889200 : List Nat := [2, 1, 1, 1, 2, 7, 2, 2, 5]
def baseStart_3889200 : Nat := 118140960795 + 3889200 * 2 ^ 59
def prefixEnd_3889200 : Nat := 4983230072969 + 3 ^ 40 * 3889200 * 2
def baseEnd_3889200 : Nat := 221892106829587635645989

theorem tailTrace_3889200 : CollatzResearch.WordTrace tailWord_3889200 prefixEnd_3889200 221892106829587635645989 := by
  unfold tailWord_3889200
  simp only [CollatzResearch.WordTrace]
  refine ⟨70925388755050048661828527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94567185006733398215771369 70925388755050048661828527)
  ·
    refine ⟨106388083132575072992742791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70925388755050048661828527 106388083132575072992742791)
    ·
      refine ⟨159582124698862609489114187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106388083132575072992742791 159582124698862609489114187)
      ·
        refine ⟨239373187048293914233671281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159582124698862609489114187 239373187048293914233671281)
        ·
          refine ⟨179529890286220435675253461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 239373187048293914233671281 179529890286220435675253461)
          ·
            refine ⟨4207731803583291461138753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 179529890286220435675253461 4207731803583291461138753)
            ·
              refine ⟨3155798852687468595854065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4207731803583291461138753 3155798852687468595854065)
              ·
                refine ⟨2366849139515601446890549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3155798852687468595854065 2366849139515601446890549)
                ·
                  refine ⟨221892106829587635645989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2366849139515601446890549 221892106829587635645989)
                  ·
                    rfl

theorem cell23_3889200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 7, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 7, 2, 2, 5].length) (baseStart_3889200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3889200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3889200 prefixEnd_3889200 := by exact prefixLift 3889200
  have htrace : WordTrace (prefixWord ++ tailWord_3889200) baseStart_3889200 baseEnd_3889200 := by
    simpa [prefixWord, tailWord_3889200, baseEnd_3889200] using wordTrace_append hprefix tailTrace_3889200
  have hstable : (prefixWord ++ tailWord_3889200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3889200).length < 2 ^ (prefixWord ++ tailWord_3889200).sum := by decide
  have hdescent : baseEnd_3889200 < baseStart_3889200 := by decide
  rcases family_descends (prefixWord ++ tailWord_3889200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3889260 : List Nat := [2, 2, 1, 1, 3, 3, 2, 4, 1, 4]
def baseStart_3889260 : Nat := 118140960795 + 3889260 * 2 ^ 59
def prefixEnd_3889260 : Nat := 4983230072969 + 3 ^ 40 * 3889260 * 2
def baseEnd_3889260 : Nat := 665686590101852828687875

theorem tailTrace_3889260 : CollatzResearch.WordTrace tailWord_3889260 prefixEnd_3889260 665686590101852828687875 := by
  unfold tailWord_3889260
  simp only [CollatzResearch.WordTrace]
  refine ⟨70926482944941363785420617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94568643926588485047227489 70926482944941363785420617)
  ·
    refine ⟨53194862208706022839065463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70926482944941363785420617 53194862208706022839065463)
    ·
      refine ⟨79792293313059034258598195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53194862208706022839065463 79792293313059034258598195)
      ·
        refine ⟨119688439969588551387897293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79792293313059034258598195 119688439969588551387897293)
        ·
          refine ⟨44883164988595706770461485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 119688439969588551387897293 44883164988595706770461485)
          ·
            refine ⟨16831186870723390038923057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44883164988595706770461485 16831186870723390038923057)
            ·
              refine ⟨12623390153042542529192293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16831186870723390038923057 12623390153042542529192293)
              ·
                refine ⟨2366885653695476724223555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12623390153042542529192293 2366885653695476724223555)
                ·
                  refine ⟨3550328480543215086335333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2366885653695476724223555 3550328480543215086335333)
                  ·
                    refine ⟨665686590101852828687875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3550328480543215086335333 665686590101852828687875)
                    ·
                      rfl

theorem cell23_3889260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 2, 4, 1, 4].length) (baseStart_3889260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3889260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3889260 prefixEnd_3889260 := by exact prefixLift 3889260
  have htrace : WordTrace (prefixWord ++ tailWord_3889260) baseStart_3889260 baseEnd_3889260 := by
    simpa [prefixWord, tailWord_3889260, baseEnd_3889260] using wordTrace_append hprefix tailTrace_3889260
  have hstable : (prefixWord ++ tailWord_3889260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3889260).length < 2 ^ (prefixWord ++ tailWord_3889260).sum := by decide
  have hdescent : baseEnd_3889260 < baseStart_3889260 := by decide
  rcases family_descends (prefixWord ++ tailWord_3889260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3889294 : List Nat := [4, 1, 1, 3, 3, 2, 1, 3, 1, 4]
def baseStart_3889294 : Nat := 118140960795 + 3889294 * 2 ^ 59
def prefixEnd_3889294 : Nat := 4983230072969 + 3 ^ 40 * 3889294 * 2
def baseEnd_3889294 : Nat := 665692409549270451012823

theorem tailTrace_3889294 : CollatzResearch.WordTrace tailWord_3889294 prefixEnd_3889294 665692409549270451012823 := by
  unfold tailWord_3889294
  simp only [CollatzResearch.WordTrace]
  refine ⟨17731775746469943922197367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 94569470647839700918385957 17731775746469943922197367)
  ·
    refine ⟨26597663619704915883296051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17731775746469943922197367 26597663619704915883296051)
    ·
      refine ⟨39896495429557373824944077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26597663619704915883296051 39896495429557373824944077)
      ·
        refine ⟨14961185786084015184354029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39896495429557373824944077 14961185786084015184354029)
        ·
          refine ⟨5610444669781505694132761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14961185786084015184354029 5610444669781505694132761)
          ·
            refine ⟨4207833502336129270599571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5610444669781505694132761 4207833502336129270599571)
            ·
              refine ⟨6311750253504193905899357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4207833502336129270599571 6311750253504193905899357)
              ·
                refine ⟨2366906345064072714712259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6311750253504193905899357 2366906345064072714712259)
                ·
                  refine ⟨3550359517596109072068389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2366906345064072714712259 3550359517596109072068389)
                  ·
                    refine ⟨665692409549270451012823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3550359517596109072068389 665692409549270451012823)
                    ·
                      rfl

theorem cell23_3889294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 2, 1, 3, 1, 4].length) (baseStart_3889294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3889294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3889294 prefixEnd_3889294 := by exact prefixLift 3889294
  have htrace : WordTrace (prefixWord ++ tailWord_3889294) baseStart_3889294 baseEnd_3889294 := by
    simpa [prefixWord, tailWord_3889294, baseEnd_3889294] using wordTrace_append hprefix tailTrace_3889294
  have hstable : (prefixWord ++ tailWord_3889294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3889294).length < 2 ^ (prefixWord ++ tailWord_3889294).sum := by decide
  have hdescent : baseEnd_3889294 < baseStart_3889294 := by decide
  rcases family_descends (prefixWord ++ tailWord_3889294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3889336 : List Nat := [2, 1, 2, 1, 2, 1, 3, 3, 1, 1, 6]
def baseStart_3889336 : Nat := 118140960795 + 3889336 * 2 ^ 59
def prefixEnd_3889336 : Nat := 4983230072969 + 3 ^ 40 * 3889336 * 2
def baseEnd_3889336 : Nat := 1997098794835300188713275

theorem tailTrace_3889336 : CollatzResearch.WordTrace tailWord_3889336 prefixEnd_3889336 1997098794835300188713275 := by
  unfold tailWord_3889336
  simp only [CollatzResearch.WordTrace]
  refine ⟨70927868918803696275303931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94570491891738261700405241 70927868918803696275303931)
  ·
    refine ⟨106391803378205544412955897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70927868918803696275303931 106391803378205544412955897)
    ·
      refine ⟨79793852533654158309716923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106391803378205544412955897 79793852533654158309716923)
      ·
        refine ⟨119690778800481237464575385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79793852533654158309716923 119690778800481237464575385)
        ·
          refine ⟨89768084100360928098431539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119690778800481237464575385 89768084100360928098431539)
          ·
            refine ⟨134652126150541392147647309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89768084100360928098431539 134652126150541392147647309)
            ·
              refine ⟨50494547306453022055367741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 134652126150541392147647309 50494547306453022055367741)
              ·
                refine ⟨18935455239919883270762903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50494547306453022055367741 18935455239919883270762903)
                ·
                  refine ⟨28403182859879824906144355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18935455239919883270762903 28403182859879824906144355)
                  ·
                    refine ⟨42604774289819737359216533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28403182859879824906144355 42604774289819737359216533)
                    ·
                      refine ⟨1997098794835300188713275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 42604774289819737359216533 1997098794835300188713275)
                      ·
                        rfl

theorem cell23_3889336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 3, 1, 1, 6].length) (baseStart_3889336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3889336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3889336 prefixEnd_3889336 := by exact prefixLift 3889336
  have htrace : WordTrace (prefixWord ++ tailWord_3889336) baseStart_3889336 baseEnd_3889336 := by
    simpa [prefixWord, tailWord_3889336, baseEnd_3889336] using wordTrace_append hprefix tailTrace_3889336
  have hstable : (prefixWord ++ tailWord_3889336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3889336).length < 2 ^ (prefixWord ++ tailWord_3889336).sum := by decide
  have hdescent : baseEnd_3889336 < baseStart_3889336 := by decide
  rcases family_descends (prefixWord ++ tailWord_3889336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3889340 : List Nat := [2, 2, 2, 3, 3, 1, 1, 1, 3, 1, 4]
def baseStart_3889340 : Nat := 118140960795 + 3889340 * 2 ^ 59
def prefixEnd_3889340 : Nat := 4983230072969 + 3 ^ 40 * 3889340 * 2
def baseEnd_3889340 : Nat := 1997100848757918173063257

theorem tailTrace_3889340 : CollatzResearch.WordTrace tailWord_3889340 prefixEnd_3889340 1997100848757918173063257 := by
  unfold tailWord_3889340
  simp only [CollatzResearch.WordTrace]
  refine ⟨70927941864796450616876737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94570589153061934155835649 70927941864796450616876737)
  ·
    refine ⟨53195956398597337962657553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70927941864796450616876737 53195956398597337962657553)
    ·
      refine ⟨39896967298948003471993165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53195956398597337962657553 39896967298948003471993165)
      ·
        refine ⟨14961362737105501301997437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39896967298948003471993165 14961362737105501301997437)
        ·
          refine ⟨5610511026414562988249039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14961362737105501301997437 5610511026414562988249039)
          ·
            refine ⟨8415766539621844482373559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5610511026414562988249039 8415766539621844482373559)
            ·
              refine ⟨12623649809432766723560339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8415766539621844482373559 12623649809432766723560339)
              ·
                refine ⟨18935474714149150085340509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12623649809432766723560339 18935474714149150085340509)
                ·
                  refine ⟨7100803017805931282002691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18935474714149150085340509 7100803017805931282002691)
                  ·
                    refine ⟨10651204526708896923004037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7100803017805931282002691 10651204526708896923004037)
                    ·
                      refine ⟨1997100848757918173063257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10651204526708896923004037 1997100848757918173063257)
                      ·
                        rfl

theorem cell23_3889340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 1, 1, 3, 1, 4].length) (baseStart_3889340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3889340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3889340 prefixEnd_3889340 := by exact prefixLift 3889340
  have htrace : WordTrace (prefixWord ++ tailWord_3889340) baseStart_3889340 baseEnd_3889340 := by
    simpa [prefixWord, tailWord_3889340, baseEnd_3889340] using wordTrace_append hprefix tailTrace_3889340
  have hstable : (prefixWord ++ tailWord_3889340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3889340).length < 2 ^ (prefixWord ++ tailWord_3889340).sum := by decide
  have hdescent : baseEnd_3889340 < baseStart_3889340 := by decide
  rcases family_descends (prefixWord ++ tailWord_3889340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3889376 : List Nat := [2, 1, 1, 3, 1, 3, 1, 1, 1, 9]
def baseStart_3889376 : Nat := 118140960795 + 3889376 * 2 ^ 59
def prefixEnd_3889376 : Nat := 4983230072969 + 3 ^ 40 * 3889376 * 2
def baseEnd_3889376 : Nat := 665706444687160010737697

theorem tailTrace_3889376 : CollatzResearch.WordTrace tailWord_3889376 prefixEnd_3889376 665706444687160010737697 := by
  unfold tailWord_3889376
  simp only [CollatzResearch.WordTrace]
  refine ⟨70928598378731239691031991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94571464504974986254709321 70928598378731239691031991)
  ·
    refine ⟨106392897568096859536547987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70928598378731239691031991 106392897568096859536547987)
    ·
      refine ⟨159589346352145289304821981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106392897568096859536547987 159589346352145289304821981)
      ·
        refine ⟨59846004882054483489308243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 159589346352145289304821981 59846004882054483489308243)
        ·
          refine ⟨89769007323081725233962365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59846004882054483489308243 89769007323081725233962365)
          ·
            refine ⟨33663377746155646962735887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 89769007323081725233962365 33663377746155646962735887)
            ·
              refine ⟨50495066619233470444103831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33663377746155646962735887 50495066619233470444103831)
              ·
                refine ⟨75742599928850205666155747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50495066619233470444103831 75742599928850205666155747)
                ·
                  refine ⟨113613899893275308499233621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 75742599928850205666155747 113613899893275308499233621)
                  ·
                    refine ⟨665706444687160010737697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 113613899893275308499233621 665706444687160010737697)
                    ·
                      rfl

theorem cell23_3889376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 1, 1, 9].length) (baseStart_3889376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3889376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3889376 prefixEnd_3889376 := by exact prefixLift 3889376
  have htrace : WordTrace (prefixWord ++ tailWord_3889376) baseStart_3889376 baseEnd_3889376 := by
    simpa [prefixWord, tailWord_3889376, baseEnd_3889376] using wordTrace_append hprefix tailTrace_3889376
  have hstable : (prefixWord ++ tailWord_3889376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3889376).length < 2 ^ (prefixWord ++ tailWord_3889376).sum := by decide
  have hdescent : baseEnd_3889376 < baseStart_3889376 := by decide
  rcases family_descends (prefixWord ++ tailWord_3889376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3889390 : List Nat := [4, 1, 2, 1, 1, 1, 1, 2, 6, 1, 3]
def baseStart_3889390 : Nat := 118140960795 + 3889390 * 2 ^ 59
def prefixEnd_3889390 : Nat := 4983230072969 + 3 ^ 40 * 3889390 * 2
def baseEnd_3889390 : Nat := 1997126522790642977438027

theorem tailTrace_3889390 : CollatzResearch.WordTrace tailWord_3889390 prefixEnd_3889390 1997126522790642977438027 := by
  unfold tailWord_3889390
  simp only [CollatzResearch.WordTrace]
  refine ⟨17732213422426469971634203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 94571804919607839848715749 17732213422426469971634203)
  ·
    refine ⟨26598320133639704957451305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17732213422426469971634203 26598320133639704957451305)
    ·
      refine ⟨19948740100229778718088479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26598320133639704957451305 19948740100229778718088479)
      ·
        refine ⟨29923110150344668077132719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19948740100229778718088479 29923110150344668077132719)
        ·
          refine ⟨44884665225517002115699079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29923110150344668077132719 44884665225517002115699079)
          ·
            refine ⟨67326997838275503173548619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44884665225517002115699079 67326997838275503173548619)
            ·
              refine ⟨100990496757413254760322929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67326997838275503173548619 100990496757413254760322929)
              ·
                refine ⟨75742872568059941070242197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 100990496757413254760322929 75742872568059941070242197)
                ·
                  refine ⟨3550447151627809737667603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 75742872568059941070242197 3550447151627809737667603)
                  ·
                    refine ⟨5325670727441714606501405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3550447151627809737667603 5325670727441714606501405)
                    ·
                      refine ⟨1997126522790642977438027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5325670727441714606501405 1997126522790642977438027)
                      ·
                        rfl

theorem cell23_3889390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 2, 6, 1, 3].length) (baseStart_3889390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3889390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3889390 prefixEnd_3889390 := by exact prefixLift 3889390
  have htrace : WordTrace (prefixWord ++ tailWord_3889390) baseStart_3889390 baseEnd_3889390 := by
    simpa [prefixWord, tailWord_3889390, baseEnd_3889390] using wordTrace_append hprefix tailTrace_3889390
  have hstable : (prefixWord ++ tailWord_3889390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3889390).length < 2 ^ (prefixWord ++ tailWord_3889390).sum := by decide
  have hdescent : baseEnd_3889390 < baseStart_3889390 := by decide
  rcases family_descends (prefixWord ++ tailWord_3889390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3889417 : List Nat := [1, 2, 1, 1, 3, 5, 1, 3, 1, 3, 2]
def baseStart_3889417 : Nat := 118140960795 + 3889417 * 2 ^ 59
def prefixEnd_3889417 : Nat := 4983230072969 + 3 ^ 40 * 3889417 * 2
def baseEnd_3889417 : Nat := 1997140386768314371800403

theorem tailTrace_3889417 : CollatzResearch.WordTrace tailWord_3889417 prefixEnd_3889417 1997140386768314371800403 := by
  unfold tailWord_3889417
  simp only [CollatzResearch.WordTrace]
  refine ⟨141858692150313943384306505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94572461433542628922871003 141858692150313943384306505)
  ·
    refine ⟨106394019112735457538229879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141858692150313943384306505 106394019112735457538229879)
    ·
      refine ⟨159591028669103186307344819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106394019112735457538229879 159591028669103186307344819)
      ·
        refine ⟨239386543003654779461017229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159591028669103186307344819 239386543003654779461017229)
        ·
          refine ⟨89769953626370542297881461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 239386543003654779461017229 89769953626370542297881461)
          ·
            refine ⟨8415933152472238340426387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 89769953626370542297881461 8415933152472238340426387)
            ·
              refine ⟨12623899728708357510639581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8415933152472238340426387 12623899728708357510639581)
              ·
                refine ⟨4733962398265634066489843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12623899728708357510639581 4733962398265634066489843)
                ·
                  refine ⟨7100943597398451099734765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4733962398265634066489843 7100943597398451099734765)
                  ·
                    refine ⟨2662853849024419162400537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7100943597398451099734765 2662853849024419162400537)
                    ·
                      refine ⟨1997140386768314371800403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2662853849024419162400537 1997140386768314371800403)
                      ·
                        rfl

theorem cell23_3889417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 1, 3, 1, 3, 2].length) (baseStart_3889417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3889417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3889417 prefixEnd_3889417 := by exact prefixLift 3889417
  have htrace : WordTrace (prefixWord ++ tailWord_3889417) baseStart_3889417 baseEnd_3889417 := by
    simpa [prefixWord, tailWord_3889417, baseEnd_3889417] using wordTrace_append hprefix tailTrace_3889417
  have hstable : (prefixWord ++ tailWord_3889417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3889417).length < 2 ^ (prefixWord ++ tailWord_3889417).sum := by decide
  have hdescent : baseEnd_3889417 < baseStart_3889417 := by decide
  rcases family_descends (prefixWord ++ tailWord_3889417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3889443 : List Nat := [1, 1, 1, 4, 2, 2, 1, 3, 2, 2, 4]
def baseStart_3889443 : Nat := 118140960795 + 3889443 * 2 ^ 59
def prefixEnd_3889443 : Nat := 4983230072969 + 3 ^ 40 * 3889443 * 2
def baseEnd_3889443 : Nat := 1997153737265331270075283

theorem tailTrace_3889443 : CollatzResearch.WordTrace tailWord_3889443 prefixEnd_3889443 1997153737265331270075283 := by
  unfold tailWord_3889443
  simp only [CollatzResearch.WordTrace]
  refine ⟨141859640448219749824752983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94573093632146499883168655 141859640448219749824752983)
  ·
    refine ⟨212789460672329624737129475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141859640448219749824752983 212789460672329624737129475)
    ·
      refine ⟨319184191008494437105694213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212789460672329624737129475 319184191008494437105694213)
      ·
        refine ⟨59847035814092706957317665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 319184191008494437105694213 59847035814092706957317665)
        ·
          refine ⟨44885276860569530217988249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59847035814092706957317665 44885276860569530217988249)
          ·
            refine ⟨33663957645427147663491187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44885276860569530217988249 33663957645427147663491187)
            ·
              refine ⟨50495936468140721495236781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33663957645427147663491187 50495936468140721495236781)
              ·
                refine ⟨18935976175552770560713793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50495936468140721495236781 18935976175552770560713793)
                ·
                  refine ⟨14201982131664577920535345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18935976175552770560713793 14201982131664577920535345)
                  ·
                    refine ⟨10651486598748433440401509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14201982131664577920535345 10651486598748433440401509)
                    ·
                      refine ⟨1997153737265331270075283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10651486598748433440401509 1997153737265331270075283)
                      ·
                        rfl

theorem cell23_3889443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 3, 2, 2, 4].length) (baseStart_3889443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3889443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3889443 prefixEnd_3889443 := by exact prefixLift 3889443
  have htrace : WordTrace (prefixWord ++ tailWord_3889443) baseStart_3889443 baseEnd_3889443 := by
    simpa [prefixWord, tailWord_3889443, baseEnd_3889443] using wordTrace_append hprefix tailTrace_3889443
  have hstable : (prefixWord ++ tailWord_3889443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3889443).length < 2 ^ (prefixWord ++ tailWord_3889443).sum := by decide
  have hdescent : baseEnd_3889443 < baseStart_3889443 := by decide
  rcases family_descends (prefixWord ++ tailWord_3889443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3889463 : List Nat := [1, 1, 3, 1, 2, 1, 1, 4, 1, 5, 3]
def baseStart_3889463 : Nat := 118140960795 + 3889463 * 2 ^ 59
def prefixEnd_3889463 : Nat := 4983230072969 + 3 ^ 40 * 3889463 * 2
def baseEnd_3889463 : Nat := 1997164006878421191825191

theorem tailTrace_3889463 : CollatzResearch.WordTrace tailWord_3889463 prefixEnd_3889463 1997164006878421191825191 := by
  unfold tailWord_3889463
  simp only [CollatzResearch.WordTrace]
  refine ⟨141860369908147293240481043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94573579938764862160320695 141860369908147293240481043)
  ·
    refine ⟨212790554862220939860721565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141860369908147293240481043 212790554862220939860721565)
    ·
      refine ⟨79796458073332852447770587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 212790554862220939860721565 79796458073332852447770587)
      ·
        refine ⟨119694687109999278671655881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79796458073332852447770587 119694687109999278671655881)
        ·
          refine ⟨89771015332499459003741911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119694687109999278671655881 89771015332499459003741911)
          ·
            refine ⟨134656522998749188505612867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89771015332499459003741911 134656522998749188505612867)
            ·
              refine ⟨201984784498123782758419301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 134656522998749188505612867 201984784498123782758419301)
              ·
                refine ⟨37872147093398209267203619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 201984784498123782758419301 37872147093398209267203619)
                ·
                  refine ⟨56808220640097313900805429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37872147093398209267203619 56808220640097313900805429)
                  ·
                    refine ⟨5325770685009123178200509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 56808220640097313900805429 5325770685009123178200509)
                    ·
                      refine ⟨1997164006878421191825191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5325770685009123178200509 1997164006878421191825191)
                      ·
                        rfl

theorem cell23_3889463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 4, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 4, 1, 5, 3].length) (baseStart_3889463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3889463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3889463 prefixEnd_3889463 := by exact prefixLift 3889463
  have htrace : WordTrace (prefixWord ++ tailWord_3889463) baseStart_3889463 baseEnd_3889463 := by
    simpa [prefixWord, tailWord_3889463, baseEnd_3889463] using wordTrace_append hprefix tailTrace_3889463
  have hstable : (prefixWord ++ tailWord_3889463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3889463).length < 2 ^ (prefixWord ++ tailWord_3889463).sum := by decide
  have hdescent : baseEnd_3889463 < baseStart_3889463 := by decide
  rcases family_descends (prefixWord ++ tailWord_3889463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3889502 : List Nat := [4, 4, 2, 1, 1, 2, 1, 2, 1, 3, 2]
def baseStart_3889502 : Nat := 118140960795 + 3889502 * 2 ^ 59
def prefixEnd_3889502 : Nat := 4983230072969 + 3 ^ 40 * 3889502 * 2
def baseEnd_3889502 : Nat := 1997184032623946539237513

theorem tailTrace_3889502 : CollatzResearch.WordTrace tailWord_3889502 prefixEnd_3889502 1997184032623946539237513 := by
  unfold tailWord_3889502
  simp only [CollatzResearch.WordTrace]
  refine ⟨17732724044375750362643845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 94574528236670668600767173 17732724044375750362643845)
  ·
    refine ⟨3324885758320453192995721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17732724044375750362643845 3324885758320453192995721)
    ·
      refine ⟨2493664318740339894746791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3324885758320453192995721 2493664318740339894746791)
      ·
        refine ⟨3740496478110509842120187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2493664318740339894746791 3740496478110509842120187)
        ·
          refine ⟨5610744717165764763180281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3740496478110509842120187 5610744717165764763180281)
          ·
            refine ⟨4208058537874323572385211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5610744717165764763180281 4208058537874323572385211)
            ·
              refine ⟨6312087806811485358577817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4208058537874323572385211 6312087806811485358577817)
              ·
                refine ⟨4734065855108614018933363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6312087806811485358577817 4734065855108614018933363)
                ·
                  refine ⟨7101098782662921028400045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4734065855108614018933363 7101098782662921028400045)
                  ·
                    refine ⟨2662912043498595385650017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7101098782662921028400045 2662912043498595385650017)
                    ·
                      refine ⟨1997184032623946539237513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2662912043498595385650017 1997184032623946539237513)
                      ·
                        rfl

theorem cell23_3889502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 2, 1, 2, 1, 3, 2].length) (baseStart_3889502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3889502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3889502 prefixEnd_3889502 := by exact prefixLift 3889502
  have htrace : WordTrace (prefixWord ++ tailWord_3889502) baseStart_3889502 baseEnd_3889502 := by
    simpa [prefixWord, tailWord_3889502, baseEnd_3889502] using wordTrace_append hprefix tailTrace_3889502
  have hstable : (prefixWord ++ tailWord_3889502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3889502).length < 2 ^ (prefixWord ++ tailWord_3889502).sum := by decide
  have hdescent : baseEnd_3889502 < baseStart_3889502 := by decide
  rcases family_descends (prefixWord ++ tailWord_3889502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3889503 : List Nat := [1, 1, 2, 3, 1, 2, 2, 1, 3, 3, 4]
def baseStart_3889503 : Nat := 118140960795 + 3889503 * 2 ^ 59
def prefixEnd_3889503 : Nat := 4983230072969 + 3 ^ 40 * 3889503 * 2
def baseEnd_3889503 : Nat := 1997184546104601035325007

theorem tailTrace_3889503 : CollatzResearch.WordTrace tailWord_3889503 prefixEnd_3889503 1997184546104601035325007 := by
  unfold tailWord_3889503
  simp only [CollatzResearch.WordTrace]
  refine ⟨141861828828002380071937163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94574552552001586714624775 141861828828002380071937163)
  ·
    refine ⟨212792743242003570107905745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141861828828002380071937163 212792743242003570107905745)
    ·
      refine ⟨159594557431502677580929309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 212792743242003570107905745 159594557431502677580929309)
      ·
        refine ⟨59847959036813504092848491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 159594557431502677580929309 59847959036813504092848491)
        ·
          refine ⟨89771938555220256139272737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59847959036813504092848491 89771938555220256139272737)
          ·
            refine ⟨67328953916415192104454553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89771938555220256139272737 67328953916415192104454553)
            ·
              refine ⟨50496715437311394078340915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67328953916415192104454553 50496715437311394078340915)
              ·
                refine ⟨75745073155967091117511373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50496715437311394078340915 75745073155967091117511373)
                ·
                  refine ⟨28404402433487659169066765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 75745073155967091117511373 28404402433487659169066765)
                  ·
                    refine ⟨10651650912557872188400037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28404402433487659169066765 10651650912557872188400037)
                    ·
                      refine ⟨1997184546104601035325007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10651650912557872188400037 1997184546104601035325007)
                      ·
                        rfl

theorem cell23_3889503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 1, 3, 3, 4].length) (baseStart_3889503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3889503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3889503 prefixEnd_3889503 := by exact prefixLift 3889503
  have htrace : WordTrace (prefixWord ++ tailWord_3889503) baseStart_3889503 baseEnd_3889503 := by
    simpa [prefixWord, tailWord_3889503, baseEnd_3889503] using wordTrace_append hprefix tailTrace_3889503
  have hstable : (prefixWord ++ tailWord_3889503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3889503).length < 2 ^ (prefixWord ++ tailWord_3889503).sum := by decide
  have hdescent : baseEnd_3889503 < baseStart_3889503 := by decide
  rcases family_descends (prefixWord ++ tailWord_3889503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3889520 : List Nat := [2, 1, 1, 1, 4, 3, 1, 3, 2, 1, 4]
def baseStart_3889520 : Nat := 118140960795 + 3889520 * 2 ^ 59
def prefixEnd_3889520 : Nat := 4983230072969 + 3 ^ 40 * 3889520 * 2
def baseEnd_3889520 : Nat := 1997193275275727468812429

theorem tailTrace_3889520 : CollatzResearch.WordTrace tailWord_3889520 prefixEnd_3889520 1997193275275727468812429 := by
  unfold tailWord_3889520
  simp only [CollatzResearch.WordTrace]
  refine ⟨70931224434470395987653007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94574965912627194650204009 70931224434470395987653007)
  ·
    refine ⟨106396836651705593981479511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70931224434470395987653007 106396836651705593981479511)
    ·
      refine ⟨159595254977558390972219267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106396836651705593981479511 159595254977558390972219267)
      ·
        refine ⟨239392882466337586458328901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159595254977558390972219267 239392882466337586458328901)
        ·
          refine ⟨44886165462438297460936669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 239392882466337586458328901 44886165462438297460936669)
          ·
            refine ⟨16832312048414361547851251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44886165462438297460936669 16832312048414361547851251)
            ·
              refine ⟨25248468072621542321776877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16832312048414361547851251 25248468072621542321776877)
              ·
                refine ⟨9468175527233078370666329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25248468072621542321776877 9468175527233078370666329)
                ·
                  refine ⟨7101131645424808777999747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9468175527233078370666329 7101131645424808777999747)
                  ·
                    refine ⟨10651697468137213166999621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7101131645424808777999747 10651697468137213166999621)
                    ·
                      refine ⟨1997193275275727468812429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10651697468137213166999621 1997193275275727468812429)
                      ·
                        rfl

theorem cell23_3889520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 1, 3, 2, 1, 4].length) (baseStart_3889520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3889520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3889520 prefixEnd_3889520 := by exact prefixLift 3889520
  have htrace : WordTrace (prefixWord ++ tailWord_3889520) baseStart_3889520 baseEnd_3889520 := by
    simpa [prefixWord, tailWord_3889520, baseEnd_3889520] using wordTrace_append hprefix tailTrace_3889520
  have hstable : (prefixWord ++ tailWord_3889520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3889520).length < 2 ^ (prefixWord ++ tailWord_3889520).sum := by decide
  have hdescent : baseEnd_3889520 < baseStart_3889520 := by decide
  rcases family_descends (prefixWord ++ tailWord_3889520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3889537 : List Nat := [1, 2, 4, 3, 1, 1, 2, 2, 2, 1, 4]
def baseStart_3889537 : Nat := 118140960795 + 3889537 * 2 ^ 59
def prefixEnd_3889537 : Nat := 4983230072969 + 3 ^ 40 * 3889537 * 2
def baseEnd_3889537 : Nat := 1997202004446853902299851

theorem tailTrace_3889537 : CollatzResearch.WordTrace tailWord_3889537 prefixEnd_3889537 1997202004446853902299851 := by
  unfold tailWord_3889537
  simp only [CollatzResearch.WordTrace]
  refine ⟨141863068909879203878674865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94575379273252802585783243 141863068909879203878674865)
  ·
    refine ⟨106397301682409402909006149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141863068909879203878674865 106397301682409402909006149)
    ·
      refine ⟨19949494065451763045438653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 106397301682409402909006149 19949494065451763045438653)
      ·
        refine ⟨7481060274544411142039495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19949494065451763045438653 7481060274544411142039495)
        ·
          refine ⟨11221590411816616713059243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7481060274544411142039495 11221590411816616713059243)
          ·
            refine ⟨16832385617724925069588865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11221590411816616713059243 16832385617724925069588865)
            ·
              refine ⟨12624289213293693802191649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16832385617724925069588865 12624289213293693802191649)
              ·
                refine ⟨9468216909970270351643737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12624289213293693802191649 9468216909970270351643737)
                ·
                  refine ⟨7101162682477702763732803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9468216909970270351643737 7101162682477702763732803)
                  ·
                    refine ⟨10651744023716554145599205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7101162682477702763732803 10651744023716554145599205)
                    ·
                      refine ⟨1997202004446853902299851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10651744023716554145599205 1997202004446853902299851)
                      ·
                        rfl

theorem cell23_3889537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 2, 2, 2, 1, 4].length) (baseStart_3889537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3889537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3889537 prefixEnd_3889537 := by exact prefixLift 3889537
  have htrace : WordTrace (prefixWord ++ tailWord_3889537) baseStart_3889537 baseEnd_3889537 := by
    simpa [prefixWord, tailWord_3889537, baseEnd_3889537] using wordTrace_append hprefix tailTrace_3889537
  have hstable : (prefixWord ++ tailWord_3889537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3889537).length < 2 ^ (prefixWord ++ tailWord_3889537).sum := by decide
  have hdescent : baseEnd_3889537 < baseStart_3889537 := by decide
  rcases family_descends (prefixWord ++ tailWord_3889537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3889538 : List Nat := [3, 4, 2, 1, 2, 2, 2, 2, 5]
def baseStart_3889538 : Nat := 118140960795 + 3889538 * 2 ^ 59
def prefixEnd_3889538 : Nat := 4983230072969 + 3 ^ 40 * 3889538 * 2
def baseEnd_3889538 : Nat := 221911390880834266487483

theorem tailTrace_3889538 : CollatzResearch.WordTrace tailWord_3889538 prefixEnd_3889538 221911390880834266487483 := by
  unfold tailWord_3889538
  simp only [CollatzResearch.WordTrace]
  refine ⟨35465776345718895262365317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94575403588583720699640845 35465776345718895262365317)
  ·
    refine ⟨6649833064822292861693497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35465776345718895262365317 6649833064822292861693497)
    ·
      refine ⟨4987374798616719646270123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6649833064822292861693497 4987374798616719646270123)
      ·
        refine ⟨7481062197925079469405185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4987374798616719646270123 7481062197925079469405185)
        ·
          refine ⟨5610796648443809602053889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7481062197925079469405185 5610796648443809602053889)
          ·
            refine ⟨4208097486332857201540417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5610796648443809602053889 4208097486332857201540417)
            ·
              refine ⟨3156073114749642901155313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4208097486332857201540417 3156073114749642901155313)
              ·
                refine ⟨2367054836062232175866485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3156073114749642901155313 2367054836062232175866485)
                ·
                  refine ⟨221911390880834266487483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2367054836062232175866485 221911390880834266487483)
                  ·
                    rfl

theorem cell23_3889538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 2, 2, 2, 5].length) (baseStart_3889538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3889538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3889538 prefixEnd_3889538 := by exact prefixLift 3889538
  have htrace : WordTrace (prefixWord ++ tailWord_3889538) baseStart_3889538 baseEnd_3889538 := by
    simpa [prefixWord, tailWord_3889538, baseEnd_3889538] using wordTrace_append hprefix tailTrace_3889538
  have hstable : (prefixWord ++ tailWord_3889538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3889538).length < 2 ^ (prefixWord ++ tailWord_3889538).sum := by decide
  have hdescent : baseEnd_3889538 < baseStart_3889538 := by decide
  rcases family_descends (prefixWord ++ tailWord_3889538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3889583 : List Nat := [1, 1, 2, 1, 2, 2, 1, 1, 1, 6, 5]
def baseStart_3889583 : Nat := 118140960795 + 3889583 * 2 ^ 59
def prefixEnd_3889583 : Nat := 4983230072969 + 3 ^ 40 * 3889583 * 2
def baseEnd_3889583 : Nat := 1997225624556960722324639

theorem tailTrace_3889583 : CollatzResearch.WordTrace tailWord_3889583 prefixEnd_3889583 1997225624556960722324639 := by
  unfold tailWord_3889583
  simp only [CollatzResearch.WordTrace]
  refine ⟨141864746667712553734849403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94576497778475035823232935 141864746667712553734849403)
  ·
    refine ⟨212797120001568830602274105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141864746667712553734849403 212797120001568830602274105)
    ·
      refine ⟨159597840001176622951705579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 212797120001568830602274105 159597840001176622951705579)
      ·
        refine ⟨239396760001764934427558369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159597840001176622951705579 239396760001764934427558369)
        ·
          refine ⟨179547570001323700820668777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 239396760001764934427558369 179547570001323700820668777)
          ·
            refine ⟨134660677500992775615501583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 179547570001323700820668777 134660677500992775615501583)
            ·
              refine ⟨201991016251489163423252375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 134660677500992775615501583 201991016251489163423252375)
              ·
                refine ⟨302986524377233745134878563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 201991016251489163423252375 302986524377233745134878563)
                ·
                  refine ⟨454479786565850617702317845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 302986524377233745134878563 454479786565850617702317845)
                  ·
                    refine ⟨21303739995274247704796149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 454479786565850617702317845 21303739995274247704796149)
                    ·
                      refine ⟨1997225624556960722324639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21303739995274247704796149 1997225624556960722324639)
                      ·
                        rfl

theorem cell23_3889583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 1, 1, 6, 5].length) (baseStart_3889583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3889583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3889583 prefixEnd_3889583 := by exact prefixLift 3889583
  have htrace : WordTrace (prefixWord ++ tailWord_3889583) baseStart_3889583 baseEnd_3889583 := by
    simpa [prefixWord, tailWord_3889583, baseEnd_3889583] using wordTrace_append hprefix tailTrace_3889583
  have hstable : (prefixWord ++ tailWord_3889583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3889583).length < 2 ^ (prefixWord ++ tailWord_3889583).sum := by decide
  have hdescent : baseEnd_3889583 < baseStart_3889583 := by decide
  rcases family_descends (prefixWord ++ tailWord_3889583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3889654 : List Nat := [5, 1, 1, 1, 2, 1, 2, 4, 2, 4]
def baseStart_3889654 : Nat := 118140960795 + 3889654 * 2 ^ 59
def prefixEnd_3889654 : Nat := 4983230072969 + 3 ^ 40 * 3889654 * 2
def baseEnd_3889654 : Nat := 665754027227809981512271

theorem tailTrace_3889654 : CollatzResearch.WordTrace tailWord_3889654 prefixEnd_3889654 665754027227809981512271 := by
  unfold tailWord_3889654
  simp only [CollatzResearch.WordTrace]
  refine ⟨8866708515653458303792751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 94578224166970221907122677 8866708515653458303792751)
  ·
    refine ⟨13300062773480187455689127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8866708515653458303792751 13300062773480187455689127)
    ·
      refine ⟨19950094160220281183533691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13300062773480187455689127 19950094160220281183533691)
      ·
        refine ⟨29925141240330421775300537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19950094160220281183533691 29925141240330421775300537)
        ·
          refine ⟨22443855930247816331475403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29925141240330421775300537 22443855930247816331475403)
          ·
            refine ⟨33665783895371724497213105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22443855930247816331475403 33665783895371724497213105)
            ·
              refine ⟨25249337921528793372909829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33665783895371724497213105 25249337921528793372909829)
              ·
                refine ⟨4734250860286648757420593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25249337921528793372909829 4734250860286648757420593)
                ·
                  refine ⟨3550688145214986568065445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4734250860286648757420593 3550688145214986568065445)
                  ·
                    refine ⟨665754027227809981512271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3550688145214986568065445 665754027227809981512271)
                    ·
                      rfl

theorem cell23_3889654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 2, 4, 2, 4].length) (baseStart_3889654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3889654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3889654 prefixEnd_3889654 := by exact prefixLift 3889654
  have htrace : WordTrace (prefixWord ++ tailWord_3889654) baseStart_3889654 baseEnd_3889654 := by
    simpa [prefixWord, tailWord_3889654, baseEnd_3889654] using wordTrace_append hprefix tailTrace_3889654
  have hstable : (prefixWord ++ tailWord_3889654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3889654).length < 2 ^ (prefixWord ++ tailWord_3889654).sum := by decide
  have hdescent : baseEnd_3889654 < baseStart_3889654 := by decide
  rcases family_descends (prefixWord ++ tailWord_3889654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3889690 : List Nat := [3, 1, 1, 3, 1, 1, 2, 1, 1, 4, 5]
def baseStart_3889690 : Nat := 118140960795 + 3889690 * 2 ^ 59
def prefixEnd_3889690 : Nat := 4983230072969 + 3 ^ 40 * 3889690 * 2
def baseEnd_3889690 : Nat := 1997280566986991803686647

theorem tailTrace_3889690 : CollatzResearch.WordTrace tailWord_3889690 prefixEnd_3889690 1997280566986991803686647 := by
  unfold tailWord_3889690
  simp only [CollatzResearch.WordTrace]
  refine ⟨35467162319581227752248631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94579099518883274005996349 35467162319581227752248631)
  ·
    refine ⟨53200743479371841628372947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35467162319581227752248631 53200743479371841628372947)
    ·
      refine ⟨79801115219057762442559421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53200743479371841628372947 79801115219057762442559421)
      ·
        refine ⟨29925418207146660915959783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79801115219057762442559421 29925418207146660915959783)
        ·
          refine ⟨44888127310719991373939675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29925418207146660915959783 44888127310719991373939675)
          ·
            refine ⟨67332190966079987060909513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44888127310719991373939675 67332190966079987060909513)
            ·
              refine ⟨50499143224559990295682135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67332190966079987060909513 50499143224559990295682135)
              ·
                refine ⟨75748714836839985443523203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50499143224559990295682135 75748714836839985443523203)
                ·
                  refine ⟨113623072255259978165284805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 75748714836839985443523203 113623072255259978165284805)
                  ·
                    refine ⟨21304326047861245905990901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 113623072255259978165284805 21304326047861245905990901)
                    ·
                      refine ⟨1997280566986991803686647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21304326047861245905990901 1997280566986991803686647)
                      ·
                        rfl

theorem cell23_3889690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 1, 1, 4, 5].length) (baseStart_3889690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3889690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3889690 prefixEnd_3889690 := by exact prefixLift 3889690
  have htrace : WordTrace (prefixWord ++ tailWord_3889690) baseStart_3889690 baseEnd_3889690 := by
    simpa [prefixWord, tailWord_3889690, baseEnd_3889690] using wordTrace_append hprefix tailTrace_3889690
  have hstable : (prefixWord ++ tailWord_3889690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3889690).length < 2 ^ (prefixWord ++ tailWord_3889690).sum := by decide
  have hdescent : baseEnd_3889690 < baseStart_3889690 := by decide
  rcases family_descends (prefixWord ++ tailWord_3889690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3889762 : List Nat := [3, 3, 2, 3, 2, 1, 1, 2, 2, 1, 3]
def baseStart_3889762 : Nat := 118140960795 + 3889762 * 2 ^ 59
def prefixEnd_3889762 : Nat := 4983230072969 + 3 ^ 40 * 3889762 * 2
def baseEnd_3889762 : Nat := 1997317537594115521986317

theorem tailTrace_3889762 : CollatzResearch.WordTrace tailWord_3889762 prefixEnd_3889762 1997317537594115521986317 := by
  unfold tailWord_3889762
  simp only [CollatzResearch.WordTrace]
  refine ⟨35467818833516016826403885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94580850222709378203743693 35467818833516016826403885)
  ·
    refine ⟨13300432062568506309901457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35467818833516016826403885 13300432062568506309901457)
    ·
      refine ⟨9975324046926379732426093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13300432062568506309901457 9975324046926379732426093)
      ·
        refine ⟨3740746517597392399659785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9975324046926379732426093 3740746517597392399659785)
        ·
          refine ⟨2805559888198044299744839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3740746517597392399659785 2805559888198044299744839)
          ·
            refine ⟨4208339832297066449617259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2805559888198044299744839 4208339832297066449617259)
            ·
              refine ⟨6312509748445599674425889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4208339832297066449617259 6312509748445599674425889)
              ·
                refine ⟨4734382311334199755819417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6312509748445599674425889 4734382311334199755819417)
                ·
                  refine ⟨3550786733500649816864563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4734382311334199755819417 3550786733500649816864563)
                  ·
                    refine ⟨5326180100250974725296845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3550786733500649816864563 5326180100250974725296845)
                    ·
                      refine ⟨1997317537594115521986317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5326180100250974725296845 1997317537594115521986317)
                      ·
                        rfl

theorem cell23_3889762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 2, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 2, 1, 1, 2, 2, 1, 3].length) (baseStart_3889762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3889762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3889762 prefixEnd_3889762 := by exact prefixLift 3889762
  have htrace : WordTrace (prefixWord ++ tailWord_3889762) baseStart_3889762 baseEnd_3889762 := by
    simpa [prefixWord, tailWord_3889762, baseEnd_3889762] using wordTrace_append hprefix tailTrace_3889762
  have hstable : (prefixWord ++ tailWord_3889762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3889762).length < 2 ^ (prefixWord ++ tailWord_3889762).sum := by decide
  have hdescent : baseEnd_3889762 < baseStart_3889762 := by decide
  rcases family_descends (prefixWord ++ tailWord_3889762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3889768 : List Nat := [2, 1, 4, 3, 2, 1, 1, 1, 4, 2, 2]
def baseStart_3889768 : Nat := 118140960795 + 3889768 * 2 ^ 59
def prefixEnd_3889768 : Nat := 4983230072969 + 3 ^ 40 * 3889768 * 2
def baseEnd_3889768 : Nat := 1997320618478042498511289

theorem tailTrace_3889768 : CollatzResearch.WordTrace tailWord_3889768 prefixEnd_3889768 1997320618478042498511289 := by
  unfold tailWord_3889768
  simp only [CollatzResearch.WordTrace]
  refine ⟨70935747086021165165166979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94580996114694886886889305 70935747086021165165166979)
  ·
    refine ⟨106403620629031747747750469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70935747086021165165166979 106403620629031747747750469)
    ·
      refine ⟨19950678867943452702703213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 106403620629031747747750469 19950678867943452702703213)
      ·
        refine ⟨7481504575478794763513705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19950678867943452702703213 7481504575478794763513705)
        ·
          refine ⟨5611128431609096072635279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7481504575478794763513705 5611128431609096072635279)
          ·
            refine ⟨8416692647413644108952919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5611128431609096072635279 8416692647413644108952919)
            ·
              refine ⟨12625038971120466163429379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8416692647413644108952919 12625038971120466163429379)
              ·
                refine ⟨18937558456680699245144069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12625038971120466163429379 18937558456680699245144069)
                ·
                  refine ⟨3550792210627631108464513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18937558456680699245144069 3550792210627631108464513)
                  ·
                    refine ⟨2663094157970723331348385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3550792210627631108464513 2663094157970723331348385)
                    ·
                      refine ⟨1997320618478042498511289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2663094157970723331348385 1997320618478042498511289)
                      ·
                        rfl

theorem cell23_3889768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 1, 1, 4, 2, 2].length) (baseStart_3889768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3889768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3889768 prefixEnd_3889768 := by exact prefixLift 3889768
  have htrace : WordTrace (prefixWord ++ tailWord_3889768) baseStart_3889768 baseEnd_3889768 := by
    simpa [prefixWord, tailWord_3889768, baseEnd_3889768] using wordTrace_append hprefix tailTrace_3889768
  have hstable : (prefixWord ++ tailWord_3889768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3889768).length < 2 ^ (prefixWord ++ tailWord_3889768).sum := by decide
  have hdescent : baseEnd_3889768 < baseStart_3889768 := by decide
  rcases family_descends (prefixWord ++ tailWord_3889768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3889774 : List Nat := [4, 1, 2, 2, 2, 2, 2, 1, 7]
def baseStart_3889774 : Nat := 118140960795 + 3889774 * 2 ^ 59
def prefixEnd_3889774 : Nat := 4983230072969 + 3 ^ 40 * 3889774 * 2
def baseEnd_3889774 : Nat := 221924855484663275004029

theorem tailTrace_3889774 : CollatzResearch.WordTrace tailWord_3889774 prefixEnd_3889774 221924855484663275004029 := by
  unfold tailWord_3889774
  simp only [CollatzResearch.WordTrace]
  refine ⟨17733964126252574169381547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 94581142006680395570034917 17733964126252574169381547)
  ·
    refine ⟨26600946189378861254072321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17733964126252574169381547 26600946189378861254072321)
    ·
      refine ⟨19950709642034145940554241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26600946189378861254072321 19950709642034145940554241)
      ·
        refine ⟨14963032231525609455415681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19950709642034145940554241 14963032231525609455415681)
        ·
          refine ⟨11222274173644207091561761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14963032231525609455415681 11222274173644207091561761)
          ·
            refine ⟨8416705630233155318671321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11222274173644207091561761 8416705630233155318671321)
            ·
              refine ⟨6312529222674866489003491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8416705630233155318671321 6312529222674866489003491)
              ·
                refine ⟨9468793834012299733505237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6312529222674866489003491 9468793834012299733505237)
                ·
                  refine ⟨221924855484663275004029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9468793834012299733505237 221924855484663275004029)
                  ·
                    rfl

theorem cell23_3889774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 2, 1, 7].length) (baseStart_3889774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3889774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3889774 prefixEnd_3889774 := by exact prefixLift 3889774
  have htrace : WordTrace (prefixWord ++ tailWord_3889774) baseStart_3889774 baseEnd_3889774 := by
    simpa [prefixWord, tailWord_3889774, baseEnd_3889774] using wordTrace_append hprefix tailTrace_3889774
  have hstable : (prefixWord ++ tailWord_3889774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3889774).length < 2 ^ (prefixWord ++ tailWord_3889774).sum := by decide
  have hdescent : baseEnd_3889774 < baseStart_3889774 := by decide
  rcases family_descends (prefixWord ++ tailWord_3889774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3889827 : List Nat := [1, 1, 1, 4, 1, 1, 2, 2, 3, 4, 3]
def baseStart_3889827 : Nat := 118140960795 + 3889827 * 2 ^ 59
def prefixEnd_3889827 : Nat := 4983230072969 + 3 ^ 40 * 3889827 * 2
def baseEnd_3889827 : Nat := 1997350913836657767673517

theorem tailTrace_3889827 : CollatzResearch.WordTrace tailWord_3889827 prefixEnd_3889827 1997350913836657767673517 := by
  unfold tailWord_3889827
  simp only [CollatzResearch.WordTrace]
  refine ⟨141873646078828583406731735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94582430719219055604487823 141873646078828583406731735)
  ·
    refine ⟨212810469118242875110097603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141873646078828583406731735 212810469118242875110097603)
    ·
      refine ⟨319215703677364312665146405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212810469118242875110097603 319215703677364312665146405)
      ·
        refine ⟨59852944439505808624714951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 319215703677364312665146405 59852944439505808624714951)
        ·
          refine ⟨89779416659258712937072427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59852944439505808624714951 89779416659258712937072427)
          ·
            refine ⟨134669124988888069405608641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89779416659258712937072427 134669124988888069405608641)
            ·
              refine ⟨101001843741666052054206481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 134669124988888069405608641 101001843741666052054206481)
              ·
                refine ⟨75751382806249539040654861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 101001843741666052054206481 75751382806249539040654861)
                ·
                  refine ⟨28406768552343577140245573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 75751382806249539040654861 28406768552343577140245573)
                  ·
                    refine ⟨5326269103564420713796045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28406768552343577140245573 5326269103564420713796045)
                    ·
                      refine ⟨1997350913836657767673517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5326269103564420713796045 1997350913836657767673517)
                      ·
                        rfl

theorem cell23_3889827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 2, 3, 4, 3].length) (baseStart_3889827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3889827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3889827 prefixEnd_3889827 := by exact prefixLift 3889827
  have htrace : WordTrace (prefixWord ++ tailWord_3889827) baseStart_3889827 baseEnd_3889827 := by
    simpa [prefixWord, tailWord_3889827, baseEnd_3889827] using wordTrace_append hprefix tailTrace_3889827
  have hstable : (prefixWord ++ tailWord_3889827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3889827).length < 2 ^ (prefixWord ++ tailWord_3889827).sum := by decide
  have hdescent : baseEnd_3889827 < baseStart_3889827 := by decide
  rcases family_descends (prefixWord ++ tailWord_3889827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3889831 : List Nat := [1, 1, 6, 3, 1, 1, 1, 1, 1, 2, 5]
def baseStart_3889831 : Nat := 118140960795 + 3889831 * 2 ^ 59
def prefixEnd_3889831 : Nat := 4983230072969 + 3 ^ 40 * 3889831 * 2
def baseEnd_3889831 : Nat := 1997352967759275752023499

theorem tailTrace_3889831 : CollatzResearch.WordTrace tailWord_3889831 prefixEnd_3889831 1997352967759275752023499 := by
  unfold tailWord_3889831
  simp only [CollatzResearch.WordTrace]
  refine ⟨141873791970814092089877347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94582527980542728059918231 141873791970814092089877347)
  ·
    refine ⟨212810687956221138134816021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141873791970814092089877347 212810687956221138134816021)
    ·
      refine ⟨9975500997947865850069501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 212810687956221138134816021 9975500997947865850069501)
      ·
        refine ⟨3740812874230449693776063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9975500997947865850069501 3740812874230449693776063)
        ·
          refine ⟨5611219311345674540664095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3740812874230449693776063 5611219311345674540664095)
          ·
            refine ⟨8416828967018511810996143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5611219311345674540664095 8416828967018511810996143)
            ·
              refine ⟨12625243450527767716494215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8416828967018511810996143 12625243450527767716494215)
              ·
                refine ⟨18937865175791651574741323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12625243450527767716494215 18937865175791651574741323)
                ·
                  refine ⟨28406797763687477362111985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18937865175791651574741323 28406797763687477362111985)
                  ·
                    refine ⟨21305098322765608021583989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28406797763687477362111985 21305098322765608021583989)
                    ·
                      refine ⟨1997352967759275752023499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21305098322765608021583989 1997352967759275752023499)
                      ·
                        rfl

theorem cell23_3889831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 1, 1, 1, 2, 5].length) (baseStart_3889831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3889831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3889831 prefixEnd_3889831 := by exact prefixLift 3889831
  have htrace : WordTrace (prefixWord ++ tailWord_3889831) baseStart_3889831 baseEnd_3889831 := by
    simpa [prefixWord, tailWord_3889831, baseEnd_3889831] using wordTrace_append hprefix tailTrace_3889831
  have hstable : (prefixWord ++ tailWord_3889831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3889831).length < 2 ^ (prefixWord ++ tailWord_3889831).sum := by decide
  have hdescent : baseEnd_3889831 < baseStart_3889831 := by decide
  rcases family_descends (prefixWord ++ tailWord_3889831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3889901 : List Nat := [1, 5, 1, 2, 1, 1, 2, 2, 1, 5, 2]
def baseStart_3889901 : Nat := 118140960795 + 3889901 * 2 ^ 59
def prefixEnd_3889901 : Nat := 4983230072969 + 3 ^ 40 * 3889901 * 2
def baseEnd_3889901 : Nat := 1997388911405090478148177

theorem tailTrace_3889901 : CollatzResearch.WordTrace tailWord_3889901 prefixEnd_3889901 1997388911405090478148177 := by
  unfold tailWord_3889901
  simp only [CollatzResearch.WordTrace]
  refine ⟨141876345080560494044925557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94584230053706996029950371 141876345080560494044925557)
  ·
    refine ⟨13300907351302546316711771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 141876345080560494044925557 13300907351302546316711771)
    ·
      refine ⟨19951361026953819475067657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13300907351302546316711771 19951361026953819475067657)
      ·
        refine ⟨14963520770215364606300743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19951361026953819475067657 14963520770215364606300743)
        ·
          refine ⟨22445281155323046909451115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14963520770215364606300743 22445281155323046909451115)
          ·
            refine ⟨33667921732984570364176673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22445281155323046909451115 33667921732984570364176673)
            ·
              refine ⟨25250941299738427773132505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33667921732984570364176673 25250941299738427773132505)
              ·
                refine ⟨18938205974803820829849379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25250941299738427773132505 18938205974803820829849379)
                ·
                  refine ⟨28407308962205731244774069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18938205974803820829849379 28407308962205731244774069)
                  ·
                    refine ⟨2663185215206787304197569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 28407308962205731244774069 2663185215206787304197569)
                    ·
                      refine ⟨1997388911405090478148177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2663185215206787304197569 1997388911405090478148177)
                      ·
                        rfl

theorem cell23_3889901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 2, 2, 1, 5, 2].length) (baseStart_3889901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3889901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3889901 prefixEnd_3889901 := by exact prefixLift 3889901
  have htrace : WordTrace (prefixWord ++ tailWord_3889901) baseStart_3889901 baseEnd_3889901 := by
    simpa [prefixWord, tailWord_3889901, baseEnd_3889901] using wordTrace_append hprefix tailTrace_3889901
  have hstable : (prefixWord ++ tailWord_3889901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3889901).length < 2 ^ (prefixWord ++ tailWord_3889901).sum := by decide
  have hdescent : baseEnd_3889901 < baseStart_3889901 := by decide
  rcases family_descends (prefixWord ++ tailWord_3889901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3889914 : List Nat := [3, 1, 1, 1, 1, 3, 4, 1, 3, 1, 4]
def baseStart_3889914 : Nat := 118140960795 + 3889914 * 2 ^ 59
def prefixEnd_3889914 : Nat := 4983230072969 + 3 ^ 40 * 3889914 * 2
def baseEnd_3889914 : Nat := 1997395586653598927285617

theorem tailTrace_3889914 : CollatzResearch.WordTrace tailWord_3889914 prefixEnd_3889914 1997395586653598927285617 := by
  unfold tailWord_3889914
  simp only [CollatzResearch.WordTrace]
  refine ⟨35469204807378349316287199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94584546153008931510099197 35469204807378349316287199)
  ·
    refine ⟨53203807211067523974430799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35469204807378349316287199 53203807211067523974430799)
    ·
      refine ⟨79805710816601285961646199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53203807211067523974430799 79805710816601285961646199)
      ·
        refine ⟨119708566224901928942469299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79805710816601285961646199 119708566224901928942469299)
        ·
          refine ⟨179562849337352893413703949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119708566224901928942469299 179562849337352893413703949)
          ·
            refine ⟨67336068501507335030138981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 179562849337352893413703949 67336068501507335030138981)
            ·
              refine ⟨12625512844032625318151059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 67336068501507335030138981 12625512844032625318151059)
              ·
                refine ⟨18938269266048937977226589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12625512844032625318151059 18938269266048937977226589)
                ·
                  refine ⟨7101850974768351741459971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18938269266048937977226589 7101850974768351741459971)
                  ·
                    refine ⟨10652776462152527612189957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7101850974768351741459971 10652776462152527612189957)
                    ·
                      refine ⟨1997395586653598927285617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10652776462152527612189957 1997395586653598927285617)
                      ·
                        rfl

theorem cell23_3889914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 4, 1, 3, 1, 4].length) (baseStart_3889914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3889914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3889914 prefixEnd_3889914 := by exact prefixLift 3889914
  have htrace : WordTrace (prefixWord ++ tailWord_3889914) baseStart_3889914 baseEnd_3889914 := by
    simpa [prefixWord, tailWord_3889914, baseEnd_3889914] using wordTrace_append hprefix tailTrace_3889914
  have hstable : (prefixWord ++ tailWord_3889914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3889914).length < 2 ^ (prefixWord ++ tailWord_3889914).sum := by decide
  have hdescent : baseEnd_3889914 < baseStart_3889914 := by decide
  rcases family_descends (prefixWord ++ tailWord_3889914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3889918 : List Nat := [4, 2, 2, 1, 2, 2, 1, 1, 1, 5, 2]
def baseStart_3889918 : Nat := 118140960795 + 3889918 * 2 ^ 59
def prefixEnd_3889918 : Nat := 4983230072969 + 3 ^ 40 * 3889918 * 2
def baseEnd_3889918 : Nat := 1997397640576216911635599

theorem tailTrace_3889918 : CollatzResearch.WordTrace tailWord_3889918 prefixEnd_3889918 1997397640576216911635599 := by
  unfold tailWord_3889918
  simp only [CollatzResearch.WordTrace]
  refine ⟨17734620640187363243536801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 94584643414332603965529605 17734620640187363243536801)
  ·
    refine ⟨13300965480140522432652601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17734620640187363243536801 13300965480140522432652601)
    ·
      refine ⟨9975724110105391824489451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13300965480140522432652601 9975724110105391824489451)
      ·
        refine ⟨14963586165158087736734177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9975724110105391824489451 14963586165158087736734177)
        ·
          refine ⟨11222689623868565802550633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14963586165158087736734177 11222689623868565802550633)
          ·
            refine ⟨8417017217901424351912975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11222689623868565802550633 8417017217901424351912975)
            ·
              refine ⟨12625525826852136527869463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8417017217901424351912975 12625525826852136527869463)
              ·
                refine ⟨18938288740278204791804195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12625525826852136527869463 18938288740278204791804195)
                ·
                  refine ⟨28407433110417307187706293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18938288740278204791804195 28407433110417307187706293)
                  ·
                    refine ⟨2663196854101622548847465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 28407433110417307187706293 2663196854101622548847465)
                    ·
                      refine ⟨1997397640576216911635599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2663196854101622548847465 1997397640576216911635599)
                      ·
                        rfl

theorem cell23_3889918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 1, 1, 1, 5, 2].length) (baseStart_3889918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3889918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3889918 prefixEnd_3889918 := by exact prefixLift 3889918
  have htrace : WordTrace (prefixWord ++ tailWord_3889918) baseStart_3889918 baseEnd_3889918 := by
    simpa [prefixWord, tailWord_3889918, baseEnd_3889918] using wordTrace_append hprefix tailTrace_3889918
  have hstable : (prefixWord ++ tailWord_3889918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3889918).length < 2 ^ (prefixWord ++ tailWord_3889918).sum := by decide
  have hdescent : baseEnd_3889918 < baseStart_3889918 := by decide
  rcases family_descends (prefixWord ++ tailWord_3889918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3889924 : List Nat := [2, 3, 2, 2, 1, 1, 1, 4, 1, 6]
def baseStart_3889924 : Nat := 118140960795 + 3889924 * 2 ^ 59
def prefixEnd_3889924 : Nat := 4983230072969 + 3 ^ 40 * 3889924 * 2
def baseEnd_3889924 : Nat := 665800240486714629386857

theorem tailTrace_3889924 : CollatzResearch.WordTrace tailWord_3889924 prefixEnd_3889924 665800240486714629386857 := by
  unfold tailWord_3889924
  simp only [CollatzResearch.WordTrace]
  refine ⟨70938591979738584486506413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94584789306318112648675217 70938591979738584486506413)
  ·
    refine ⟨26601971992401969182439905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70938591979738584486506413 26601971992401969182439905)
    ·
      refine ⟨19951478994301476886829929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26601971992401969182439905 19951478994301476886829929)
      ·
        refine ⟨14963609245726107665122447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19951478994301476886829929 14963609245726107665122447)
        ·
          refine ⟨22445413868589161497683671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14963609245726107665122447 22445413868589161497683671)
          ·
            refine ⟨33668120802883742246525507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22445413868589161497683671 33668120802883742246525507)
            ·
              refine ⟨50502181204325613369788261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33668120802883742246525507 50502181204325613369788261)
              ·
                refine ⟨9469158975811052506835299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50502181204325613369788261 9469158975811052506835299)
                ·
                  refine ⟨14203738463716578760252949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9469158975811052506835299 14203738463716578760252949)
                  ·
                    refine ⟨665800240486714629386857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14203738463716578760252949 665800240486714629386857)
                    ·
                      rfl

theorem cell23_3889924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 4, 1, 6].length) (baseStart_3889924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3889924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3889924 prefixEnd_3889924 := by exact prefixLift 3889924
  have htrace : WordTrace (prefixWord ++ tailWord_3889924) baseStart_3889924 baseEnd_3889924 := by
    simpa [prefixWord, tailWord_3889924, baseEnd_3889924] using wordTrace_append hprefix tailTrace_3889924
  have hstable : (prefixWord ++ tailWord_3889924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3889924).length < 2 ^ (prefixWord ++ tailWord_3889924).sum := by decide
  have hdescent : baseEnd_3889924 < baseStart_3889924 := by decide
  rcases family_descends (prefixWord ++ tailWord_3889924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3889928 : List Nat := [2, 1, 3, 2, 2, 4, 2, 1, 1, 5]
def baseStart_3889928 : Nat := 118140960795 + 3889928 * 2 ^ 59
def prefixEnd_3889928 : Nat := 4983230072969 + 3 ^ 40 * 3889928 * 2
def baseEnd_3889928 : Nat := 665800925127587290836851

theorem tailTrace_3889928 : CollatzResearch.WordTrace tailWord_3889928 prefixEnd_3889928 665800925127587290836851 := by
  unfold tailWord_3889928
  simp only [CollatzResearch.WordTrace]
  refine ⟨70938664925731338828079219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94584886567641785104105625 70938664925731338828079219)
  ·
    refine ⟨106407997388597008242118829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70938664925731338828079219 106407997388597008242118829)
    ·
      refine ⟨39902999020723878090794561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106407997388597008242118829 39902999020723878090794561)
      ·
        refine ⟨29927249265542908568095921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39902999020723878090794561 29927249265542908568095921)
        ·
          refine ⟨22445436949157181426071941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29927249265542908568095921 22445436949157181426071941)
          ·
            refine ⟨4208519427966971517388489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22445436949157181426071941 4208519427966971517388489)
            ·
              refine ⟨3156389570975228638041367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4208519427966971517388489 3156389570975228638041367)
              ·
                refine ⟨4734584356462842957062051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3156389570975228638041367 4734584356462842957062051)
                ·
                  refine ⟨7101876534694264435593077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4734584356462842957062051 7101876534694264435593077)
                  ·
                    refine ⟨665800925127587290836851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7101876534694264435593077 665800925127587290836851)
                    ·
                      rfl

theorem cell23_3889928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 4, 2, 1, 1, 5].length) (baseStart_3889928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3889928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3889928 prefixEnd_3889928 := by exact prefixLift 3889928
  have htrace : WordTrace (prefixWord ++ tailWord_3889928) baseStart_3889928 baseEnd_3889928 := by
    simpa [prefixWord, tailWord_3889928, baseEnd_3889928] using wordTrace_append hprefix tailTrace_3889928
  have hstable : (prefixWord ++ tailWord_3889928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3889928).length < 2 ^ (prefixWord ++ tailWord_3889928).sum := by decide
  have hdescent : baseEnd_3889928 < baseStart_3889928 := by decide
  rcases family_descends (prefixWord ++ tailWord_3889928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3889931 : List Nat := [1, 1, 1, 1, 5, 1, 1, 1, 7, 2, 2]
def baseStart_3889931 : Nat := 118140960795 + 3889931 * 2 ^ 59
def prefixEnd_3889931 : Nat := 4983230072969 + 3 ^ 40 * 3889931 * 2
def baseEnd_3889931 : Nat := 1997404315824725360773039

theorem tailTrace_3889931 : CollatzResearch.WordTrace tailWord_3889931 prefixEnd_3889931 1997404315824725360773039 := by
  unfold tailWord_3889931
  simp only [CollatzResearch.WordTrace]
  refine ⟨141877439270451809168517647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94584959513634539445678431 141877439270451809168517647)
  ·
    refine ⟨212816158905677713752776471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141877439270451809168517647 212816158905677713752776471)
    ·
      refine ⟨319224238358516570629164707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212816158905677713752776471 319224238358516570629164707)
      ·
        refine ⟨478836357537774855943747061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 319224238358516570629164707 478836357537774855943747061)
        ·
          refine ⟨44890908519166392744726287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 478836357537774855943747061 44890908519166392744726287)
          ·
            refine ⟨67336362778749589117089431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44890908519166392744726287 67336362778749589117089431)
            ·
              refine ⟨101004544168124383675634147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67336362778749589117089431 101004544168124383675634147)
              ·
                refine ⟨151506816252186575513451221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 101004544168124383675634147 151506816252186575513451221)
                ·
                  refine ⟨3550941005910622863596513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 151506816252186575513451221 3550941005910622863596513)
                  ·
                    refine ⟨2663205754432967147697385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3550941005910622863596513 2663205754432967147697385)
                    ·
                      refine ⟨1997404315824725360773039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2663205754432967147697385 1997404315824725360773039)
                      ·
                        rfl

theorem cell23_3889931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 1, 7, 2, 2].length) (baseStart_3889931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3889931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3889931 prefixEnd_3889931 := by exact prefixLift 3889931
  have htrace : WordTrace (prefixWord ++ tailWord_3889931) baseStart_3889931 baseEnd_3889931 := by
    simpa [prefixWord, tailWord_3889931, baseEnd_3889931] using wordTrace_append hprefix tailTrace_3889931
  have hstable : (prefixWord ++ tailWord_3889931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3889931).length < 2 ^ (prefixWord ++ tailWord_3889931).sum := by decide
  have hdescent : baseEnd_3889931 < baseStart_3889931 := by decide
  rcases family_descends (prefixWord ++ tailWord_3889931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3889934 : List Nat := [4, 1, 1, 2, 1, 1, 1, 5, 1, 1, 5]
def baseStart_3889934 : Nat := 118140960795 + 3889934 * 2 ^ 59
def prefixEnd_3889934 : Nat := 4983230072969 + 3 ^ 40 * 3889934 * 2
def baseEnd_3889934 : Nat := 1997405856266688849035525

theorem tailTrace_3889934 : CollatzResearch.WordTrace tailWord_3889934 prefixEnd_3889934 1997405856266688849035525 := by
  unfold tailWord_3889934
  simp only [CollatzResearch.WordTrace]
  refine ⟨17734693586180117585109607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 94585032459627293787251237 17734693586180117585109607)
  ·
    refine ⟨26602040379270176377664411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17734693586180117585109607 26602040379270176377664411)
    ·
      refine ⟨39903060568905264566496617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26602040379270176377664411 39903060568905264566496617)
      ·
        refine ⟨29927295426678948424872463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39903060568905264566496617 29927295426678948424872463)
        ·
          refine ⟨44890943140018422637308695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29927295426678948424872463 44890943140018422637308695)
          ·
            refine ⟨67336414710027633955963043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44890943140018422637308695 67336414710027633955963043)
            ·
              refine ⟨101004622065041450933944565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67336414710027633955963043 101004622065041450933944565)
              ·
                refine ⟨9469183318597636025057303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 101004622065041450933944565 9469183318597636025057303)
                ·
                  refine ⟨14203774977896454037585955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9469183318597636025057303 14203774977896454037585955)
                  ·
                    refine ⟨21305662466844681056378933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14203774977896454037585955 21305662466844681056378933)
                    ·
                      refine ⟨1997405856266688849035525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21305662466844681056378933 1997405856266688849035525)
                      ·
                        rfl

theorem cell23_3889934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 5, 1, 1, 5].length) (baseStart_3889934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3889934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3889934 prefixEnd_3889934 := by exact prefixLift 3889934
  have htrace : WordTrace (prefixWord ++ tailWord_3889934) baseStart_3889934 baseEnd_3889934 := by
    simpa [prefixWord, tailWord_3889934, baseEnd_3889934] using wordTrace_append hprefix tailTrace_3889934
  have hstable : (prefixWord ++ tailWord_3889934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3889934).length < 2 ^ (prefixWord ++ tailWord_3889934).sum := by decide
  have hdescent : baseEnd_3889934 < baseStart_3889934 := by decide
  rcases family_descends (prefixWord ++ tailWord_3889934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3889948 : List Nat := [2, 2, 3, 1, 1, 3, 1, 3, 3, 2, 2]
def baseStart_3889948 : Nat := 118140960795 + 3889948 * 2 ^ 59
def prefixEnd_3889948 : Nat := 4983230072969 + 3 ^ 40 * 3889948 * 2
def baseEnd_3889948 : Nat := 1997413044995851794260461

theorem tailTrace_3889948 : CollatzResearch.WordTrace tailWord_3889948 prefixEnd_3889948 1997413044995851794260461 := by
  unfold tailWord_3889948
  simp only [CollatzResearch.WordTrace]
  refine ⟨70939029655695110535943249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94585372874260147381257665 70939029655695110535943249)
  ·
    refine ⟨53204272241771332901957437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70939029655695110535943249 53204272241771332901957437)
    ·
      refine ⟨19951602090664249838234039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53204272241771332901957437 19951602090664249838234039)
      ·
        refine ⟨29927403135996374757351059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19951602090664249838234039 29927403135996374757351059)
        ·
          refine ⟨44891104703994562136026589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29927403135996374757351059 44891104703994562136026589)
          ·
            refine ⟨16834164263997960801009971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44891104703994562136026589 16834164263997960801009971)
            ·
              refine ⟨25251246395996941201514957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16834164263997960801009971 25251246395996941201514957)
              ·
                refine ⟨9469217398498852950568109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25251246395996941201514957 9469217398498852950568109)
                ·
                  refine ⟨3550956524437069856463041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9469217398498852950568109 3550956524437069856463041)
                  ·
                    refine ⟨2663217393327802392347281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3550956524437069856463041 2663217393327802392347281)
                    ·
                      refine ⟨1997413044995851794260461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2663217393327802392347281 1997413044995851794260461)
                      ·
                        rfl

theorem cell23_3889948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 1, 3, 3, 2, 2].length) (baseStart_3889948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3889948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3889948 prefixEnd_3889948 := by exact prefixLift 3889948
  have htrace : WordTrace (prefixWord ++ tailWord_3889948) baseStart_3889948 baseEnd_3889948 := by
    simpa [prefixWord, tailWord_3889948, baseEnd_3889948] using wordTrace_append hprefix tailTrace_3889948
  have hstable : (prefixWord ++ tailWord_3889948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3889948).length < 2 ^ (prefixWord ++ tailWord_3889948).sum := by decide
  have hdescent : baseEnd_3889948 < baseStart_3889948 := by decide
  rcases family_descends (prefixWord ++ tailWord_3889948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3889971 : List Nat := [1, 1, 1, 2, 6, 3, 2, 7]
def baseStart_3889971 : Nat := 118140960795 + 3889971 * 2 ^ 59
def prefixEnd_3889971 : Nat := 4983230072969 + 3 ^ 40 * 3889971 * 2
def baseEnd_3889971 : Nat := 73978698335218711269365

theorem tailTrace_3889971 : CollatzResearch.WordTrace tailWord_3889971 prefixEnd_3889971 73978698335218711269365 := by
  unfold tailWord_3889971
  simp only [CollatzResearch.WordTrace]
  refine ⟨141878898190306895999973767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94585932126871263999982511 141878898190306895999973767)
  ·
    refine ⟨212818347285460343999960651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141878898190306895999973767 212818347285460343999960651)
    ·
      refine ⟨319227520928190515999940977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212818347285460343999960651 319227520928190515999940977)
      ·
        refine ⟨239420640696142886999955733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 319227520928190515999940977 239420640696142886999955733)
        ·
          refine ⟨11222842532631697828122925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 239420640696142886999955733 11222842532631697828122925)
          ·
            refine ⟨4208565949736886685546097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11222842532631697828122925 4208565949736886685546097)
            ·
              refine ⟨3156424462302665014159573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4208565949736886685546097 3156424462302665014159573)
              ·
                refine ⟨73978698335218711269365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3156424462302665014159573 73978698335218711269365)
                ·
                  rfl

theorem cell23_3889971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 3, 2, 7].length) (baseStart_3889971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3889971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3889971 prefixEnd_3889971 := by exact prefixLift 3889971
  have htrace : WordTrace (prefixWord ++ tailWord_3889971) baseStart_3889971 baseEnd_3889971 := by
    simpa [prefixWord, tailWord_3889971, baseEnd_3889971] using wordTrace_append hprefix tailTrace_3889971
  have hstable : (prefixWord ++ tailWord_3889971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3889971).length < 2 ^ (prefixWord ++ tailWord_3889971).sum := by decide
  have hdescent : baseEnd_3889971 < baseStart_3889971 := by decide
  rcases family_descends (prefixWord ++ tailWord_3889971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3889988 : List Nat := [2, 3, 4, 2, 1, 2, 9]
def baseStart_3889988 : Nat := 118140960795 + 3889988 * 2 ^ 59
def prefixEnd_3889988 : Nat := 4983230072969 + 3 ^ 40 * 3889988 * 2
def baseEnd_3889988 : Nat := 24659673879284341206917

theorem tailTrace_3889988 : CollatzResearch.WordTrace tailWord_3889988 prefixEnd_3889988 24659673879284341206917 := by
  unfold tailWord_3889988
  simp only [CollatzResearch.WordTrace]
  refine ⟨70939759115622653951671309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94586345487496871935561745 70939759115622653951671309)
  ·
    refine ⟨26602409668358495231876741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70939759115622653951671309 26602409668358495231876741)
    ·
      refine ⟨4987951812817217855976889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26602409668358495231876741 4987951812817217855976889)
      ·
        refine ⟨3740963859612913391982667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4987951812817217855976889 3740963859612913391982667)
        ·
          refine ⟨5611445789419370087974001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3740963859612913391982667 5611445789419370087974001)
          ·
            refine ⟨4208584342064527565980501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5611445789419370087974001 4208584342064527565980501)
            ·
              refine ⟨24659673879284341206917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4208584342064527565980501 24659673879284341206917)
              ·
                rfl

theorem cell23_3889988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 2, 9].length) (baseStart_3889988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3889988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3889988 prefixEnd_3889988 := by exact prefixLift 3889988
  have htrace : WordTrace (prefixWord ++ tailWord_3889988) baseStart_3889988 baseEnd_3889988 := by
    simpa [prefixWord, tailWord_3889988, baseEnd_3889988] using wordTrace_append hprefix tailTrace_3889988
  have hstable : (prefixWord ++ tailWord_3889988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3889988).length < 2 ^ (prefixWord ++ tailWord_3889988).sum := by decide
  have hdescent : baseEnd_3889988 < baseStart_3889988 := by decide
  rcases family_descends (prefixWord ++ tailWord_3889988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3889991 : List Nat := [1, 1, 4, 1, 2, 1, 1, 2, 5, 3, 2]
def baseStart_3889991 : Nat := 118140960795 + 3889991 * 2 ^ 59
def prefixEnd_3889991 : Nat := 4983230072969 + 3 ^ 40 * 3889991 * 2
def baseEnd_3889991 : Nat := 1997435124663995126022763

theorem tailTrace_3889991 : CollatzResearch.WordTrace tailWord_3889991 prefixEnd_3889991 1997435124663995126022763 := by
  unfold tailWord_3889991
  simp only [CollatzResearch.WordTrace]
  refine ⟨141879627650234439415701827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94586418433489626277134551 141879627650234439415701827)
  ·
    refine ⟨212819441475351659123552741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141879627650234439415701827 212819441475351659123552741)
    ·
      refine ⟨39903645276628436085666139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 212819441475351659123552741 39903645276628436085666139)
      ·
        refine ⟨59855467914942654128499209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39903645276628436085666139 59855467914942654128499209)
        ·
          refine ⟨44891600936206990596374407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59855467914942654128499209 44891600936206990596374407)
          ·
            refine ⟨67337401404310485894561611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44891600936206990596374407 67337401404310485894561611)
            ·
              refine ⟨101006102106465728841842417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67337401404310485894561611 101006102106465728841842417)
              ·
                refine ⟨75754576579849296631381813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 101006102106465728841842417 75754576579849296631381813)
                ·
                  refine ⟨7101991554360871559192045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 75754576579849296631381813 7101991554360871559192045)
                  ·
                    refine ⟨2663246832885326834697017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7101991554360871559192045 2663246832885326834697017)
                    ·
                      refine ⟨1997435124663995126022763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2663246832885326834697017 1997435124663995126022763)
                      ·
                        rfl

theorem cell23_3889991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 2, 5, 3, 2].length) (baseStart_3889991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3889991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3889991 prefixEnd_3889991 := by exact prefixLift 3889991
  have htrace : WordTrace (prefixWord ++ tailWord_3889991) baseStart_3889991 baseEnd_3889991 := by
    simpa [prefixWord, tailWord_3889991, baseEnd_3889991] using wordTrace_append hprefix tailTrace_3889991
  have hstable : (prefixWord ++ tailWord_3889991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3889991).length < 2 ^ (prefixWord ++ tailWord_3889991).sum := by decide
  have hdescent : baseEnd_3889991 < baseStart_3889991 := by decide
  rcases family_descends (prefixWord ++ tailWord_3889991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3890050 : List Nat := [3, 4, 2, 2, 2, 1, 2, 2, 1, 2, 2]
def baseStart_3890050 : Nat := 118140960795 + 3890050 * 2 ^ 59
def prefixEnd_3890050 : Nat := 4983230072969 + 3 ^ 40 * 3890050 * 2
def baseEnd_3890050 : Nat := 1997465420022610395184993

theorem tailTrace_3890050 : CollatzResearch.WordTrace tailWord_3890050 prefixEnd_3890050 1997465420022610395184993 := by
  unfold tailWord_3890050
  simp only [CollatzResearch.WordTrace]
  refine ⟨35470444889255173123024901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94587853038013794994733069 35470444889255173123024901)
  ·
    refine ⟨6650708416735344960567169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35470444889255173123024901 6650708416735344960567169)
    ·
      refine ⟨4988031312551508720425377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6650708416735344960567169 4988031312551508720425377)
      ·
        refine ⟨3741023484413631540319033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4988031312551508720425377 3741023484413631540319033)
        ·
          refine ⟨2805767613310223655239275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3741023484413631540319033 2805767613310223655239275)
          ·
            refine ⟨4208651419965335482858913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2805767613310223655239275 4208651419965335482858913)
            ·
              refine ⟨3156488564974001612144185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4208651419965335482858913 3156488564974001612144185)
              ·
                refine ⟨2367366423730501209108139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3156488564974001612144185 2367366423730501209108139)
                ·
                  refine ⟨3551049635595751813662209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2367366423730501209108139 3551049635595751813662209)
                  ·
                    refine ⟨2663287226696813860246657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3551049635595751813662209 2663287226696813860246657)
                    ·
                      refine ⟨1997465420022610395184993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2663287226696813860246657 1997465420022610395184993)
                      ·
                        rfl

theorem cell23_3890050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 2, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 2, 1, 2, 2, 1, 2, 2].length) (baseStart_3890050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3890050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3890050 prefixEnd_3890050 := by exact prefixLift 3890050
  have htrace : WordTrace (prefixWord ++ tailWord_3890050) baseStart_3890050 baseEnd_3890050 := by
    simpa [prefixWord, tailWord_3890050, baseEnd_3890050] using wordTrace_append hprefix tailTrace_3890050
  have hstable : (prefixWord ++ tailWord_3890050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3890050).length < 2 ^ (prefixWord ++ tailWord_3890050).sum := by decide
  have hdescent : baseEnd_3890050 < baseStart_3890050 := by decide
  rcases family_descends (prefixWord ++ tailWord_3890050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3890055 : List Nat := [1, 1, 4, 2, 3, 1, 1, 4, 2, 2, 2]
def baseStart_3890055 : Nat := 118140960795 + 3890055 * 2 ^ 59
def prefixEnd_3890055 : Nat := 4983230072969 + 3 ^ 40 * 3890055 * 2
def baseEnd_3890055 : Nat := 1997467987425882875622469

theorem tailTrace_3890055 : CollatzResearch.WordTrace tailWord_3890055 prefixEnd_3890055 1997467987425882875622469 := by
  unfold tailWord_3890055
  simp only [CollatzResearch.WordTrace]
  refine ⟨141881961922002578346031619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94587974614668385564021079 141881961922002578346031619)
  ·
    refine ⟨212822942883003867519047429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141881961922002578346031619 212822942883003867519047429)
    ·
      refine ⟨39904301790563225159821393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 212822942883003867519047429 39904301790563225159821393)
      ·
        refine ⟨29928226342922418869866045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39904301790563225159821393 29928226342922418869866045)
        ·
          refine ⟨11223084878595907076199767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29928226342922418869866045 11223084878595907076199767)
          ·
            refine ⟨16834627317893860614299651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11223084878595907076199767 16834627317893860614299651)
            ·
              refine ⟨25251940976840790921449477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16834627317893860614299651 25251940976840790921449477)
              ·
                refine ⟨4734738933157648297771777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25251940976840790921449477 4734738933157648297771777)
                ·
                  refine ⟨3551054199868236223328833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4734738933157648297771777 3551054199868236223328833)
                  ·
                    refine ⟨2663290649901177167496625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3551054199868236223328833 2663290649901177167496625)
                    ·
                      refine ⟨1997467987425882875622469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2663290649901177167496625 1997467987425882875622469)
                      ·
                        rfl

theorem cell23_3890055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 1, 4, 2, 2, 2].length) (baseStart_3890055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3890055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3890055 prefixEnd_3890055 := by exact prefixLift 3890055
  have htrace : WordTrace (prefixWord ++ tailWord_3890055) baseStart_3890055 baseEnd_3890055 := by
    simpa [prefixWord, tailWord_3890055, baseEnd_3890055] using wordTrace_append hprefix tailTrace_3890055
  have hstable : (prefixWord ++ tailWord_3890055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3890055).length < 2 ^ (prefixWord ++ tailWord_3890055).sum := by decide
  have hdescent : baseEnd_3890055 < baseStart_3890055 := by decide
  rcases family_descends (prefixWord ++ tailWord_3890055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
